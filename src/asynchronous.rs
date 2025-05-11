use crate::{schedule::ScheduleIterator, Schedule};
use chrono::{DateTime, TimeZone, Utc};
use futures::{future::FusedFuture, stream::FusedStream, Stream};
use pin_project::{pin_project, pinned_drop};
use std::{
    collections::BTreeMap,
    future::Future,
    pin::Pin,
    sync::{
        atomic::{AtomicU16, Ordering},
        mpsc::{self, RecvTimeoutError, Sender},
        OnceLock,
    },
    task::{Context, Poll, Waker},
    thread,
    time::{Duration, Instant},
};

type Serial = u16;
type ControlChannel = Sender<ControlCmd>;

/// Represents a kind (character) of the async cron event returned by [`CronSleep`] or [`CronStream`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub enum CronEvent {
    /// The event happened in time.
    Ok,
    /// The event was missed and happened after it's scheduled time.
    Missed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum FutureState {
    Idle,
    Waiting(SleepQueueKey),
    Completed,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
struct SleepQueueKey {
    until: Instant,
    serial: Serial,
}

impl SleepQueueKey {
    #[inline]
    fn new(until: Instant) -> Self {
        static KEY_SERIAL: AtomicU16 = AtomicU16::new(0);

        Self {
            until,
            serial: KEY_SERIAL.fetch_add(1, Ordering::Relaxed),
        }
    }
}

#[derive(Debug, Clone)]
enum ControlCmd {
    Insert { key: SleepQueueKey, waker: Waker },
    Remove { key: SleepQueueKey },
}

/// Implements [`Future`](https://doc.rust-lang.org/core/future/trait.Future.html)
/// which sleeps until the upcoming scheduled event.
///
/// When awaited, it returns an instance of the [`CronEvent`],
/// which represents a kind of the happened event - in time or missed.
///
/// May panic if the background thread (which controls all sleep and stream events) fails.
///
/// Be aware that the precision of the time when events happen is not perfect
/// due to the nature of the asynchronous Rust implementation and
/// possible aspects of the specific async runtime.
/// So events may occur a few (1-5) milliseconds sooner or later, this is expected and
/// normal.
///
/// # Examples:
/// ```rust
/// use chrono::{Local, Utc};
/// use cron_lite::{CronEvent, Schedule, Result};
/// use std::time::Duration;
///
/// #[tokio::main]
/// async fn main() -> Result<()> {
///     let schedule = Schedule::new("*/2 * * * * *")?;
///
///     // Wakes up on the next 2-second instant.
///     // This (first) event may be "Missed" if "now" is exactly at the 2-second-slice.
///     let event = schedule.sleep(&Local::now()).unwrap().await;
///
///     // But the next one happens definitely in time
///     let sleep = schedule.sleep(&Local::now()).unwrap();
///     assert_eq!(sleep.await, CronEvent::Ok);
///
///     // In case we spent too much time between creating and awaiting
///     // of the CronSleep instance, we can "oversleep" scheduled event and
///     // get "Missed" one.
///     let sleep = schedule.sleep(&Utc::now()).unwrap();
///     tokio::time::sleep(Duration::from_secs(3)).await;
///     assert_eq!(sleep.await, CronEvent::Missed);
///
///     Ok(())
/// }
/// ```
#[derive(Debug, Clone)]
pub struct CronSleep {
    until: Instant,
    tx: ControlChannel,
    state: FutureState,
    returned: Option<CronEvent>,
}

impl CronSleep {
    fn new(until: Instant) -> Self {
        Self {
            until,
            tx: sleep_thread_tx().clone(),
            state: FutureState::Idle,
            returned: Some(CronEvent::Ok),
        }
    }

    #[inline]
    fn send_cmd(&self, cmd: ControlCmd) {
        self.tx.send(cmd).expect("sleep control channel is closed");
    }

    #[inline]
    fn finish(&mut self, event: CronEvent) -> Poll<CronEvent> {
        self.state = FutureState::Completed;
        self.returned = Some(event);

        Poll::Ready(event)
    }
}

impl Future for CronSleep {
    type Output = CronEvent;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let now_inst = Instant::now();
        match self.state {
            FutureState::Idle => {
                // It wasn't started yet
                if now_inst >= self.until {
                    // But it's already missed
                    self.finish(CronEvent::Missed)
                } else {
                    // If not missed - push it to the sleep thread
                    let waker = cx.waker().clone();
                    let key = SleepQueueKey::new(self.until);
                    self.send_cmd(ControlCmd::Insert { key, waker });
                    self.state = FutureState::Waiting(key);
                    Poll::Pending
                }
            }
            FutureState::Waiting(key) => {
                // Already running in the sleep thread
                if now_inst >= self.until {
                    // And finished in time
                    self.send_cmd(ControlCmd::Remove { key });
                    self.finish(CronEvent::Ok)
                } else {
                    // Or not finished yet, so refresh the Waker instance in the sleep thread
                    self.send_cmd(ControlCmd::Insert {
                        key,
                        waker: cx.waker().clone(),
                    });
                    Poll::Pending
                }
            }
            // Theoretically, this branch is unreachable if you use a valid async runtime,
            // but to protect form invalid ones, we return the last actual returned value.
            FutureState::Completed => Poll::Ready(self.returned.expect("unexpected call to poll, looks like a BUG!")),
        }
    }
}

impl FusedFuture for CronSleep {
    #[inline]
    fn is_terminated(&self) -> bool {
        self.state == FutureState::Completed
    }
}

impl Drop for CronSleep {
    #[inline]
    fn drop(&mut self) {
        if let FutureState::Waiting(key) = self.state {
            self.send_cmd(ControlCmd::Remove { key });
        }
        self.state = FutureState::Completed;
    }
}

/// Implements [`Stream`](https://docs.rs/futures/latest/futures/stream/index.html)
/// that generate stream of [`CronEvent`] based on the schedule.
///
/// It sleeps until the time of the upcoming scheduled event
/// and returns the next value (event) just in time of the schedule.
///
/// If an interval between consecutive calls to the stream is longer
/// than an interval of the scheduled events, it returns [`CronEvent::Missed`];
/// that means the scheduled event happened in the past.
///
/// May panic if the background thread (which controls all sleep and stream events) fails.
///
/// Be aware that the precision of the time when events happen is not perfect
/// due to the nature of the asynchronous Rust implementation and
/// possible aspects of the specific async runtime.
/// So events may occur a few (1-5) milliseconds sooner or later, this is expected and
/// normal.
///
/// # Examples:
/// ```rust
/// use chrono::Local;
/// use cron_lite::{CronEvent, Schedule, Result};
/// use futures::stream::StreamExt;
/// use std::time::Instant;
///
/// #[tokio::main]
/// async fn main() -> Result<()> {
///     let schedule = Schedule::new("*/2 * * * * *")?;
///
///     // Create a stream of three events starting from the 2nd one.
///     let mut stream = schedule.into_stream(&Local::now()).skip(1).take(3);
///     let start = Instant::now();
///
///     while let Some(event) = stream.next().await {
///         assert_eq!(event, CronEvent::Ok);
///         println!("Elapsed: {:?}", start.elapsed());
///     }
///
///     Ok(())
/// }
/// ```
#[pin_project(PinnedDrop)]
#[derive(Debug, Clone)]
pub struct CronStream<Tz: TimeZone> {
    state: FutureState,
    iter: ScheduleIterator<Tz>,
    tx: ControlChannel,
}

impl<Tz: TimeZone> CronStream<Tz> {
    #[inline]
    fn new(iter: ScheduleIterator<Tz>) -> Self {
        Self {
            state: FutureState::Idle,
            tx: sleep_thread_tx().clone(),
            iter,
        }
    }

    #[inline]
    fn send_cmd(&self, cmd: ControlCmd) {
        self.tx.send(cmd).expect("sleep control channel is closed");
    }
}

impl<Tz: TimeZone> Stream for CronStream<Tz> {
    type Item = CronEvent;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let now_nanos = Utc::now().timestamp_nanos_opt().unwrap();
        let now_inst = Instant::now();
        match self.state {
            FutureState::Idle => {
                // No active events in the queue
                // Try to push the next one
                if let Some(next) = self.iter.next() {
                    // And if we have a next event
                    if let Some(until) = next_instant(now_nanos, &next) {
                        // And it's not a past (missed) event, then push it to the sleep thread
                        let key = SleepQueueKey::new(until);
                        self.send_cmd(ControlCmd::Insert {
                            key,
                            waker: cx.waker().clone(),
                        });
                        self.state = FutureState::Waiting(key);
                        Poll::Pending
                    } else {
                        // We got an event, but it's already in the past
                        Poll::Ready(Some(CronEvent::Missed))
                    }
                } else {
                    // The iterator is gone, so we finish the stream
                    self.state = FutureState::Completed;
                    Poll::Ready(None)
                }
            }
            FutureState::Waiting(key) => {
                if key.until > now_inst {
                    // Still waiting, so refresh Waker
                    self.send_cmd(ControlCmd::Insert {
                        key,
                        waker: cx.waker().clone(),
                    });
                    Poll::Pending
                } else {
                    // The expected time of this particular event was arrived
                    self.send_cmd(ControlCmd::Remove { key });
                    self.state = FutureState::Idle;
                    Poll::Ready(Some(CronEvent::Ok))
                }
            }
            // Theoretically, this branch is unreachable.
            // But in case of an invalid runtime call to a completed stream,
            // we return the "end-of-stream" value.
            FutureState::Completed => Poll::Ready(None),
        }
    }
}

impl<Tz: TimeZone> FusedStream for CronStream<Tz> {
    #[inline]
    fn is_terminated(&self) -> bool {
        self.state == FutureState::Completed
    }
}

#[pinned_drop]
impl<Tz: TimeZone> PinnedDrop for CronStream<Tz> {
    fn drop(mut self: Pin<&mut Self>) {
        if let FutureState::Waiting(key) = self.state {
            self.send_cmd(ControlCmd::Remove { key });
        }
        self.state = FutureState::Completed;
    }
}

// We use the single thread to watch all CronSleep and CronStream events.
//
// Use BTreeMap to store all upcoming events (their wake-up Instant values) in order of
// time to wake. This thread is very cheap because it sleeps almost all the time.
//
// To communicate between CronSleep/CronStream mpcs channel is used.
//
// To communicate with runtime, each map value contains its corresponding Waker instance and wakes its Future
// when "thread::sleep" completes and starts the next sleep in the queue after that.
fn sleep_thread_tx() -> &'static ControlChannel {
    static SLEEP_THREAD: OnceLock<Sender<ControlCmd>> = OnceLock::new();

    SLEEP_THREAD.get_or_init(|| {
        let (tx, rx) = mpsc::channel::<ControlCmd>();
        thread::spawn(move || {
            let mut sleep_map: BTreeMap<SleepQueueKey, Waker> = BTreeMap::new();
            let control_rx = rx;

            loop {
                let cmd = if sleep_map.is_empty() {
                    control_rx.recv().expect("sleep control channel is closed")
                } else {
                    let (first, _) = sleep_map.first_key_value().unwrap();
                    let time_to_sleep = first.until.saturating_duration_since(Instant::now());

                    match control_rx.recv_timeout(time_to_sleep) {
                        Ok(cmd) => cmd,
                        Err(RecvTimeoutError::Timeout) => {
                            let (_, waker) = sleep_map.pop_first().unwrap();
                            waker.wake();
                            continue;
                        }
                        Err(e) => panic!("sleep control channel is closed: {e}"),
                    }
                };

                match cmd {
                    ControlCmd::Insert { key, waker } => {
                        sleep_map.insert(key, waker);
                    }
                    ControlCmd::Remove { key } => {
                        sleep_map.remove(&key);
                    }
                }
            }
        });

        tx
    })
}

// Returns Instant of the next event based on provided raw "now"
fn next_instant<Tz: TimeZone>(now_nanos: i64, next: &DateTime<Tz>) -> Option<Instant> {
    let now_inst = Instant::now();
    let until_nanos = next.timestamp_nanos_opt()?;
    let delta = until_nanos - now_nanos;

    if delta < 0 {
        None
    } else {
        Some(now_inst + Duration::from_nanos(delta as u64))
    }
}

impl Schedule {
    // Returns Instant of the upcoming event based on the provided current DateTime
    fn upcoming_instant<Tz: TimeZone>(&self, current: &DateTime<Tz>) -> Option<Instant> {
        let next = self.upcoming(current)?;
        let now_nanos = current.timestamp_nanos_opt()?;
        next_instant(now_nanos, &next)
    }

    /// Returns [`CronSleep`] instance (wrapped into the `Option`) which implements
    /// [`Future`](https://doc.rust-lang.org/core/future/trait.Future.html).
    /// This `Future` falls asleep until the next upcoming event happened.
    ///
    /// In case when the schedule has no upcoming events, it returns `None` immediately.
    ///
    /// See [`CronSleep`] for complete documentation with examples.
    pub fn sleep<Tz: TimeZone>(&self, current: &DateTime<Tz>) -> Option<CronSleep> {
        let until = self.upcoming_instant(current)?;
        let sleep = CronSleep::new(until);
        Some(sleep)
    }

    /// Returns [`CronStream`] instance which implements
    /// [`Stream`](https://docs.rs/futures/latest/futures/stream/index.html)
    /// as an asynchronous generator of the consecutive scheduled events.
    ///
    /// See [`CronStream`] for complete documentation with examples.
    pub fn stream<Tz: TimeZone>(&self, current: &DateTime<Tz>) -> CronStream<Tz> {
        let iter = ScheduleIterator {
            schedule: self.clone(),
            next: self.upcoming(current),
        };
        CronStream::new(iter)
    }

    /// The same as [`Schedule::stream()`] but consumes its `Schedule`.
    pub fn into_stream<Tz: TimeZone>(self, current: &DateTime<Tz>) -> CronStream<Tz> {
        let next = self.upcoming(current);
        let iter = ScheduleIterator { schedule: self, next };
        CronStream::new(iter)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use chrono::Utc;
    #[cfg(feature = "tz")]
    use chrono_tz::Europe::Kyiv;
    use futures::{select, StreamExt};
    use rstest::rstest;

    const ACCEPTED_SLEEP_DRIFT: Duration = Duration::from_millis(2);
    const ACCEPTED_STREAM_DRIFT: Duration = Duration::from_millis(5);

    fn test_upcoming_instant_case<T: TimeZone>(schedule: &str, current: DateTime<T>, expected_delta: Duration) {
        let schedule = Schedule::try_from(schedule).unwrap();
        let instant = schedule.upcoming_instant(&current).unwrap();
        let delta = instant - Instant::now();
        assert!(
            delta <= expected_delta,
            "sleeps too long: delta={delta:?}, expected={expected_delta:?}"
        );
        assert!(
            delta >= expected_delta - ACCEPTED_SLEEP_DRIFT,
            "drift is out of range: delta={delta:?}, expected={expected_delta:?}"
        );
    }

    #[rstest]
    #[case("*/2 * * * * * 2024", "2025-01-01T00:00:00.001Z")]
    #[case("* * * 29 2 * 2025", "2024-12-31T23:59:59Z")]
    #[timeout(Duration::from_secs(3))]
    fn test_upcoming_instant_unschedulable(#[case] schedule: &str, #[case] current: &str) {
        let current = DateTime::parse_from_rfc3339(current).unwrap();
        let schedule = Schedule::try_from(schedule).unwrap();
        let instant = schedule.upcoming_instant(&current);
        assert!(instant.is_none(), "instant={instant:?}");
    }

    #[rstest]
    #[timeout(Duration::from_secs(3))]
    fn test_next_instant_unschedulable() {
        let now = (Utc::now() + Duration::from_secs(10)).timestamp_nanos_opt().unwrap();
        let next = Utc::now();
        let instant = next_instant(now, &next);
        assert!(instant.is_none(), "instant={instant:?}");
    }

    #[rstest]
    #[case("*/2 * * * * *", "2025-01-01T00:00:00.001Z", Duration::from_millis(2000))]
    #[case("*/15 * * * * *", "2024-12-31T23:59:59Z", Duration::from_millis(1000))]
    #[case("*/15 * * * * *", "2024-12-31T23:59:45.001Z", Duration::from_millis(14999))]
    #[case("1 5 * * *", "2024-01-01T23:59:59.999+05:00", Duration::from_secs(5*3600+60)+Duration::from_millis(1))]
    #[timeout(Duration::from_secs(3))]
    fn test_upcoming_instant_without_tz(
        #[case] schedule: &str,
        #[case] current: &str,
        #[case] expected_delta: Duration,
    ) {
        let current = DateTime::parse_from_rfc3339(current).unwrap();
        test_upcoming_instant_case(schedule, current, expected_delta)
    }

    #[cfg(feature = "tz")]
    #[rstest]
    #[case(
        "TZ=Europe/Kyiv */2 * * * * *",
        "2025-01-01T00:00:00.001Z",
        Duration::from_millis(2000)
    )]
    #[case("TZ=Europe/Kyiv */15 * * * * *", "2024-12-31T23:59:59Z", Duration::from_millis(1000))]
    #[case(
        "TZ=Europe/Kyiv */15 * * * * *",
        "2024-12-31T23:59:45.001Z",
        Duration::from_millis(14999)
    )]
    #[case("TZ=UTC 1 5 * * *", "2025-03-30T02:59:59.999Z", Duration::from_secs(2*60*60 /*hours*/ + 60 /*minutes*/) + Duration::from_millis(1))]
    #[case("TZ=UTC 1 5 * * *", "2025-03-30T02:59:59.999+02:00", Duration::from_secs(4*60*60 /*hours*/ + 60 /*minutes*/) + Duration::from_millis(1))]
    #[case("TZ=Europe/Kyiv 1 5 * * *", "2025-03-30T02:59:59.999Z", Duration::from_secs(23*60*60 /*hours*/ + 60 /*minutes*/) + Duration::from_millis(1))]
    #[case("TZ=Europe/Kyiv 1 5 * * *", "2025-03-30T02:59:59.999+02:00", Duration::from_secs(60*60 /*hours*/ + 60 /*minutes*/) + Duration::from_millis(1))]
    #[case("TZ=Europe/Kyiv 1 3 * * *", "2025-03-30T02:59:59.999+02:00", Duration::from_secs(23*60*60 /*hours*/ + 60 /*minutes*/) + Duration::from_millis(1))]
    #[timeout(Duration::from_secs(3))]
    fn test_upcoming_instant_with_schedule_tz(
        #[case] schedule: &str,
        #[case] current: &str,
        #[case] expected_delta: Duration,
    ) {
        let current = DateTime::parse_from_rfc3339(current).unwrap();
        test_upcoming_instant_case(schedule, current, expected_delta)
    }

    #[cfg(feature = "tz")]
    #[rstest]
    #[case("TZ=Europe/Kyiv 1 5 * * *", Kyiv.with_ymd_and_hms(2025, 3, 30, 2, 59, 59).unwrap(), Duration::from_secs(60*60 /*hours*/ + 60 /*minutes*/ + 1))]
    #[case("TZ=UTC 1 5 * * *", Kyiv.with_ymd_and_hms(2025, 3, 30, 2, 59, 59).unwrap(), Duration::from_secs(4*60*60 /*hours*/ + 60 /*minutes*/ + 1))]
    #[case("TZ=Europe/Paris 1 5 * * *", Kyiv.with_ymd_and_hms(2025, 3, 30, 2, 59, 59).unwrap(), Duration::from_secs(2*60*60 /*hours*/ + 60 /*minutes*/ + 1))]
    #[case("TZ=Europe/Kyiv 1 5 * * *", Kyiv.with_ymd_and_hms(2025, 1, 1, 2, 59, 59).unwrap(), Duration::from_secs(2*60*60 /*hours*/ + 60 /*minutes*/ + 1))]
    #[case("TZ=UTC 1 5 * * *", Kyiv.with_ymd_and_hms(2025, 1, 1, 2, 59, 59).unwrap(), Duration::from_secs(4*60*60 /*hours*/ + 60 /*minutes*/ + 1))]
    #[case("TZ=Europe/Paris 1 5 * * *", Kyiv.with_ymd_and_hms(2025, 1, 1, 2, 59, 59).unwrap(), Duration::from_secs(3*60*60 /*hours*/ + 60 /*minutes*/ + 1))]
    #[timeout(Duration::from_secs(3))]
    fn test_upcoming_instant_with_both_tz<T: TimeZone>(
        #[case] schedule: &str,
        #[case] current: DateTime<T>,
        #[case] expected_delta: Duration,
    ) {
        test_upcoming_instant_case(schedule, current, expected_delta)
    }

    #[tokio::test]
    #[rstest]
    #[timeout(Duration::from_secs(3))]
    async fn test_sleep_ok() {
        let schedule = Schedule::try_from("*/2 * * * * *").unwrap();
        let now = Utc::now();
        let res = schedule.sleep(&now).unwrap().await;
        assert_eq!(res, CronEvent::Ok);
    }

    #[tokio::test]
    #[rstest]
    #[timeout(Duration::from_secs(3))]
    async fn test_sleep_missed() {
        let schedule = Schedule::try_from("*/2 * * * * *").unwrap();
        let now = Utc::now();
        let sleep = schedule.sleep(&now).unwrap();
        tokio::time::sleep(Duration::from_millis(2100)).await;
        assert_eq!(sleep.await, CronEvent::Missed);
    }

    #[tokio::test]
    #[rstest]
    #[timeout(Duration::from_secs(8))]
    async fn test_stream_with_order() {
        const INTERVAL: Duration = Duration::from_millis(2000);

        let schedule = Schedule::try_from("*/2 * * * * *").unwrap();
        let now = Utc::now();
        let mut stream = schedule.stream(&now);

        stream.next().await;
        let next = stream.next().await;
        let start = Instant::now();
        assert_eq!(next, Some(CronEvent::Ok));

        tokio::time::sleep(INTERVAL - Duration::from_millis(50)).await;
        let next = stream.next().await;
        let elapsed = start.elapsed();
        assert_eq!(next, Some(CronEvent::Ok));

        assert!(
            elapsed <= INTERVAL + ACCEPTED_STREAM_DRIFT,
            "sleeps too long: elapsed={elapsed:?}"
        );
        assert!(
            elapsed >= INTERVAL - ACCEPTED_STREAM_DRIFT,
            "drift is out of range: elapsed={elapsed:?}"
        );
    }

    #[tokio::test]
    #[rstest]
    #[timeout(Duration::from_secs(10))]
    async fn test_stream_with_delays() {
        let schedule = Schedule::try_from("* * * * * *").unwrap();
        let now = Utc::now();
        let mut stream = schedule.into_stream(&now);

        stream.next().await;
        tokio::time::sleep(Duration::from_millis(5500)).await;
        let mut missed = 0;

        while let Some(CronEvent::Missed) = stream.next().await {
            missed += 1;
        }

        assert_eq!(missed, 5);
        assert_eq!(stream.next().await, Some(CronEvent::Ok));
    }

    #[tokio::test]
    #[rstest]
    #[timeout(Duration::from_secs(3))]
    async fn test_stream_finish() {
        let schedule = Schedule::try_from("0 0 0 1 1 * 2024").unwrap();
        let now = Utc.with_ymd_and_hms(2023, 12, 31, 23, 23, 23).unwrap();
        let mut stream = schedule.stream(&now);

        assert_eq!(stream.next().await, Some(CronEvent::Missed));
        assert_eq!(stream.next().await, None);
    }

    #[tokio::test]
    #[rstest]
    #[timeout(Duration::from_secs(3))]
    async fn test_sleep_is_terminated() {
        let schedule = Schedule::try_from("* * * * * *").unwrap();
        let now = Utc::now();
        let mut test_sleep = schedule.sleep(&now).unwrap();
        assert!(!test_sleep.is_terminated());

        select! {
            _ = test_sleep => {
                assert_eq!(test_sleep.state, FutureState::Completed);
                assert!(test_sleep.is_terminated())
            },
            _ = futures::future::pending::<()>() => {
                unreachable!()
            },
        }

        assert!(test_sleep.is_terminated());
    }

    #[tokio::test]
    #[rstest]
    #[timeout(Duration::from_secs(3))]
    async fn test_streem_is_terminated() {
        let schedule = Schedule::try_from("0 0 0 1 1 * 2024").unwrap();
        let now = Utc.with_ymd_and_hms(2023, 12, 31, 23, 23, 23).unwrap();
        let mut test_stream = schedule.stream(&now);
        assert!(!test_stream.is_terminated());

        assert_eq!(test_stream.next().await, Some(CronEvent::Missed));
        assert!(!test_stream.is_terminated());

        assert_eq!(test_stream.next().await, None);
        assert!(test_stream.is_terminated());

        assert_eq!(test_stream.next().await, None);
        assert!(test_stream.is_terminated());
    }

    #[tokio::test]
    #[rstest]
    #[timeout(Duration::from_secs(7))]
    async fn test_streem_take() {
        let schedule = Schedule::try_from("* * * * * *").unwrap();
        let now = Utc::now();

        let test_stream = schedule.stream(&now).skip(1).take(5).collect::<Vec<_>>().await;

        assert_eq!(test_stream.len(), 5);
        assert!(test_stream.iter().all(|e| e == &CronEvent::Ok))
    }
}
