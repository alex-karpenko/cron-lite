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

static KEY_SERIAL: AtomicU16 = AtomicU16::new(0);

/// Represents a kind of the async cron event returned by [`CronWaiter`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CronEvent {
    /// Event happened in time.
    Ok,
    /// This event was missed and happened with delay.
    Missed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum WaiterState {
    Created,
    Pushed,
    Finished,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
struct WaiterKey {
    until: Instant,
    serial: Serial,
}

#[derive(Debug, Clone)]
enum ControlCmd {
    Insert { key: WaiterKey, waker: Waker },
    Remove { key: WaiterKey },
}

/// Sleep future state
#[derive(Debug, Clone)]
pub struct CronWaiter {
    key: WaiterKey,
    tx: ControlChannel,
    state: WaiterState,
}

impl CronWaiter {
    fn new(until: Instant) -> Self {
        Self {
            key: WaiterKey {
                until,
                serial: KEY_SERIAL.fetch_add(1, Ordering::SeqCst),
            },
            tx: sleep_thread_tx().clone(),
            state: WaiterState::Created,
        }
    }

    #[inline]
    fn send_cmd(&self, cmd: ControlCmd) {
        self.tx.send(cmd).expect("sleep control channel is closed");
    }

    #[inline]
    fn is_elapsed(&self) -> bool {
        Instant::now() >= self.key.until
    }
}

impl Future for CronWaiter {
    type Output = CronEvent;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.is_elapsed() {
            let event = if self.state == WaiterState::Pushed {
                self.send_cmd(ControlCmd::Remove { key: self.key });
                CronEvent::Ok
            } else {
                CronEvent::Missed
            };

            self.state = WaiterState::Finished;
            Poll::Ready(event)
        } else {
            if self.state != WaiterState::Finished {
                let waker = cx.waker().clone();
                self.send_cmd(ControlCmd::Insert { key: self.key, waker });
                self.state = WaiterState::Pushed;
            }
            Poll::Pending
        }
    }
}

impl Unpin for CronWaiter {}

impl FusedFuture for CronWaiter {
    #[inline]
    fn is_terminated(&self) -> bool {
        self.state == WaiterState::Finished
    }
}

impl Drop for CronWaiter {
    #[inline]
    fn drop(&mut self) {
        if self.state == WaiterState::Pushed {
            self.send_cmd(ControlCmd::Remove { key: self.key });
        }
        self.state = WaiterState::Finished;
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum StreamState {
    Idle,
    Waiting(WaiterKey),
    Completed,
}

/// Implements `Stream` trait and generates stream of [`CronEvent`].
/// It sleeps until upcoming scheduled event time and returns just in time of planned event.
#[pin_project(PinnedDrop)]
#[derive(Debug, Clone)]
pub struct CronStream<Tz: TimeZone> {
    state: StreamState,
    iter: ScheduleIterator<Tz>,
    tx: ControlChannel,
}

impl<Tz: TimeZone> CronStream<Tz> {
    #[inline]
    fn new(iter: ScheduleIterator<Tz>) -> Self {
        Self {
            state: StreamState::Idle,
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
        match self.state {
            StreamState::Idle => {
                // No active events in queue
                // Try to push next one
                if let Some(next) = self.iter.next() {
                    if let Some(until) = next_instant(Utc::now().timestamp_nanos_opt().unwrap(), &next) {
                        // Got valid event, push it to the waiter thread
                        let key = WaiterKey {
                            until,
                            serial: KEY_SERIAL.fetch_add(1, Ordering::SeqCst),
                        };
                        self.send_cmd(ControlCmd::Insert {
                            key,
                            waker: cx.waker().clone(),
                        });
                        self.state = StreamState::Waiting(key);
                        Poll::Pending
                    } else {
                        // We had an event but it's already in the past
                        Poll::Ready(Some(CronEvent::Missed))
                    }
                } else {
                    // Iterator is gone, so finish stream
                    self.state = StreamState::Completed;
                    Poll::Ready(None)
                }
            }
            StreamState::Waiting(key) => {
                if key.until > Instant::now() {
                    // Still waiting, so refresh waker
                    self.send_cmd(ControlCmd::Insert {
                        key,
                        waker: cx.waker().clone(),
                    });
                    Poll::Pending
                } else {
                    // Expected time is arrived
                    self.send_cmd(ControlCmd::Remove { key });
                    self.state = StreamState::Idle;
                    Poll::Ready(Some(CronEvent::Ok))
                }
            }
            StreamState::Completed => Poll::Ready(None),
        }
    }
}

impl<Tz: TimeZone> FusedStream for CronStream<Tz> {
    #[inline]
    fn is_terminated(&self) -> bool {
        self.state == StreamState::Completed
    }
}

#[pinned_drop]
impl<Tz: TimeZone> PinnedDrop for CronStream<Tz> {
    fn drop(mut self: Pin<&mut Self>) {
        if let StreamState::Waiting(key) = self.state {
            self.send_cmd(ControlCmd::Remove { key });
        }
        self.state = StreamState::Completed;
    }
}

fn sleep_thread_tx() -> &'static ControlChannel {
    static SLEEP_THREAD: OnceLock<Sender<ControlCmd>> = OnceLock::new();

    SLEEP_THREAD.get_or_init(|| {
        let (tx, rx) = mpsc::channel::<ControlCmd>();
        thread::spawn(move || {
            let mut sleep_map: BTreeMap<WaiterKey, Waker> = BTreeMap::new();
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
    fn upcoming_instant<Tz: TimeZone>(&self, current: &DateTime<Tz>) -> Option<Instant> {
        let next = self.upcoming(current)?;
        let now_nanos = current.timestamp_nanos_opt()?;
        next_instant(now_nanos, &next)
    }

    /// Returns [`CronWaiter`] which implements [`Future`](). It becomes asleep until next upcoming event happened.
    pub fn wait_upcoming<Tz: TimeZone>(&self, current: &DateTime<Tz>) -> Option<CronWaiter> {
        let until = self.upcoming_instant(current)?;
        let waiter = CronWaiter::new(until);
        Some(waiter)
    }

    /// q
    pub fn stream<Tz: TimeZone>(&self, current: &DateTime<Tz>) -> CronStream<Tz> {
        let iter = ScheduleIterator {
            schedule: self.clone(),
            next: self.upcoming(current),
        };
        CronStream::new(iter)
    }

    /// q
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
    use chrono_tz::Europe::Kyiv;
    use futures::StreamExt;
    use rstest::rstest;

    const ACCEPTED_DRIFT: Duration = Duration::from_millis(2);

    fn test_upcoming_instant_case<T: TimeZone>(schedule: &str, current: DateTime<T>, expected_delta: Duration) {
        let schedule = Schedule::try_from(schedule).unwrap();
        let instant = schedule.upcoming_instant(&current).unwrap();
        let delta = instant - Instant::now();
        assert!(
            delta <= expected_delta,
            "sleeps too long: delta={delta:?}, expected={expected_delta:?}"
        );
        assert!(
            delta >= expected_delta - ACCEPTED_DRIFT,
            "drift is out of range: delta={delta:?}, expected={expected_delta:?}"
        );
    }

    #[rstest]
    #[case("*/2 * * * * * 2024", "2025-01-01T00:00:00.001Z")]
    #[case("* * * 29 2 * 2025", "2024-12-31T23:59:59Z")]
    fn test_upcoming_instant_unschedulable(#[case] schedule: &str, #[case] current: &str) {
        let current = DateTime::parse_from_rfc3339(current).unwrap();
        let schedule = Schedule::try_from(schedule).unwrap();
        let instant = schedule.upcoming_instant(&current);
        assert!(instant.is_none(), "instant={instant:?}");
    }

    #[test]
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
    fn test_upcoming_instant_with_both_tz<T: TimeZone>(
        #[case] schedule: &str,
        #[case] current: DateTime<T>,
        #[case] expected_delta: Duration,
    ) {
        test_upcoming_instant_case(schedule, current, expected_delta)
    }

    #[tokio::test]
    async fn test_wait_upcoming_ok() {
        let schedule = Schedule::try_from("*/2 * * * * *").unwrap();
        let now = Utc::now();
        let res = schedule.wait_upcoming(&now).unwrap().await;
        assert_eq!(res, CronEvent::Ok);
    }

    #[tokio::test]
    async fn test_wait_upcoming_missed() {
        let schedule = Schedule::try_from("*/2 * * * * *").unwrap();
        let now = Utc::now();
        let waiter = schedule.wait_upcoming(&now).unwrap();
        tokio::time::sleep(Duration::from_millis(2100)).await;
        assert_eq!(waiter.await, CronEvent::Missed);
    }

    #[tokio::test]
    async fn test_stream_with_order() {
        let schedule = Schedule::try_from("* * * * * *").unwrap();
        let now = Utc::now();
        let mut stream = schedule.stream(&now);

        assert_eq!(stream.next().await, Some(CronEvent::Ok));
        assert_eq!(stream.next().await, Some(CronEvent::Ok));
        assert_eq!(stream.next().await, Some(CronEvent::Ok));
    }
}
