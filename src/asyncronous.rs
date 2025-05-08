use crate::Schedule;
use chrono::{DateTime, TimeZone};
use futures::future::FusedFuture;
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
enum FutureState {
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
    state: FutureState,
}

impl CronWaiter {
    fn new(until: Instant) -> Self {
        Self {
            key: WaiterKey {
                until,
                serial: KEY_SERIAL.fetch_add(1, Ordering::SeqCst),
            },
            tx: sleep_thread_tx().clone(),
            state: FutureState::Created,
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
            let event = if self.state == FutureState::Pushed {
                self.send_cmd(ControlCmd::Remove { key: self.key });
                CronEvent::Ok
            } else {
                CronEvent::Missed
            };

            self.state = FutureState::Finished;
            Poll::Ready(event)
        } else {
            if self.state != FutureState::Finished {
                let waker = cx.waker().clone();
                self.send_cmd(ControlCmd::Insert { key: self.key, waker });
                self.state = FutureState::Pushed;
            }
            Poll::Pending
        }
    }
}

impl Unpin for CronWaiter {}

impl FusedFuture for CronWaiter {
    #[inline]
    fn is_terminated(&self) -> bool {
        self.state == FutureState::Finished
    }
}

impl Drop for CronWaiter {
    #[inline]
    fn drop(&mut self) {
        if self.state == FutureState::Pushed {
            self.send_cmd(ControlCmd::Remove { key: self.key });
        }
        self.state = FutureState::Finished;
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

impl Schedule {
    fn upcoming_as_instant<Tz: TimeZone>(&self, current: &DateTime<Tz>) -> Option<Instant> {
        let upcoming = self.upcoming(current)?;

        let now_inst = Instant::now();
        let until_nano = upcoming.timestamp_nanos_opt()?;
        let now_nano = current.timestamp_nanos_opt()?;

        Some(now_inst + Duration::from_nanos((until_nano - now_nano) as u64))
    }

    /// Returns [`CronWaiter`] which implements [`Future`](). It becomes asleep until next upcoming event happened.
    pub fn wait_upcoming<Tz: TimeZone>(&self, current: &DateTime<Tz>) -> Option<CronWaiter> {
        let until = self.upcoming_as_instant(current)?;
        let waiter = CronWaiter::new(until);
        Some(waiter)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use chrono::Utc;
    use chrono_tz::Europe::Kyiv;
    use rstest::rstest;

    const ACCEPTED_DRIFT: Duration = Duration::from_millis(2);

    fn test_upcoming_as_instant_case<T: TimeZone>(schedule: &str, current: DateTime<T>, expected_delta: Duration) {
        let schedule = Schedule::try_from(schedule).unwrap();
        let instant = schedule.upcoming_as_instant(&current).unwrap();
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
    #[case("*/2 * * * * *", "2025-01-01T00:00:00.001Z", Duration::from_millis(2000))]
    #[case("*/15 * * * * *", "2024-12-31T23:59:59Z", Duration::from_millis(1000))]
    #[case("*/15 * * * * *", "2024-12-31T23:59:45.001Z", Duration::from_millis(14999))]
    #[case("1 5 * * *", "2024-01-01T23:59:59.999+05:00", Duration::from_secs(5*3600+60)+Duration::from_millis(1))]
    fn test_upcoming_as_instant_without_tz(
        #[case] schedule: &str,
        #[case] current: &str,
        #[case] expected_delta: Duration,
    ) {
        let current = DateTime::parse_from_rfc3339(current).unwrap();
        test_upcoming_as_instant_case(schedule, current, expected_delta)
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
    #[case("TZ=UTC 1 5 * * *", "2025-03-30T02:59:59.999Z", Duration::from_secs(2*60*60 /*hours*/ + 1*60 /*minutes*/) + Duration::from_millis(1))]
    #[case("TZ=UTC 1 5 * * *", "2025-03-30T02:59:59.999+02:00", Duration::from_secs(4*60*60 /*hours*/ + 1*60 /*minutes*/) + Duration::from_millis(1))]
    #[case("TZ=Europe/Kyiv 1 5 * * *", "2025-03-30T02:59:59.999Z", Duration::from_secs(23*60*60 /*hours*/ + 1*60 /*minutes*/) + Duration::from_millis(1))]
    #[case("TZ=Europe/Kyiv 1 5 * * *", "2025-03-30T02:59:59.999+02:00", Duration::from_secs(1*60*60 /*hours*/ + 1*60 /*minutes*/) + Duration::from_millis(1))]
    #[case("TZ=Europe/Kyiv 1 3 * * *", "2025-03-30T02:59:59.999+02:00", Duration::from_secs(23*60*60 /*hours*/ + 1*60 /*minutes*/) + Duration::from_millis(1))]
    fn test_upcoming_as_instant_with_schedule_tz(
        #[case] schedule: &str,
        #[case] current: &str,
        #[case] expected_delta: Duration,
    ) {
        let current = DateTime::parse_from_rfc3339(current).unwrap();
        test_upcoming_as_instant_case(schedule, current, expected_delta)
    }

    #[cfg(feature = "tz")]
    #[rstest]
    #[case("TZ=Europe/Kyiv 1 5 * * *", Kyiv.with_ymd_and_hms(2025, 3, 30, 2, 59, 59).unwrap(), Duration::from_secs(1*60*60 /*hours*/ + 1*60 /*minutes*/ + 1))]
    #[case("TZ=UTC 1 5 * * *", Kyiv.with_ymd_and_hms(2025, 3, 30, 2, 59, 59).unwrap(), Duration::from_secs(4*60*60 /*hours*/ + 1*60 /*minutes*/ + 1))]
    #[case("TZ=Europe/Paris 1 5 * * *", Kyiv.with_ymd_and_hms(2025, 3, 30, 2, 59, 59).unwrap(), Duration::from_secs(2*60*60 /*hours*/ + 1*60 /*minutes*/ + 1))]
    #[case("TZ=Europe/Kyiv 1 5 * * *", Kyiv.with_ymd_and_hms(2025, 1, 1, 2, 59, 59).unwrap(), Duration::from_secs(2*60*60 /*hours*/ + 1*60 /*minutes*/ + 1))]
    #[case("TZ=UTC 1 5 * * *", Kyiv.with_ymd_and_hms(2025, 1, 1, 2, 59, 59).unwrap(), Duration::from_secs(4*60*60 /*hours*/ + 1*60 /*minutes*/ + 1))]
    #[case("TZ=Europe/Paris 1 5 * * *", Kyiv.with_ymd_and_hms(2025, 1, 1, 2, 59, 59).unwrap(), Duration::from_secs(3*60*60 /*hours*/ + 1*60 /*minutes*/ + 1))]
    fn test_upcoming_as_instant_with_both_tz<T: TimeZone>(
        #[case] schedule: &str,
        #[case] current: DateTime<T>,
        #[case] expected_delta: Duration,
    ) {
        test_upcoming_as_instant_case(schedule, current, expected_delta)
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
}
