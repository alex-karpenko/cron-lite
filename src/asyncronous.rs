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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CronEvent {
    Ok,
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
    /// Returns [`CronWaiter`] which implements [`Future`](). It becomes asleep until next upcoming event happened.
    pub fn wait_upcoming<Tz: TimeZone>(&self, current: &DateTime<Tz>) -> Option<CronWaiter> {
        let upcoming = self.upcoming(current)?;

        let now_inst = Instant::now();
        let until_nano = upcoming.timestamp_nanos_opt()?;
        let now_nano = current.timestamp_nanos_opt()?;
        let until_inst = now_inst + Duration::from_nanos((until_nano - now_nano) as u64);

        let waiter = CronWaiter::new(until_inst);
        Some(waiter)
    }
}
