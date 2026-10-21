//! A pool of worker threads for the gate commands (`snapshot`, `oracle`).
//!
//! Each worker has a [`weft_sema::STACK`] stack, so the deepest program that the
//! parser accepts does not overflow it. The pool catches a panic of the work and
//! gives [`Ended::Panic`]. An entry that takes more than the time limit gives
//! [`Ended::Timeout`]: the pool stops to wait for its worker and starts a new
//! worker. The old worker continues until its entry ends, and the pool ignores
//! its result. So a command that uses the pool must make sure that each entry
//! ends in a finite time, for example with a step limit.
//!
//! A command that uses the pool must call [`install_panic_hook`] first.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::mpsc::{self, RecvTimeoutError, Sender};
use std::sync::Arc;
use std::time::{Duration, Instant};

use crate::manifest::Entry;
use crate::Error;

/// The name of each worker thread starts with this text.
pub const WORKER_PREFIX: &str = "weft-gate-worker";

/// How the work on one entry ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ended<T> {
    /// The work ended with this result.
    Done(T),
    /// The work panicked.
    Panic {
        /// The text of the panic: the message and the location.
        text: String,
        /// The time from the start of the entry to the panic, in milliseconds.
        ms: u64,
    },
    /// The work did not end in the time limit.
    Timeout,
}

std::thread_local! {
    /// The text of the last panic on this worker thread
    /// ([`install_panic_hook`]).
    static LAST_PANIC: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// Installs a panic hook for the `weft-gate` command.
///
/// On a worker thread, the hook keeps the text of the panic (the message and
/// the location) for [`Ended::Panic`], and writes nothing. On another thread,
/// the earlier hook runs.
pub fn install_panic_hook() {
    let earlier = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let worker = std::thread::current()
            .name()
            .is_some_and(|n| n.starts_with(WORKER_PREFIX));
        if worker {
            LAST_PANIC.with(|p| *p.borrow_mut() = Some(info.to_string()));
        } else {
            earlier(info);
        }
    }));
}

/// The text of a panic payload.
fn payload_text(payload: &(dyn std::any::Any + Send)) -> String {
    payload
        .downcast_ref::<&str>()
        .map(ToString::to_string)
        .or_else(|| payload.downcast_ref::<String>().cloned())
        .unwrap_or_else(|| "a panic with no text".to_string())
}

/// The work of a pool: the result of one entry.
pub type Work<T> = Arc<dyn Fn(&Entry) -> T + Send + Sync>;

/// A message from a worker to the pool.
enum Msg<T> {
    /// The worker starts entry `index`.
    Start {
        worker: usize,
        index: usize,
        at: Instant,
    },
    /// The worker ends entry `index`.
    Done {
        worker: usize,
        index: usize,
        ended: Box<Ended<T>>,
    },
}

/// What a worker shares with the pool.
struct Shared<T> {
    entries: Arc<Vec<Entry>>,
    next: Arc<AtomicUsize>,
    work: Work<T>,
    tx: Sender<Msg<T>>,
}

/// The time from `at` to now in milliseconds.
fn ms_since(at: Instant) -> u64 {
    u64::try_from(at.elapsed().as_millis()).unwrap_or(u64::MAX)
}

/// Starts worker `id`. The worker takes the next entry until no entry is left
/// or until the pool sets its stop flag.
fn spawn_worker<T: Send + 'static>(
    id: usize,
    shared: &Shared<T>,
) -> Result<Arc<AtomicBool>, Error> {
    let stop = Arc::new(AtomicBool::new(false));
    let flag = Arc::clone(&stop);
    let entries = Arc::clone(&shared.entries);
    let next = Arc::clone(&shared.next);
    let work = Arc::clone(&shared.work);
    let tx = shared.tx.clone();
    std::thread::Builder::new()
        .name(format!("{WORKER_PREFIX}-{id}"))
        .stack_size(weft_sema::STACK)
        .spawn(move || {
            // The thread has a large stack: sema runs on it with no new thread.
            weft_sema::on_current_stack(|| {
                while !flag.load(Ordering::SeqCst) {
                    let index = next.fetch_add(1, Ordering::SeqCst);
                    let Some(entry) = entries.get(index) else {
                        break;
                    };
                    let at = Instant::now();
                    if tx
                        .send(Msg::Start {
                            worker: id,
                            index,
                            at,
                        })
                        .is_err()
                    {
                        break;
                    }
                    LAST_PANIC.with(|p| p.borrow_mut().take());
                    let run =
                        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| work(entry)));
                    let ended = match run {
                        Ok(result) => Ended::Done(result),
                        Err(payload) => Ended::Panic {
                            text: LAST_PANIC
                                .with(|p| p.borrow_mut().take())
                                .unwrap_or_else(|| payload_text(payload.as_ref())),
                            ms: ms_since(at),
                        },
                    };
                    let done = Msg::Done {
                        worker: id,
                        index,
                        ended: Box::new(ended),
                    };
                    if tx.send(done).is_err() {
                        break;
                    }
                }
            });
        })
        .map_err(Error::Thread)?;
    Ok(stop)
}

/// Runs `work` on each entry, on `workers` worker threads, and calls `emit`
/// once for each entry with its index, the entry and how the work ended, in the
/// order in which the entries end.
///
/// # Errors
///
/// Returns [`Error::Thread`] if the system cannot start a worker thread.
pub fn run<T: Send + 'static>(
    entries: Vec<Entry>,
    workers: usize,
    limit: Duration,
    work: Work<T>,
    mut emit: impl FnMut(usize, &Entry, Ended<T>),
) -> Result<(), Error> {
    let n = entries.len();
    if n == 0 {
        return Ok(());
    }
    let (tx, rx) = mpsc::channel();
    let shared = Shared {
        entries: Arc::new(entries),
        next: Arc::new(AtomicUsize::new(0)),
        work,
        tx,
    };
    let mut stops = Vec::new();
    for id in 0..workers.clamp(1, n) {
        stops.push(spawn_worker(id, &shared)?);
    }
    // The entry and the start time of each busy worker.
    let mut busy: BTreeMap<usize, (usize, Instant)> = BTreeMap::new();
    let mut done = vec![false; n];
    let mut left = n;
    while left > 0 {
        let now = Instant::now();
        let wait = busy
            .values()
            .map(|&(_, at)| (at + limit).saturating_duration_since(now))
            .min();
        let msg = match wait {
            Some(w) => rx.recv_timeout(w),
            None => rx.recv().map_err(|_| RecvTimeoutError::Disconnected),
        };
        match msg {
            Ok(Msg::Start { worker, index, at }) => {
                busy.insert(worker, (index, at));
            }
            Ok(Msg::Done {
                worker,
                index,
                ended,
            }) => {
                if busy.get(&worker).is_some_and(|&(i, _)| i == index) {
                    busy.remove(&worker);
                }
                if let (Some(d), Some(entry)) = (done.get_mut(index), shared.entries.get(index)) {
                    if !*d {
                        *d = true;
                        left -= 1;
                        emit(index, entry, *ended);
                    }
                }
            }
            Err(RecvTimeoutError::Timeout) => {
                let now = Instant::now();
                let late: Vec<usize> = busy
                    .iter()
                    .filter(|(_, &(_, at))| now.duration_since(at) >= limit)
                    .map(|(&w, _)| w)
                    .collect();
                for worker in late {
                    let Some((index, _)) = busy.remove(&worker) else {
                        continue;
                    };
                    if let Some(stop) = stops.get(worker) {
                        stop.store(true, Ordering::SeqCst);
                    }
                    if let (Some(d), Some(entry)) = (done.get_mut(index), shared.entries.get(index))
                    {
                        if !*d {
                            *d = true;
                            left -= 1;
                            emit(index, entry, Ended::Timeout);
                        }
                    }
                    if shared.next.load(Ordering::SeqCst) < n {
                        let id = stops.len();
                        stops.push(spawn_worker(id, &shared)?);
                    }
                }
            }
            Err(RecvTimeoutError::Disconnected) => break,
        }
    }
    Ok(())
}
