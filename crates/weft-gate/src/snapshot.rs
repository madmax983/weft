//! Snapshots: one record for each program and pipeline (plan §2.3, items 1 to 3).
//!
//! A [`Record`] holds the diagnostics `(code, file, line)`, the violations of the
//! checker with names (`digest::violations`), the number of tuples of each input
//! relation and the SHA-256 of the canonical fact digest (`digest`). The full
//! digest is in [`Outcome::digest`]; it is too large to commit.
//!
//! The snapshot runs in this process, on a pool of worker threads
//! ([`run_pool`]). Each worker has a [`weft_sema::STACK`] stack, so the deepest
//! program that the parser accepts does not overflow it. A panic of the pipeline
//! gives a record of kind [`Kind::Crash`]. A program that takes more than the time
//! limit gives a record of kind [`Kind::Timeout`]: the pool stops to wait for its
//! worker and starts a new worker. The old worker continues until its program
//! ends, and the pool ignores its result.
//!
//! The field [`Record::ms`] is the time of the check. It is different on each
//! run, so a comparison of two snapshots must ignore it.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::path::Path;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::mpsc::{self, RecvTimeoutError, Sender};
use std::sync::Arc;
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};
use weft_cli::package::{Profile, SyntaxError};

use crate::digest;
use crate::manifest::Entry;
use crate::Error;

pub use crate::digest::violation_relations;

/// The default time limit for one program.
pub const LIMIT: Duration = Duration::from_secs(60);

/// The name of each worker thread starts with this text.
pub const WORKER_PREFIX: &str = "weft-gate-worker";

/// The pipeline that makes the facts (`--facts`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Pipeline {
    /// The fact generator of `crates/weft-sema/src/body/`.
    Old,
}

impl Pipeline {
    /// Returns the pipeline with the name `name`, or `None`.
    pub fn parse(name: &str) -> Option<Self> {
        match name {
            "old" => Some(Self::Old),
            _ => None,
        }
    }

    /// The name, as `--facts` takes it.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Old => "old",
        }
    }
}

/// The kind of a record.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Kind {
    /// The pipeline ended. The record has its result.
    Ok,
    /// The pipeline panicked.
    Crash,
    /// The pipeline did not end in the time limit.
    Timeout,
    /// The program cannot be loaded, for example a file that is not UTF-8.
    Error,
}

impl Kind {
    /// All the kinds, in order.
    pub const ALL: [Self; 4] = [Self::Ok, Self::Crash, Self::Timeout, Self::Error];

    /// The name in the record.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Ok => "ok",
            Self::Crash => "crash",
            Self::Timeout => "timeout",
            Self::Error => "error",
        }
    }
}

/// One diagnostic: the code, the file (relative to the base of the manifest)
/// and the line. In JSON, an array of three values.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Diag(pub String, pub String, pub usize);

/// One violation of the checker, with names (see `digest`).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Violation {
    /// The file of the body, relative to the base of the manifest.
    pub file: String,
    /// The name of the body.
    pub function: String,
    /// The sink relation of the spec, for example `error`.
    pub relation: String,
    /// The arguments: a variable is its name, a place its display text and a
    /// node `@LINE`.
    pub args: Vec<String>,
}

/// The snapshot of one program with one pipeline. One line of the JSONL file.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Record {
    /// The path of the manifest entry.
    pub path: String,
    /// The hash of the manifest entry.
    pub hash: String,
    /// The set of the manifest entry.
    pub set: String,
    /// The pipeline ([`Pipeline::name`]).
    pub pipeline: String,
    /// The kind.
    pub kind: Kind,
    /// Why the record is not [`Kind::Ok`].
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
    /// The diagnostics, in sorted order (a multiset).
    #[serde(default)]
    pub diagnostics: Vec<Diag>,
    /// The violations, in sorted order.
    #[serde(default)]
    pub violations: Vec<Violation>,
    /// The number of tuples of each input relation.
    #[serde(default)]
    pub counts: BTreeMap<String, usize>,
    /// The SHA-256 of the canonical fact digest. Empty if the kind is not
    /// [`Kind::Ok`].
    #[serde(default)]
    pub digest: String,
    /// The time of the check in milliseconds. Different on each run.
    #[serde(default)]
    pub ms: u64,
}

impl Record {
    /// A record with no result.
    fn empty(entry: &Entry, pipeline: Pipeline, kind: Kind, message: Option<String>) -> Self {
        Self {
            path: entry.path.clone(),
            hash: entry.hash.clone(),
            set: entry.set.clone(),
            pipeline: pipeline.name().to_string(),
            kind,
            message,
            diagnostics: Vec::new(),
            violations: Vec::new(),
            counts: BTreeMap::new(),
            digest: String::new(),
            ms: 0,
        }
    }

    /// The record as one line of JSON, with no line feed.
    ///
    /// # Errors
    ///
    /// Returns the error of `serde_json`.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }
}

/// The result of one program: the record and the full digest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Outcome {
    /// The record.
    pub record: Record,
    /// The canonical fact digest (`digest::FactDigest::text`). Empty if the
    /// kind is not [`Kind::Ok`] or the program does not parse.
    pub digest: String,
}

impl Outcome {
    fn empty(entry: &Entry, pipeline: Pipeline, kind: Kind, message: String) -> Self {
        Self {
            record: Record::empty(entry, pipeline, kind, Some(message)),
            digest: String::new(),
        }
    }
}

/// The settings of a snapshot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Settings {
    /// The pipeline.
    pub pipeline: Pipeline,
    /// The number of worker threads (at least 1).
    pub workers: usize,
    /// The time limit for one program.
    pub limit: Duration,
}

/// Removes the text `BASE/` from `text`, so a message does not hold the
/// directory of this computer.
fn without_base(base: &Path, text: &str) -> String {
    let dir = format!("{}/", base.display());
    text.replace(&dir, "")
}

/// Checks the program `entry` below `base` with `pipeline`, on this thread.
///
/// A panic of the pipeline continues in the caller: [`run_pool`] catches it.
pub fn check(base: &Path, entry: &Entry, pipeline: Pipeline) -> Outcome {
    let start = Instant::now();
    let path = base.join(&entry.path);
    let mut record = Record::empty(entry, pipeline, Kind::Ok, None);
    let mut text = String::new();
    match weft_cli::check_path(&path, Profile::default()) {
        Ok((pkg, checked)) => {
            for d in &checked.diags {
                let (file, line) = pkg.files.get(d.unit).map_or((String::new(), 0), |f| {
                    (
                        digest::relative_name(base, &f.name),
                        f.line_col(d.span.lo).0,
                    )
                });
                record
                    .diagnostics
                    .push(Diag(d.code.as_str().to_string(), file, line));
            }
            record.violations = digest::violations(base, &pkg, &checked);
            let facts = digest::fact_digest(base, &pkg, &checked);
            text = facts.text();
            record.counts = facts.counts;
        }
        Err(e) => match e.downcast::<SyntaxError>() {
            Ok(s) => {
                let file = digest::relative_name(base, &s.file.name);
                let line = s.file.line_col(s.diag.span.lo).0;
                record
                    .diagnostics
                    .push(Diag(s.diag.code.as_str().to_string(), file, line));
            }
            Err(e) => {
                let message = without_base(base, &format!("{e:#}"));
                return Outcome::empty(entry, pipeline, Kind::Error, message);
            }
        },
    }
    record.diagnostics.sort();
    record.digest = digest::sha256(&text);
    record.ms = u64::try_from(start.elapsed().as_millis()).unwrap_or(u64::MAX);
    Outcome {
        record,
        digest: text,
    }
}

std::thread_local! {
    /// The text of the last panic on this worker thread
    /// ([`install_panic_hook`]).
    static LAST_PANIC: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// Installs a panic hook for the `weft-gate` command.
///
/// On a worker thread, the hook keeps the text of the panic (the message and
/// the location) for the crash record, and writes nothing. On another thread,
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

/// The work of a pool: the outcome of one entry.
pub type Work = Arc<dyn Fn(&Entry) -> Outcome + Send + Sync>;

/// A message from a worker to the pool.
enum Msg {
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
        outcome: Box<Outcome>,
    },
}

/// What a worker shares with the pool.
struct Shared {
    entries: Arc<Vec<Entry>>,
    next: Arc<AtomicUsize>,
    work: Work,
    pipeline: Pipeline,
    tx: Sender<Msg>,
}

/// Starts worker `id`. The worker takes the next entry until no entry is left
/// or until the pool sets its stop flag.
fn spawn_worker(id: usize, shared: &Shared) -> Result<Arc<AtomicBool>, Error> {
    let stop = Arc::new(AtomicBool::new(false));
    let flag = Arc::clone(&stop);
    let entries = Arc::clone(&shared.entries);
    let next = Arc::clone(&shared.next);
    let work = Arc::clone(&shared.work);
    let pipeline = shared.pipeline;
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
                    let outcome = run.unwrap_or_else(|payload| {
                        let text = LAST_PANIC
                            .with(|p| p.borrow_mut().take())
                            .unwrap_or_else(|| payload_text(payload.as_ref()));
                        let mut o = Outcome::empty(entry, pipeline, Kind::Crash, text);
                        o.record.ms = u64::try_from(at.elapsed().as_millis()).unwrap_or(u64::MAX);
                        o
                    });
                    let done = Msg::Done {
                        worker: id,
                        index,
                        outcome: Box::new(outcome),
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

/// Runs `work` on each entry, on `settings.workers` worker threads, and calls
/// `emit` once for each entry with its index and its outcome, in the order in
/// which the entries end.
///
/// A panic of `work` gives an outcome of kind [`Kind::Crash`]. An entry that
/// takes more than `settings.limit` gives an outcome of kind [`Kind::Timeout`].
///
/// # Errors
///
/// Returns [`Error::Thread`] if the system cannot start a worker thread.
pub fn run_pool(
    entries: Vec<Entry>,
    settings: &Settings,
    work: Work,
    mut emit: impl FnMut(usize, Outcome),
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
        pipeline: settings.pipeline,
        tx,
    };
    let mut stops = Vec::new();
    for id in 0..settings.workers.clamp(1, n) {
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
            .map(|&(_, at)| (at + settings.limit).saturating_duration_since(now))
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
                outcome,
            }) => {
                if busy.get(&worker).is_some_and(|&(i, _)| i == index) {
                    busy.remove(&worker);
                }
                if let Some(d) = done.get_mut(index).filter(|d| !**d) {
                    *d = true;
                    left -= 1;
                    emit(index, *outcome);
                }
            }
            Err(RecvTimeoutError::Timeout) => {
                let now = Instant::now();
                let late: Vec<usize> = busy
                    .iter()
                    .filter(|(_, &(_, at))| now.duration_since(at) >= settings.limit)
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
                            let text = format!(
                                "the check takes more than {} ms",
                                settings.limit.as_millis()
                            );
                            let mut o =
                                Outcome::empty(entry, settings.pipeline, Kind::Timeout, text);
                            o.record.ms = u64::try_from(settings.limit.as_millis()).unwrap_or(0);
                            emit(index, o);
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

/// Checks each entry below `base` with [`check`] on a pool ([`run_pool`]).
///
/// # Errors
///
/// Returns [`Error::Thread`] if the system cannot start a worker thread.
pub fn snapshot(
    base: &Path,
    entries: Vec<Entry>,
    settings: &Settings,
    emit: impl FnMut(usize, Outcome),
) -> Result<(), Error> {
    let base = base.to_path_buf();
    let pipeline = settings.pipeline;
    let work: Work = Arc::new(move |e: &Entry| check(&base, e, pipeline));
    run_pool(entries, settings, work, emit)
}
