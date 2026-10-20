//! Snapshots: one record for each program and pipeline (plan §2.3, items 1 to 3).
//!
//! A [`Record`] holds the diagnostics `(code, file, line)`, the violations of the
//! checker with names (`digest::violations`), the number of tuples of each input
//! relation and the SHA-256 of the canonical fact digest (`digest`). The full
//! digest is in [`Outcome::digest`]; it is too large to commit.
//!
//! The snapshot runs in this process, on a pool of worker threads
//! ([`run_pool`], [`crate::pool`]). Each worker has a [`weft_sema::STACK`] stack,
//! so the deepest program that the parser accepts does not overflow it. A panic
//! of the pipeline gives a record of kind [`Kind::Crash`]. A program that takes
//! more than the time limit gives a record of kind [`Kind::Timeout`]: the pool
//! stops to wait for its worker and starts a new worker. The old worker continues
//! until its program ends, and the pool ignores its result.
//!
//! The field [`Record::ms`] is the time of the check. It is different on each
//! run, so a comparison of two snapshots must ignore it.

use std::collections::BTreeMap;
use std::path::Path;
use std::sync::Arc;
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};
use weft_cli::package::{Profile, SyntaxError};

use crate::digest;
use crate::manifest::Entry;
use crate::pool::{self, Ended};
use crate::Error;

pub use crate::digest::violation_relations;
pub use crate::pool::{install_panic_hook, WORKER_PREFIX};

/// The default time limit for one program.
pub const LIMIT: Duration = Duration::from_secs(60);

/// The work of a pool: the outcome of one entry.
pub type Work = pool::Work<Outcome>;

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

/// Runs `work` on each entry, on `settings.workers` worker threads
/// ([`pool::run`]), and calls `emit` once for each entry with its index and its
/// outcome, in the order in which the entries end.
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
    let pipeline = settings.pipeline;
    let limit = settings.limit;
    pool::run(entries, settings.workers, limit, work, |i, entry, ended| {
        let outcome = match ended {
            Ended::Done(o) => o,
            Ended::Panic { text, ms } => {
                let mut o = Outcome::empty(entry, pipeline, Kind::Crash, text);
                o.record.ms = ms;
                o
            }
            Ended::Timeout => {
                let text = format!("the check takes more than {} ms", limit.as_millis());
                let mut o = Outcome::empty(entry, pipeline, Kind::Timeout, text);
                o.record.ms = u64::try_from(limit.as_millis()).unwrap_or(0);
                o
            }
        };
        emit(i, outcome);
    })
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
