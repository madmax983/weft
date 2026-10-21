//! The baseline of the old pipeline (plan §1 rule 3, §2.3 and stage G6).
//!
//! A baseline is the old snapshot of a tier in the committed form of §2.3:
//! one [`Record`] for each program, with the diagnostics, the violations, the
//! counts of each input relation and the SHA-256 of the fact digest. It holds
//! no fact tuples and no time ([`committed`]). The baseline of tier 1 is
//! committed ([`TIER1`]). The baseline of tier 2 stays in `target/` ([`TIER2`]).
//!
//! A stage that does not turn a construct group on must not change a result
//! of the old pipeline. [`compare`] compares the old records of a run with the
//! baseline, program by program (the key is the path).
//!
//! # The rule for a timeout
//!
//! The baseline comes from a release build. A debug build is 5 to 15 times
//! slower, so a program that finishes in the release build can time out in a
//! debug build (`cargo test` runs tier 1 in a debug build). The result of such
//! a program is not known. Thus:
//!
//! 1. If the record of a program is a `timeout` on one side or on the two
//!    sides, the program is *unknown*. The comparison skips it and lists its
//!    path ([`Comparison::unknown`]). A program whose text changed (another
//!    hash) is a difference, also when it is unknown.
//! 2. Each other program is compared on all the fields of the committed form,
//!    also a `crash` or an `error` record. Thus a timeout cannot hide a change
//!    of a program that finishes on the two sides.
//! 3. If more than [`MAX_UNKNOWN_PERCENT`] % of the programs are unknown, the
//!    comparison fails: the build is too slow for the gate, or a change makes
//!    many programs hang.
//!
//! The result of the comparison is the same in a debug and in a release
//! build: only the list of unknown programs changes.

use std::collections::BTreeMap;
use std::path::Path;

use crate::snapshot::{Kind, Record};
use crate::Error;

/// The committed baseline of tier 1, relative to the repository.
pub const TIER1: &str = "tests/gate/baseline-tier1.jsonl";

/// The baseline of tier 2, relative to the repository (not committed).
pub const TIER2: &str = "target/gate/baseline-tier2.jsonl";

/// The largest share of unknown programs (in percent of the programs of the
/// run) that the comparison accepts.
pub const MAX_UNKNOWN_PERCENT: usize = 1;

/// The baseline file of the tier `tier`, relative to the repository.
pub const fn file(tier: u8) -> &'static str {
    if tier == 1 {
        TIER1
    } else {
        TIER2
    }
}

/// The record in the committed form: the same record with no time.
pub fn committed(record: &Record) -> Record {
    let mut r = record.clone();
    r.ms = 0;
    r
}

/// The records in the committed form, as JSON lines, in the order of
/// `records`.
///
/// # Errors
///
/// Returns [`Error::Baseline`] if a record cannot be written as JSON.
pub fn to_jsonl(records: &[Record]) -> Result<String, Error> {
    let mut text = String::new();
    for (i, r) in records.iter().enumerate() {
        let line = committed(r).to_json().map_err(|e| Error::Baseline {
            line: i + 1,
            message: e.to_string(),
        })?;
        text.push_str(&line);
        text.push('\n');
    }
    Ok(text)
}

/// Reads the JSON lines of a baseline. An empty line is ignored.
///
/// # Errors
///
/// Returns [`Error::Baseline`] with the number of the first line that is not
/// a record.
pub fn from_jsonl(text: &str) -> Result<Vec<Record>, Error> {
    let mut out = Vec::new();
    for (i, line) in text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let r: Record = serde_json::from_str(line).map_err(|e| Error::Baseline {
            line: i + 1,
            message: e.to_string(),
        })?;
        out.push(committed(&r));
    }
    Ok(out)
}

/// Reads the baseline file `path`. A file that does not exist gives `None`.
///
/// # Errors
///
/// Returns [`Error::Io`] if the file cannot be read, and the errors of
/// [`from_jsonl`].
pub fn read(path: &Path) -> Result<Option<Vec<Record>>, Error> {
    match std::fs::read_to_string(path) {
        Ok(text) => from_jsonl(&text).map(Some),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(Error::io(path, e)),
    }
}

/// One program whose record is not the record of the baseline.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Difference {
    /// The path of the program.
    pub path: String,
    /// What is different, one item for each field.
    pub what: Vec<String>,
}

/// The result of [`compare`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Comparison {
    /// The number of programs of the run.
    pub programs: usize,
    /// The number of programs that the comparison compared.
    pub compared: usize,
    /// The paths of the unknown programs (a timeout on one side), in order.
    pub unknown: Vec<String>,
    /// The programs that are different, in the order of their paths.
    pub differences: Vec<Difference>,
}

impl Comparison {
    /// True if more than [`MAX_UNKNOWN_PERCENT`] % of the programs are
    /// unknown.
    pub fn too_many_unknown(&self) -> bool {
        self.unknown.len().saturating_mul(100) > self.programs.saturating_mul(MAX_UNKNOWN_PERCENT)
    }

    /// True if no program is different and not too many are unknown.
    pub fn passes(&self) -> bool {
        self.differences.is_empty() && !self.too_many_unknown()
    }

    /// One blocker for each different program, and one if too many programs
    /// are unknown. `file` is the baseline file, for the message.
    pub fn blockers(&self, file: &str) -> Vec<String> {
        let tier = if file == TIER1 { "1" } else { "2" };
        let mut out: Vec<String> = self
            .differences
            .iter()
            .map(|d| {
                format!(
                    "baseline {}: {} (the old pipeline does not give the record of `{file}`; if the change is a fix under rule 6, run `cargo run -p weft-gate --release -- run --tier {tier} --write-baseline` and commit the file with the reason)",
                    d.path,
                    d.what.join("; ")
                )
            })
            .collect();
        if self.too_many_unknown() {
            out.push(format!(
                "baseline: {} of {} programs are unknown (a timeout); the limit is {MAX_UNKNOWN_PERCENT} %: the build is too slow, or a change makes programs hang",
                self.unknown.len(),
                self.programs
            ));
        }
        out
    }
}

/// The fields of the committed form that are different in `a` and `b`.
fn fields(a: &Record, b: &Record) -> Vec<String> {
    let mut out = Vec::new();
    if a.hash != b.hash {
        out.push("the text changed (another hash)".to_string());
    }
    if a.set != b.set {
        out.push(format!("set `{}` -> `{}`", a.set, b.set));
    }
    if a.pipeline != b.pipeline {
        out.push(format!("pipeline `{}` -> `{}`", a.pipeline, b.pipeline));
    }
    if a.kind != b.kind {
        out.push(format!("kind {} -> {}", a.kind.name(), b.kind.name()));
    }
    if a.message != b.message {
        out.push(format!(
            "message {:?} -> {:?}",
            a.message.as_deref().unwrap_or(""),
            b.message.as_deref().unwrap_or("")
        ));
    }
    if a.diagnostics != b.diagnostics {
        let text = |d: &[crate::snapshot::Diag]| {
            d.iter()
                .map(|x| format!("{}@{}:{}", x.0, x.1, x.2))
                .collect::<Vec<_>>()
                .join(" ")
        };
        out.push(format!(
            "diagnostics [{}] -> [{}]",
            text(&a.diagnostics),
            text(&b.diagnostics)
        ));
    }
    if a.violations != b.violations {
        let gone = a
            .violations
            .iter()
            .filter(|v| !b.violations.contains(v))
            .count();
        let new = b
            .violations
            .iter()
            .filter(|v| !a.violations.contains(v))
            .count();
        out.push(format!("violations: {gone} gone, {new} new"));
    }
    if a.counts != b.counts {
        let deltas: Vec<String> = a
            .counts
            .keys()
            .chain(b.counts.keys())
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .filter(|k| a.counts.get(*k) != b.counts.get(*k))
            .map(|k| {
                format!(
                    "{k} {} -> {}",
                    a.counts.get(k).copied().unwrap_or(0),
                    b.counts.get(k).copied().unwrap_or(0)
                )
            })
            .collect();
        out.push(format!("counts: {}", deltas.join(", ")));
    }
    if a.digest != b.digest {
        out.push("the fact digest changed".to_string());
    }
    if a.problems != b.problems {
        out.push("problems changed".to_string());
    }
    out
}

/// Compares the records of a run (`current`) with the `baseline`, with the
/// rule for a timeout of the module text. The time ([`Record::ms`]) does not
/// count.
pub fn compare(baseline: &[Record], current: &[Record]) -> Comparison {
    let old: BTreeMap<&str, &Record> = baseline.iter().map(|r| (r.path.as_str(), r)).collect();
    let now: BTreeMap<&str, &Record> = current.iter().map(|r| (r.path.as_str(), r)).collect();
    let mut c = Comparison {
        programs: current.len(),
        ..Comparison::default()
    };
    let paths: std::collections::BTreeSet<&str> = old.keys().chain(now.keys()).copied().collect();
    for path in paths {
        let what = match (old.get(path), now.get(path)) {
            (Some(_), None) => {
                vec!["not in this run (the program is not in the manifest)".to_string()]
            }
            (None, Some(_)) => vec!["not in the baseline (a new program)".to_string()],
            (Some(a), Some(b)) if a.kind == Kind::Timeout || b.kind == Kind::Timeout => {
                if a.hash == b.hash {
                    c.unknown.push(path.to_string());
                    continue;
                }
                vec!["the text changed (another hash)".to_string()]
            }
            (Some(a), Some(b)) => {
                c.compared += 1;
                fields(a, b)
            }
            (None, None) => continue,
        };
        if !what.is_empty() {
            c.differences.push(Difference {
                path: path.to_string(),
                what,
            });
        }
    }
    c
}
