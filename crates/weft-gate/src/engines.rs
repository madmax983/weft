//! The engine differential (plan stage I5, `docs/ir.md` 8.5): the AST engine
//! and the IR engine of the interpreter on each runnable program of a tier.
//!
//! Each program runs with the oracle on, in the six configurations of the
//! oracle (`crate::oracle::CONFIGS`), once with each engine, in child
//! processes (`crate::oracle::run_isolated_observed`). The runs of one
//! engine stop after a run that faults, as in the oracle. [`compare`] takes
//! the observations of the two engines, configuration by configuration, and
//! gives the first [`Difference`]: in the output, the status (how the run
//! ends), the message of a run-time error, or the line of the error. The
//! output of a run that does not end is not compared.
//!
//! The run of a program uses no checker, as the oracle: no task is
//! stealable, and a program that the checker rejects runs too.
//!
//! Each difference must have a ledger entry of class `engine`
//! (`crate::ledger`). The entry names a difference class ([`Kind`]); the
//! shape of the class ([`Kind::fits`]) must hold for the difference. An entry
//! with `checker = "rejects"` is a rule: it accepts a difference of its
//! class on each program that the checker rejects. A difference on a program
//! that the checker accepts needs an entry that names the program (no glob).
//!
//! A run that the time limit stops is noise under load. The `engines` command
//! runs each program with a time limit on one side again, alone; then a
//! difference of class [`Kind::Timeout`] is a real difference of speed.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;
use std::sync::Arc;

use sha2::{Digest as _, Sha256};

use crate::ledger::{EntryClass, Ledger};
use crate::manifest::Entry;
use crate::oracle::{self, Engine, Observation, Settings, CONFIGS};
use crate::pool::{self, Ended};
use crate::Error;

/// The observations of one program with each engine.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Runs {
    /// The runs of the AST engine.
    pub ast: Vec<Observation>,
    /// The runs of the IR engine.
    pub ir: Vec<Observation>,
}

impl Runs {
    /// Why the IR engine ran the program with the AST compiler, if it did.
    pub fn fallback(&self) -> Option<&str> {
        self.ir.iter().find_map(|o| o.fallback.as_deref())
    }

    /// True if a run of one engine stops at the time limit and the run of the
    /// other engine in the same configuration does not.
    pub fn one_sided_timeout(&self) -> bool {
        compare(&self.ast, &self.ir).is_some_and(|d| d.kind_of_timeout())
    }
}

/// True if two observations show the same run: the same status, and for a
/// run that ends, the same message, line and output.
pub fn same(a: &Observation, b: &Observation) -> bool {
    if a.is_timeout() || b.is_timeout() {
        return a.is_timeout() == b.is_timeout();
    }
    a.status == b.status
        && a.message == b.message
        && a.line == b.line
        && a.output_hash == b.output_hash
}

/// The first configuration in which the two engines differ.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Difference {
    /// The index of the configuration.
    pub config: usize,
    /// The run of the AST engine, if it ran in this configuration.
    pub ast: Option<Observation>,
    /// The run of the IR engine, if it ran in this configuration.
    pub ir: Option<Observation>,
}

impl Difference {
    /// True if exactly one side stops at the time limit.
    fn kind_of_timeout(&self) -> bool {
        let t = |o: &Option<Observation>| o.as_ref().is_some_and(Observation::is_timeout);
        t(&self.ast) != t(&self.ir)
    }
}

/// Compares the runs of the two engines, configuration by configuration.
/// Gives the first difference, or `None`.
pub fn compare(ast: &[Observation], ir: &[Observation]) -> Option<Difference> {
    for config in 0..CONFIGS.len() {
        let a = ast.iter().find(|o| o.config == config);
        let b = ir.iter().find(|o| o.config == config);
        match (a, b) {
            (None, None) => {}
            (Some(x), Some(y)) if same(x, y) => {}
            _ => {
                return Some(Difference {
                    config,
                    ast: a.cloned(),
                    ir: b.cloned(),
                });
            }
        }
    }
    None
}

/// What a run shows, in a few groups: the facts that the shapes of the
/// difference classes read.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Facet {
    /// The run ends with no error and with no fault marker in the output.
    Ok,
    /// The run does not end.
    Timeout,
    /// A read of a moved value: the fault "used after it was moved", the
    /// oracle fault "a read of a moved value", the marker `<moved>`, or a
    /// place that does not exist.
    Moved,
    /// A dangling reference: an oracle fault or the marker `<dangling>` or
    /// `<freed>`.
    Dangling,
    /// A data race of the oracle.
    Race,
    /// A linear leak of the oracle.
    Leak,
    /// The W0315 fault of the IR engine: a jump out of a handled body, a
    /// clause or a scope body.
    Fence,
    /// A native method finds a value of another kind as its receiver (`a
    /// `Vec` is needed here`).
    Receiver,
    /// Another fault.
    Fault,
    /// Another way to end: `fail`, an assertion, a deadlock, an interpreter
    /// that stops.
    Other,
}

/// The facet of a run (`None`: the engine did not run the configuration).
pub fn facet(o: Option<&Observation>) -> Option<Facet> {
    let o = o?;
    if o.is_timeout() {
        return Some(Facet::Timeout);
    }
    let m = o.message.as_str();
    let text = |needles: &[&str]| needles.iter().any(|n| m.contains(n));
    let f = if text(&["data race"]) {
        Facet::Race
    } else if text(&["linear leak"]) {
        Facet::Leak
    } else if text(&["dangling reference"]) {
        Facet::Dangling
    } else if text(&[
        "used after it was moved",
        "a read of a moved value",
        "place does not exist",
    ]) {
        Facet::Moved
    } else if text(&[
        "cannot leave a handled body",
        "cannot leave a handler clause",
        "cannot leave a scope body",
    ]) {
        Facet::Fence
    } else if text(&[" is needed here", " needs an `"]) {
        Facet::Receiver
    } else if o.status == "fault" {
        Facet::Fault
    } else if o.output.contains("<dangling>") || o.output.contains("<freed>") {
        Facet::Dangling
    } else if o.output.contains("<moved>") {
        Facet::Moved
    } else if o.status == "ok" {
        Facet::Ok
    } else {
        Facet::Other
    };
    Some(f)
}

/// A class of differences of the engines (the ledger names it in the field
/// `difference`). Each class has a shape ([`Kind::fits`]) that the
/// difference must have.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Kind {
    /// Choice A (`docs/ir.md` 5.1.1): the IR reads an operand where the
    /// source writes it. Shape: both runs end the same way with another
    /// output, or the AST run reads a dangling reference and the IR run ends
    /// with no fault.
    ChoiceA,
    /// The tail temporaries of a loop body end at each iteration (5.1.2).
    /// Shape: both runs end with no error, with another output.
    LoopTemps,
    /// The temporaries of a branch of `if` or `match` end before the join
    /// (5.12); the AST engine keeps them to the end of the statement. Shape:
    /// the IR run reads a dangling reference, and the AST run does not.
    BranchTemps,
    /// The unwind order of the cleanup chains (5.1.6, 8.2, stage I6): the
    /// chain of a clause unwinds its fresh continuation first, where the AST
    /// engine unwinds the clause frame first; and the chain runs the `on
    /// abort` of each value when it gets to the value, so an `on abort` can
    /// run before the fault at a linear value with no `on abort` (W0602).
    /// Shape: both runs end with the same status and message (the line can
    /// differ), with another output.
    UnwindOrder,
    /// Rule CAPTURE (5.1.7): a borrowed capture is `ByRef`, so the oracle
    /// sees a dangling cell earlier. Shape: the IR run reads a dangling
    /// reference, and the AST run does not, or reads one at another line or
    /// after another output.
    Capture,
    /// The IR reads a receiver after the arguments of the call (5.19), and
    /// an operand where the source writes it: a dangling read moves to
    /// another point. Shape: both runs read a dangling reference, at other
    /// lines or after other output.
    ReadOrder,
    /// A local ends at its `Dead` in the IR, at the end of its scope: the
    /// oracle finds a linear leak there, where the AST engine finds it at
    /// the statement of the local. Shape: both runs find a linear leak, at
    /// other lines, with the same output.
    LeakAtDead,
    /// W0315 (5.36): the IR engine faults at a jump out of a fence; the AST
    /// engine jumps. Shape: the IR run has the W0315 fault.
    W0315,
    /// A native method gets a moved receiver: one engine faults with "a
    /// `Vec` is needed here" (or "`clone` needs an `Rc`"). Shape: one run
    /// has that fault.
    Receiver,
    /// A place in statement position is a `Mention` in the IR (a place tail
    /// of a block or a loop body): the AST engine moves the value, the IR
    /// engine does not. Shape: the AST run reads a moved value and the IR
    /// run does not, or the AST run finds a linear leak (the moved value goes
    /// away) and the IR run ends with no fault.
    Mention,
    /// The IR reads an operand at the operand, so a moved or unset value
    /// faults there. Shape: the IR run reads a moved value, and the AST run
    /// faults in another way or shows `<moved>`.
    MovedRead,
    /// A local or a temporary ends at its `Dead` in the IR: one engine reads
    /// a dangling reference where the other reads a moved value. Shape: one
    /// run is dangling, the other moved.
    DanglingMoved,
    /// Both engines fault in the same configuration with the same output,
    /// with another text or line. Shape: both runs fault, with the same
    /// output.
    FaultText,
    /// The IR engine runs more operations in a quantum, so the scheduler
    /// interleaves the tasks in another way. Shape: the outputs have the
    /// same lines in another order, or both runs find a data race.
    Schedule,
    /// A closure value moves at another point in the IR (a `once` closure
    /// moves into a call or a spawn; closure values are shared at run time),
    /// so a use faults on one engine only, or at another line. Shape: one
    /// run reads a moved value and the other ends with no fault, or both
    /// read a moved value at other lines or after other output.
    MovedClosure,
    /// A function value is plain data in the IR (B12b): a read copies it,
    /// where the AST engine moves it. Shape: the AST run reads a moved
    /// value, and the IR run ends with no fault.
    ClosureCopy,
    /// The IR reads the place of a compound assignment before it writes it,
    /// so the oracle finds a data race at the read. Shape: both runs find a
    /// data race, or the IR run finds one and the AST run does not.
    RaceReadFirst,
    /// The IR run finds a data race before a dangling read (the read order
    /// of a compound assignment). Shape: one run finds a data race, the
    /// other a dangling reference.
    RaceBeforeDangling,
    /// The IR reads a value with its static type (`on abort` parameter of a
    /// copy type that holds a linear value), and drops a linear value. Shape:
    /// the IR run finds a linear leak, and the AST run does not, or finds it
    /// after other output.
    StaticTypeRead,
    /// One engine runs out of time in a configuration in which the other
    /// ends, also in a second run alone. Shape: exactly one run is a
    /// timeout.
    Timeout,
}

impl Kind {
    /// All the classes.
    pub const ALL: [Self; 20] = [
        Self::ChoiceA,
        Self::LoopTemps,
        Self::BranchTemps,
        Self::UnwindOrder,
        Self::Capture,
        Self::ReadOrder,
        Self::LeakAtDead,
        Self::W0315,
        Self::Receiver,
        Self::Mention,
        Self::MovedRead,
        Self::DanglingMoved,
        Self::FaultText,
        Self::Schedule,
        Self::MovedClosure,
        Self::ClosureCopy,
        Self::RaceReadFirst,
        Self::RaceBeforeDangling,
        Self::StaticTypeRead,
        Self::Timeout,
    ];

    /// The name in the ledger.
    pub const fn name(self) -> &'static str {
        match self {
            Self::ChoiceA => "choice-a",
            Self::LoopTemps => "loop-temps",
            Self::BranchTemps => "branch-temps",
            Self::UnwindOrder => "unwind-order",
            Self::Capture => "capture",
            Self::ReadOrder => "read-order",
            Self::LeakAtDead => "leak-at-dead",
            Self::W0315 => "w0315",
            Self::Receiver => "receiver",
            Self::Mention => "mention",
            Self::MovedRead => "moved-read",
            Self::DanglingMoved => "dangling-moved",
            Self::FaultText => "fault-text",
            Self::Schedule => "schedule",
            Self::MovedClosure => "moved-closure",
            Self::ClosureCopy => "closure-copy",
            Self::RaceReadFirst => "race-read-first",
            Self::RaceBeforeDangling => "race-before-dangling",
            Self::StaticTypeRead => "static-type-read",
            Self::Timeout => "timeout",
        }
    }

    /// The class with the name `name`, or `None`.
    pub fn parse(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|k| k.name() == name)
    }

    /// True if the difference `d` has the shape of the class.
    pub fn fits(self, d: &Difference) -> bool {
        let (Some(a), Some(i)) = (facet(d.ast.as_ref()), facet(d.ir.as_ref())) else {
            return false;
        };
        let (ao, io) = (d.ast.as_ref(), d.ir.as_ref());
        let same_end = ao.zip(io).is_some_and(|(x, y)| {
            x.status == y.status && x.message == y.message && x.line == y.line
        });
        let same_status = ao
            .zip(io)
            .is_some_and(|(x, y)| x.status == y.status && x.message == y.message);
        let other_output = ao
            .zip(io)
            .is_some_and(|(x, y)| x.output_hash != y.output_hash);
        let same_output = ao
            .zip(io)
            .is_some_and(|(x, y)| x.output_hash == y.output_hash);
        let faults = |f: Facet| !matches!(f, Facet::Ok | Facet::Timeout | Facet::Other);
        // Both runs have the facet `f`, at other lines or after other output.
        let elsewhere = |f: Facet| {
            a == f
                && i == f
                && ao
                    .zip(io)
                    .is_some_and(|(x, y)| x.line != y.line || x.output_hash != y.output_hash)
        };
        match self {
            Self::ChoiceA => (same_end && other_output) || (a == Facet::Dangling && i == Facet::Ok),
            Self::LoopTemps => a == Facet::Ok && i == Facet::Ok && other_output,
            Self::BranchTemps => i == Facet::Dangling && a != Facet::Dangling,
            Self::UnwindOrder => same_status && other_output,
            Self::Capture => {
                (i == Facet::Dangling && a != Facet::Dangling) || elsewhere(Facet::Dangling)
            }
            Self::ReadOrder => elsewhere(Facet::Dangling),
            Self::LeakAtDead => elsewhere(Facet::Leak) && same_output,
            Self::W0315 => i == Facet::Fence,
            Self::Receiver => a == Facet::Receiver || i == Facet::Receiver,
            Self::Mention => {
                (a == Facet::Moved && i != Facet::Moved) || (a == Facet::Leak && i == Facet::Ok)
            }
            Self::MovedRead => i == Facet::Moved && (a == Facet::Moved || faults(a)),
            Self::DanglingMoved => {
                matches!(
                    (a, i),
                    (Facet::Dangling, Facet::Moved) | (Facet::Moved, Facet::Dangling)
                )
            }
            Self::FaultText => faults(a) && faults(i) && same_output,
            Self::Schedule => {
                (a == Facet::Race && i == Facet::Race)
                    || ao.zip(io).is_some_and(|(x, y)| {
                        x.status == y.status && other_output && same_lines(&x.output, &y.output)
                    })
            }
            Self::MovedClosure => {
                matches!(
                    (a, i),
                    (Facet::Moved, Facet::Ok) | (Facet::Ok, Facet::Moved)
                ) || elsewhere(Facet::Moved)
            }
            Self::ClosureCopy => a == Facet::Moved && i == Facet::Ok,
            Self::RaceReadFirst => i == Facet::Race && (a == Facet::Race || !faults(a)),
            Self::RaceBeforeDangling => {
                matches!(
                    (a, i),
                    (Facet::Race, Facet::Dangling) | (Facet::Dangling, Facet::Race)
                )
            }
            Self::StaticTypeRead => i == Facet::Leak && (a != Facet::Leak || other_output),
            Self::Timeout => (a == Facet::Timeout) != (i == Facet::Timeout),
        }
    }
}

/// True if two texts have the same lines, in any order. The output of a run
/// keeps only its start, so the last line of each text does not count.
fn same_lines(a: &str, b: &str) -> bool {
    sorted_lines(a) == sorted_lines(b)
}

/// The lines of a text in sorted order, with no last line for a text that
/// [`oracle::MAX_OUTPUT`] cut.
fn sorted_lines(t: &str) -> Vec<&str> {
    let mut v: Vec<&str> = t.lines().collect();
    if t.len() >= oracle::MAX_OUTPUT {
        v.pop();
    }
    v.sort_unstable();
    v
}

/// The engine entries of the ledger, with their classes.
#[derive(Clone, Debug, Default)]
pub struct Rules {
    /// The index of each engine entry in the ledger, and its class.
    pub entries: Vec<(usize, Kind)>,
    /// The problems of the engine entries.
    pub problems: Vec<String>,
}

impl Rules {
    /// The engine entries of `ledger`. An entry with no known class, or with
    /// a problem of [`crate::ledger::Entry::problem`] (no reason, a glob and
    /// no `checker = "rejects"`), is a problem.
    pub fn from_ledger(ledger: &Ledger) -> Self {
        let mut out = Self::default();
        for (k, e) in ledger.entries.iter().enumerate() {
            if e.class != EntryClass::Engine {
                continue;
            }
            let label = format!("ledger entry {} ({})", k + 1, e.label());
            if let Some(p) = e.problem() {
                out.problems.push(format!("{label}: {p}"));
            }
            match e.difference.as_deref().and_then(Kind::parse) {
                Some(kind) => out.entries.push((k, kind)),
                None => out.problems.push(format!(
                    "{label}: `difference` must be one of {}",
                    Kind::ALL.map(Kind::name).join(", ")
                )),
            }
        }
        out
    }
}

/// The result of the differential for one program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Result1 {
    /// The engines agree.
    Same,
    /// The IR engine ran the program with the AST compiler (the reason).
    Fallback(String),
    /// The engines differ.
    Differ {
        /// The first difference.
        diff: Box<Difference>,
        /// The ledger entry that accepts it (its index in the ledger).
        entry: Option<usize>,
        /// The classes whose shape holds for the difference.
        kinds: Vec<Kind>,
    },
}

/// One program of the report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Row {
    /// The path of the manifest entry.
    pub path: String,
    /// True if the checker (the `old` pipeline) rejects the program.
    pub rejected: bool,
    /// True if the program ran again alone after a timeout on one side.
    pub rerun: bool,
    /// The result.
    pub result: Result1,
}

/// Gives the result of one program: the comparison, and the ledger entry
/// that accepts a difference.
///
/// `paths` are the paths of the program that an entry can name; `rejected`
/// is true if the checker rejects the program.
pub fn judge(
    runs: &Runs,
    paths: &[String],
    rejected: bool,
    ledger: &Ledger,
    rules: &Rules,
) -> Result1 {
    if let Some(why) = runs.fallback() {
        if compare(&runs.ast, &runs.ir).is_none() {
            return Result1::Fallback(why.to_string());
        }
    }
    let Some(diff) = compare(&runs.ast, &runs.ir) else {
        return Result1::Same;
    };
    judge_difference(diff, paths, rejected, ledger, rules)
}

/// Gives the result of a difference: the classes whose shape holds, and the
/// first engine entry of the ledger that accepts it.
pub fn judge_difference(
    diff: Difference,
    paths: &[String],
    rejected: bool,
    ledger: &Ledger,
    rules: &Rules,
) -> Result1 {
    let kinds: Vec<Kind> = Kind::ALL.into_iter().filter(|k| k.fits(&diff)).collect();
    let entry = rules.entries.iter().find_map(|&(k, kind)| {
        let e = ledger.entries.get(k)?;
        let rule = e.checker.as_deref() == Some("rejects");
        let applies = if rule { rejected } else { true };
        (applies && kinds.contains(&kind) && e.matches(paths)).then_some(k)
    });
    Result1::Differ {
        diff: Box::new(diff),
        entry,
        kinds,
    }
}

/// One difference of a file of [`Report::differences_jsonl`].
#[derive(Clone, Debug, serde::Deserialize)]
pub struct Saved {
    /// The path of the manifest entry.
    pub path: String,
    /// True if the checker rejects the program.
    pub rejected: bool,
    /// True if the program ran again alone.
    #[serde(default)]
    pub rerun: bool,
    /// The difference.
    pub diff: Difference,
}

/// Reads the differences of a file of [`Report::differences_jsonl`].
///
/// # Errors
///
/// Returns a message for a line that is not a difference.
pub fn read_differences(text: &str) -> Result<Vec<Saved>, String> {
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .enumerate()
        .map(|(i, l)| serde_json::from_str(l).map_err(|e| format!("line {}: {e}", i + 1)))
        .collect()
}

/// Runs the program `entry` below `base` with both engines (child processes
/// if `settings.exe` is set, else this thread).
pub fn run_both(base: &Path, entry: &Entry, settings: &Settings) -> Runs {
    let mut runs = Runs::default();
    for engine in Engine::ALL {
        let s = Settings {
            engine,
            ..settings.clone()
        };
        let seen = match &s.exe {
            Some(exe) => oracle::run_isolated_observed(exe, base, entry, &s).1,
            None => oracle::run_entry_observed(base, entry, &s).1,
        };
        match engine {
            Engine::Ast => runs.ast = seen,
            Engine::Ir => runs.ir = seen,
        }
    }
    runs
}

/// Runs both engines on each entry below `base` on a pool.
///
/// Calls `emit` once for each entry with its index and its runs, in the
/// order in which the entries end. A panic or a timeout of the pool gives a
/// run with the status `stopped` or `timeout` for both engines.
///
/// # Errors
///
/// Returns [`Error::Thread`] if the system cannot start a worker thread.
pub fn run_all(
    base: &Path,
    entries: Vec<Entry>,
    settings: &Settings,
    mut emit: impl FnMut(usize, Runs),
) -> Result<(), Error> {
    let dir = base.to_path_buf();
    let s = settings.clone();
    let runs = u32::try_from(2 * (CONFIGS.len() + 1)).unwrap_or(u32::MAX);
    let limit = settings
        .limit
        .saturating_mul(runs)
        .saturating_add(std::time::Duration::from_secs(120));
    let work: pool::Work<Runs> = Arc::new(move |e: &Entry| run_both(&dir, e, &s));
    pool::run(entries, settings.workers, limit, work, |i, _, ended| {
        let runs = match ended {
            Ended::Done(r) => r,
            Ended::Panic { text, .. } => {
                let o = Observation::bare(0, oracle::Verdict::Fault, "stopped", text);
                Runs {
                    ast: vec![o.clone()],
                    ir: vec![o],
                }
            }
            Ended::Timeout => {
                let o = Observation::bare(0, oracle::Verdict::Timeout, "timeout", "");
                Runs {
                    ast: vec![o.clone()],
                    ir: vec![o],
                }
            }
        };
        emit(i, runs);
    })
}

/// True if the sample of `percent` with the seed `seed` holds the program
/// with the hash `hash`: the first 8 bytes of the SHA-256 of `seed:hash`,
/// modulo 100, are below `percent`.
pub fn in_sample(hash: &str, percent: u64, seed: u64) -> bool {
    let d = Sha256::digest(format!("{seed}:{hash}").as_bytes());
    let mut n = [0u8; 8];
    n.copy_from_slice(d.get(..8).unwrap_or(&[0; 8]));
    u64::from_be_bytes(n) % 100 < percent
}

/// The report of the differential.
#[derive(Clone, Debug, Default)]
pub struct Report {
    /// Lines for the head of the report.
    pub notes: Vec<String>,
    /// One row for each program that ran.
    pub rows: Vec<Row>,
    /// The problems of the engine entries of the ledger.
    pub problems: Vec<String>,
    /// The ledger: the label and the class of each engine entry, by its index.
    pub entries: BTreeMap<usize, (String, Kind)>,
}

impl Report {
    /// The rows with a difference that no entry accepts.
    pub fn unledgered(&self) -> Vec<&Row> {
        self.rows
            .iter()
            .filter(|r| matches!(r.result, Result1::Differ { entry: None, .. }))
            .collect()
    }

    /// True if each difference has an entry and the ledger has no problem.
    pub fn passes(&self) -> bool {
        self.unledgered().is_empty() && self.problems.is_empty()
    }

    /// The number of programs that are the same, that fall back, and that
    /// differ.
    pub fn counts(&self) -> (usize, usize, usize) {
        let mut n = (0, 0, 0);
        for r in &self.rows {
            match r.result {
                Result1::Same => n.0 += 1,
                Result1::Fallback(_) => n.1 += 1,
                Result1::Differ { .. } => n.2 += 1,
            }
        }
        n
    }

    /// The number of differences that each entry accepts, by the index of
    /// the entry.
    pub fn entry_counts(&self) -> BTreeMap<usize, usize> {
        let mut out = BTreeMap::new();
        for r in &self.rows {
            if let Result1::Differ { entry: Some(k), .. } = r.result {
                *out.entry(k).or_default() += 1;
            }
        }
        out
    }

    /// The number of differences of each class: the class of the entry that
    /// accepts the difference, or `unledgered`.
    pub fn class_counts(&self) -> BTreeMap<String, usize> {
        let mut out = BTreeMap::new();
        for r in &self.rows {
            if let Result1::Differ { entry, .. } = &r.result {
                let name = entry
                    .and_then(|k| self.entries.get(&k))
                    .map_or("unledgered", |(_, kind)| kind.name());
                *out.entry(name.to_string()).or_default() += 1;
            }
        }
        out
    }

    /// The report as Markdown.
    pub fn to_markdown(&self) -> String {
        let mut md = String::from("# Engine differential\n\n");
        for n in &self.notes {
            let _ = writeln!(md, "- {n}");
        }
        let (same, fallback, differ) = self.counts();
        let verdict = if self.passes() {
            "passes"
        } else {
            "fails: a difference has no ledger entry, or the ledger has a problem"
        };
        let _ = writeln!(
            md,
            "- programs: {}; same {same}, fallback {fallback}, differ {differ}; the differential {verdict}\n",
            self.rows.len()
        );
        md.push_str("## Differences by class\n\n| class | programs |\n|---|---:|\n");
        for (c, n) in self.class_counts() {
            let _ = writeln!(md, "| {c} | {n} |");
        }
        md.push_str("\n## Ledger entries\n\n| entry | class | programs |\n|---|---|---:|\n");
        let counts = self.entry_counts();
        for (k, (label, kind)) in &self.entries {
            let n = counts.get(k).copied().unwrap_or(0);
            let _ = writeln!(md, "| {} {label} | {} | {n} |", k + 1, kind.name());
        }
        let mut fallbacks: BTreeMap<&str, usize> = BTreeMap::new();
        for r in &self.rows {
            if let Result1::Fallback(why) = &r.result {
                *fallbacks.entry(why.as_str()).or_default() += 1;
            }
        }
        if !fallbacks.is_empty() {
            md.push_str("\n## Fallbacks\n\n| reason | programs |\n|---|---:|\n");
            for (why, n) in fallbacks {
                let _ = writeln!(md, "| {} | {n} |", why.replace('|', "\\|"));
            }
        }
        md.push_str("\n## Problems\n\n");
        if self.problems.is_empty() {
            md.push_str("None.\n");
        }
        for p in &self.problems {
            let _ = writeln!(md, "- {p}");
        }
        md.push_str("\n## Differences\n\n");
        md.push_str("| path | checker | config | class | shapes | ast | ir |\n|---|---|---:|---|---|---|---|\n");
        for r in &self.rows {
            let Result1::Differ { diff, entry, kinds } = &r.result else {
                continue;
            };
            let class = entry
                .and_then(|k| self.entries.get(&k))
                .map_or("**unledgered**", |(_, kind)| kind.name());
            let shapes: Vec<&str> = kinds.iter().map(|k| k.name()).collect();
            let _ = writeln!(
                md,
                "| {} | {} | {} | {class} | {} | {} | {} |",
                r.path,
                if r.rejected { "rejects" } else { "accepts" },
                diff.config,
                shapes.join(" "),
                cell(diff.ast.as_ref()),
                cell(diff.ir.as_ref()),
            );
        }
        md
    }

    /// The differences as JSON lines: one object for each program that
    /// differs.
    pub fn differences_jsonl(&self) -> String {
        let mut out = String::new();
        for r in &self.rows {
            let Result1::Differ { diff, entry, kinds } = &r.result else {
                continue;
            };
            let v = serde_json::json!({
                "path": r.path,
                "rejected": r.rejected,
                "rerun": r.rerun,
                "entry": entry.map(|k| k + 1),
                "class": entry.and_then(|k| self.entries.get(&k)).map(|(_, kind)| kind.name()),
                "shapes": kinds.iter().map(|k| k.name()).collect::<Vec<_>>(),
                "diff": diff,
            });
            out.push_str(&v.to_string());
            out.push('\n');
        }
        out
    }
}

/// A short text of a run for a table cell.
fn cell(o: Option<&Observation>) -> String {
    let Some(o) = o else {
        return "no run".to_string();
    };
    let mut t = o.status.clone();
    if !o.message.is_empty() {
        let m: String = o.message.chars().take(80).collect();
        let _ = write!(t, ": {m}");
    }
    if let Some(l) = o.line {
        let _ = write!(t, " (line {l})");
    }
    let out: String = o.output.chars().take(60).collect();
    let _ = write!(t, "; out `{}`", out.replace('\n', "⏎"));
    t.replace('|', "\\|")
}

/// The paths of each entry that a ledger entry can name: its path, its other
/// paths, and (for tier 2) the same paths below `alias`.
pub fn entry_paths(e: &Entry, alias: Option<&str>) -> Vec<String> {
    let mut p: Vec<String> = std::iter::once(e.path.clone())
        .chain(e.others.iter().cloned())
        .collect();
    if let Some(a) = alias {
        let more: Vec<String> = p.iter().map(|x| format!("{a}/{x}")).collect();
        p.extend(more);
    }
    p
}

/// The hashes of the programs that the checker rejects, from the `old`
/// records of a tier: the records of kind `ok` with an error. A record of a
/// check that does not end or that crashes is not a rejection.
pub fn rejected_hashes(records: &[crate::snapshot::Record]) -> BTreeSet<String> {
    records
        .iter()
        .filter(|r| r.kind == crate::snapshot::Kind::Ok && !crate::classify::errors(r).is_empty())
        .map(|r| r.hash.clone())
        .collect()
}
