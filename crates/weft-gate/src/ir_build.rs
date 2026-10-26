//! The `ir-build` command: the builder of the IR and its verifier on each
//! program of a tier (plan stage B12).
//!
//! For each program the command loads the package, analyzes it, builds the IR
//! ([`weft_sema::irbuild::build`], which runs the verifier) and counts the
//! outcomes of the bodies ([`thir::IrCounts`]): the bodies that the builder
//! lowers, the bodies with no IR for each reason, the bodies that it does not
//! lower (none, since stage B12), and the rules that the IR breaks. The pool
//! catches a panic of one program, so a panic does not hide the other
//! programs. The summary also lists the programs whose build takes the most
//! time.

use std::fmt::Write as _;
use std::path::Path;
use std::sync::Arc;
use std::time::{Duration, Instant};

use crate::manifest::Entry;
use crate::pool::{self, Ended};
use crate::thir::{self, IrCounts};
use crate::Error;

/// The most programs in the list of the slowest builds.
pub const SLOWEST: usize = 20;

/// The most programs in each list of a summary.
pub const NOTES: usize = 400;

/// What `ir-build` made of one program.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Outcome {
    /// Why the program does not load, if it does not.
    pub error: Option<String>,
    /// What the builder made of the bodies.
    pub ir: IrCounts,
    /// The time of the analysis, in milliseconds.
    pub analyze_ms: u64,
    /// The time of the build and the verifier, in milliseconds.
    pub build_ms: u64,
}

/// The time from `at` to now in milliseconds.
fn ms_since(at: Instant) -> u64 {
    u64::try_from(at.elapsed().as_millis()).unwrap_or(u64::MAX)
}

/// Builds the IR of program `entry` below `base`, on this thread.
pub fn check(base: &Path, entry: &Entry) -> Outcome {
    let path = base.join(&entry.path);
    let pkg = match weft_cli::package::load(&path) {
        Ok(p) => p,
        Err(e) => {
            return Outcome {
                error: Some(format!("{e:#}")),
                ..Outcome::default()
            }
        }
    };
    let opts = pkg.options(weft_cli::package::Profile::default());
    let start = Instant::now();
    let analysis = weft_sema::analyze(&pkg.units, opts);
    let analyze_ms = ms_since(start);
    let start = Instant::now();
    let ir = thir::ir_counts(&analysis);
    let build_ms = ms_since(start);
    Outcome {
        error: None,
        ir,
        analyze_ms,
        build_ms,
    }
}

/// The time of one program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Timing {
    /// The program, relative to the base.
    pub path: String,
    /// The time of the analysis, in milliseconds.
    pub analyze_ms: u64,
    /// The time of the build and the verifier, in milliseconds.
    pub build_ms: u64,
}

/// The totals of `ir-build` over the programs of a tier.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Summary {
    /// The programs.
    pub programs: usize,
    /// The programs that load.
    pub loaded: usize,
    /// The programs that do not load (a parse error, a bad manifest).
    pub load_errors: usize,
    /// The programs whose analysis or build panicked, each with the text of
    /// the panic.
    pub crashes: Vec<String>,
    /// The programs that took more than the time limit.
    pub timeouts: Vec<String>,
    /// What the builder made of the bodies.
    pub ir: IrCounts,
    /// The programs whose IR breaks a rule of the verifier, with the rules.
    pub ir_broken: Vec<String>,
    /// The programs with an unsupported body.
    pub unsupported_programs: Vec<String>,
    /// The total time of the analyses, in milliseconds.
    pub analyze_ms: u64,
    /// The total time of the builds and the verifier, in milliseconds.
    pub build_ms: u64,
    /// The programs whose build takes the most time, the slowest first.
    pub slowest: Vec<Timing>,
}

impl Summary {
    /// Adds the outcome of program `path`.
    pub fn add(&mut self, path: &str, o: Outcome) {
        self.programs += 1;
        if o.error.is_some() {
            self.load_errors += 1;
            return;
        }
        self.loaded += 1;
        if !o.ir.broken.is_empty() && self.ir_broken.len() < NOTES {
            self.ir_broken
                .push(format!("{path}: {}", o.ir.broken.join("; ")));
        }
        if !o.ir.unsupported.is_empty() && self.unsupported_programs.len() < NOTES {
            self.unsupported_programs.push(path.to_string());
        }
        self.ir.add(IrCounts {
            broken: Vec::new(),
            ..o.ir
        });
        self.analyze_ms = self.analyze_ms.saturating_add(o.analyze_ms);
        self.build_ms = self.build_ms.saturating_add(o.build_ms);
        let t = Timing {
            path: path.to_string(),
            analyze_ms: o.analyze_ms,
            build_ms: o.build_ms,
        };
        let at = self
            .slowest
            .iter()
            .position(|s| (s.build_ms, &s.path) < (t.build_ms, &t.path))
            .unwrap_or(self.slowest.len());
        if at < SLOWEST {
            self.slowest.insert(at, t);
            self.slowest.truncate(SLOWEST);
        }
    }

    /// Returns true if the builder is total and correct on each program: no
    /// panic, no broken rule and no unsupported body. A timeout does not fail:
    /// the summary lists it.
    pub fn holds(&self) -> bool {
        self.crashes.is_empty() && self.ir_broken.is_empty() && self.ir.unsupported.is_empty()
    }

    /// The summary as Markdown.
    pub fn to_markdown(&self, title: &str) -> String {
        let mut s = format!("# The builder of the IR, {title}\n\n");
        let _ = writeln!(
            s,
            "{} programs ({} load, {} do not load, {} panic, {} time out).\n",
            self.programs,
            self.loaded,
            self.load_errors,
            self.crashes.len(),
            self.timeouts.len(),
        );
        let _ = writeln!(
            s,
            "{} bodies built, {} with no IR, {} unsupported; {} programs whose IR breaks a rule.\n",
            self.ir.built,
            self.ir.no_ir,
            self.ir.unsupported.values().sum::<usize>(),
            self.ir_broken.len()
        );
        let _ = writeln!(
            s,
            "Time: analysis {:.1} s, build and verifier {:.1} s (the sum over the programs).\n",
            ms_to_s(self.analyze_ms),
            ms_to_s(self.build_ms)
        );
        s.push_str("| no IR: reason | bodies |\n| --- | --- |\n");
        for (r, n) in &self.ir.no_ir_reasons {
            let _ = writeln!(s, "| {r} | {n} |");
        }
        if !self.ir.unsupported.is_empty() {
            s.push_str("\n| unsupported construct (stage) | bodies |\n| --- | --- |\n");
            for (c, n) in &self.ir.unsupported {
                let _ = writeln!(s, "| {c} | {n} |");
            }
        }
        s.push_str("\n## The slowest builds\n\n| program | analysis (ms) | build and verifier (ms) |\n| --- | --- | --- |\n");
        for t in &self.slowest {
            let _ = writeln!(s, "| `{}` | {} | {} |", t.path, t.analyze_ms, t.build_ms);
        }
        for p in &self.ir_broken {
            let _ = writeln!(s, "- broken: `{p}`");
        }
        for (what, list) in [
            ("Unsupported", &self.unsupported_programs),
            ("Panics", &self.crashes),
            ("Timeouts", &self.timeouts),
        ] {
            if !list.is_empty() {
                let _ = writeln!(s, "\n## {what}\n");
                for p in list {
                    let _ = writeln!(s, "- `{p}`");
                }
            }
        }
        s
    }
}

/// Returns `ms` in seconds.
fn ms_to_s(ms: u64) -> f64 {
    // The sums stay far below 2^52 ms, so the conversion is exact.
    #[allow(clippy::cast_precision_loss)]
    let x = ms as f64;
    x / 1000.0
}

/// Builds the IR of each entry below `base` on `workers` worker threads, with
/// time limit `limit` for each program.
///
/// # Errors
///
/// Returns [`Error::Thread`] if the system cannot start a worker thread.
pub fn run(
    base: &Path,
    entries: Vec<Entry>,
    workers: usize,
    limit: Duration,
    progress: impl FnMut(usize),
) -> Result<Summary, Error> {
    let root = base.to_path_buf();
    let work: pool::Work<Outcome> = Arc::new(move |e: &Entry| check(&root, e));
    run_work(entries, workers, limit, work, progress)
}

/// [`run`] with the work `work` for each entry.
///
/// # Errors
///
/// Returns [`Error::Thread`] if the system cannot start a worker thread.
pub fn run_work(
    entries: Vec<Entry>,
    workers: usize,
    limit: Duration,
    work: pool::Work<Outcome>,
    mut progress: impl FnMut(usize),
) -> Result<Summary, Error> {
    let mut sum = Summary::default();
    let mut ended = 0;
    pool::run(entries, workers, limit, work, |_, entry, end| {
        match end {
            Ended::Done(o) => sum.add(&entry.path, o),
            Ended::Panic { text, .. } => {
                sum.programs += 1;
                sum.crashes.push(format!("{}: {text}", entry.path));
            }
            Ended::Timeout => {
                sum.programs += 1;
                sum.timeouts.push(entry.path.clone());
            }
        }
        ended += 1;
        progress(ended);
    })?;
    sum.crashes.sort();
    sum.timeouts.sort();
    sum.ir_broken.sort();
    sum.unsupported_programs.sort();
    Ok(sum)
}
