//! The `thir` command: test D0, part 1, on each program of a tier (plan stage
//! T3), and the builder of the IR on the same analysis (plan stage B3).
//!
//! For each program the command loads the package, analyzes it and runs
//! [`weft_sema::thir::d0::d0`] on the THIR tables that the old lowering
//! records. [`Summary`] counts the failures of each check and keeps examples.
//! Then it builds the IR ([`weft_sema::irbuild::build`]) and counts the bodies
//! that the builder lowers, the bodies that it does not lower yet (for each
//! construct), and the rules that the IR breaks (each one is a bug of the
//! builder).

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::Path;
use std::sync::Arc;
use std::time::Duration;

use weft_sema::thir::d0::{self, Check};

use crate::manifest::Entry;
use crate::pool::{self, Ended};
use crate::Error;

/// The most examples of each check in a summary.
pub const EXAMPLES: usize = 12;

/// The most notes in a summary.
pub const NOTES: usize = 400;

/// One failure of D0, with its program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Example {
    /// The program, relative to the base.
    pub path: String,
    /// The file and the line of the failure.
    pub at: String,
    /// The body.
    pub body: String,
    /// What is wrong.
    pub text: String,
}

/// The result of D0 on one program.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Outcome {
    /// The report, or the error of the load.
    pub report: Option<d0::Report>,
    /// The file and the line of each finding, in the order of the findings.
    pub lines: Vec<String>,
    /// The file and the line of each note, in the order of the notes.
    pub note_lines: Vec<String>,
    /// Why the program has no report.
    pub error: Option<String>,
    /// What the builder of the IR made of the program.
    pub ir: IrCounts,
}

/// What the builder of the IR made of the bodies of one or more programs.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct IrCounts {
    /// The bodies that the builder lowers.
    pub built: usize,
    /// The bodies with no IR (a `typeck` error).
    pub no_ir: usize,
    /// The bodies that the builder does not lower yet, for each construct (its
    /// name and the plan stage that lowers it).
    pub unsupported: BTreeMap<String, usize>,
    /// The rules that the IR breaks, as text.
    pub broken: Vec<String>,
}

impl IrCounts {
    /// Adds the counts of `o`.
    pub fn add(&mut self, o: Self) {
        self.built += o.built;
        self.no_ir += o.no_ir;
        for (k, n) in o.unsupported {
            *self.unsupported.entry(k).or_default() += n;
        }
        self.broken.extend(o.broken);
    }
}

/// Builds the IR of `analysis` and counts the outcomes.
fn ir_counts(analysis: &weft_sema::Analysis) -> IrCounts {
    let b = weft_sema::irbuild::build(analysis);
    let (built, no_ir, unsupported) = b.counts();
    IrCounts {
        built,
        no_ir,
        unsupported: unsupported
            .into_iter()
            .map(|(c, n)| (format!("{} ({})", c.name(), c.stage()), n))
            .collect(),
        broken: b.broken.iter().map(ToString::to_string).collect(),
    }
}

/// Runs D0 on program `entry` below `base`, on this thread.
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
    let analysis = weft_sema::analyze(&pkg.units, opts);
    let report = d0::d0(&analysis);
    let ir = ir_counts(&analysis);
    let at = |f: &d0::Finding| {
        pkg.files.get(f.unit).map_or_else(String::new, |sf| {
            format!(
                "{}:{}",
                crate::digest::relative_name(base, &sf.name),
                sf.line_col(f.span.lo).0
            )
        })
    };
    let lines = report.findings.iter().map(at).collect();
    let note_lines = report.notes.iter().map(at).collect();
    Outcome {
        report: Some(report),
        lines,
        note_lines,
        error: None,
        ir,
    }
}

/// The totals of D0 over the programs of a tier.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Summary {
    /// The programs.
    pub programs: usize,
    /// The programs that D0 checked: they load.
    pub loaded: usize,
    /// The programs that do not load (a parse error, a bad manifest).
    pub load_errors: usize,
    /// The programs whose analysis panicked.
    pub crashes: Vec<String>,
    /// The programs that took more than the time limit.
    pub timeouts: Vec<String>,
    /// The bodies.
    pub bodies: usize,
    /// The bodies that D0 checked.
    pub checked: usize,
    /// The expressions of the checked bodies.
    pub exprs: usize,
    /// The expressions whose type had a free type variable.
    pub free: usize,
    /// The conflicts in the bodies that D0 did not check.
    pub skipped_conflicts: usize,
    /// The number of failures of each check, and the programs with failures.
    pub counts: BTreeMap<Check, (usize, usize)>,
    /// Examples of each check.
    pub examples: BTreeMap<Check, Vec<Example>>,
    /// The notes (`d0::Report::notes`): each conflict in a body that D0 does
    /// not check, and each free type variable.
    pub notes: Vec<Example>,
    /// What the builder of the IR made of the bodies.
    pub ir: IrCounts,
    /// The programs whose IR breaks a rule of the verifier.
    pub ir_broken: Vec<String>,
}

impl Summary {
    /// Adds the outcome of program `path`.
    pub fn add(&mut self, path: &str, o: Outcome) {
        self.programs += 1;
        let Some(r) = o.report else {
            self.load_errors += 1;
            return;
        };
        self.loaded += 1;
        if !o.ir.broken.is_empty() && self.ir_broken.len() < NOTES {
            self.ir_broken
                .push(format!("{path}: {}", o.ir.broken.join("; ")));
        }
        self.ir.add(IrCounts {
            broken: Vec::new(),
            ..o.ir
        });
        self.bodies += r.bodies;
        self.checked += r.checked;
        self.exprs += r.exprs;
        self.free += r.free;
        self.skipped_conflicts += r.skipped_conflicts;
        for (f, at) in r.notes.into_iter().zip(o.note_lines) {
            if self.notes.len() >= NOTES {
                break;
            }
            self.notes.push(Example {
                path: path.to_string(),
                at,
                body: f.body,
                text: f.text,
            });
        }
        let mut seen: Vec<Check> = Vec::new();
        for (f, at) in r.findings.into_iter().zip(o.lines) {
            let c = self.counts.entry(f.check).or_default();
            c.0 += 1;
            if !seen.contains(&f.check) {
                seen.push(f.check);
                c.1 += 1;
            }
            let ex = self.examples.entry(f.check).or_default();
            if ex.len() < EXAMPLES && !ex.iter().any(|e| e.path == path) {
                ex.push(Example {
                    path: path.to_string(),
                    at,
                    body: f.body,
                    text: f.text,
                });
            }
        }
    }

    /// Returns true if D0 holds on each program: no failure, no crash and no
    /// timeout. The IR of each program breaks no rule.
    pub fn holds(&self) -> bool {
        self.counts.is_empty()
            && self.crashes.is_empty()
            && self.timeouts.is_empty()
            && self.ir_broken.is_empty()
    }

    /// The summary as Markdown.
    pub fn to_markdown(&self, title: &str) -> String {
        let mut s = format!("# D0 (THIR tables), {title}\n\n");
        let _ = writeln!(
            s,
            "{} programs ({} load, {} do not load, {} crash, {} time out); {} bodies, {} checked; {} expressions, {} with a free type variable; {} conflicts in bodies that D0 does not check.\n",
            self.programs,
            self.loaded,
            self.load_errors,
            self.crashes.len(),
            self.timeouts.len(),
            self.bodies,
            self.checked,
            self.exprs,
            self.free,
            self.skipped_conflicts
        );
        s.push_str("| check | failures | programs |\n| --- | --- | --- |\n");
        for c in Check::ALL {
            let (n, p) = self.counts.get(&c).copied().unwrap_or_default();
            let _ = writeln!(s, "| {} | {n} | {p} |", c.name());
        }
        for (c, ex) in &self.examples {
            let _ = writeln!(s, "\n## {}\n", c.name());
            for e in ex {
                let _ = writeln!(s, "- `{}` {}: {}", e.at, e.body, e.text);
            }
        }
        let _ = writeln!(
            s,
            "\n## The builder of the IR\n\n{} bodies built, {} with no IR (a `typeck` error), {} unsupported; {} programs whose IR breaks a rule.\n",
            self.ir.built,
            self.ir.no_ir,
            self.ir.unsupported.values().sum::<usize>(),
            self.ir_broken.len()
        );
        s.push_str("| unsupported construct (stage) | bodies |\n| --- | --- |\n");
        for (c, n) in &self.ir.unsupported {
            let _ = writeln!(s, "| {c} | {n} |");
        }
        for p in &self.ir_broken {
            let _ = writeln!(s, "- broken: `{p}`");
        }
        if !self.notes.is_empty() {
            s.push_str("\n## Notes (not failures)\n\n");
            for e in &self.notes {
                let _ = writeln!(s, "- `{}` {}: {}", e.at, e.body, e.text);
            }
        }
        for (what, list) in [("Crashes", &self.crashes), ("Timeouts", &self.timeouts)] {
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

/// Runs D0 on each entry below `base` on `workers` worker threads, with time
/// limit `limit` for each program.
///
/// # Errors
///
/// Returns [`Error::Thread`] if the system cannot start a worker thread.
pub fn run(
    base: &Path,
    entries: Vec<Entry>,
    workers: usize,
    limit: Duration,
    mut progress: impl FnMut(usize),
) -> Result<Summary, Error> {
    let root = base.to_path_buf();
    let work: pool::Work<Outcome> = Arc::new(move |e: &Entry| check(&root, e));
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
    for ex in sum.examples.values_mut() {
        ex.sort_by(|a, b| a.path.cmp(&b.path));
    }
    sum.notes
        .sort_by(|a, b| (&a.at, &a.text).cmp(&(&b.at, &b.text)));
    Ok(sum)
}
