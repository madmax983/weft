//! The run of the gate and its report (plan §2.5 and §2.7).
//!
//! [`run`] checks each program of a manifest, reads the oracle verdicts from
//! the cache ([`verdicts`]), classifies each program (`crate::classify`) and
//! applies the rules of §2.5 with the ledger (`crate::ledger`). The result is
//! a [`Report`]: one [`Row`] for each program, the blockers, and the warnings.
//! [`Report::to_markdown`] gives the text of `target/gate/report.md`.
//!
//! Before stage F1 the `ir` pipeline does not exist. Then no program is in
//! scope (§2.6), and the `ir` record of each program is its `old` record: the
//! snapshot runs once. Each program is `same` or `open`.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::Path;
use std::time::Duration;

use crate::classify::{self, Class};
use crate::ledger::{self, Ledger};
use crate::manifest::{self, Entry, Manifest, Options};
use crate::oracle::{self, Cache, Engine, Verdict};
use crate::snapshot::{self, Kind, Pipeline, Record, Settings};
use crate::Error;

/// The sets of tier 1 in which a `new-fp` program blocks, also with a ledger
/// entry: the corpus, the interpreter programs, the examples and the packages.
pub const STRICT_SETS: [&str; 4] = ["corpus", "interp", "examples", "packages"];

/// The construct groups of §2.6.
pub const GROUPS: [char; 6] = ['A', 'B', 'C', 'D', 'E', 'F'];

/// The rules that change from one stage to the next.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Policy {
    /// True if an `open` program needs a ledger entry (of class `open`, `edge`
    /// or `open-old`). False until stage G6 writes the `open-old` entries of
    /// the old pipeline: then an `open` program with no entry is reported, but
    /// it does not block.
    pub open_needs_entry: bool,
}

impl Default for Policy {
    /// The rules of this stage.
    fn default() -> Self {
        Self {
            open_needs_entry: false,
        }
    }
}

/// One program to classify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Input {
    /// The record of the `old` pipeline.
    pub old: Record,
    /// The record of the `ir` pipeline.
    pub ir: Record,
    /// The oracle verdict of the engine of the `ir` pipeline.
    pub verdict: Verdict,
    /// The paths that a ledger entry can match: the path of the manifest
    /// entry, its other paths, and (in tier 2) the same paths below
    /// `tests/gate/probes/`.
    pub paths: Vec<String>,
    /// True if the program uses the `ir` pipeline (§2.6).
    pub in_scope: bool,
}

/// The result of one program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Row {
    /// The path of the manifest entry.
    pub path: String,
    /// The set of the manifest entry.
    pub set: String,
    /// The class.
    pub class: Class,
    /// The oracle verdict.
    pub verdict: Verdict,
    /// True if the program uses the `ir` pipeline.
    pub in_scope: bool,
    /// True if the `old` pipeline accepts the program.
    pub old_accepts: bool,
    /// The index of the ledger entry that accepts the program, from 0.
    pub entry: Option<usize>,
    /// Why the program blocks the gate, or `None`.
    pub blocker: Option<String>,
    /// A note for the report: the errors of the two sides, or the message of
    /// a record that is not `ok`.
    pub note: String,
}

/// The report of a run of the gate.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Report {
    /// Lines for the head of the report (the tier, the interpreter hash).
    pub notes: Vec<String>,
    /// The groups that are on (§2.6). Empty before stage F1.
    pub groups_on: String,
    /// One row for each program, in the order of the manifest.
    pub rows: Vec<Row>,
    /// The blockers: one line for each program that blocks, and for each rule
    /// of the whole run that fails.
    pub blockers: Vec<String>,
    /// The warnings: the stale ledger entries.
    pub warnings: Vec<String>,
}

/// The diagnostics of a record as a short text.
fn errors_text(r: &Record) -> String {
    let errors = classify::errors(r);
    if errors.is_empty() {
        return "accepts".to_string();
    }
    let items: Vec<String> = errors.iter().map(|d| format!("{}@{}", d.0, d.2)).collect();
    items.join(" ")
}

/// The note of a row.
fn note(input: &Input, class: Class) -> String {
    if class == Class::Crash {
        let mut parts = Vec::new();
        if let Some(m) = &input.ir.message {
            parts.push(m.clone());
        }
        parts.extend(input.ir.problems.iter().cloned());
        return parts.join("; ");
    }
    let (o, i) = (errors_text(&input.old), errors_text(&input.ir));
    if o == i {
        o
    } else {
        format!("old: {o}; ir: {i}")
    }
}

impl Report {
    /// Classifies each input and applies the rules of §2.5 with `ledger` and
    /// `policy`.
    pub fn build(inputs: &[Input], ledger: &Ledger, policy: &Policy) -> Self {
        let mut report = Self::default();
        let mut used = vec![false; ledger.entries.len()];
        let mut matched = vec![false; ledger.entries.len()];
        for input in inputs {
            let class = classify::classify(&input.old, &input.ir, input.verdict);
            let mut row = Row {
                path: input.old.path.clone(),
                set: input.old.set.clone(),
                class,
                verdict: input.verdict,
                in_scope: input.in_scope,
                old_accepts: classify::errors(&input.old).is_empty(),
                entry: None,
                blocker: None,
                note: note(input, class),
            };
            let candidates: Vec<usize> = ledger
                .entries
                .iter()
                .enumerate()
                .filter(|(_, e)| e.matches(&input.paths))
                .map(|(k, _)| k)
                .collect();
            for &k in &candidates {
                if let Some(m) = matched.get_mut(k) {
                    *m = true;
                }
            }
            let (entry, blocker) = rule(input, class, &candidates, ledger, *policy);
            if let Some(k) = entry {
                if let Some(u) = used.get_mut(k) {
                    *u = true;
                }
            }
            row.entry = entry;
            if let Some(b) = blocker {
                report
                    .blockers
                    .push(format!("{} {}: {b}", class.name(), row.path));
                row.blocker = Some(b);
            }
            report.rows.push(row);
        }
        report.new_fp_share();
        for (k, e) in ledger.entries.iter().enumerate() {
            let label = format!("ledger entry {} ({})", k + 1, e.label());
            if !matched.get(k).copied().unwrap_or(false) {
                report
                    .warnings
                    .push(format!("{label} matches no program of this run"));
            } else if !used.get(k).copied().unwrap_or(false) {
                report.warnings.push(format!(
                    "{label} matches programs, but it accepts none of them (no program of class `{}` or the entry does not cover its codes)",
                    e.class.program_class().name()
                ));
            }
        }
        report
    }

    /// The rule of §2.5 on the share of `new-fp` in the probes: at most 0.1 %
    /// of the programs of the probe sets that `old` accepts.
    fn new_fp_share(&mut self) {
        let probe = |r: &&Row| !STRICT_SETS.contains(&r.set.as_str());
        let new_fp = self
            .rows
            .iter()
            .filter(probe)
            .filter(|r| r.class == Class::NewFp)
            .count();
        let accepted = self
            .rows
            .iter()
            .filter(probe)
            .filter(|r| r.old_accepts)
            .count();
        if new_fp > 0 && new_fp.saturating_mul(1000) > accepted {
            self.blockers.push(format!(
                "new-fp: {new_fp} programs of the probes are `new-fp`; that is more than 0.1 % of the {accepted} probes that `old` accepts"
            ));
        }
    }

    /// True if the gate has no blocker.
    pub fn passes(&self) -> bool {
        self.blockers.is_empty()
    }

    /// The number of programs of each set and class.
    pub fn counts(&self) -> BTreeMap<(String, Class), usize> {
        let mut out = BTreeMap::new();
        for r in &self.rows {
            *out.entry((r.set.clone(), r.class)).or_default() += 1;
        }
        out
    }

    /// The number of programs of each class.
    pub fn class_counts(&self) -> BTreeMap<Class, usize> {
        let mut out = BTreeMap::new();
        for r in &self.rows {
            *out.entry(r.class).or_default() += 1;
        }
        out
    }

    /// The sets, in the order of their first program.
    fn sets(&self) -> Vec<&str> {
        let mut out: Vec<&str> = Vec::new();
        for r in &self.rows {
            if !out.contains(&r.set.as_str()) {
                out.push(&r.set);
            }
        }
        out
    }

    /// The report as Markdown.
    pub fn to_markdown(&self) -> String {
        let mut md = String::from("# Gate report\n\n");
        for n in &self.notes {
            let _ = writeln!(md, "- {n}");
        }
        let verdict = if self.passes() {
            "passes".to_string()
        } else {
            format!("fails: {} blockers", self.blockers.len())
        };
        let _ = writeln!(md, "- programs: {}; the gate {verdict}\n", self.rows.len());

        md.push_str("## Counts\n\n| set |");
        for c in Class::ALL {
            let _ = write!(md, " {} |", c.name());
        }
        md.push_str(" total |\n|---|");
        md.push_str(&"---:|".repeat(Class::ALL.len() + 1));
        md.push('\n');
        let counts = self.counts();
        let mut rows: Vec<(String, Vec<usize>)> = self
            .sets()
            .into_iter()
            .map(|s| {
                let n = Class::ALL
                    .iter()
                    .map(|c| counts.get(&(s.to_string(), *c)).copied().unwrap_or(0))
                    .collect();
                (s.to_string(), n)
            })
            .collect();
        let all = Class::ALL
            .iter()
            .map(|c| self.class_counts().get(c).copied().unwrap_or(0))
            .collect();
        rows.push(("all".to_string(), all));
        for (s, n) in rows {
            let _ = write!(md, "| {s} |");
            for k in &n {
                let _ = write!(md, " {k} |");
            }
            let _ = writeln!(md, " {} |", n.iter().sum::<usize>());
        }

        md.push_str("\n## Coverage\n\n");
        let on = if self.groups_on.is_empty() {
            "none".to_string()
        } else {
            self.groups_on.clone()
        };
        let _ = writeln!(md, "Groups on: {on}.\n");
        md.push_str("| group | on |\n|---|---|\n");
        for g in GROUPS {
            let yes = if self.groups_on.contains(g) {
                "yes"
            } else {
                "no"
            };
            let _ = writeln!(md, "| {g} | {yes} |");
        }
        md.push_str("\n| set | in scope | programs | share |\n|---|---:|---:|---:|\n");
        for s in self.sets() {
            let total = self.rows.iter().filter(|r| r.set == s).count();
            let scope = self
                .rows
                .iter()
                .filter(|r| r.set == s && r.in_scope)
                .count();
            let share = if total == 0 {
                0.0
            } else {
                f64::from(u32::try_from(scope).unwrap_or(u32::MAX)) * 100.0
                    / f64::from(u32::try_from(total).unwrap_or(u32::MAX))
            };
            let _ = writeln!(md, "| {s} | {scope} | {total} | {share:.1} % |");
        }

        md.push_str("\n## Blockers\n\n");
        if self.blockers.is_empty() {
            md.push_str("None.\n");
        }
        for b in &self.blockers {
            let _ = writeln!(md, "- {b}");
        }
        md.push_str("\n## Warnings\n\n");
        if self.warnings.is_empty() {
            md.push_str("None.\n");
        }
        for w in &self.warnings {
            let _ = writeln!(md, "- {w}");
        }

        md.push_str("\n## Programs that are not `same`\n\n");
        md.push_str("| class | set | path | oracle | ledger | note |\n|---|---|---|---|---|---|\n");
        for r in self.rows.iter().filter(|r| r.class != Class::Same) {
            let entry = r
                .entry
                .map_or_else(String::new, |k| format!("entry {}", k + 1));
            let _ = writeln!(
                md,
                "| {} | {} | `{}` | {} | {entry} | {} |",
                r.class.name(),
                r.set,
                r.path,
                r.verdict.name(),
                cell(&r.note)
            );
        }
        md
    }
}

/// The text for one cell of a Markdown table.
fn cell(text: &str) -> String {
    text.replace('|', "\\|").replace('\n', " ")
}

/// The rule of §2.5 for one program: the ledger entry that accepts it and the
/// reason why it blocks.
fn rule(
    input: &Input,
    class: Class,
    candidates: &[usize],
    ledger: &Ledger,
    policy: Policy,
) -> (Option<usize>, Option<String>) {
    let strict = STRICT_SETS.contains(&input.old.set.as_str());
    match class {
        Class::Same | Class::Fixed => (None, None),
        Class::Crash => (None, Some("the `ir` pipeline crashes".to_string())),
        Class::LostFault => (
            None,
            Some("the `ir` pipeline accepts a program that `old` rejects and the oracle faults on (a regression)".to_string()),
        ),
        Class::NewFp if strict => (
            None,
            Some(format!(
                "a new false positive in the set `{}`",
                input.old.set
            )),
        ),
        _ => {
            let codes = if matches!(class, Class::Moved | Class::Changed) {
                classify::changed_codes(&classify::errors(&input.old), &classify::errors(&input.ir))
            } else {
                Vec::new()
            };
            let applicable: Vec<usize> = candidates
                .iter()
                .copied()
                .filter(|&k| {
                    ledger.entries.get(k).is_some_and(|e| {
                        e.class.program_class() == class && e.accepts_codes(&codes)
                    })
                })
                .collect();
            let complete = applicable
                .iter()
                .copied()
                .find(|&k| ledger.entries.get(k).is_some_and(|e| e.problem().is_none()));
            if let Some(k) = complete {
                return (Some(k), None);
            }
            if let Some((k, e)) = applicable
                .first()
                .and_then(|&k| ledger.entries.get(k).map(|e| (k, e)))
            {
                let why = e.problem().unwrap_or_default();
                return (
                    Some(k),
                    Some(format!("ledger entry {} ({}): {why}", k + 1, e.label())),
                );
            }
            if class == Class::Open && !policy.open_needs_entry {
                return (None, None);
            }
            let need = match class {
                Class::Open => "an entry of class `open` (verdict \"stays\"), `edge` (with an issue) or `open-old`",
                Class::NewFp => "an entry of class `new-fp` with a `reason_class`",
                Class::LostClean => "an entry of class `lost-clean` with `signed_by`",
                Class::Moved => "an entry of class `moved` with a reason",
                _ => "an entry of class `changed` with a reason",
            };
            let codes = if codes.is_empty() {
                String::new()
            } else {
                format!(" for the codes {}", codes.join(", "))
            };
            (
                None,
                Some(format!("the ledger has no entry for it: add {need}{codes}")),
            )
        }
    }
}

/// The oracle verdict of each entry from `cache`, in the order of `entries`.
///
/// # Errors
///
/// Returns [`Error::Stale`] if the cache has no row with the key of an entry
/// (its hash, `engine` and `interp`): the interpreter sources or the programs
/// changed after the last run of the oracle.
pub fn verdicts(
    entries: &[Entry],
    cache: &Cache,
    engine: Engine,
    interp: &str,
) -> Result<Vec<Verdict>, Error> {
    let mut out = Vec::with_capacity(entries.len());
    let mut missing = Vec::new();
    for e in entries {
        match cache.get(&e.hash, engine, interp) {
            Some(row) => out.push(row.verdict),
            None => missing.push(e.path.as_str()),
        }
    }
    if missing.is_empty() {
        return Ok(out);
    }
    let first: Vec<&str> = missing.iter().take(5).copied().collect();
    Err(Error::Stale {
        programs: missing.len(),
        message: format!(
            "the oracle cache `{}` has no verdict for {} programs with the interpreter hash {interp} (the first: {}). The interpreter sources (`{}`) or the programs changed. Run `cargo run -p weft-gate --release -- oracle --engine {} --tier 1` and commit `tests/gate/{}`",
            oracle::cache_name(engine),
            missing.len(),
            first.join(", "),
            oracle::INTERP_SRC,
            engine.name(),
            oracle::cache_name(engine),
        ),
    })
}

/// The settings of [`run`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RunSettings {
    /// The number of worker threads of the snapshot (at least 1).
    pub workers: usize,
    /// The time limit of the check of one program.
    pub limit: Duration,
    /// The rules of this stage.
    pub policy: Policy,
}

impl Default for RunSettings {
    /// One worker for each CPU and the time limit of the snapshot.
    fn default() -> Self {
        Self {
            workers: std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get),
            limit: snapshot::LIMIT,
            policy: Policy::default(),
        }
    }
}

/// Runs the gate on the programs of `manifest` below `base`.
///
/// Reads the verdicts of the `ast` engine for the interpreter `interp` from
/// `cache` first, so a stale cache stops the run before the snapshot. Then
/// checks each program with the `old` pipeline. Before stage F1 no program is
/// in scope, so the `ir` record is the `old` record. `alias` is a directory
/// such as `tests/gate/probes`: a ledger entry can also name a program by its
/// path below it (for tier 2).
///
/// # Errors
///
/// Returns [`Error::Stale`] for a stale cache and [`Error::Thread`] if the
/// system cannot start a worker thread.
pub fn run(
    base: &Path,
    manifest: Manifest,
    cache: &Cache,
    interp: &str,
    ledger: &Ledger,
    settings: &RunSettings,
    alias: Option<&str>,
) -> Result<Report, Error> {
    let verdicts = verdicts(&manifest.entries, cache, Engine::Ast, interp)?;
    let paths: Vec<Vec<String>> = manifest
        .entries
        .iter()
        .map(|e| {
            let mut p: Vec<String> = std::iter::once(e.path.clone())
                .chain(e.others.iter().cloned())
                .collect();
            if let Some(a) = alias {
                let more: Vec<String> = p.iter().map(|x| format!("{a}/{x}")).collect();
                p.extend(more);
            }
            p
        })
        .collect();
    let total = manifest.entries.len();
    let snap = Settings {
        pipeline: Pipeline::Old,
        workers: settings.workers.max(1),
        limit: settings.limit,
    };
    snapshot::install_panic_hook();
    let mut records: Vec<Option<Record>> = vec![None; total];
    snapshot::snapshot(base, manifest.entries, &snap, |i, o| {
        if let Some(slot) = records.get_mut(i) {
            *slot = Some(o.record);
        }
    })?;
    let mut inputs = Vec::with_capacity(total);
    let mut not_ok = BTreeMap::<Kind, usize>::new();
    for ((record, verdict), paths) in records.into_iter().zip(verdicts).zip(paths) {
        let Some(old) = record else {
            continue;
        };
        if old.kind != Kind::Ok {
            *not_ok.entry(old.kind).or_default() += 1;
        }
        inputs.push(Input {
            ir: old.clone(),
            old,
            verdict,
            paths,
            in_scope: false,
        });
    }
    let mut report = Report::build(&inputs, ledger, &settings.policy);
    report.notes.push(format!(
        "oracle: the `ast` engine, interpreter hash {interp}"
    ));
    report.notes.push(
        "the `ir` pipeline does not exist before stage F1: no program is in scope, and the `ir` record of each program is its `old` record".to_string(),
    );
    report.notes.push(format!(
        "time limit of a check: {} s, {} workers",
        settings.limit.as_secs(),
        snap.workers
    ));
    let kinds: Vec<String> = not_ok
        .iter()
        .map(|(k, n)| format!("{n} {}", k.name()))
        .collect();
    if !kinds.is_empty() {
        let why = if not_ok.contains_key(&Kind::Timeout) {
            " (a debug build is slower, so it can give more timeouts)"
        } else {
            ""
        };
        report.notes.push(format!(
            "records that are not `ok`: {}{why}",
            kinds.join(", ")
        ));
    }
    Ok(report)
}

/// Runs the gate on tier 1 of the repository `repo`: the manifest of the
/// tier-1 roots, the committed oracle cache `tests/gate/oracle-ast.tsv`, and
/// the ledger [`ledger::LEDGER`].
///
/// # Errors
///
/// Returns the errors of [`run`], and an error if the manifest, the cache or
/// the ledger cannot be read.
pub fn run_tier1(repo: &Path, settings: &RunSettings) -> Result<Report, Error> {
    let m = manifest::build(
        repo,
        &manifest::tier1_roots(),
        Options {
            exclude_copies: false,
        },
    )?;
    let file = repo
        .join("tests/gate")
        .join(oracle::cache_name(Engine::Ast));
    let text = std::fs::read_to_string(&file).map_err(|e| Error::io(&file, e))?;
    let cache = Cache::from_tsv(&text)?;
    let interp = oracle::interp_hash(repo)?;
    let ledger = Ledger::read(&repo.join(ledger::LEDGER))?;
    let mut report = run(repo, m, &cache, &interp, &ledger, settings, None)?;
    report.notes.insert(0, "tier 1".to_string());
    Ok(report)
}
