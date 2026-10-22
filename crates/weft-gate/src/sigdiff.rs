//! The `sigdiff` command: the signature diff of plan stage F6.
//!
//! The `ir` pipeline infers the effects of a function with the fixpoint of
//! its summaries (`docs/ir.md` 6.8). For each program in scope (with the
//! groups that are on), the command compares the `EffectSig` of each
//! function of the program that the `ir` pipeline gives
//! (`weft_sema::analysis::sig::to_effect_sig`) with the `EffectSig` of the
//! old inference. It compares each part; a `mut` place is its root and its
//! steps, and its text is a part of its own (`muts text`: W0701 shows it).
//!
//! Each difference needs a ledger entry of class `sig`
//! (`tests/gate/ledger.toml`) whose files match the program and whose
//! `parts` hold each part that differs (no `parts`: each part), with a
//! reason. A difference with no entry fails the command.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::Path;
use std::sync::Arc;
use std::time::Duration;

use weft_sema::program::{EffectSig, SigPlace, SigStep};
use weft_sema::{FactGen, Groups};

use crate::ledger::{EntryClass, Ledger};
use crate::manifest::Entry;
use crate::pool::{self, Ended};
use crate::Error;

/// The most differences that the report lists.
pub const LISTED: usize = 400;

/// A `mut` place with no text: its root and the kinds of its steps.
fn place_key(p: &SigPlace) -> String {
    let steps: Vec<String> = p
        .steps
        .iter()
        .map(|s| match s {
            SigStep::Step(st, _) => format!("{st:?}"),
            other => format!("{other:?}"),
        })
        .collect();
    format!("{:?}/{}", p.root, steps.join("/"))
}

/// The names of the parts of `old` and `ir` that differ. Each field of
/// [`EffectSig`] is named, so a new field needs a decision here.
pub fn compare(old: &EffectSig, ir: &EffectSig) -> Vec<&'static str> {
    let EffectSig {
        muts,
        named,
        passthrough,
        lent,
        ret,
        stores,
        reaches,
        reach_given,
        reach_repeats,
        multi,
        tasks,
        task_runs,
        pins,
        op_fns,
        op_effects,
        task_effects,
        repeats,
        fn_stores,
        ret_refs,
        group_stores,
        fn_store_refs,
        drops,
        holds,
        raises,
    } = old;
    let mut out = Vec::new();
    let keys = |ms: &[SigPlace]| {
        let mut k: Vec<String> = ms.iter().map(place_key).collect();
        k.sort();
        k
    };
    let texts = |ms: &[SigPlace]| {
        let mut k: Vec<String> = ms
            .iter()
            .map(|m| format!("{} {}", place_key(m), m.text))
            .collect();
        k.sort();
        k
    };
    if keys(muts) != keys(&ir.muts) {
        out.push("muts");
    } else if texts(muts) != texts(&ir.muts) {
        out.push("muts text");
    }
    let mut part = |name: &'static str, same: bool| {
        if !same {
            out.push(name);
        }
    };
    part("named", *named == ir.named);
    part("passthrough", *passthrough == ir.passthrough);
    part("lent", *lent == ir.lent);
    part("ret", *ret == ir.ret);
    part("stores", *stores == ir.stores);
    part("reaches", *reaches == ir.reaches);
    part("reach_given", *reach_given == ir.reach_given);
    part("reach_repeats", *reach_repeats == ir.reach_repeats);
    part("multi", *multi == ir.multi);
    part("tasks", *tasks == ir.tasks);
    part("task_runs", *task_runs == ir.task_runs);
    part("pins", *pins == ir.pins);
    part("op_fns", *op_fns == ir.op_fns);
    part("op_effects", *op_effects == ir.op_effects);
    part("task_effects", *task_effects == ir.task_effects);
    part("repeats", *repeats == ir.repeats);
    part("fn_stores", *fn_stores == ir.fn_stores);
    part("ret_refs", *ret_refs == ir.ret_refs);
    part("group_stores", *group_stores == ir.group_stores);
    part("fn_store_refs", *fn_store_refs == ir.fn_store_refs);
    part("drops", *drops == ir.drops);
    part("holds", *holds == ir.holds);
    part("raises", *raises == ir.raises);
    out
}

/// A short text of the parts of a signature that the diff shows.
fn show(e: &EffectSig) -> String {
    let muts: Vec<&str> = e.muts.iter().map(|m| m.text.as_str()).collect();
    let named: Vec<&str> = e.named.iter().map(String::as_str).collect();
    format!(
        "mut({}) [{}]{}{}",
        muts.join(", "),
        named.join(", "),
        if e.raises { " raises" } else { "" },
        if e.multi { " multi" } else { "" },
    )
}

/// One function whose signatures differ.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnDiff {
    /// The path of the function.
    pub function: String,
    /// The parts that differ ([`compare`]).
    pub parts: Vec<&'static str>,
    /// The signature of the old inference, as a short text.
    pub old: String,
    /// The signature of the `ir` pipeline.
    pub ir: String,
}

/// What `sigdiff` made of one program.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Outcome {
    /// Why the program does not load, if it does not.
    pub error: Option<String>,
    /// The program is in scope of the `ir` pipeline.
    pub in_scope: bool,
    /// The functions that the command compares.
    pub fns: usize,
    /// The functions whose signatures differ.
    pub diffs: Vec<FnDiff>,
}

/// Compares the signatures of program `entry` below `base`, with the groups
/// `groups` on, on this thread.
pub fn check(base: &Path, entry: &Entry, groups: Groups) -> Outcome {
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
    let mut opts = pkg.options(weft_cli::package::Profile::default());
    opts.facts = FactGen::Both;
    opts.ir_groups = groups;
    let a = weft_sema::analyze(&pkg.units, opts);
    let Some(ir) = a.ir_facts.as_ref() else {
        return Outcome::default();
    };
    let mut out = Outcome {
        in_scope: true,
        ..Outcome::default()
    };
    for f in a.program.fn_ids() {
        let def = &a.program.fns[f];
        if def.is_std || def.decl.body.is_none() {
            continue;
        }
        let (Some(old), Some(new)) = (a.sigs.get(f.index()), ir.sigs.get(f.index())) else {
            continue;
        };
        out.fns += 1;
        let parts = compare(&old.effects, &new.effects);
        if !parts.is_empty() {
            out.diffs.push(FnDiff {
                function: def.path.clone(),
                parts,
                old: show(&old.effects),
                ir: show(&new.effects),
            });
        }
    }
    out
}

/// One difference of the report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Listed {
    /// The program.
    pub path: String,
    /// The difference.
    pub diff: FnDiff,
    /// The ledger entry (index from 1) that accepts it, if one does.
    pub entry: Option<usize>,
}

/// The totals of `sigdiff` over the programs of a tier.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Summary {
    /// The programs.
    pub programs: usize,
    /// The programs that do not load.
    pub load_errors: usize,
    /// The programs in scope.
    pub in_scope: usize,
    /// The functions that the command compares.
    pub fns: usize,
    /// The functions whose signatures are the same.
    pub same: usize,
    /// The number of functions with a difference of each part.
    pub by_part: BTreeMap<&'static str, usize>,
    /// The differences, at most [`LISTED`].
    pub listed: Vec<Listed>,
    /// The differences with no ledger entry.
    pub unledgered: usize,
    /// The number of differences that each ledger entry accepts.
    pub by_entry: BTreeMap<usize, usize>,
    /// The programs whose analysis panicked.
    pub crashes: Vec<String>,
    /// The programs that took more than the time limit.
    pub timeouts: Vec<String>,
}

/// The ledger entry (index from 1) of class `sig` that accepts the
/// difference `d` of program `path`: its files match the program and its
/// `parts` hold each part of the difference.
pub fn entry_of(ledger: &Ledger, path: &str, d: &FnDiff) -> Option<usize> {
    ledger
        .entries
        .iter()
        .enumerate()
        .find(|(_, e)| {
            e.class == EntryClass::Sig
                && e.matches(&[path])
                && (e.parts.is_empty() || d.parts.iter().all(|p| e.parts.iter().any(|k| k == p)))
        })
        .map(|(i, _)| i + 1)
}

impl Summary {
    /// Adds the outcome of program `path`.
    pub fn add(&mut self, path: &str, o: Outcome, ledger: &Ledger) {
        self.programs += 1;
        if o.error.is_some() {
            self.load_errors += 1;
            return;
        }
        if !o.in_scope {
            return;
        }
        self.in_scope += 1;
        self.fns += o.fns;
        self.same += o.fns.saturating_sub(o.diffs.len());
        for d in o.diffs {
            for p in &d.parts {
                *self.by_part.entry(p).or_insert(0) += 1;
            }
            let entry = entry_of(ledger, path, &d);
            match entry {
                Some(i) => *self.by_entry.entry(i).or_insert(0) += 1,
                None => self.unledgered += 1,
            }
            if self.listed.len() < LISTED {
                self.listed.push(Listed {
                    path: path.to_string(),
                    diff: d,
                    entry,
                });
            }
        }
    }

    /// True if each difference has a ledger entry and no program panics.
    pub fn holds(&self) -> bool {
        self.unledgered == 0 && self.crashes.is_empty()
    }

    /// The summary as Markdown.
    pub fn to_markdown(&self, title: &str) -> String {
        let mut s = format!("# The signature diff, {title}\n\n");
        let _ = writeln!(
            s,
            "{} programs ({} do not load, {} panic, {} time out); {} in scope.\n",
            self.programs,
            self.load_errors,
            self.crashes.len(),
            self.timeouts.len(),
            self.in_scope
        );
        let _ = writeln!(
            s,
            "{} functions: {} with the same signature, {} with a difference ({} with no ledger entry).\n",
            self.fns,
            self.same,
            self.fns.saturating_sub(self.same),
            self.unledgered
        );
        if !self.by_part.is_empty() {
            s.push_str("| part | functions |\n| --- | --- |\n");
            for (p, n) in &self.by_part {
                let _ = writeln!(s, "| {p} | {n} |");
            }
        }
        if !self.by_entry.is_empty() {
            s.push_str("\n| ledger entry | differences |\n| --- | --- |\n");
            for (e, n) in &self.by_entry {
                let _ = writeln!(s, "| {e} | {n} |");
            }
        }
        if !self.listed.is_empty() {
            s.push_str("\n## Differences\n\n");
            for l in &self.listed {
                let entry = l
                    .entry
                    .map_or_else(|| "no entry".to_string(), |i| format!("entry {i}"));
                let _ = writeln!(
                    s,
                    "- `{}` `{}` ({}; {}): old `{}`, ir `{}`",
                    l.path,
                    l.diff.function,
                    l.diff.parts.join(", "),
                    entry,
                    l.diff.old,
                    l.diff.ir
                );
            }
        }
        for (what, list) in [("Panics", &self.crashes), ("Timeouts", &self.timeouts)] {
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

/// Compares the signatures of each entry below `base` on `workers` worker
/// threads, with time limit `limit` for each program, the groups `groups`
/// on, and the entries of class `sig` of `ledger`.
///
/// # Errors
///
/// Returns [`Error::Thread`] if the system cannot start a worker thread.
pub fn run(
    base: &Path,
    entries: Vec<Entry>,
    workers: usize,
    limit: Duration,
    groups: Groups,
    ledger: &Ledger,
    mut progress: impl FnMut(usize),
) -> Result<Summary, Error> {
    let root = base.to_path_buf();
    let work: pool::Work<Outcome> = Arc::new(move |e: &Entry| check(&root, e, groups));
    let mut sum = Summary::default();
    let mut ended = 0;
    pool::run(entries, workers, limit, work, |_, entry, end| {
        match end {
            Ended::Done(o) => sum.add(&entry.path, o, ledger),
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
    sum.listed
        .sort_by(|a, b| (&a.path, &a.diff.function).cmp(&(&b.path, &b.diff.function)));
    Ok(sum)
}
