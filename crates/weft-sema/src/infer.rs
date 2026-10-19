//! Effect inference: a fixpoint over the signatures.
//!
//! A function that does not state its effects gets the effect row of its body.
//! The row of a body depends on the rows of the functions that it calls, so the
//! inference lowers bodies again until no row changes.
//!
//! The inference joins each new row with the old row, so a row only grows. A
//! row is in a finite lattice: the effects of the program, the parameters, and
//! the `mut` places of at most [`SIG_PLACE_STEPS`] steps under the parameters
//! and the `rc` groups. So the inference always reaches a fixpoint.
//! [`growth_limit`] is the height of that lattice. If a row grows more often,
//! the inference has a bug: it stops, and each function whose signature can
//! still change gets W0706.
//!
//! A signature also has parts that the body always infers, also for a function
//! that states its effects: what it lends to its function parameters, what its
//! returned function value does, which function parameters it stores, whether
//! it can run a stored function value, what it gives to that value, whether an
//! unknown function value that it calls can resume more than once, which
//! function parameters a task of the body can call, which function parameters it
//! gives to an operation of a handler of a caller, which effects its tasks perform
//! through a handler of a caller, and which function parameters it can call more
//! than once. Each new lowering replaces these parts, so they do not only grow. A
//! part that is not known yet can be larger than its final value: for example, a
//! callee with no inferred returned function value counts as unknown. So the
//! inference does not join these parts. Instead, the parts of one function can change at most
//! [`parts_limit`] times. After that, the inference keeps the parts of that
//! function as they are, and it continues with the other functions. At the
//! end, each function whose parts still change gets W0704. Its row can still
//! grow, and its callers use its last parts.
//!
//! A worklist holds the functions to lower. It starts with callees before
//! callers. When a signature changes, only the functions whose bodies name that
//! function go back on the worklist.

use std::collections::{BTreeSet, HashMap};

use weft_facts::{FnFacts, Step, StepKind};
use weft_syntax::diag::Diagnostic;

use crate::body::Lowered;
use crate::program::{EffectSig, FnSig, Program, SigPlace, SigStep};
use crate::{effects, unit_of};

/// The most steps of a `mut` place in an inferred row. Lowering cuts a
/// longer place to this length.
pub const SIG_PLACE_STEPS: u32 = 8;

/// The result of effect inference.
pub(crate) struct Inferred {
    /// The last lowering of each function, in the order of the input.
    pub lowered: Vec<Lowered>,
    /// The number of lowerings before the last ones.
    pub lowerings: usize,
    /// W0704 for each function whose other parts changed [`parts_limit`]
    /// times and still change. If a row grew past its limit and stopped the
    /// inference, W0706 for each function with a change that the inference
    /// could still apply.
    pub diags: Vec<Diagnostic>,
}

/// Returns the most times that the parts of one signature other than the row
/// can change in a program with `fns` functions: 32, and two more for each
/// function.
pub const fn parts_limit(fns: usize) -> usize {
    fns.saturating_mul(2).saturating_add(32)
}

/// Returns the most times that the row of `sig` can grow: the height of its
/// lattice. `steps` is the number of different steps in the places so far.
pub fn growth_limit(prog: &Program, sig: &FnSig, steps: usize) -> usize {
    let named = prog.effects.len() + effects::STD_EFFECTS.len();
    let roots = sig.params.len() + prog.adts.len();
    // The places of 0 to SIG_PLACE_STEPS steps under one root.
    let mut paths: usize = 0;
    let mut level: usize = 1;
    for _ in 0..=SIG_PLACE_STEPS {
        paths = paths.saturating_add(level);
        level = level.saturating_mul(steps);
    }
    named
        .saturating_add(sig.params.len())
        .saturating_add(roots.saturating_mul(paths))
}

/// Returns true if `a` is `b` or a place that holds `b`. The texts do not count.
fn place_covers(a: &SigPlace, b: &SigPlace) -> bool {
    a.root == b.root
        && a.steps.len() <= b.steps.len()
        && a.steps.iter().zip(&b.steps).all(|(x, y)| match (x, y) {
            (SigStep::Step(s, _), SigStep::Step(t, _)) => s == t,
            _ => x == y,
        })
}

/// Returns true if row `a` holds all of row `b`: each effect, each
/// pass-through parameter and each `mut` place. The other parts do not count.
pub(crate) fn covers(a: &EffectSig, b: &EffectSig) -> bool {
    b.named.is_subset(&a.named)
        && b.passthrough.is_subset(&a.passthrough)
        && b.muts
            .iter()
            .all(|m| a.muts.iter().any(|k| place_covers(k, m)))
}

/// Returns the smallest row that holds `a` and `b`. The other parts are empty.
pub(crate) fn join(a: &EffectSig, b: &EffectSig) -> EffectSig {
    let mut muts: Vec<SigPlace> = Vec::new();
    for m in a.muts.iter().chain(&b.muts) {
        if muts.iter().any(|k| place_covers(k, m)) {
            continue;
        }
        muts.retain(|k| !place_covers(m, k));
        muts.push(m.clone());
    }
    EffectSig {
        muts,
        named: a.named.union(&b.named).cloned().collect(),
        passthrough: a.passthrough.union(&b.passthrough).copied().collect(),
        ..EffectSig::default()
    }
}

/// Returns the next row if `new` adds to `old`. A row that holds `old` stays
/// as the body gives it; other rows are joined with `old`. Only the row part of
/// the result counts.
fn grow(old: &EffectSig, new: &EffectSig) -> Option<EffectSig> {
    if covers(old, new) {
        None
    } else if covers(new, old) {
        Some(new.clone())
    } else {
        Some(join(old, new))
    }
}

/// Returns true if the parts other than the row are equal in `a` and `b`.
fn same_parts(a: &EffectSig, b: &EffectSig) -> bool {
    a.lent == b.lent
        && a.ret == b.ret
        && a.stores == b.stores
        && a.reaches == b.reaches
        && a.reach_given == b.reach_given
        && a.multi == b.multi
        && a.tasks == b.tasks
        && a.op_fns == b.op_fns
        && a.task_effects == b.task_effects
        && a.repeats == b.repeats
        && a.drops == b.drops
}

/// Returns the row of `row` with the other parts of `body`.
fn with_parts(row: &EffectSig, body: &EffectSig) -> EffectSig {
    EffectSig {
        lent: body.lent.clone(),
        ret: body.ret.clone(),
        stores: body.stores.clone(),
        reaches: body.reaches,
        reach_given: body.reach_given.clone(),
        multi: body.multi,
        tasks: body.tasks.clone(),
        op_fns: body.op_fns.clone(),
        task_effects: body.task_effects.clone(),
        repeats: body.repeats.clone(),
        drops: body.drops.clone(),
        ..row.clone()
    }
}

/// A change of a signature that a new lowering of its body gives.
struct Change {
    /// The next effects of the signature.
    effects: EffectSig,
    /// The row grows.
    row: bool,
    /// The other parts change.
    parts: bool,
}

/// Returns the change that the effects `body` of a new lowering make to `sig`,
/// if any. The row of a function that states its effects does not change.
fn change(sig: &FnSig, body: &EffectSig) -> Option<Change> {
    let row = if sig.declared {
        None
    } else {
        grow(&sig.effects, body)
    };
    let parts = !same_parts(&sig.effects, body);
    if row.is_none() && !parts {
        return None;
    }
    Some(Change {
        effects: with_parts(row.as_ref().unwrap_or(&sig.effects), body),
        row: row.is_some(),
        parts,
    })
}

/// The counts of the inference for each function.
struct Counts {
    /// How often the row of each function grew.
    growths: Vec<usize>,
    /// How often the other parts of each function changed.
    changes: Vec<usize>,
    /// The functions whose other parts changed [`parts_limit`] times. The
    /// inference does not change their other parts again.
    frozen: Vec<bool>,
    /// The [`parts_limit`] of the program.
    most_changes: usize,
}

/// What [`Counts::apply`] did with a change.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Applied {
    /// The signature changed.
    Changed,
    /// The signature did not change, because its other parts are frozen.
    Frozen,
    /// The row grew past its limit, so the inference must stop.
    Overgrown,
}

impl Counts {
    fn new(n: usize, fns: usize) -> Self {
        Self {
            growths: vec![0; n],
            changes: vec![0; n],
            frozen: vec![false; n],
            most_changes: parts_limit(fns),
        }
    }

    /// Returns true if the inference can still apply `c` to `f`: the row
    /// grows, or the other parts change and are not frozen.
    fn open(&self, f: usize, c: &Change) -> bool {
        c.row || (c.parts && !self.frozen[f])
    }

    /// Applies the change `c` to the signature of `f`. `steps` is the number of
    /// different steps so far, and `limit`, if given, is the most growths of
    /// one row.
    fn apply(
        &mut self,
        prog: &Program,
        sigs: &mut [FnSig],
        f: usize,
        c: Change,
        steps: usize,
        limit: Option<usize>,
    ) -> Applied {
        if c.row {
            self.growths[f] += 1;
            let most = growth_limit(prog, &sigs[f], steps).min(limit.unwrap_or(usize::MAX));
            if self.growths[f] > most {
                return Applied::Overgrown;
            }
        }
        let mut parts = c.parts && !self.frozen[f];
        if parts {
            self.changes[f] += 1;
            if self.changes[f] > self.most_changes {
                self.frozen[f] = true;
                parts = false;
            }
        }
        if !c.row && !parts {
            return Applied::Frozen;
        }
        sigs[f].effects = if parts {
            c.effects
        } else {
            with_parts(&c.effects, &sigs[f].effects)
        };
        Applied::Changed
    }
}

/// Adds the steps of the places of `facts`, as an inferred row writes them.
fn add_steps(steps: &mut BTreeSet<Step>, facts: &FnFacts) {
    for p in &facts.places {
        steps.extend(p.steps.iter().map(|s| match s.kind {
            StepKind::Seg { .. } => Step {
                kind: StepKind::Elem,
                unstable: s.unstable,
            },
            _ => *s,
        }));
    }
}

/// Which bodies name which functions. A body reads the signature of a function
/// almost always through its name, so each call is an edge of the graph. The
/// last lowering of [`infer`] finds the other reads.
struct NameGraph {
    /// For each function, the open functions whose bodies name it.
    callers: Vec<Vec<usize>>,
    /// The position of each open function. A callee comes before its callers,
    /// except in a cycle.
    order: Vec<usize>,
}

impl NameGraph {
    fn new(prog: &Program, open: &[usize]) -> Self {
        let n = prog.fns.len();
        let mut by_name: HashMap<&str, Vec<usize>> = HashMap::new();
        for &g in open {
            by_name
                .entry(prog.fns[g].name.as_str())
                .or_default()
                .push(g);
        }
        let mut callees: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); n];
        let mut callers: Vec<Vec<usize>> = vec![Vec::new(); n];
        for &f in open {
            let Some(body) = &prog.fns[f].decl.body else {
                continue;
            };
            // Each word of the printed body is a name or a part of a literal.
            let text = weft_syntax::pretty::pretty_block(body);
            let words = text
                .split(|c: char| !(c.is_alphanumeric() || c == '_'))
                .filter(|w| !w.is_empty());
            for w in words {
                for &g in by_name.get(w).map_or(&[][..], Vec::as_slice) {
                    if callees[f].insert(g) {
                        callers[g].push(f);
                    }
                }
            }
        }
        // A depth-first post-order puts callees first. The stack is explicit,
        // because a call chain can be long.
        let mut order = vec![usize::MAX; n];
        let mut seen = vec![false; n];
        let mut next = 0;
        for &s in open {
            if seen[s] {
                continue;
            }
            seen[s] = true;
            let mut stack: Vec<(usize, Vec<usize>)> =
                vec![(s, callees[s].iter().copied().collect())];
            while let Some((f, todo)) = stack.last_mut() {
                let f = *f;
                if let Some(g) = todo.pop() {
                    if !seen[g] {
                        seen[g] = true;
                        stack.push((g, callees[g].iter().copied().collect()));
                    }
                } else {
                    order[f] = next;
                    next += 1;
                    stack.pop();
                }
            }
        }
        Self { callers, order }
    }
}

/// Infers the signatures of the functions in `fns`: the row of each function
/// that does not state its effects, and the other inferred parts of each
/// function. Then it lowers each function of `fns` with the final signatures.
/// `lower` lowers one function. `limit`, if given, is the most growths of one
/// row.
pub(crate) fn infer(
    prog: &Program,
    sigs: &mut [FnSig],
    fns: &[usize],
    limit: Option<usize>,
    lower: &dyn Fn(&[FnSig], usize) -> Lowered,
) -> Inferred {
    // A function that states its effects still infers its other parts, so each
    // function of `fns` is open.
    let graph = NameGraph::new(prog, fns);
    let mut work: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut counts = Counts::new(prog.fns.len(), fns.len());
    let mut steps = BTreeSet::new();
    let mut lowerings = 0;
    let mut overgrown = false;
    work.extend(fns.iter().map(|&f| (graph.order[f], f)));
    loop {
        while !overgrown {
            let Some((_, f)) = work.pop_first() else {
                break;
            };
            lowerings += 1;
            let l = lower(sigs, f);
            add_steps(&mut steps, &l.facts);
            let Some(c) = change(&sigs[f], &l.effects) else {
                continue;
            };
            match counts.apply(prog, sigs, f, c, steps.len(), limit) {
                Applied::Changed => {
                    work.extend(graph.callers[f].iter().map(|&g| (graph.order[g], g)));
                }
                Applied::Frozen => {}
                Applied::Overgrown => overgrown = true,
            }
        }
        // The last lowering also shows if the signatures are a fixpoint.
        let lowered: Vec<Lowered> = fns.iter().map(|&f| lower(sigs, f)).collect();
        let short: Vec<(usize, Change)> = fns
            .iter()
            .zip(&lowered)
            .filter_map(|(&f, l)| change(&sigs[f], &l.effects).map(|c| (f, c)))
            .collect();
        if overgrown || !short.iter().any(|(f, c)| counts.open(*f, c)) {
            let mut diags = Vec::new();
            for (f, c) in &short {
                if c.parts && counts.frozen[*f] {
                    diags.push(not_stable(prog, *f, counts.most_changes));
                }
                // Only a row that grew past its limit leaves an open change.
                if counts.open(*f, c) {
                    diags.push(not_converged(prog, *f));
                }
            }
            return Inferred {
                lowered,
                lowerings,
                diags,
            };
        }
        // A body read a signature that the name graph does not show. Apply
        // the changes, and lower every open function again.
        for l in &lowered {
            add_steps(&mut steps, &l.facts);
        }
        for (f, c) in short {
            if !overgrown
                && counts.apply(prog, sigs, f, c, steps.len(), limit) == Applied::Overgrown
            {
                overgrown = true;
            }
        }
        work.extend(fns.iter().map(|&f| (graph.order[f], f)));
    }
}

/// W0706: the row of `f` did not reach a fixpoint.
fn not_converged(prog: &Program, f: usize) -> Diagnostic {
    let mut d = Diagnostic::error(
        "W0706",
        format!(
            "effect inference stopped before a fixpoint; the effects of `{}` can be incomplete",
            prog.fns[f].path
        ),
        prog.fns[f].decl.name.span,
    )
    .note("state the effects of this function, and report the program as a checker bug");
    d.unit = unit_of(prog, prog.fns[f].module);
    d
}

/// W0704: the inferred parts of the signature of `f` other than the row still
/// change after `most` changes.
fn not_stable(prog: &Program, f: usize, most: usize) -> Diagnostic {
    let mut d = Diagnostic::error(
        "W0704",
        format!(
            "the effects of `{}` do not become stable after {most} changes in effect inference",
            prog.fns[f].path
        ),
        prog.fns[f].decl.name.span,
    )
    .note("the inferred effects of this function can be incomplete; report the program");
    d.unit = unit_of(prog, prog.fns[f].module);
    d
}
