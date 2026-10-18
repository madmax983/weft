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
//! the inference has a bug: it stops, and each function whose row can still
//! grow gets W0706.
//!
//! A worklist holds the functions to lower. It starts with callees before
//! callers. When a row grows, only the functions whose bodies name that
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
    /// W0706 for each function whose row did not reach a fixpoint.
    pub diags: Vec<Diagnostic>,
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
/// pass-through parameter and each `mut` place.
pub(crate) fn covers(a: &EffectSig, b: &EffectSig) -> bool {
    b.named.is_subset(&a.named)
        && b.passthrough.is_subset(&a.passthrough)
        && b.muts
            .iter()
            .all(|m| a.muts.iter().any(|k| place_covers(k, m)))
}

/// Returns the smallest row that holds `a` and `b`.
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
    }
}

/// Returns the next row if `new` adds to `old`. A row that holds `old` stays
/// as the body gives it; other rows are joined with `old`.
fn grow(old: &EffectSig, new: &EffectSig) -> Option<EffectSig> {
    if covers(old, new) {
        None
    } else if covers(new, old) {
        Some(new.clone())
    } else {
        Some(join(old, new))
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
/// only through its name, so each call is an edge of the graph.
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

/// Infers the rows of the functions in `fns` that do not state their effects,
/// then lowers each function of `fns` with the final signatures. `lower`
/// lowers one function. `limit`, if given, is the most growths of one row.
pub(crate) fn infer(
    prog: &Program,
    sigs: &mut [FnSig],
    fns: &[usize],
    limit: Option<usize>,
    lower: &dyn Fn(&[FnSig], usize) -> Lowered,
) -> Inferred {
    let open: Vec<usize> = fns.iter().copied().filter(|&f| !sigs[f].declared).collect();
    let graph = NameGraph::new(prog, &open);
    let mut work: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut growths = vec![0_usize; prog.fns.len()];
    let mut steps = BTreeSet::new();
    let mut lowerings = 0;
    let mut stopped = false;
    // Applies a new row of `f`. Returns false if the row grows past its limit.
    let mut apply = |sigs: &mut [FnSig], f: usize, row: EffectSig, steps: usize| {
        growths[f] += 1;
        let most = growth_limit(prog, &sigs[f], steps).min(limit.unwrap_or(usize::MAX));
        if growths[f] > most {
            return false;
        }
        sigs[f].effects = row;
        true
    };
    work.extend(open.iter().map(|&f| (graph.order[f], f)));
    loop {
        while !stopped {
            let Some((_, f)) = work.pop_first() else {
                break;
            };
            lowerings += 1;
            let l = lower(sigs, f);
            add_steps(&mut steps, &l.facts);
            let Some(row) = grow(&sigs[f].effects, &l.effects) else {
                continue;
            };
            if !apply(sigs, f, row, steps.len()) {
                stopped = true;
                break;
            }
            work.extend(graph.callers[f].iter().map(|&g| (graph.order[g], g)));
        }
        // The last lowering also shows if the rows are a fixpoint.
        let lowered: Vec<Lowered> = fns.iter().map(|&f| lower(sigs, f)).collect();
        let short: Vec<(usize, EffectSig)> = fns
            .iter()
            .zip(&lowered)
            .filter(|(&f, _)| !sigs[f].declared)
            .filter_map(|(&f, l)| grow(&sigs[f].effects, &l.effects).map(|row| (f, row)))
            .collect();
        if short.is_empty() || stopped {
            let diags = short.iter().map(|&(f, _)| not_converged(prog, f)).collect();
            return Inferred {
                lowered,
                lowerings,
                diags,
            };
        }
        // A body read a signature that the name graph does not show. Apply
        // the rows, and lower every open function again.
        for l in &lowered {
            add_steps(&mut steps, &l.facts);
        }
        for (f, row) in short {
            stopped |= !apply(sigs, f, row, steps.len());
        }
        work.extend(open.iter().map(|&f| (graph.order[f], f)));
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
