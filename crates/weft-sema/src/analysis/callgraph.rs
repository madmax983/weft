//! The call graph and the fixpoint of the summaries (`docs/ir.md` 6.6,
//! "Interprocedural order", and 6.8).
//!
//! The analysis of a body reads the summaries of the functions that it
//! calls. [`infer`] links each function body to each function body whose
//! summary it reads (a `Call` of a function item, and an `on abort` function
//! of an `UnwindValue`; stage F11 and later add closures, clauses and
//! tasks), and finds the strongly connected components
//! of that graph. It runs each component to a fixpoint, callees first:
//!
//! - the summary of each function of the component starts with its stated
//!   row (or an empty row) and empty inferred parts;
//! - each round runs the fact generator on each body of the component with
//!   the summaries of now, and projects its facts onto its interface
//!   (`super::summarize`); the inferred parts only grow (a join,
//!   [`Inferred::join`]);
//! - the fixpoint is the first round with no growth. A component with one
//!   function that does not call itself needs one round.
//!
//! The parts are finite (places of at most `SIG_PLACE_STEPS` steps, the
//! effects of the program), so the iteration ends. W0706 is a guard: a row
//! that grows more often than the height of its lattice
//! (`crate::infer::growth_limit`) shows a bug. Then the iteration of that
//! component stops, and each function of it gets W0706.
//!
//! This fixpoint is the effect inference of the `ir` pipeline: it reads the
//! IR and needs no new lowering of a body. The facts of the last round of
//! each body are the facts of the body: the emit pass takes them
//! ([`Inference::facts`]).

use std::collections::{BTreeSet, HashMap};

use weft_facts::{FnFacts, StepKind};
use weft_ir::{BodyId, Callee, StmtKind, TermKind, UnwindAction};
use weft_syntax::diag::Diagnostic;

use super::sig::{self, Inferred};
use super::summary::{Summaries, Summary};
use crate::factgen::{self, Unsupported};
use crate::irbuild::scope::Group;
use crate::irbuild::{Built, Outcome};
use crate::program::{EffectSig, FnSig};
use crate::Analysis;

/// The facts of one body and the diagnostics of its fact generation, or why
/// the fact generator does not support it.
pub type BodyOut = Result<(FnFacts, Vec<Diagnostic>), Unsupported>;

/// The result of the fixpoint.
#[derive(Clone, Debug, Default)]
pub struct Inference {
    /// The summary of each function of the IR, or why it has none.
    pub sums: Summaries,
    /// The `EffectSig` of each function of the program of the analysis
    /// whose summary comes from its body (`super::sig::to_effect_sig`).
    pub effects: Vec<(crate::FnId, EffectSig)>,
    /// W0706 for each function of a component whose fixpoint stopped.
    pub diags: Vec<Diagnostic>,
    /// The facts of the last round of each function body, by the index of
    /// the body in [`Analysis::bodies`]. They hold with the final summaries.
    pub facts: HashMap<usize, BodyOut>,
    /// The rounds of the fixpoint: the number of runs of the fact generator
    /// on a body.
    pub rounds: usize,
}

/// One function whose summary comes from its body: a node of the graph.
struct Node {
    /// The function of the program of the analysis.
    sema: crate::FnId,
    /// The function of the IR.
    f: weft_ir::FnId,
    /// The index of the body in [`Analysis::bodies`].
    index: usize,
    /// The body of the IR.
    body: BodyId,
    /// The bodies of its component.
    comp: Vec<BodyId>,
    /// The nodes whose summaries it reads.
    callees: BTreeSet<usize>,
}

/// The reason of a function whose body the fact generator does not support,
/// for its callers: a fixed text for each group, so `factgen` finds the
/// group of the caller again.
const fn failed(g: Group) -> &'static str {
    match g {
        Group::A => "a call of a function whose body the fact generator does not support yet",
        Group::B => "a call of a function with a loop or an iterator (stage F10)",
        Group::C => "a call of a function with a closure or a function value (stage F11)",
        Group::D => "a call of a function with a handler or a continuation (stage F14)",
        Group::E => "a call of a function with a task or a scope (stage F18)",
        Group::F => "a call of a function with a type parameter (stage F20)",
    }
}

/// The strongly connected components of the graph `succ`, each one after
/// the components that it reaches (Tarjan, with an explicit stack: a call
/// chain can be long).
fn sccs(succ: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = succ.len();
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0usize; n];
    let mut on = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut out = Vec::new();
    let mut next = 0usize;
    for s in 0..n {
        if index.get(s).copied() != Some(usize::MAX) {
            continue;
        }
        // (node, position of the next successor)
        let mut work: Vec<(usize, usize)> = vec![(s, 0)];
        while let Some(&mut (v, ref mut k)) = work.last_mut() {
            if *k == 0 && index.get(v).copied() == Some(usize::MAX) {
                if let Some(x) = index.get_mut(v) {
                    *x = next;
                }
                if let Some(x) = low.get_mut(v) {
                    *x = next;
                }
                next += 1;
                stack.push(v);
                if let Some(x) = on.get_mut(v) {
                    *x = true;
                }
            }
            let ws = succ.get(v).map_or(&[][..], Vec::as_slice);
            if let Some(&w) = ws.get(*k) {
                *k += 1;
                if index.get(w).copied() == Some(usize::MAX) {
                    work.push((w, 0));
                } else if on.get(w).copied().unwrap_or(false) {
                    let iw = index.get(w).copied().unwrap_or(0);
                    if let Some(x) = low.get_mut(v) {
                        *x = (*x).min(iw);
                    }
                }
                continue;
            }
            work.pop();
            let lv = low.get(v).copied().unwrap_or(0);
            if let Some(&(u, _)) = work.last() {
                if let Some(x) = low.get_mut(u) {
                    *x = (*x).min(lv);
                }
            }
            if lv == index.get(v).copied().unwrap_or(0) {
                let mut comp = Vec::new();
                while let Some(w) = stack.pop() {
                    if let Some(x) = on.get_mut(w) {
                        *x = false;
                    }
                    comp.push(w);
                    if w == v {
                        break;
                    }
                }
                comp.sort_unstable();
                out.push(comp);
            }
        }
    }
    out
}

/// The parts of a function with a stated row: the stated row, and the
/// parts that only its body gives from `body` (`raises`, `multi`, `drops`,
/// `holds`).
fn stated(
    sig: &FnSig,
    decl: &weft_ir::FnDecl,
    tys: &weft_ir::TyTable,
    body: &Inferred,
) -> Inferred {
    let mut out = Inferred::of_signature(sig, decl, tys);
    out.raises = body.raises;
    out.assert = body.assert;
    out.multi = body.multi;
    out.drops.clone_from(&body.drops);
    out.holds.clone_from(&body.holds);
    out
}

/// The summary of function `sema` with the parts `inf`.
///
/// # Errors
///
/// Returns the reason if a function with a stated row has a signature that
/// a summary cannot carry yet (`super::sig::from_signature`), or if a
/// function with no stated row has a function value in its signature.
fn summary_of(
    a: &Analysis,
    tys: &weft_ir::TyTable,
    decl: &weft_ir::FnDecl,
    sema: crate::FnId,
    inf: &Inferred,
) -> Result<Summary, &'static str> {
    let sig = a
        .sigs
        .get(sema.index())
        .ok_or("a call of a function with no signature")?;
    if sig.declared {
        let mut s = sig.clone();
        s.effects.raises = inf.raises;
        s.effects.multi = inf.multi;
        s.effects.drops = inf.drops.iter().map(|&j| j as usize).collect();
        s.effects.holds = inf.holds.iter().map(|&j| j as usize).collect();
        // The signature has no part for an `assert`: the body gives it.
        return sig::from_signature(&a.program, sema, &s, decl, tys).map(|mut sum| {
            if inf.assert {
                sum.aborts.insert(super::summary::Abort::Assert);
            }
            sum
        });
    }
    if decl.params.iter().any(|&t| tys.mentions_fn(t)) || tys.mentions_fn(decl.ret) {
        return Err("a call of a function with a function value in its signature (stage F12)");
    }
    Ok(sig::build(&a.program, sig, decl, tys, inf))
}

/// The `EffectSig` of function `sema` with the parts `inf` and the summary
/// `sum`: a function with a stated row keeps its row and gets the parts that
/// its body gives.
fn effect_sig(a: &Analysis, sema: crate::FnId, inf: &Inferred, sum: &Summary) -> EffectSig {
    match a.sigs.get(sema.index()) {
        Some(sig) if sig.declared => EffectSig {
            muts: sig.effects.muts.clone(),
            named: sig.effects.named.clone(),
            passthrough: sig.effects.passthrough.clone(),
            raises: inf.raises,
            multi: inf.multi,
            drops: inf.drops.iter().map(|&j| j as usize).collect(),
            holds: inf.holds.iter().map(|&j| j as usize).collect(),
            ..EffectSig::default()
        },
        _ => sig::to_effect_sig(&a.program, sum),
    }
}

/// Adds the steps of the places of `facts` to `steps`, as an inferred row
/// writes them (a side of a split is an element step).
fn add_steps(steps: &mut BTreeSet<weft_facts::Step>, facts: &FnFacts) {
    for p in &facts.places {
        steps.extend(p.steps.iter().map(|s| match s.kind {
            StepKind::Seg { .. } => weft_facts::Step {
                kind: StepKind::Elem,
                unstable: s.unstable,
            },
            _ => *s,
        }));
    }
}

/// Runs the summaries of the functions of the IR `built` of the analysis `a`
/// to their fixpoint (see the module). `limit`, if given, is the most
/// growths of one row: a test can make the guard W0706 fire.
pub fn infer(a: &Analysis, built: &Built, limit: Option<usize>) -> Inference {
    let mut out = Inference::default();
    let tys = &built.tys;
    let prog = &a.program;
    let index_of: HashMap<crate::FnId, usize> = a
        .bodies
        .iter()
        .enumerate()
        .filter_map(|(i, b)| b.func.map(|f| (f, i)))
        .collect();
    let mut nodes: Vec<Node> = Vec::new();
    let mut fns: Vec<(&crate::FnId, &weft_ir::FnId)> = built.fns.iter().collect();
    fns.sort();
    for (&sema, &f) in fns {
        let (Some(sig), Some(decl)) = (a.sigs.get(sema.index()), built.program.fns.get(f.index()))
        else {
            continue;
        };
        if decl.intrinsic.is_some() {
            out.sums
                .insert(f, Err("a call of `sim.run` or `with_timeout` (stage F19)"));
            continue;
        }
        let entry =
            index_of
                .get(&sema)
                .and_then(|&i| match built.entries.get(i).map(|e| &e.outcome) {
                    Some(Outcome::Built(b)) => Some((i, *b)),
                    _ => None,
                });
        let Some((index, body)) = entry else {
            // An extern function, or a body with no IR (a type error): the
            // summary of its signature, with the parts of the old inference.
            out.sums
                .insert(f, sig::from_signature(prog, sema, sig, decl, tys));
            continue;
        };
        nodes.push(Node {
            sema,
            f,
            index,
            body,
            comp: factgen::component(built, body),
            callees: BTreeSet::new(),
        });
    }
    let by_fn: HashMap<weft_ir::FnId, usize> =
        nodes.iter().enumerate().map(|(i, n)| (n.f, i)).collect();
    for n in &mut nodes {
        for &b in &n.comp {
            let Some(body) = built.program.bodies.get(b.index()) else {
                continue;
            };
            for blk in &body.blocks {
                if let TermKind::Call {
                    callee: Callee::Fn(g, _),
                    ..
                } = &blk.term.kind
                {
                    if let Some(&j) = by_fn.get(g) {
                        n.callees.insert(j);
                    }
                }
                // The unwinder runs an `on abort` function on a cleanup
                // path: its summary applies there (stage F7).
                for s in &blk.stmts {
                    if let StmtKind::UnwindValue(_, UnwindAction::OnAbort(g)) = &s.kind {
                        if let Some(&j) = by_fn.get(g) {
                            n.callees.insert(j);
                        }
                    }
                }
            }
        }
    }
    let succ: Vec<Vec<usize>> = nodes
        .iter()
        .map(|n| n.callees.iter().copied().collect())
        .collect();
    let mut inf: Vec<Inferred> = vec![Inferred::default(); nodes.len()];
    let mut ok = vec![true; nodes.len()];
    let mut steps: BTreeSet<weft_facts::Step> = BTreeSet::new();
    for comp in sccs(&succ) {
        // The start: the stated row, or an empty row.
        for &i in &comp {
            let Some(n) = nodes.get(i) else { continue };
            let (Some(sig), Some(decl)) = (
                a.sigs.get(n.sema.index()),
                built.program.fns.get(n.f.index()),
            ) else {
                continue;
            };
            let start = if sig.declared {
                stated(sig, decl, tys, &Inferred::default())
            } else {
                Inferred::default()
            };
            out.sums
                .insert(n.f, summary_of(a, tys, decl, n.sema, &start));
            if let Some(x) = inf.get_mut(i) {
                *x = start;
            }
        }
        let recursive = comp.len() > 1
            || comp
                .first()
                .and_then(|&i| nodes.get(i))
                .is_some_and(|n| comp.iter().any(|j| n.callees.contains(j)));
        let mut failed_nodes: BTreeSet<usize> = BTreeSet::new();
        let mut growths: HashMap<usize, usize> = HashMap::new();
        let mut stopped = false;
        loop {
            let mut grew = false;
            for &i in &comp {
                if failed_nodes.contains(&i) {
                    continue;
                }
                let Some(n) = nodes.get(i) else { continue };
                let (Some(sig), Some(decl), Some(old)) = (
                    a.sigs.get(n.sema.index()),
                    built.program.fns.get(n.f.index()),
                    a.bodies.get(n.index),
                ) else {
                    continue;
                };
                out.rounds += 1;
                let mut facts = factgen::seed(&old.facts);
                let run = factgen::emit_component(a, built, &out.sums, n.index, n.body, &mut facts);
                match run {
                    Ok((diags, roots)) => {
                        let body = super::summarize::summarize(
                            &built.program,
                            tys,
                            &out.sums,
                            &facts,
                            &roots,
                            &n.comp,
                            n.body,
                            sig,
                        );
                        add_steps(&mut steps, &facts);
                        let new = if sig.declared {
                            stated(sig, decl, tys, &body)
                        } else {
                            body
                        };
                        let Some(cur) = inf.get_mut(i) else { continue };
                        if cur.join(&new) {
                            grew = true;
                            let g = growths.entry(i).or_insert(0);
                            *g += 1;
                            let most = crate::infer::growth_limit(prog, sig, steps.len())
                                .min(limit.unwrap_or(usize::MAX));
                            if *g > most {
                                stopped = true;
                            }
                            out.sums.insert(n.f, summary_of(a, tys, decl, n.sema, cur));
                        }
                        out.facts.insert(n.index, Ok((facts, diags)));
                    }
                    Err(u) => {
                        failed_nodes.insert(i);
                        if let Some(x) = ok.get_mut(i) {
                            *x = false;
                        }
                        grew = true;
                        let s = if sig.declared {
                            // The summary of stage F5: the signature, with
                            // the parts of the old inference.
                            sig::from_signature(prog, n.sema, sig, decl, tys)
                        } else {
                            Err(failed(u.group))
                        };
                        out.sums.insert(n.f, s);
                        out.facts.insert(n.index, Err(u));
                    }
                }
                if stopped {
                    break;
                }
            }
            if stopped {
                for &i in &comp {
                    if let Some(n) = nodes.get(i) {
                        out.diags
                            .push(crate::infer::not_converged(prog, n.sema.index()));
                        // The facts of the last round do not hold with the
                        // summaries of now.
                        out.facts.remove(&n.index);
                    }
                }
                break;
            }
            if !grew || !recursive {
                break;
            }
        }
    }
    for (i, n) in nodes.iter().enumerate() {
        let (Ok(sum), Some(x), Some(true)) = (out.sums.get(n.f), inf.get(i), ok.get(i)) else {
            continue;
        };
        out.effects.push((n.sema, effect_sig(a, n.sema, x, sum)));
    }
    out
}
