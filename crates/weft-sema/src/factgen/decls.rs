//! The relations with no node (`docs/ir.md` 6.3): they come from the
//! declarations, not from a template.
//!
//! - [`params`]: the places of the interface of a function body (the
//!   `Param` roots of its parameters, and the `in` places), and the value of
//!   each parameter at the entry.
//! - [`signature`]: `has_signature`, `declared_mut`, `declared_effect` and
//!   `shared_root` from the stated signature, as the old lowering
//!   (`body/stmt.rs`) gives them.
//! - [`ret_places`]: the stated returned places (`ref_in` of `Return`).
//! - [`tasks`]: `task` and `fork_task`, one task for each spawn site and each
//!   branch of a `fork`.
//! - [`std_effects`]: `std_effect` for each standard effect that the facts
//!   name.
//!
//! `library()`, `started()` and `no_runtime()` come from the unit and the
//! driver: the fact generator copies them from the facts of the
//! declarations of the body (`super::seed`).

use std::collections::{BTreeMap, BTreeSet};

use weft_facts::{FnFacts, PlaceId, RootKind, Step, StepKind, TaskId, TaskKind};
use weft_ir::{BodyId, LocalId, Program, SpawnId, TermKind, Ty, TyTable};

use super::alpha::{AlphaError, Role, Roots};
use crate::analysis::{AbsVal, State, Tree};
use crate::effects;
use crate::program::{FnSig, SigPlace, SigRoot, SigStep};
use crate::props::ir_props;

/// The places of the interface of a function body.
#[derive(Clone, Debug, Default)]
pub struct Params {
    /// The places of each parameter, by index: what a reference parameter
    /// points into (its `Param` root, or its `in` place), or the root of a
    /// by-value parameter and the `Param` root of its references.
    pub bases: Vec<Vec<PlaceId>>,
    /// The value of each parameter local at the entry.
    pub entry: Vec<(LocalId, Tree)>,
}

/// The span of the facts for an IR span.
const fn span(s: weft_ir::Span) -> weft_facts::Span {
    weft_facts::Span { lo: s.lo, hi: s.hi }
}

/// True if a value of type `t` is a reference.
fn is_ref(tys: &TyTable, t: weft_ir::TyId) -> bool {
    matches!(tys.try_get(t), Some(Ty::Ref(_)))
}

/// The places of the parameters of function body `body` with signature
/// `sig`, and their values at the entry.
///
/// A reference parameter points into its `Param` root (with the text of the
/// parameter), or into the places of its `in` place. A by-value parameter
/// that can hold references points into a `Param` root of its own. Each
/// value has the linear part of its type and the `@ uniq` mode of its
/// declaration.
///
/// # Errors
///
/// The errors of α for the root of a by-value parameter.
pub fn params(
    p: &Program,
    tys: &mut TyTable,
    facts: &mut FnFacts,
    roots: &mut Roots,
    body: BodyId,
    sig: &FnSig,
) -> Result<Params, AlphaError> {
    let Some(b) = p.bodies.get(body.index()) else {
        return Err(AlphaError::BadPlace(format!("no body b{}", body.0)));
    };
    let mut out = Params::default();
    for (i, &l) in b.params.iter().enumerate() {
        let i32 = u32::try_from(i).unwrap_or(u32::MAX);
        let d = b
            .locals
            .get(l.index())
            .ok_or_else(|| AlphaError::BadPlace(format!("no parameter {i}")))?;
        let name = d.name.clone().unwrap_or_else(|| format!("parameter {i}"));
        let stated_in = sig.params.get(i).is_some_and(|ps| ps.place.is_some());
        let base = if is_ref(tys, d.ty) {
            if stated_in {
                Vec::new()
            } else {
                vec![roots.param(facts, body, i32, &name)]
            }
        } else {
            let r = roots.local(p, tys, facts, body, l)?;
            let fnv = matches!(tys.try_get(d.ty), Some(Ty::Fn(_)));
            if !fnv && ir_props(tys, d.ty).holds_refs {
                vec![r, roots.param(facts, body, i32, &name)]
            } else {
                vec![r]
            }
        };
        out.bases.push(base);
    }
    // The root parameter of an `in` place first: it can come later in the
    // list, and it can have an `in` place itself.
    for i in crate::program::in_place_order(&sig.params).0 {
        if let Some(pl) = sig.params.get(i).and_then(|ps| ps.place.as_ref()) {
            let b = subst(p, tys, facts, roots, pl, &out.bases);
            if let Some(slot) = out.bases.get_mut(i) {
                *slot = b;
            }
        }
    }
    for (i, &l) in b.params.iter().enumerate() {
        let Some(d) = b.locals.get(l.index()) else {
            continue;
        };
        let base = out.bases.get(i).cloned().unwrap_or_default();
        let refs = if is_ref(tys, d.ty) {
            base
        } else {
            base.get(1).copied().into_iter().collect()
        };
        let mut v = AbsVal::of_type(d.props.linear);
        v.refs = refs.into_iter().collect();
        v.uniq = d.props.uniq;
        out.entry.push((l, Tree::leaf(v)));
    }
    Ok(out)
}

/// The state at the entry of a body whose parameters have the values
/// `entry`.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if a local does not exist.
pub fn entry_state(
    p: &Program,
    body: BodyId,
    entry: &[(LocalId, Tree)],
) -> Result<State, AlphaError> {
    let mut st = State::new();
    for (l, v) in entry {
        let k = crate::analysis::transfer::key(p, body, *l)?;
        st.write(k, &[], v.clone());
    }
    Ok(st)
}

/// The places that the references at or below each place of `ps` point
/// into: the pointees behind a parameter (its `Held` root), or the places of
/// the value of a by-value parameter at the entry.
fn held_refs(
    p: &Program,
    facts: &mut FnFacts,
    roots: &mut Roots,
    bases: &[Vec<PlaceId>],
    ps: &[PlaceId],
) -> Vec<PlaceId> {
    let mut out = Vec::new();
    for &q in ps {
        let Some(root) = facts.places.get(q.index()).map(|i| i.root) else {
            continue;
        };
        match roots.role(root) {
            Some(Role::Param(b, i) | Role::Held(b, i)) => {
                let name = crate::analysis::transfer::param_name(p, b, i);
                let h = roots.held(facts, b, i, &name);
                out.push(facts.wildcard(h));
            }
            Some(Role::Local((b, l))) => {
                // The references of a by-value parameter: its `Param` root.
                let i = p
                    .bodies
                    .get(b.index())
                    .and_then(|x| x.params.iter().position(|&pl| pl == l));
                if let Some(base) = i.and_then(|i| bases.get(i)) {
                    out.extend(base.iter().skip(1).copied());
                }
            }
            Some(Role::Group | Role::Frame(_) | Role::Caller) | None => {}
        }
    }
    out.sort();
    out.dedup();
    out
}

/// The places of the signature place `sp`, with the places `bases` of the
/// parameters.
pub fn subst(
    p: &Program,
    tys: &TyTable,
    facts: &mut FnFacts,
    roots: &mut Roots,
    sp: &SigPlace,
    bases: &[Vec<PlaceId>],
) -> Vec<PlaceId> {
    let start = match &sp.root {
        SigRoot::Param(i) => bases.get(*i).cloned().unwrap_or_default(),
        SigRoot::Group(a) => {
            let a = weft_ir::AdtId(u32::try_from(a.index()).unwrap_or(u32::MAX));
            vec![roots.group_of_adt(tys, facts, a)]
        }
    };
    let mut out = Vec::new();
    for base in start {
        let mut ps = vec![base];
        for st in &sp.steps {
            let mut next = Vec::new();
            for q in ps {
                match st {
                    SigStep::Step(s, text) => next.push(facts.child(q, *s, text)),
                    SigStep::Wild => next.push(facts.wildcard(q)),
                    SigStep::Held => next.extend(held_refs(p, facts, roots, bases, &[q])),
                    SigStep::Seg {
                        label,
                        hi,
                        unstable,
                    } => {
                        let text = if *hi { "[k..]" } else { "[..k]" };
                        let step = Step {
                            kind: StepKind::Seg {
                                split: u32::try_from(*label).unwrap_or(u32::MAX),
                                hi: *hi,
                            },
                            unstable: *unstable,
                        };
                        next.push(facts.child(q, step, text));
                    }
                }
            }
            ps = next;
        }
        out.extend(ps);
    }
    out.sort();
    out.dedup();
    out
}

/// The relations of the stated signature `sig` of a function body.
///
/// They are `shared_root` for each `@ shared` parameter, and, if the source
/// states the effects, `has_signature`, `declared_mut` (the `mut` places in
/// the places of the parameters) and `declared_effect` (the stated effects,
/// closed under implication).
pub fn signature(
    p: &Program,
    tys: &TyTable,
    facts: &mut FnFacts,
    roots: &mut Roots,
    sig: &FnSig,
    bases: &[Vec<PlaceId>],
) {
    for (i, ps) in sig.params.iter().enumerate() {
        if ps.shared {
            facts
                .shared_root
                .extend(bases.get(i).into_iter().flatten().copied());
        }
    }
    if sig.declared {
        facts.has_signature = true;
        for m in &sig.effects.muts {
            let ps = subst(p, tys, facts, roots, m, bases);
            facts.declared_mut.extend(ps);
        }
        facts.declared_effect = effects::close(&sig.effects.named).into_iter().collect();
    }
}

/// The places that the signature `sig` states for the returned references,
/// with the places `bases` of the parameters (a by-value parameter: its
/// root), or `None` if it states none.
pub fn ret_places(
    p: &Program,
    tys: &TyTable,
    facts: &mut FnFacts,
    roots: &mut Roots,
    body: BodyId,
    sig: &FnSig,
    bases: &[Vec<PlaceId>],
) -> Option<Vec<PlaceId>> {
    if sig.ret_places.is_empty() {
        return None;
    }
    let b = p.bodies.get(body.index())?;
    let bases: Vec<Vec<PlaceId>> = bases
        .iter()
        .enumerate()
        .map(|(i, base)| {
            let by_ref = b
                .params
                .get(i)
                .and_then(|l| b.locals.get(l.index()))
                .is_some_and(|d| is_ref(tys, d.ty));
            if by_ref {
                base.clone()
            } else {
                base.iter().take(1).copied().collect()
            }
        })
        .collect();
    let mut out = Vec::new();
    for rp in &sig.ret_places {
        out.extend(subst(p, tys, facts, roots, &rp.place, &bases));
    }
    out.sort();
    out.dedup();
    Some(out)
}

/// The tasks of the bodies `comp` of a component (`task(T)`, `fork_task(T)`).
///
/// There is one task for each spawn site of a `spawn` and for each branch of
/// a `fork`, in the order of the sites (the order of the source). Returns the
/// task of each site.
pub fn tasks(p: &Program, comp: &[BodyId], facts: &mut FnFacts) -> BTreeMap<SpawnId, TaskId> {
    let mut sites: BTreeSet<SpawnId> = BTreeSet::new();
    for &bid in comp {
        let Some(b) = p.bodies.get(bid.index()) else {
            continue;
        };
        for blk in &b.blocks {
            match &blk.term.kind {
                TermKind::Spawn { site, .. } => {
                    sites.insert(*site);
                }
                TermKind::Fork { sites: fs, .. } => sites.extend(fs.iter().copied()),
                _ => {}
            }
        }
    }
    let mut out = BTreeMap::new();
    for s in sites {
        let Some(d) = p.spawns.get(s.index()) else {
            continue;
        };
        let kind = if d.fork {
            TaskKind::Fork
        } else {
            TaskKind::Spawn
        };
        out.insert(s, facts.add_task(kind, span(d.origin.span)));
    }
    out
}

/// `std_effect(E)` for each standard effect that the facts name.
///
/// The facts name the effects that escape, the stated effects, the effects
/// that a clause performs, the handled effects and the effects of function
/// arguments (as the old lowering, `name_effects`).
pub fn std_effects(facts: &mut FnFacts) {
    let named: BTreeSet<&str> = facts
        .escapes_at
        .iter()
        .map(|(_, e)| e.as_str())
        .chain(facts.declared_effect.iter().map(String::as_str))
        .chain(facts.clause_performs.iter().map(|(_, e)| e.as_str()))
        .chain(facts.handlers.iter().map(|h| h.effect.as_str()))
        .chain(facts.fn_arg_effect.iter().map(|(_, _, e)| e.as_str()))
        .chain(facts.param_effect.iter().map(|(_, _, e)| e.as_str()))
        .collect();
    let std: Vec<String> = named
        .into_iter()
        .filter(|e| effects::is_std(e))
        .map(str::to_string)
        .collect();
    facts.std_effects = std;
}

/// True if root `r` of `facts` is the value of a local.
pub fn is_local_root(facts: &FnFacts, p: PlaceId) -> bool {
    facts
        .places
        .get(p.index())
        .and_then(|i| facts.roots.get(i.root.index()))
        .is_some_and(|r| r.kind == RootKind::Local)
}
