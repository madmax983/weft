//! Summaries from signatures (`docs/ir.md` 6.7, plan stage F5).
//!
//! [`from_signature`] gives the summary of a function whose signature states
//! what it does: an extern function (of the prelude or of the program), or a
//! function with a stated row. The summary has:
//!
//! - `muts`: the `mut` places of the row, of a reference parameter, of a
//!   receiver `self`, or of a by-value parameter that holds references;
//! - `reads`: the places of each argument;
//! - `performs` and `aborts`: each effect of the row, through the
//!   capability that a caller gives; `raises` is an abort too;
//! - `lends`: the places of each argument, if an operation of an effect of
//!   the row takes a reference (a clause of a caller can change them);
//! - `ret`: the stated places of the result, and the places that flow from
//!   the arguments into a result with no stated place;
//! - `stores`: a reference parameter that the row changes gets the held
//!   references of the other arguments, and a reference into another
//!   argument only where its type can hold one (R3RT6, checked at the run
//!   node with the types of the call);
//! - `drops`, `holds`, `uniq_needs` and `only_self` as the signature states
//!   them.
//!
//! The signature of a function with a body also has the parts that the old
//! inference gives (`drops`, `holds`, `raises`): until stage F6 the summary
//! takes them from there. A signature with a part that a summary of stage F5
//! cannot carry (a function value, a store into an `rc` object, a task)
//! gives an error: the program stays with the old pipeline.

use weft_ir::{FnDecl, Ty, TyId, TyTable};

use super::summary::{
    Abort, CapIface, Flow, IPlace, IRoot, IStep, ParamIface, Perform, Ret, Store, Summary,
};
use crate::body::roots;
use crate::program::{FnSig, SigPlace, SigRoot, SigStep};
use crate::props::ir_props;

/// True if a value of type `t` is a reference.
pub fn is_ref(tys: &TyTable, t: TyId) -> bool {
    matches!(tys.try_get(t), Some(Ty::Ref(_)))
}

/// True if a value of type `t` can hold a reference. A type parameter does
/// not count (`Program::ty_holds_refs`).
pub fn holds_refs(tys: &TyTable, t: TyId) -> bool {
    ir_props(tys, t).holds_refs
}

/// True if a by-value parameter of type `t` holds references that point
/// into places of a caller: not a reference, not a function value, and its
/// type can hold a reference (`Lower::byval_refs`).
pub fn byval_refs(tys: &TyTable, t: TyId) -> bool {
    !is_ref(tys, t) && !matches!(tys.try_get(t), Some(Ty::Fn(_))) && holds_refs(tys, t)
}

/// The number of reference types in type `t`.
fn count_refs(tys: &TyTable, t: TyId, depth: usize) -> usize {
    if depth > 32 {
        return 1;
    }
    let deep = |x: &TyId| count_refs(tys, *x, depth + 1);
    match tys.try_get(t) {
        Some(Ty::Ref(x)) => 1 + deep(x),
        Some(Ty::Tuple(ts) | Ty::Adt(_, ts)) => ts.iter().map(deep).sum(),
        Some(Ty::Slice(x) | Ty::Array(x, _)) => deep(x),
        _ => 0,
    }
}

/// The interface place of the signature place `sp`. A `Held` step after the
/// parameter gives the `Held` root.
pub fn sig_place(sp: &SigPlace) -> IPlace {
    let mut root = match sp.root {
        SigRoot::Param(i) => IRoot::Param(u32::try_from(i).unwrap_or(u32::MAX)),
        SigRoot::Group(a) => {
            IRoot::Group(weft_ir::AdtId(u32::try_from(a.index()).unwrap_or(u32::MAX)))
        }
    };
    let mut steps = Vec::new();
    for (k, s) in sp.steps.iter().enumerate() {
        match s {
            SigStep::Held => match root {
                IRoot::Param(i) if k == 0 => root = IRoot::Held(i),
                // A held step deeper in the place: each place behind it.
                _ => {
                    steps.push(IStep::Wild);
                    break;
                }
            },
            SigStep::Step(st, text) => steps.push(IStep::Step(*st, text.clone())),
            SigStep::Wild => steps.push(IStep::Wild),
            SigStep::Seg {
                label,
                hi,
                unstable,
            } => steps.push(IStep::Seg {
                label: u32::try_from(*label).unwrap_or(u32::MAX),
                hi: *hi,
                unstable: *unstable,
            }),
        }
    }
    IPlace::cut(root, steps)
}

/// The callee root index of parameter `i` of `sig`: a parameter with an
/// `in` place has the root of the parameter of its place
/// (`Lower::sig_root`).
fn sig_root(sig: &FnSig, i: usize) -> u32 {
    let mut i = i;
    for _ in 0..sig.params.len() {
        match sig
            .params
            .get(i)
            .and_then(|p| p.place.as_ref())
            .map(|pl| &pl.root)
        {
            Some(SigRoot::Param(j)) if *j != i => i = *j,
            _ => break,
        }
    }
    roots::param(i)
}

/// The part of a signature that a summary of stage F5 cannot carry, if any.
fn unsupported(sig: &FnSig, decl: &FnDecl, tys: &TyTable) -> Option<&'static str> {
    let e = &sig.effects;
    if decl.params.iter().any(|&t| tys.mentions_fn(t)) || tys.mentions_fn(decl.ret) {
        return Some("a call of a function with a function value in its signature (stage F12)");
    }
    if !e.passthrough.is_empty()
        || !e.lent.is_empty()
        || e.ret.is_some()
        || !e.stores.is_empty()
        || e.reaches
        || !e.fn_stores.is_empty()
        || !e.fn_store_refs.is_empty()
        || !e.op_fns.is_empty()
        || !e.op_effects.is_empty()
    {
        return Some("a call of a function that runs or keeps function values (stage F12)");
    }
    if !e.group_stores.is_empty() {
        return Some("a call of a function that stores into an `rc` object (stage F13)");
    }
    if e.pins || !e.tasks.is_empty() || !e.task_runs.is_empty() || !e.task_effects.is_empty() {
        return Some("a call of a function that starts tasks (stage F18)");
    }
    None
}

/// True if an operation of the effect with identity `e` takes a reference
/// (`Lower::effect_lends`).
fn effect_lends(prog: &crate::Program, e: &str) -> bool {
    crate::effects::by_identity(prog, e).is_some_and(|id| {
        prog.effects[id]
            .ops
            .iter()
            .any(|o| o.params.iter().any(|t| prog.ty_holds_refs(t)))
    })
}

/// True if the effect with identity `e` has a `multi` operation.
fn effect_multi(prog: &crate::Program, e: &str) -> bool {
    crate::effects::by_identity(prog, e).is_some_and(|id| prog.effects[id].has_multi())
}

/// The summary of the function `f` of the program of the analysis, with the
/// signature `sig` and the declaration `decl` of the IR.
///
/// # Errors
///
/// Returns the reason if the signature has a part that a summary of stage
/// F5 cannot carry.
pub fn from_signature(
    prog: &crate::Program,
    f: crate::FnId,
    sig: &FnSig,
    decl: &FnDecl,
    tys: &TyTable,
) -> Result<Summary, &'static str> {
    if let Some(why) = unsupported(sig, decl, tys) {
        return Err(why);
    }
    let def = prog.fns.get(f.index());
    let foreign = def.is_some_and(|d| d.decl.body.is_none() && !d.is_std);
    if foreign
        && sig
            .effects
            .muts
            .iter()
            .any(|m| matches!(m.root, SigRoot::Group(_)))
    {
        return Err("a call of a foreign function that changes an `rc` object (stage F13)");
    }
    let e = &sig.effects;
    let declared = |i: usize| decl.params.get(i).copied();
    let u = |i: usize| u32::try_from(i).unwrap_or(u32::MAX);
    let mut s = Summary::default();
    for (i, p) in sig.params.iter().enumerate() {
        s.params.push(ParamIface {
            name: p.name.clone(),
            root: sig_root(sig, i),
            in_place: p.place.as_ref().map(sig_place),
        });
        s.reads.push(IPlace::root(IRoot::Param(u(i))));
        let by_ref = declared(i).is_some_and(|t| is_ref(tys, t));
        if p.uniq && by_ref {
            s.uniq_needs.insert(u(i));
        }
    }
    for m in &e.muts {
        let idx = match &m.root {
            SigRoot::Param(i) => {
                let t = declared(*i);
                let by_ref = t.is_some_and(|t| is_ref(tys, t));
                let receiver = *i == 0 && sig.params.first().is_some_and(|p| p.name == "self");
                let holds = t.is_some_and(|t| byval_refs(tys, t));
                if !by_ref && !receiver && !holds {
                    continue;
                }
                sig_root(sig, *i)
            }
            SigRoot::Group(a) => roots::group(*a),
        };
        s.muts.push((sig_place(m), idx));
    }
    for name in &e.named {
        let perform = Perform {
            effect: name.clone(),
            cap: CapIface::Row,
        };
        s.aborts.insert(Abort::Perform(perform.clone()));
        s.performs.insert(perform);
        if effect_multi(prog, name) {
            s.multi = true;
        }
    }
    if e.raises {
        s.aborts.insert(Abort::Raises);
    }
    if e.multi {
        s.multi = true;
    }
    if e.named.iter().any(|n| effect_lends(prog, n)) {
        s.lends = (0..sig.params.len())
            .map(|i| IPlace::root(IRoot::Param(u(i))))
            .collect();
    }
    s.ret = ret_of(sig, decl, tys);
    // A reference parameter that the body changes can keep what the other
    // arguments give: the run node checks the types (R3RT6).
    for (j, &tj) in decl.params.iter().enumerate() {
        if !is_ref(tys, tj) {
            continue;
        }
        let mut flows = Vec::new();
        for (i, &ti) in decl.params.iter().enumerate() {
            if i == j {
                continue;
            }
            // `Held(i)` holds only for an argument whose type with the type
            // arguments of the call is a reference (`Sigma::helds`).
            flows.push(Flow::Held(u(i)));
            if holds_refs(tys, ti) {
                flows.push(Flow::Into(u(i)));
            } else if tys.mentions_param(ti) {
                flows.push(Flow::Value(u(i)));
            }
        }
        if !flows.is_empty() {
            s.stores.push(Store { into: u(j), flows });
        }
    }
    s.drops = e.drops.iter().map(|&j| u(j)).collect();
    s.holds = e.holds.iter().map(|&j| u(j)).collect();
    s.only_self =
        e.named.is_empty() && !e.multi && e.muts.iter().all(|m| m.root == SigRoot::Param(0));
    Ok(s)
}

/// The part `ret` of a signature: the stated places of the result (a part of
/// a tuple result for a stated place inside it), and the places that flow
/// from the arguments if a reference of the result has no stated place or
/// the result names a type parameter (`Lower::call_flows`).
fn ret_of(sig: &FnSig, decl: &FnDecl, tys: &TyTable) -> Ret {
    let mut r = Ret::default();
    let tuple = matches!(tys.try_get(decl.ret), Some(Ty::Tuple(_)));
    for rp in &sig.ret_places {
        let p = sig_place(&rp.place);
        match rp.path.first() {
            Some(&k) if tuple => {
                let k = u32::try_from(k).unwrap_or(u32::MAX);
                match r.parts.iter_mut().find(|(i, _, _)| *i == k) {
                    Some((_, ps, uniq)) => {
                        ps.push(p);
                        *uniq &= rp.uniq;
                    }
                    None => r.parts.push((k, vec![p], rp.uniq)),
                }
            }
            _ => {
                r.places.push(p);
                r.uniq = rp.uniq;
            }
        }
    }
    let unstated = count_refs(tys, decl.ret, 0) > sig.ret_places.len();
    if unstated || tys.mentions_param(decl.ret) {
        for (i, &t) in decl.params.iter().enumerate() {
            let i = u32::try_from(i).unwrap_or(u32::MAX);
            // With no stated place, the result can point anywhere inside an
            // argument that can hold a reference (`Lower::flow_refs`).
            if unstated && holds_refs(tys, t) {
                r.flows.push(IPlace::wild(IRoot::Param(i)));
            } else if !is_ref(tys, t) && tys.mentions_param(t) {
                r.flows.push(IPlace::root(IRoot::Param(i)));
            }
            // Only an argument whose type with the type arguments of the call
            // is a reference has places behind it (`Sigma::helds`).
            r.flows.push(IPlace::root(IRoot::Held(i)));
        }
    }
    r
}
