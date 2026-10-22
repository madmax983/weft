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
//! inference gives (`drops`, `holds`, `raises`). From stage F6 the fixpoint
//! of `super::callgraph` gives them from the body ([`Inferred`]); a function
//! with a stated row whose body the fact generator does not support yet
//! keeps the parts of the old inference. A signature with a part that a
//! summary cannot carry yet (a function value, a store into an `rc` object,
//! a task) gives an error: the program stays with the old pipeline.
//!
//! [`build`] gives the summary of a function with no stated row from its
//! signature and the parts that its body gives, and [`to_effect_sig`]
//! projects a summary onto the `EffectSig` of today (`docs/ir.md` 6.8).

use std::collections::BTreeSet;

use weft_ir::{FnDecl, Ty, TyId, TyTable};

use super::summary::{
    Abort, CapIface, Flow, IPlace, IRoot, IStep, ParamIface, Perform, Ret, Store, Summary,
};
use crate::body::roots;
use crate::program::{EffectSig, FnSig, SigPlace, SigRoot, SigStep};
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
pub(crate) fn sig_root(sig: &FnSig, i: usize) -> u32 {
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

/// The parts of a summary that effect inference gives (`docs/ir.md` 6.8).
///
/// They are the row (the changed places and the effects), and the parts
/// that a body always infers (`raises`, `assert`, `drops`, `holds`). A signature
/// states the row, and the body of a function with no stated row gives it
/// (`super::summarize`). Each part only grows in the fixpoint
/// (`super::callgraph`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Inferred {
    /// The places that the body changes, each with the callee root index of
    /// its parameter.
    pub muts: Vec<(IPlace, u32)>,
    /// The effects that the body performs through a capability of a caller.
    pub named: BTreeSet<String>,
    /// The body can raise a failure that the runtime makes.
    pub raises: bool,
    /// The body can end with a failed `assert`, also in a callee (part
    /// `aborts`, `docs/ir.md` 6.5). The `EffectSig` of today has no part
    /// for it.
    pub assert: bool,
    /// The body can resume a continuation more than once with no effect of
    /// the row that says so (a call of an unknown function value).
    pub multi: bool,
    /// The type parameters of the values that the body drops.
    pub drops: BTreeSet<u32>,
    /// The type parameters of the values that the body holds across a node
    /// that can abort or resume more than once.
    pub holds: BTreeSet<u32>,
}

/// True if interface place `a` is `b` or a place that holds `b`.
///
/// They have the same root, and the steps of `a` are a prefix of the steps
/// of `b` (the texts do not count), or `a` ends with a wildcard step at that
/// point.
pub fn covers(a: &IPlace, b: &IPlace) -> bool {
    if a.root != b.root {
        return false;
    }
    for (k, x) in a.steps.iter().enumerate() {
        let Some(y) = b.steps.get(k) else {
            return false;
        };
        let same = match (x, y) {
            (IStep::Wild, _) => return true,
            (IStep::Step(s, _), IStep::Step(t, _)) => s == t,
            _ => x == y,
        };
        if !same {
            return false;
        }
    }
    true
}

impl Inferred {
    /// Adds the parts of `o`. Returns true if a part grows. A changed place
    /// that a place of the row covers adds nothing; a new place removes the
    /// places that it covers.
    pub fn join(&mut self, o: &Self) -> bool {
        let mut grew = false;
        for (m, idx) in &o.muts {
            if self.muts.iter().any(|(k, _)| covers(k, m)) {
                continue;
            }
            self.muts.retain(|(k, _)| !covers(m, k));
            self.muts.push((m.clone(), *idx));
            grew = true;
        }
        for n in &o.named {
            grew |= self.named.insert(n.clone());
        }
        for d in &o.drops {
            grew |= self.drops.insert(*d);
        }
        for h in &o.holds {
            grew |= self.holds.insert(*h);
        }
        if o.raises && !self.raises {
            self.raises = true;
            grew = true;
        }
        if o.assert && !self.assert {
            self.assert = true;
            grew = true;
        }
        if o.multi && !self.multi {
            self.multi = true;
            grew = true;
        }
        if grew {
            self.muts.sort();
        }
        grew
    }

    /// The parts that the signature `sig` states (`decl` is the declaration
    /// of the IR): its `mut` places, its effects, and the parts that the old
    /// inference gives for a function with a body.
    pub fn of_signature(sig: &FnSig, decl: &FnDecl, tys: &TyTable) -> Self {
        let e = &sig.effects;
        let declared = |i: usize| decl.params.get(i).copied();
        let mut out = Self::default();
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
            out.muts.push((sig_place(m), idx));
        }
        out.named.clone_from(&e.named);
        out.raises = e.raises;
        out.multi = e.multi;
        out.drops = e.drops.iter().map(|&j| u32_of(j)).collect();
        out.holds = e.holds.iter().map(|&j| u32_of(j)).collect();
        out
    }
}

/// `i` as a `u32` (saturated).
fn u32_of(i: usize) -> u32 {
    u32::try_from(i).unwrap_or(u32::MAX)
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
    let mut s = build(
        prog,
        sig,
        decl,
        tys,
        &Inferred::of_signature(sig, decl, tys),
    );
    let e = &sig.effects;
    s.only_self =
        e.named.is_empty() && !e.multi && e.muts.iter().all(|m| m.root == SigRoot::Param(0));
    Ok(s)
}

/// The summary of a function with the signature `sig` (its parameters, its
/// stated places and its types; `decl` is the declaration of the IR) and the
/// inferred parts `inf`.
///
/// The signature gives the parameters, the reads (the places of each
/// argument), the `@ uniq` parameters, the result and the stores. The parts
/// `inf` give the changed places, the effects (each one a perform and an
/// abort through the capability of a caller), `raises`, `multi`, `drops` and
/// `holds`. An effect of the row whose operation takes a reference lends
/// the places of each argument: a clause of a caller can change them. An
/// effect of the row also lends the places of the callers: a clause can
/// change a place that a result of an operation points into (`docs/ir.md`
/// 6.7, "An operation of a caller").
pub fn build(
    prog: &crate::Program,
    sig: &FnSig,
    decl: &FnDecl,
    tys: &TyTable,
    inf: &Inferred,
) -> Summary {
    let declared = |i: usize| decl.params.get(i).copied();
    let u = u32_of;
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
    s.muts.clone_from(&inf.muts);
    for name in &inf.named {
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
    if inf.raises {
        s.aborts.insert(Abort::Raises);
    }
    if inf.assert {
        s.aborts.insert(Abort::Assert);
    }
    if inf.multi {
        s.multi = true;
        s.unknown_multi = true;
    }
    if inf.named.iter().any(|n| effect_lends(prog, n)) {
        s.lends = (0..sig.params.len())
            .map(|i| IPlace::root(IRoot::Param(u(i))))
            .collect();
    }
    if !inf.named.is_empty() {
        s.lends.push(IPlace::wild(IRoot::Caller));
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
    s.drops.clone_from(&inf.drops);
    s.holds.clone_from(&inf.holds);
    s.only_self = inf.named.is_empty()
        && !inf.multi
        && inf
            .muts
            .iter()
            .all(|(m, _)| matches!(m.root, IRoot::Param(0) | IRoot::Held(0)));
    s
}

/// The `EffectSig` of a summary (`docs/ir.md` 6.8).
///
/// It is for the users of the signatures outside fact generation: W0701,
/// `weft deps`, the `pins` part that the interpreter reads. The parts of a
/// summary of a body of group A
/// are the changed places, the effects through the capability of a caller,
/// `raises`, `drops` and `holds`; the other parts are empty.
///
/// A changed place becomes a signature place of its parameter (a `Held`
/// root is the parameter with a first `Held` step) or of its `rc` group,
/// with the text of the parameter and of its steps, at most
/// [`crate::infer::SIG_PLACE_STEPS`] steps (as the old inference).
pub fn to_effect_sig(prog: &crate::Program, sum: &Summary) -> EffectSig {
    let mut out = EffectSig::default();
    let most = crate::infer::SIG_PLACE_STEPS as usize;
    for (m, _) in &sum.muts {
        let name = |i: u32| {
            sum.params
                .get(i as usize)
                .map_or_else(|| format!("parameter {i}"), |p| p.name.clone())
        };
        let (root, mut steps, mut text) = match m.root {
            IRoot::Param(i) => (SigRoot::Param(i as usize), Vec::new(), name(i)),
            IRoot::Held(i) => (
                SigRoot::Param(i as usize),
                vec![SigStep::Held],
                format!("*{}", name(i)),
            ),
            IRoot::Group(a) => {
                let id = crate::AdtId(a.index());
                let text = prog
                    .adts
                    .get(id.index())
                    .map_or_else(|| format!("group {}", a.0), |d| d.name.clone());
                (SigRoot::Group(id), Vec::new(), text)
            }
            _ => continue,
        };
        for st in &m.steps {
            match st {
                IStep::Step(step, t) => {
                    text.push_str(t);
                    steps.push(SigStep::Step(*step, t.clone()));
                }
                IStep::Wild => {
                    text.push_str("..");
                    steps.push(SigStep::Wild);
                }
                IStep::Seg {
                    label,
                    hi,
                    unstable,
                } => steps.push(SigStep::Seg {
                    label: *label as usize,
                    hi: *hi,
                    unstable: *unstable,
                }),
            }
        }
        steps.truncate(most);
        let sp = SigPlace { root, steps, text };
        if !out.muts.contains(&sp) {
            out.muts.push(sp);
        }
    }
    for p in &sum.performs {
        if p.cap == CapIface::Row {
            out.named.insert(p.effect.clone());
        }
    }
    out.raises = sum.aborts.contains(&Abort::Raises);
    out.multi = sum.unknown_multi;
    out.drops = sum.drops.iter().map(|&j| j as usize).collect();
    out.holds = sum.holds.iter().map(|&j| j as usize).collect();
    out
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
