//! The application of a summary at a run node (`docs/ir.md` 6.7):
//! `apply(Σ, σ, n, kind)`.
//!
//! `σ` ([`Sigma`]) maps the places of the interface of the callee onto the
//! places of the caller at the run node: the places of each argument, the
//! places that the references behind a reference argument point into, the
//! `rc` groups, the frame root of the callee, and the places of a caller
//! (the root of the places of the callers of the run node). Stage F5 knows one kind of
//! run node: a `Call` of a function item ([`RunKind::Item`]). Stage F7 adds
//! the `UnwindValue` of a value whose type has an `on abort` function
//! ([`RunKind::OnAbort`]).
//!
//! - [`main`] gives the facts of the `Main` node: the parts `reads`, `muts`,
//!   `lends`, `performs`, `multi`, and the checks of one call
//!   against its callee (`call_arg` of each place that an argument reaches,
//!   also through the references behind it, R3RT3; `call_mut`, `arg_at`,
//!   `param_in`, `uniq_param`, `arg_aliased`, the argument sites).
//! - [`ret_value`] gives the value of the result (part `ret`): it binds at
//!   the `Ret` node.
//! - [`stores`] gives the values that go behind a reference argument that
//!   the callee changes (part `stores`, R3RT6).
//!
//! The analysis (`super::transfer`) and the templates of the fact generator
//! (`crate::factgen::templates`) both read these functions, so the state
//! after a call and the facts of the call agree.

use std::collections::BTreeSet;

use weft_facts::{ArgSite, NodeId, PlaceId, Span, Step, StepKind};
use weft_ir::ty::AdtKind;
use weft_ir::{BodyId, FnDecl, Operand, Ty, TyId, TyTable};

use super::domain::{AbsVal, PathStep, State, Tree};
use super::sig::{byval_refs, holds_refs, is_ref};
use super::summary::{CapIface, Flow, IPlace, IRoot, IStep, Summary};
use super::transfer::{self, Cx};
use crate::factgen::alpha::AlphaError;
use crate::irbuild::subst;
use crate::props::ir_props;

/// The kind of a run node (`docs/ir.md` 6.7, "The kinds of run node").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RunKind {
    /// A `Call` of a function item: σ maps the parameters to the arguments.
    Item,
    /// An `UnwindValue` with an `on abort` function (`docs/ir.md` 5.28): σ
    /// maps the parameter to the value. The function gets the root
    /// handlers (`CapArgs::Root`), so its effects do not go to a handler of
    /// the code that aborts, and the unwinder drops its result. W0118 checks
    /// the rest of the function (`crate::factgen::checks`).
    OnAbort,
}

/// σ of a run node: the places of the caller for the interface roots of the
/// callee.
#[derive(Clone, Debug, Default)]
pub struct Sigma {
    /// The type of each parameter with the type arguments of the call.
    pub tys: Vec<TyId>,
    /// σ(`Param(i)`) for the parts `muts`, `reads`, `lends` and the stated
    /// places: the places of a reference argument, or the places that the
    /// references of a by-value argument point into if its parameter can hold
    /// references. Else empty.
    pub args: Vec<Vec<PlaceId>>,
    /// The places that the references of each argument point into, also for
    /// a parameter of a type parameter: what flows into the result.
    pub values: Vec<Vec<PlaceId>>,
    /// The handle places `h.*` of the `Rc` handles on the way to each
    /// argument: a reference through a handle depends on it (ADR 0003).
    pub deps: Vec<Vec<PlaceId>>,
    /// σ(`Held(i)`): the places that the references behind a reference
    /// argument point into, if its pointee can hold a reference.
    pub helds: Vec<Vec<PlaceId>>,
    /// Each argument is `@ uniq`.
    pub uniq: Vec<bool>,
    /// σ(`Frame`): the root of the callee frame of the run node.
    pub frame: Option<PlaceId>,
    /// The id of the run node: each run node gives its splits and its
    /// one-place instances ids of their own.
    pub inst: u32,
}

/// The type behind a reference type `t`.
fn pointee(tys: &TyTable, t: TyId) -> Option<TyId> {
    match tys.try_get(t) {
        Some(Ty::Ref(x)) => Some(*x),
        _ => None,
    }
}

/// True if the value behind the reference type `t` can hold a reference.
/// The value behind a slice reference is its elements (`Lower::pointee_refs`).
pub fn pointee_refs(tys: &TyTable, t: TyId) -> bool {
    match pointee(tys, t).and_then(|x| tys.try_get(x).cloned()) {
        Some(Ty::Slice(x)) => holds_refs(tys, x),
        Some(_) => pointee(tys, t).is_some_and(|x| holds_refs(tys, x)),
        None => false,
    }
}

/// The types of the parts of a value of type `t` that it holds inline: the
/// type itself, its fields, its tuple parts, its elements and its payloads.
/// A reference ends the walk.
fn parts(tys: &mut TyTable, t: TyId, out: &mut BTreeSet<TyId>) {
    if !out.insert(t) || out.len() > 256 {
        return;
    }
    let inner: Vec<TyId> = match tys.try_get(t).cloned() {
        Some(Ty::Tuple(ts)) => ts,
        Some(Ty::Array(x, _) | Ty::Slice(x)) => vec![x],
        Some(Ty::Adt(a, args)) => {
            let kind = tys.adts().get(a.index()).map(|d| d.kind.clone());
            match kind {
                Some(AdtKind::Struct(fs)) => fs.iter().map(|f| subst(tys, f.ty, &args)).collect(),
                Some(AdtKind::Enum(vs)) => vs
                    .iter()
                    .flat_map(|v| v.fields.clone())
                    .map(|x| subst(tys, x, &args))
                    .collect(),
                Some(AdtKind::Extern { .. }) | None => args,
            }
        }
        _ => Vec::new(),
    };
    for x in inner {
        parts(tys, x, out);
    }
}

/// The types that the references in a value of type `t` can point to. A
/// type parameter can be any type: it gives `None`.
fn targets(tys: &mut TyTable, t: TyId) -> Option<BTreeSet<TyId>> {
    let mut seen = BTreeSet::new();
    parts(tys, t, &mut seen);
    let mut out = BTreeSet::new();
    let mut work: Vec<TyId> = seen.into_iter().collect();
    let mut done = BTreeSet::new();
    while let Some(x) = work.pop() {
        if !done.insert(x) || done.len() > 256 {
            continue;
        }
        match tys.try_get(x).cloned() {
            Some(Ty::Param(_)) => return None,
            Some(Ty::Ref(y)) => {
                out.insert(y);
                let mut more = BTreeSet::new();
                parts(tys, y, &mut more);
                work.extend(more);
            }
            _ => {}
        }
    }
    Some(out)
}

/// True if a value of type `holder` can hold a reference into a value of
/// type `pointee`: to the value or to a part of it (R3RT6).
fn can_hold_into(tys: &mut TyTable, holder: TyId, pointee: TyId) -> bool {
    let Some(ts) = targets(tys, holder) else {
        return true;
    };
    let mut ps = BTreeSet::new();
    parts(tys, pointee, &mut ps);
    ts.iter().any(|t| ps.contains(t)) || ps.iter().any(|&p| tys.mentions_param(p))
}

/// True if a value of type `holder` can hold the references of a value of
/// type `value`: they can point to one type (R3RT6).
fn can_hold_value(tys: &mut TyTable, holder: TyId, value: TyId) -> bool {
    match (targets(tys, holder), targets(tys, value)) {
        (Some(h), Some(v)) => h.iter().any(|t| v.contains(t)),
        _ => true,
    }
}

/// σ of a `Call` of `decl` with the type arguments `targs` and the
/// arguments `args`, in state `st` of body `body`. `inst` is the id of the
/// run node.
///
/// # Errors
///
/// The errors of α, and [`AlphaError::BadPlace`] for an argument with no
/// parameter.
#[allow(clippy::too_many_arguments)]
pub fn sigma(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    decl: &FnDecl,
    targs: &[TyId],
    args: &[Operand],
    inst: u32,
) -> Result<Sigma, AlphaError> {
    let mut s = Sigma {
        inst,
        ..Sigma::default()
    };
    for (i, op) in args.iter().enumerate() {
        let declared = *decl
            .params
            .get(i)
            .ok_or_else(|| AlphaError::BadPlace(format!("an argument {i} with no parameter")))?;
        let ty = subst(cx.tys, declared, targs);
        let v = transfer::operand(cx, body, st, op)?.flat();
        let (named, deps): (Vec<PlaceId>, Vec<PlaceId>) = v
            .refs
            .iter()
            .copied()
            .partition(|&r| !cx.roots.is_handle(r));
        let placed = is_ref(cx.tys, ty) || byval_refs(cx.tys, declared);
        let mut helds = Vec::new();
        if is_ref(cx.tys, ty) && pointee_refs(cx.tys, ty) {
            for &q in &named {
                helds.extend(transfer::held_at(cx.p, st, cx.facts, cx.roots, q, None)?);
            }
            helds.sort();
            helds.dedup();
        }
        s.tys.push(ty);
        s.args.push(if placed { named.clone() } else { Vec::new() });
        s.values.push(named);
        s.deps.push(deps);
        s.helds.push(helds);
        s.uniq.push(v.uniq);
    }
    Ok(s)
}

/// The split id of the split at parameter `label` of run node `inst`: each
/// run node has splits of its own (QA17).
fn seg_split(inst: u32, label: u32) -> u32 {
    0x0010_0000_u32
        .saturating_add(inst.saturating_mul(64))
        .saturating_add(label.min(63))
}

/// What σ maps a `Param` root to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Base {
    /// The places of the argument ([`Sigma::args`]).
    Args,
    /// The places of the value of the argument ([`Sigma::values`]), and a
    /// one-place instance for each wildcard step if the bool is true.
    Values(bool),
}

/// σ of the interface place `place`.
///
/// # Errors
///
/// Returns [`AlphaError::Later`] for a root of a closure, of a handler or of
/// a caller (stages F11 and later).
fn places(
    cx: &mut Cx<'_>,
    s: &Sigma,
    place: &IPlace,
    base: Base,
) -> Result<Vec<PlaceId>, AlphaError> {
    let get = |v: &[Vec<PlaceId>], i: u32| v.get(i as usize).cloned().unwrap_or_default();
    let start = match place.root {
        IRoot::Param(i) => match base {
            Base::Args => get(&s.args, i),
            Base::Values(_) => get(&s.values, i),
        },
        IRoot::Held(i) => get(&s.helds, i),
        IRoot::Group(a) => vec![cx.roots.group_of_adt(cx.tys, cx.facts, a)],
        IRoot::Frame => s.frame.into_iter().collect(),
        // A place of a caller of the callee is a place of a caller of the
        // run node, or a place of the run node that it cannot name: the
        // places of the caller of the run node.
        IRoot::Caller => vec![cx.roots.caller(cx.facts)],
        IRoot::CaptureCell(_)
        | IRoot::Capture(_)
        | IRoot::Cap(_)
        | IRoot::OpResult(_)
        | IRoot::ResumeResult => {
            return Err(AlphaError::Later(
                "a summary that names a capture or a handler (stages F11 and later)",
            ))
        }
    };
    let one = matches!(base, Base::Values(true));
    let mut out = Vec::new();
    for b in start {
        let mut q = b;
        for step in &place.steps {
            q = match step {
                IStep::Step(st, text) => cx.facts.child(q, *st, text),
                IStep::Wild if one => cx.facts.wildcard_one(q, s.inst),
                IStep::Wild => cx.facts.wildcard(q),
                IStep::Seg {
                    label,
                    hi,
                    unstable,
                } => {
                    let step = Step {
                        kind: StepKind::Seg {
                            split: seg_split(s.inst, *label),
                            hi: *hi,
                        },
                        unstable: *unstable,
                    };
                    let text = if *hi { "[k..]" } else { "[..k]" };
                    cx.facts.child(q, step, text)
                }
            };
        }
        out.push(q);
    }
    if let (IRoot::Param(i), Base::Values(_)) = (&place.root, base) {
        out.extend(get(&s.deps, *i));
    }
    out.sort();
    out.dedup();
    Ok(out)
}

/// The handles that a place of an `rc` group in the result depends on: the
/// handle places on the way to each argument, and the handle of each
/// reference argument to an `Rc` (`&Rc<T>`), or to a value that holds one
/// (each handle below it: the wildcard place). A new value of such a handle
/// can free the object (`Lower::group_arg_deps`, ADR 0003).
fn group_deps(cx: &mut Cx<'_>, s: &Sigma) -> Vec<PlaceId> {
    let mut out: Vec<PlaceId> = s.deps.iter().flatten().copied().collect();
    for (i, &t) in s.tys.iter().enumerate() {
        let Some(x) = pointee(cx.tys, t) else {
            continue;
        };
        let top = matches!(cx.tys.lang(x), Some((weft_ir::ty::Lang::Rc, _)));
        if !top && !ir_props(cx.tys, x).nonportable {
            continue;
        }
        for &p in s.args.get(i).into_iter().flatten() {
            let h = if top { p } else { cx.facts.wildcard(p) };
            out.push(cx.roots.handle_place(cx.facts, h));
        }
    }
    out.sort();
    out.dedup();
    out
}

/// True if a result of type `t` is one reference to a value with no
/// reference in it, or an `Option` of one: a call gives it a one-place
/// instance of each wildcard place (ADR 0003).
fn one_result(tys: &TyTable, t: TyId) -> bool {
    let one = |x: TyId| pointee(tys, x).is_some_and(|y| !holds_refs(tys, y));
    match tys.try_get(t) {
        Some(Ty::Adt(a, args)) => {
            let option = tys
                .adts()
                .get(a.index())
                .is_some_and(|d| d.name == "Option" && matches!(d.kind, AdtKind::Enum(_)));
            option && args.first().is_some_and(|&x| one(x))
        }
        _ => one(t),
    }
}

/// The value of the result of a run node of `sum` with σ `s`, for a result
/// of type `ret` (part `ret`).
///
/// The stated places of the result, each part of a tuple with its own
/// places; and, if the type of the result can hold a reference, the places
/// that flow from the arguments. A call in no cycle gives a one-place
/// result a one-place instance of each wildcard place.
///
/// # Errors
///
/// The errors of σ.
pub fn ret_value(cx: &mut Cx<'_>, sum: &Summary, s: &Sigma, ret: TyId) -> Result<Tree, AlphaError> {
    let props = ir_props(cx.tys, ret);
    let mut top = AbsVal::of_type(props.linear);
    for p in &sum.ret.places {
        top.refs.extend(places(cx, s, p, Base::Args)?);
        match p.root {
            IRoot::Param(i) => top
                .refs
                .extend(s.deps.get(i as usize).into_iter().flatten().copied()),
            IRoot::Group(_) => top.refs.extend(group_deps(cx, s)),
            _ => {}
        }
    }
    if !sum.ret.places.is_empty() && sum.ret.uniq {
        top.uniq = true;
    }
    let mut flows = std::collections::BTreeSet::new();
    if props.holds_refs {
        let one = one_result(cx.tys, ret);
        for p in &sum.ret.flows {
            flows.extend(places(cx, s, p, Base::Values(one))?);
        }
    }
    if sum.ret.parts.is_empty() {
        top.refs.extend(flows);
        return Ok(Tree::leaf(top));
    }
    // A tuple with stated places of its parts: each stated part has its own
    // places; the flows go to the other parts (`Lower::result_places`). The
    // parts name the whole value, so the top holds nothing of its own (a
    // part keeps its `@ uniq` mode).
    top.uniq = true;
    let mut t = Tree::leaf(top);
    let arity = match cx.tys.try_get(ret) {
        Some(Ty::Tuple(ts)) => ts.len(),
        _ => 0,
    };
    for k in 0..arity {
        let k = u32::try_from(k).unwrap_or(u32::MAX);
        let mut v = AbsVal::refs([]);
        match sum.ret.parts.iter().find(|(i, _, _)| *i == k) {
            Some((_, ps, uniq)) => {
                for p in ps {
                    v.refs.extend(places(cx, s, p, Base::Args)?);
                }
                v.uniq = *uniq;
            }
            None => v.refs.extend(flows.iter().copied()),
        }
        t.kids.insert(PathStep::Field(k), Tree::leaf(v));
    }
    Ok(t)
}

/// The places that the run node of `sum` with σ `s` changes (part
/// `muts`), each with the callee root index of its parameter.
///
/// # Errors
///
/// The errors of σ.
pub fn muts(cx: &mut Cx<'_>, sum: &Summary, s: &Sigma) -> Result<Vec<(PlaceId, u32)>, AlphaError> {
    let mut out = Vec::new();
    for (m, idx) in &sum.muts {
        for p in places(cx, s, m, Base::Args)? {
            out.push((p, *idx));
        }
    }
    Ok(out)
}

/// The values that go behind the reference arguments that the run node of
/// `sum` with σ `s` changes (part `stores`).
///
/// For each place of such an argument whose root the node changes, the
/// result has the places that its value can point into after the node.
///
/// A place gets the references behind the other arguments, and a reference
/// into another argument only if the type of the pointee can hold one
/// (R3RT6).
///
/// # Errors
///
/// The errors of σ.
pub fn stores(
    cx: &mut Cx<'_>,
    sum: &Summary,
    s: &Sigma,
    changed: &[(PlaceId, u32)],
) -> Result<Vec<(PlaceId, Vec<PlaceId>)>, AlphaError> {
    let roots: BTreeSet<weft_facts::RootId> = changed
        .iter()
        .filter_map(|(m, _)| cx.facts.places.get(m.index()).map(|i| i.root))
        .collect();
    let mut out = Vec::new();
    for st in &sum.stores {
        let j = st.into as usize;
        let Some(&tj) = s.tys.get(j) else {
            continue;
        };
        let Some(holder) = pointee(cx.tys, tj) else {
            continue;
        };
        if !pointee_refs(cx.tys, tj) {
            continue;
        }
        let into: Vec<PlaceId> = s
            .args
            .get(j)
            .into_iter()
            .flatten()
            .copied()
            .filter(|p| {
                cx.facts
                    .places
                    .get(p.index())
                    .is_some_and(|i| roots.contains(&i.root))
            })
            .collect();
        if into.is_empty() {
            continue;
        }
        let mut refs = Vec::new();
        for f in &st.flows {
            match *f {
                Flow::Held(i) => refs.extend(s.helds.get(i as usize).into_iter().flatten()),
                Flow::Into(i) => {
                    let Some(&ti) = s.tys.get(i as usize) else {
                        continue;
                    };
                    let ok = match pointee(cx.tys, ti) {
                        Some(pi) => can_hold_into(cx.tys, holder, pi),
                        None => can_hold_value(cx.tys, holder, ti),
                    };
                    if ok {
                        refs.extend(places(
                            cx,
                            s,
                            &IPlace::wild(IRoot::Param(i)),
                            Base::Values(false),
                        )?);
                    }
                }
                Flow::Value(i) => {
                    let Some(&ti) = s.tys.get(i as usize) else {
                        continue;
                    };
                    if can_hold_value(cx.tys, holder, ti) {
                        refs.extend(places(
                            cx,
                            s,
                            &IPlace::root(IRoot::Param(i)),
                            Base::Values(false),
                        )?);
                    }
                }
            }
        }
        refs.sort();
        refs.dedup();
        if refs.is_empty() {
            continue;
        }
        for p in into {
            out.push((p, refs.clone()));
        }
    }
    Ok(out)
}

/// What [`main`] needs to know about the call besides σ.
#[derive(Clone, Debug)]
pub struct Site<'a> {
    /// The name of the callee, for the argument sites.
    pub callee: &'a str,
    /// The span of each argument.
    pub spans: Vec<Span>,
    /// The places of each argument as a place of the caller (a by-value
    /// argument is the base of the places inside it), for the stated `in`
    /// places.
    pub bases: Vec<Vec<PlaceId>>,
}

/// The facts of the `Main` node `n` of a run node of `sum` with σ `s`.
///
/// They are `reads_at`, `mutates_at` and `call_mut` (part `muts`),
/// `lends_mut`, `escapes_at` (part `performs`), `multi_at`, and the checks
/// of the call against its callee: `call_arg`, `param_in` and `arg_at`
/// (W0203), `uniq_param` and `arg_aliased` (W0406). The template gives
/// `may_abort` if the node keeps an abort edge (`crate::factgen::frames`).
///
/// For [`RunKind::OnAbort`] only `reads_at`, `mutates_at` and `lends_mut`
/// (not of the places of a caller): the function gets the root handlers.
///
/// Returns the places that the node changes, with their callee root
/// indexes.
///
/// # Errors
///
/// The errors of σ.
pub fn main(
    cx: &mut Cx<'_>,
    n: NodeId,
    sum: &Summary,
    s: &Sigma,
    site: &Site<'_>,
    kind: RunKind,
) -> Result<Vec<(PlaceId, u32)>, AlphaError> {
    let item = kind == RunKind::Item;
    for r in &sum.reads {
        for p in places(cx, s, r, Base::Args)? {
            cx.facts.reads_at.push((n, p));
        }
    }
    // The checks of the arguments compare the arguments of one call: the
    // unwinder gives an `on abort` function one value.
    for (i, pi) in sum.params.iter().enumerate().filter(|_| item) {
        let args = s.args.get(i).cloned().unwrap_or_default();
        let given = if args.is_empty() {
            s.values.get(i).cloned().unwrap_or_default()
        } else {
            args
        };
        // An argument reaches the places that the references behind it
        // point into too (R3RT3).
        let held = s.helds.get(i).cloned().unwrap_or_default();
        cx.facts
            .call_arg
            .extend(given.into_iter().chain(held).map(|p| (n, p, pi.root)));
    }
    let changed = muts(cx, sum, s)?;
    for &(p, idx) in &changed {
        cx.facts.mutates_at.push((n, p));
        if item {
            cx.facts.call_mut.push((n, p, idx));
        }
    }
    for l in &sum.lends {
        // The root handlers do not change a place of a caller.
        if !item && l.root == IRoot::Caller {
            continue;
        }
        let root = match l.root {
            IRoot::Param(i) => Some(sum.params.get(i as usize).map_or(0, |p| p.root)),
            IRoot::Caller => None,
            _ => Some(0),
        };
        for p in places(cx, s, l, Base::Args)? {
            cx.facts.lends_mut.push((n, p));
            // A place of a caller is no argument of the call: no alias
            // check (W0312) compares it.
            if let (Some(root), true) = (root, item) {
                cx.facts.call_mut.push((n, p, root));
            }
        }
    }
    if !item {
        // The root handlers serve the effects of an `on abort` function:
        // no effect leaves the code that aborts, and no clause resumes it.
        return Ok(changed);
    }
    for pf in &sum.performs {
        match pf.cap {
            CapIface::Row => cx.facts.escapes_at.push((n, pf.effect.clone())),
            CapIface::Cap(_) => {
                return Err(AlphaError::Later(
                    "a perform through a capability of the interface (stage F14)",
                ))
            }
        }
    }
    if sum.multi {
        cx.facts.multi_at.push(n);
    }
    check_args(cx, n, sum, s, site)?;
    Ok(changed)
}

/// The checks of the arguments of the call at node `n` against the
/// parameters of its callee: a reference argument must point into the
/// stated `in` place of its parameter (`param_in`, `arg_at`, W0203), and the
/// argument of a `@ uniq` parameter must be `@ uniq` (`uniq_param`,
/// `arg_aliased`, W0406).
fn check_args(cx: &mut Cx<'_>, n: NodeId, sum: &Summary, s: &Sigma, site: &Site<'_>) -> R {
    // A by-value argument is the base of the places inside it.
    let mut bases = s.clone();
    for (i, a) in bases.args.iter_mut().enumerate() {
        if a.is_empty() {
            a.clone_from(site.bases.get(i).unwrap_or(&Vec::new()));
        }
    }
    for (i, pi) in sum.params.iter().enumerate() {
        let index = u32::try_from(i).unwrap_or(u32::MAX);
        let mut needs = None;
        if let Some(pl) = &pi.in_place {
            let allowed = places(cx, &bases, pl, Base::Args)?;
            let named = s.args.get(i).cloned().unwrap_or_default();
            if !named.is_empty() {
                cx.facts
                    .param_in
                    .extend(allowed.iter().map(|&d| (n, index, d)));
                cx.facts.arg_at.extend(named.iter().map(|&r| (n, index, r)));
                let texts: Vec<&str> = allowed
                    .iter()
                    .map(|&p| cx.facts.place(p).display.as_str())
                    .collect();
                needs = Some(texts.join(" | "));
            }
        }
        let uniq = sum.uniq_needs.contains(&index);
        if uniq {
            cx.facts.uniq_param.push((n, index));
            if !s.uniq.get(i).copied().unwrap_or(false) {
                cx.facts.arg_aliased.push((n, index));
            }
        }
        if needs.is_some() || uniq {
            let span = site
                .spans
                .get(i)
                .copied()
                .unwrap_or_else(|| cx.facts.node(n).span);
            cx.facts.arg_sites.push(ArgSite {
                node: n,
                index,
                span,
                callee: site.callee.to_string(),
                param: pi.name.clone(),
                needs: needs.unwrap_or_default(),
                via: None,
            });
        }
    }
    Ok(())
}

/// The result of a check.
type R = Result<(), AlphaError>;
