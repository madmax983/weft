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
use crate::factgen::alpha::{AlphaError, Role};
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
    /// A `Call` of a closure value that the body knows (stage F11): σ maps
    /// the parameters of the closure to the arguments, and each capture to
    /// the places of its variable at the run node (`Sigma::captures`).
    Closure,
    /// A `Call` of a function value that the body does not know (stage
    /// F12): code of a caller (`super::unknown::code_of_caller`, map N2).
    Unknown,
    /// A run of a function value that a callee does (part `runs`, stage
    /// F12): the callee gives the arguments, so the node has no check of
    /// the arguments against the parameters of the value (`call_arg`,
    /// `call_mut`, W0312), only the check of the places that the value
    /// changes against the places that its environment points into.
    Run,
    /// [`RunKind::Run`] at the `Main` node of the call: the check of the
    /// arguments of the call is at that node, so the run has no check of
    /// its own there (its check is at `Ret`).
    RunShared,
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
    /// The run node is in a cycle of the CFG (a loop): its result gets no
    /// one-place instance (`docs/ir.md` 6.6).
    pub cyclic: bool,
    /// σ(`Capture(k)`) of a closure: the places of the variable of a `Kept`
    /// or a `ByRef` capture at the run node (its value now, RR7), or the
    /// place of the closure value for a `ByMove` capture.
    pub captures: Vec<Vec<PlaceId>>,
    /// σ(`CaptureHeld(k)`) of a closure: what the references in the value of
    /// capture `k` point into at the run node.
    pub cap_helds: Vec<Vec<PlaceId>>,
    /// For a run that a callee does ([`RunKind::Run`]): the places of the
    /// other arguments of the call that gives the value to the callee. The
    /// callee can keep them across the run, so the value must not change
    /// them through its environment (W0312).
    pub others: Vec<PlaceId>,
    /// σ(`CaptureDeep(k)`) of a closure: what the references behind those
    /// point into at the run node.
    pub cap_deeps: Vec<Vec<PlaceId>>,
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
    let mut params = Vec::with_capacity(args.len());
    for i in 0..args.len() {
        let declared = *decl
            .params
            .get(i)
            .ok_or_else(|| AlphaError::BadPlace(format!("an argument {i} with no parameter")))?;
        params.push((declared, subst(cx.tys, declared, targs)));
    }
    sigma_of(cx, body, st, &params, args, inst)
}

/// σ of a run node with the arguments `args`: `params` has the declared
/// type of each parameter and its type with the type arguments of the call.
///
/// # Errors
///
/// The errors of α, and [`AlphaError::BadPlace`] for an argument with no
/// parameter.
pub fn sigma_with(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    params: &[(TyId, TyId)],
    args: &[Operand],
    inst: u32,
) -> Result<Sigma, AlphaError> {
    sigma_of(cx, body, st, params, args, inst)
}

/// σ of a run that a callee does with arguments that the run node does not know.
///
/// The run is a part `runs` of the callee: each parameter of the types `params` gets the places `places`, and the places that the
/// references there point into.
pub fn opaque_sigma(
    cx: &mut Cx<'_>,
    st: &State,
    params: &[(TyId, TyId)],
    places: &[PlaceId],
    inst: u32,
) -> Sigma {
    let mut helds = Vec::new();
    for &q in places {
        if let Ok(h) = transfer::held_at(cx.p, st, cx.facts, cx.roots, q, None) {
            helds.extend(h);
        }
    }
    helds.sort();
    helds.dedup();
    let mut s = Sigma {
        inst,
        ..Sigma::default()
    };
    for &(_, t) in params {
        s.tys.push(t);
        s.args.push(places.to_vec());
        s.values.push(places.to_vec());
        s.deps.push(Vec::new());
        s.helds.push(helds.clone());
        s.uniq.push(false);
    }
    s
}

/// σ of a run node with the arguments `args`: `params` has the declared
/// type of each parameter and its type with the type arguments of the call.
///
/// # Errors
///
/// The errors of α, and [`AlphaError::BadPlace`] for an argument with no
/// parameter.
fn sigma_of(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    params: &[(TyId, TyId)],
    args: &[Operand],
    inst: u32,
) -> Result<Sigma, AlphaError> {
    let mut s = Sigma {
        inst,
        ..Sigma::default()
    };
    for (i, op) in args.iter().enumerate() {
        let &(declared, ty) = params
            .get(i)
            .ok_or_else(|| AlphaError::BadPlace(format!("an argument {i} with no parameter")))?;
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

/// σ of a `Call` of closure `c` in state `st` of body `body`: `callee` is
/// the operand of the closure value and `args` the arguments (`docs/ir.md`
/// 6.7, "The kinds of run node").
///
/// The parameters of the closure map to the arguments, as for an item.
/// `Capture(k)` of a `Kept` or a `ByRef` capture maps to the places of its
/// variable at the run node (the source of the capture, in its maker), and
/// `CaptureHeld(k)` to what the references in the value of the variable
/// point into now (RR7, V103). `Capture(k)` of a `ByMove` capture maps to
/// the place of the closure value, and `CaptureHeld(k)` to the references of
/// the closure value.
///
/// # Errors
///
/// The errors of α, and [`AlphaError::Later`] for a capture of a capability
/// or a continuation (stage F14).
pub fn closure_sigma(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    c: weft_ir::ClosureId,
    (callee, callee_body): (&Operand, BodyId),
    given: transfer::Given<'_>,
    inst: u32,
) -> Result<Sigma, AlphaError> {
    let p = cx.p;
    let decl = p
        .closures
        .get(c.index())
        .ok_or_else(|| AlphaError::BadPlace(format!("no closure c{}", c.0)))?;
    let cb = p
        .bodies
        .get(decl.body.index())
        .ok_or_else(|| AlphaError::BadPlace(format!("no body b{}", decl.body.0)))?;
    let params: Vec<(TyId, TyId)> = cb
        .params
        .iter()
        .skip(1)
        .filter_map(|l| cb.locals.get(l.index()).map(|d| (d.ty, d.ty)))
        .collect();
    let mut s = match given {
        transfer::Given::Args(args) => {
            let n = args.len().min(params.len());
            sigma_of(cx, body, st, params.get(..n).unwrap_or(&[]), args, inst)?
        }
        transfer::Given::Opaque(places, _) => opaque_sigma(cx, st, &params, places, inst),
    };
    let held = |cx: &mut Cx<'_>, ps: &[PlaceId]| -> Result<Vec<PlaceId>, AlphaError> {
        let mut out = Vec::new();
        for &q in ps {
            out.extend(transfer::held_at(cx.p, st, cx.facts, cx.roots, q, None)?);
        }
        out.sort();
        out.dedup();
        Ok(out)
    };
    for cap in &decl.captures {
        match cap.mode {
            weft_ir::CaptureMode::Kept | weft_ir::CaptureMode::ByRef => {
                let a = transfer::alpha(cx, decl.maker, st, &cap.source)?;
                let v = transfer::place_value(cx, decl.maker, st, &cap.source)?.flat();
                let refs: Vec<PlaceId> = v.refs.into_iter().collect();
                s.cap_deeps.push(held(cx, &refs)?);
                s.captures.push(a.places);
                s.cap_helds.push(refs);
            }
            weft_ir::CaptureMode::ByMove => {
                let (places, refs) = match callee {
                    Operand::Copy(q) | Operand::Move(q) => {
                        let a = transfer::alpha(cx, callee_body, st, q)?;
                        let v = transfer::operand(cx, callee_body, st, callee)?.flat();
                        (a.places, v.refs.into_iter().collect())
                    }
                    Operand::Const(_) => (Vec::new(), Vec::new()),
                };
                s.cap_deeps.push(held(cx, &refs)?);
                s.captures.push(places);
                s.cap_helds.push(refs);
            }
            weft_ir::CaptureMode::Cap | weft_ir::CaptureMode::Kont => {
                return Err(AlphaError::Later(
                    "a closure that captures a capability or a continuation (stage F14)",
                ))
            }
        }
    }
    Ok(s)
}

/// σ of a `Call` of closure `c` that a callee made and gave back (`FnVal::Made`).
///
/// The parameters map to the arguments, and each capture to the place of the closure
/// value and to its references (stage F12). The maker frame is gone: the value holds the environment, as a `ByMove` capture of a
/// closure of the component.
///
/// # Errors
///
/// The errors of α, and [`AlphaError::Later`] for a capture of a capability
/// or a continuation (stage F14).
pub fn made_sigma(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    c: weft_ir::ClosureId,
    (callee, callee_body): (&Operand, BodyId),
    given: transfer::Given<'_>,
    inst: u32,
) -> Result<Sigma, AlphaError> {
    let p = cx.p;
    let decl = p
        .closures
        .get(c.index())
        .ok_or_else(|| AlphaError::BadPlace(format!("no closure c{}", c.0)))?;
    let cb = p
        .bodies
        .get(decl.body.index())
        .ok_or_else(|| AlphaError::BadPlace(format!("no body b{}", decl.body.0)))?;
    let params: Vec<(TyId, TyId)> = cb
        .params
        .iter()
        .skip(1)
        .filter_map(|l| cb.locals.get(l.index()).map(|d| (d.ty, d.ty)))
        .collect();
    let mut s = match given {
        transfer::Given::Args(args) => {
            let n = args.len().min(params.len());
            sigma_of(cx, body, st, params.get(..n).unwrap_or(&[]), args, inst)?
        }
        transfer::Given::Opaque(places, _) => opaque_sigma(cx, st, &params, places, inst),
    };
    let (places, refs): (Vec<PlaceId>, Vec<PlaceId>) = match callee {
        Operand::Copy(q) | Operand::Move(q) => {
            // A value that a run of the callee gives back (`with_results`:
            // the run of a maker `mk` makes the closure) is not in the
            // place of the callee: only its references are the environment.
            let holds =
                transfer::reach_fns(cx, callee_body, st, callee)?.contains(&super::FnVal::Made(c));
            let a = if holds {
                transfer::alpha(cx, callee_body, st, q)?
            } else {
                crate::factgen::alpha::Alpha::default()
            };
            let v = transfer::operand(cx, callee_body, st, callee)?.flat();
            // A value behind a reference argument (a run of `fs[i]` in a
            // callee that gets `&fs`): the places of its environment.
            let mut refs: Vec<PlaceId> = v.refs.into_iter().collect();
            refs.extend(transfer::reach_refs(cx, callee_body, st, callee)?);
            refs.sort();
            refs.dedup();
            (a.places, refs)
        }
        Operand::Const(_) => (Vec::new(), Vec::new()),
    };
    // The cell of a variable that the closure captures `ByRef` stands for
    // the current value of the variable (hole N1 of the second review of the
    // ABC preview: a closure that a maker in a closure or a callee made).
    let (cells, cell_refs) = transfer::cell_values(cx, st, &refs)?;
    let mut helds = refs.clone();
    helds.extend(cell_refs);
    helds.sort();
    helds.dedup();
    let mut deep = Vec::new();
    for &q in &helds {
        deep.extend(transfer::held_at(cx.p, st, cx.facts, cx.roots, q, None)?);
    }
    deep.sort();
    deep.dedup();
    for (k, cap) in decl.captures.iter().enumerate() {
        if matches!(
            cap.mode,
            weft_ir::CaptureMode::Cap | weft_ir::CaptureMode::Kont
        ) {
            return Err(AlphaError::Later(
                "a closure that captures a capability or a continuation (stage F14)",
            ));
        }
        // A `Kept` or `ByRef` capture whose variable is a variable of this
        // body (through the `Kept` and `ByRef` captures of the makers) is
        // that variable, as for a closure of the component: the closure
        // changes it and reads it, and no other capture (hole H7 and false
        // positive FP4 of the third review of the ABC preview).
        if let Some(src) = made_capture_source(p, c, k, body) {
            let a = transfer::alpha(cx, body, st, &src)?;
            let v = transfer::place_value(cx, body, st, &src)?.flat();
            let refs: Vec<PlaceId> = v.refs.into_iter().collect();
            let mut deeps = Vec::new();
            for &q in &refs {
                deeps.extend(transfer::held_at(cx.p, st, cx.facts, cx.roots, q, None)?);
            }
            deeps.sort();
            deeps.dedup();
            s.cap_deeps.push(deeps);
            s.captures.push(a.places);
            s.cap_helds.push(refs);
            continue;
        }
        // A `ByRef` capture points into the place of its variable, and a
        // `Kept` capture names the variable: the closure value holds that
        // place as a reference (`transfer::closure_value`), so the capture
        // is also each place that the value points into (hole H2 of the
        // review of the ABC preview: a closure that a closure gives back).
        let mut at = places.clone();
        if matches!(
            cap.mode,
            weft_ir::CaptureMode::ByRef | weft_ir::CaptureMode::Kept
        ) {
            at.extend(refs.iter().copied());
            at.extend(cells.iter().copied());
            at.sort();
            at.dedup();
        }
        s.captures.push(at);
        s.cap_helds.push(helds.clone());
        s.cap_deeps.push(deep.clone());
    }
    Ok(s)
}

/// The place in body `body` that capture `k` of closure `c` names, if the
/// capture is `Kept` or `ByRef` and its variable is a variable of `body`
/// through the `Kept` and `ByRef` captures of the makers of `c` (`env.j`
/// of a `Kept` capture, `(*env.j)` of a `ByRef` capture). A `ByMove` capture
/// on the way is a value of a closure, not a variable: `None`.
fn made_capture_source(
    p: &weft_ir::Program,
    c: weft_ir::ClosureId,
    k: usize,
    body: BodyId,
) -> Option<weft_ir::Place> {
    use weft_ir::{CaptureMode, DerefKind, Proj};
    let decl = p.closures.get(c.index())?;
    let cap = decl.captures.get(k)?;
    if !matches!(cap.mode, CaptureMode::Kept | CaptureMode::ByRef) {
        return None;
    }
    let (mut maker, mut src) = (decl.maker, cap.source.clone());
    // A maker has a lower id than its closures, so the walk ends.
    for _ in 0..=p.closures.len() {
        if maker == body {
            return Some(src);
        }
        let (c2, j, mode) = crate::factgen::alpha::env_capture(p, maker, &src)?;
        let rest = match mode {
            CaptureMode::Kept => src.proj.get(1..)?.to_vec(),
            CaptureMode::ByRef => match src.proj.get(1) {
                Some(Proj::Deref(DerefKind::Ref)) => src.proj.get(2..)?.to_vec(),
                _ => return None,
            },
            _ => return None,
        };
        let d2 = p.closures.get(c2.index())?;
        let cap2 = d2.captures.get(j as usize)?;
        let mut proj = cap2.source.proj.clone();
        proj.extend(rest);
        maker = d2.maker;
        src = weft_ir::Place {
            local: cap2.source.local,
            proj,
        };
    }
    None
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
/// Returns [`AlphaError::Later`] for the cell of a capture and for a root of
/// a handler (stages F14 and later).
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
        IRoot::Capture(k) => get(&s.captures, k),
        IRoot::CaptureHeld(k) => get(&s.cap_helds, k),
        IRoot::CaptureDeep(k) => get(&s.cap_deeps, k),
        IRoot::CaptureCell(_) | IRoot::Cap(_) | IRoot::OpResult(_) | IRoot::ResumeResult => {
            return Err(AlphaError::Later(
                "a summary that names the cell of a capture or a handler (stages F14 and later)",
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

/// σ of the interface place `place`: the places of the run node for it
/// (the places of an argument for a `Param` root).
///
/// # Errors
///
/// The errors of σ.
pub fn iplaces(cx: &mut Cx<'_>, s: &Sigma, place: &IPlace) -> Result<Vec<PlaceId>, AlphaError> {
    places(cx, s, place, Base::Args)
}

/// σ of the interface place `place` as a value that flows.
///
/// The places of the value of an argument for a `Param` root, with the
/// handle places on the way to it (a reference through a handle depends on
/// it, ADR 0003).
///
/// # Errors
///
/// The errors of σ.
pub fn vplaces(cx: &mut Cx<'_>, s: &Sigma, place: &IPlace) -> Result<Vec<PlaceId>, AlphaError> {
    places(cx, s, place, Base::Values(false))
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
/// that flow from the arguments. A call in no cycle ([`Sigma::cyclic`])
/// gives a one-place result a one-place instance of each wildcard place.
///
/// # Errors
///
/// The errors of σ.
pub fn ret_value(cx: &mut Cx<'_>, sum: &Summary, s: &Sigma, ret: TyId) -> Result<Tree, AlphaError> {
    let props = ir_props(cx.tys, ret);
    let mut top = AbsVal::of_type(props.linear || sum.ret.linear);
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
    // A function value can hold references in its environment (stage F12).
    if props.holds_refs || crate::props::ir_has_fns(cx.tys, ret) {
        let one = !s.cyclic && one_result(cx.tys, ret);
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
/// The callee can also store through a reference that the argument holds
/// (`out[0].push(&v[0])` with `out: &Vec<&Vec<&T>>`, hole H-C of the second
/// review of stage F10, `docs/ir.md` 6.7 "As built (F10.2)"). So each
/// referent of such a reference whose root the node changes gets the
/// stored values too (a weak update): the places of `σ(Held(j))` for a
/// reference argument, and the places of `σ(Param(j))` for a by-value
/// argument that holds references. This is the reach of the part `muts`
/// (`mut(out..)` changes `*out`). The type of the value of the root of the
/// referent must be able to hold the stored references (the R3RT6 rule).
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
    let in_changed = |cx: &Cx<'_>, ps: &[PlaceId]| -> Vec<PlaceId> {
        ps.iter()
            .copied()
            .filter(|p| {
                cx.facts
                    .places
                    .get(p.index())
                    .is_some_and(|i| roots.contains(&i.root))
            })
            .collect()
    };
    let mut out = Vec::new();
    for st in &sum.stores {
        let j = st.into as usize;
        let Some(&tj) = s.tys.get(j) else {
            continue;
        };
        // The pointee of a reference argument.
        if let Some(holder) = pointee(cx.tys, tj).filter(|_| pointee_refs(cx.tys, tj)) {
            let into = in_changed(cx, s.args.get(j).map_or(&[][..], Vec::as_slice));
            if !into.is_empty() {
                let refs = flow_refs(cx, s, &st.flows, &[holder])?;
                if !refs.is_empty() {
                    out.extend(into.into_iter().map(|p| (p, refs.clone())));
                }
            }
        }
        // The referents of the references that the argument holds.
        let (held, holder) = if is_ref(cx.tys, tj) {
            (s.helds.get(j), pointee(cx.tys, tj))
        } else if byval_refs(cx.tys, tj) {
            (s.args.get(j), Some(tj))
        } else {
            continue;
        };
        let (Some(held), Some(holder)) = (held, holder) else {
            continue;
        };
        let into = in_changed(cx, held);
        if into.is_empty() {
            continue;
        }
        // The types that a referent can have: the targets of the references
        // in the holder. A type parameter can be any type (the holder then
        // passes each check).
        let kinds: Vec<TyId> =
            targets(cx.tys, holder).map_or_else(|| vec![holder], |ts| ts.into_iter().collect());
        for q in into {
            let tys: Vec<TyId> = match root_ty(cx, q) {
                Some(t) => vec![t],
                None => kinds.clone(),
            };
            let tys: Vec<TyId> = tys
                .into_iter()
                .filter(|&t| holds_refs(cx.tys, t) || cx.tys.mentions_param(t))
                .collect();
            if tys.is_empty() {
                continue;
            }
            let refs = flow_refs(cx, s, &st.flows, &tys)?;
            if !refs.is_empty() {
                out.push((q, refs));
            }
        }
    }
    Ok(out)
}

/// The type of the value of the root of fact place `q`, if the node knows
/// it: the type of a local, or the pointee of a reference parameter.
fn root_ty(cx: &Cx<'_>, q: PlaceId) -> Option<TyId> {
    let root = cx.facts.places.get(q.index())?.root;
    match cx.roots.role(root)? {
        Role::Local((b, l)) => {
            cx.p.bodies
                .get(b.index())?
                .locals
                .get(l.index())
                .map(|d| d.ty)
        }
        Role::Param(b, i) => {
            let body = cx.p.bodies.get(b.index())?;
            let l = body.params.get(i as usize)?;
            pointee(cx.tys, body.locals.get(l.index())?.ty)
        }
        _ => None,
    }
}

/// The places that the flows `flows` of a store give to a value of one of
/// the types `holders` (part `stores`, R3RT6): the references behind the
/// other arguments, and a reference into another argument only if a
/// holder type can hold one.
///
/// # Errors
///
/// The errors of σ.
fn flow_refs(
    cx: &mut Cx<'_>,
    s: &Sigma,
    flows: &[Flow],
    holders: &[TyId],
) -> Result<Vec<PlaceId>, AlphaError> {
    let mut refs = Vec::new();
    for f in flows {
        match *f {
            Flow::Held(i) => refs.extend(s.helds.get(i as usize).into_iter().flatten()),
            Flow::Into(i) => {
                let Some(&ti) = s.tys.get(i as usize) else {
                    continue;
                };
                let pi = pointee(cx.tys, ti);
                let ok = holders.iter().any(|&h| match pi {
                    Some(pi) => can_hold_into(cx.tys, h, pi),
                    None => can_hold_value(cx.tys, h, ti),
                });
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
                if holders.iter().any(|&h| can_hold_value(cx.tys, h, ti)) {
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
    Ok(refs)
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
    // The checks of the arguments compare the arguments of one call: a call
    // of an item or of a closure.
    let item = !matches!(kind, RunKind::OnAbort | RunKind::Run | RunKind::RunShared);
    // An `on abort` function gets the root handlers; a run that a callee
    // does performs and resumes as the value.
    let acts = kind != RunKind::OnAbort;
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
    // A run that a callee does gives the value places that its arguments
    // reach; the value must not change a place that its environment points
    // into (W0312, as for a call of the value with two such arguments).
    let run = kind == RunKind::Run;
    // The places that the callee gives to the run are one argument: the
    // value must not change them through its environment (W0312: the
    // callee keeps them across the run). A change through a parameter of
    // the value is a change of what the callee gives.
    let given = sum.params.first().map(|p| p.root);
    let as_given = |idx: u32| -> u32 {
        match given {
            Some(g) if run && sum.params.iter().any(|p| p.root == idx) => g,
            _ => idx,
        }
    };
    if run {
        for ps in &s.cap_helds {
            cx.facts
                .call_arg
                .extend(ps.iter().map(|&p| (n, p, crate::body::roots::STORED)));
        }
        let g = given.unwrap_or_else(|| crate::body::roots::param(0));
        let mut places: Vec<PlaceId> = s.args.iter().flatten().copied().collect();
        places.extend(s.others.iter().copied());
        places.sort();
        places.dedup();
        cx.facts
            .call_arg
            .extend(places.into_iter().map(|p| (n, p, g)));
    }
    let changed = muts(cx, sum, s)?;
    for &(p, idx) in &changed {
        cx.facts.mutates_at.push((n, p));
        if item || run {
            cx.facts.call_mut.push((n, p, as_given(idx)));
        }
    }
    for l in &sum.lends {
        // The root handlers do not change a place of a caller.
        if !acts && l.root == IRoot::Caller {
            continue;
        }
        let root = match l.root {
            IRoot::Param(i) => Some(sum.params.get(i as usize).map_or(0, |p| p.root)),
            IRoot::Caller => None,
            // A capture is no argument: the value that the call runs.
            IRoot::Capture(_) | IRoot::CaptureHeld(_) | IRoot::CaptureDeep(_) => {
                Some(crate::body::roots::STORED)
            }
            _ => Some(0),
        };
        for p in places(cx, s, l, Base::Args)? {
            cx.facts.lends_mut.push((n, p));
            // A place of a caller is no argument of the call: no alias
            // check (W0312) compares it.
            if let (Some(root), true) = (root, item || run) {
                cx.facts.call_mut.push((n, p, as_given(root)));
            }
        }
    }
    if !acts {
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
    if item {
        check_args(cx, n, sum, s, site)?;
    }
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
