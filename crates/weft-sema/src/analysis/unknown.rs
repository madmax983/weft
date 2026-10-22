//! Code that the body does not know (`docs/ir.md` 6.7): an operation of a
//! caller.
//!
//! A `Perform` through the capability of a caller (`CapOperand::Row`) runs a
//! clause of a handler of a caller. The body does not know the clause, so
//! the run node takes the worst case of map N1 (`docs/ir.md` 6.3, the
//! caller frame root):
//!
//! - it reads and lends the places of each reference argument, and the
//!   places of the callers (`Caller..`): the clause can change them;
//! - its result points into the wildcard place of each reference argument,
//!   of each parameter of the body (a place of a caller that the body can
//!   name), and of the root of the places of the callers;
//! - it can abort; it can resume more than once if the operation is
//!   `multi`.
//!
//! The analysis (`super::transfer`) and the templates of the fact generator
//! (`crate::factgen::templates`) both read [`op_of_caller`], so the state
//! after a perform and its facts agree.

use weft_facts::PlaceId;
use weft_ir::{BodyId, EffectId, OpIdx, Operand, Ty};

use super::apply::pointee_refs;
use super::domain::{AbsVal, State, Tree};
use super::sig::{byval_refs, holds_refs, is_ref};
use super::transfer::{self, Cx};
use crate::factgen::alpha::AlphaError;
use crate::props::ir_props;

/// What a perform of an operation of a caller gives.
#[derive(Clone, Debug)]
pub struct OpOut {
    /// The identity of the effect, for `escapes_at`.
    pub effect: String,
    /// The operation is `multi`.
    pub multi: bool,
    /// For each argument of a reference type, the places that it points
    /// into; empty for another argument.
    pub args: Vec<Vec<PlaceId>>,
    /// For each by-value argument, the places that its references point
    /// into.
    pub values: Vec<Vec<PlaceId>>,
    /// The wildcard place of the root of the places of the callers.
    pub caller: PlaceId,
    /// The value of the result.
    pub ret: Tree,
}

/// The run node of a perform of operation `op` of effect `e` through the
/// capability of a caller, with the arguments `args`, in state `st` of body
/// `body` (map N1).
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] for an effect or an operation that the
/// type table does not have, and the errors of α.
pub fn op_of_caller(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    e: EffectId,
    op: OpIdx,
    args: &[Operand],
) -> Result<OpOut, AlphaError> {
    let decl = cx
        .tys
        .effects()
        .get(e.index())
        .ok_or_else(|| AlphaError::BadPlace(format!("no effect {}", e.0)))?;
    let effect = decl.identity.clone();
    let o = decl
        .ops
        .get(op.index())
        .cloned()
        .ok_or_else(|| AlphaError::BadPlace(format!("no operation {} of {effect}", op.0)))?;
    let mut out = OpOut {
        effect,
        multi: o.multi,
        args: Vec::new(),
        values: Vec::new(),
        caller: PlaceId(0),
        ret: Tree::leaf(AbsVal::none()),
    };
    let mut wild: Vec<PlaceId> = Vec::new();
    for (i, a) in args.iter().enumerate() {
        let v = transfer::operand(cx, body, st, a)?.flat();
        let refs: Vec<PlaceId> = v.refs.iter().copied().collect();
        let by_ref = o.params.get(i).is_some_and(|&t| is_ref(cx.tys, t));
        if by_ref {
            wild.extend(refs.iter().map(|&r| cx.facts.wildcard(r)));
            out.args.push(refs);
            out.values.push(Vec::new());
        } else {
            out.args.push(Vec::new());
            out.values.push(refs);
        }
    }
    let c = cx.roots.caller(cx.facts);
    out.caller = cx.facts.wildcard(c);
    let props = ir_props(cx.tys, o.ret);
    let mut top = AbsVal::of_type(props.linear);
    if holds_refs(cx.tys, o.ret) {
        top.refs.extend(wild);
        top.refs.extend(param_places(cx, body)?);
        top.refs.insert(out.caller);
    }
    out.ret = Tree::leaf(top);
    Ok(out)
}

/// The wildcard place of the interface root of each parameter of body
/// `body` that can point into a place of a caller: the pointee of a
/// reference parameter, the pointees of the references of a by-value
/// parameter, and the pointees of the references behind a reference
/// parameter.
fn param_places(cx: &mut Cx<'_>, body: BodyId) -> Result<Vec<PlaceId>, AlphaError> {
    let p = cx.p;
    let b = p
        .bodies
        .get(body.index())
        .ok_or_else(|| AlphaError::BadPlace(format!("no body b{}", body.0)))?;
    let mut out = Vec::new();
    for (i, &l) in b.params.iter().enumerate() {
        let Some(d) = b.locals.get(l.index()) else {
            continue;
        };
        if !matches!(d.kind, weft_ir::LocalKind::Param(_)) {
            continue;
        }
        let i = u32::try_from(i).unwrap_or(u32::MAX);
        let t = d.ty;
        let name = transfer::param_name(p, body, i);
        if is_ref(cx.tys, t) || byval_refs(cx.tys, t) {
            let r = cx.roots.param(cx.facts, body, i, &name);
            out.push(cx.facts.wildcard(r));
        }
        if matches!(cx.tys.try_get(t), Some(Ty::Ref(_))) && pointee_refs(cx.tys, t) {
            let r = cx.roots.held(cx.facts, body, i, &name);
            out.push(cx.facts.wildcard(r));
        }
    }
    Ok(out)
}
