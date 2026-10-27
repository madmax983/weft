//! The transfer functions of the analysis (`docs/ir.md` 6.6).
//!
//! There is one function for each statement kind and for each terminator
//! kind: `Switch`, `Goto`, `Return`, the terminators with no effect on the
//! state, a `Call` of a function item, which applies the summary of the
//! callee (`super::apply`, stage F5), a `Perform` through the capability of
//! a caller (`super::unknown`, stage F6), and a `Call` of a function value
//! that the body knows: a closure of the component or an item (stage F11,
//! [`value_out`]). The other terminators that run another body give
//! [`AlphaError::Later`]. A run node that changes a place of a local that
//! can hold a linear value can put one there.
//!
//! - `Ref(q)` gives `refs = α(q)` and the handle places of each `Deref(Rc)`
//!   on `q`.
//! - `Use(copy q)` gives the value at `q`, with the structure of its move
//!   paths. `Use(move q)` gives it too, and then `q` has no value.
//! - An aggregate gives the values of its operands as its parts. A closure
//!   aggregate gives the closure, the cell roots of its `ByRef` captures and
//!   what its `ByMove` captures hold.
//! - α of `Deref(Ref)` reads the state: the places that the reference points
//!   into ([`held_at`]).

use std::collections::{BTreeMap, BTreeSet};

use weft_facts::{FnFacts, PlaceId};
use weft_ir::ty::AdtKind;
use weft_ir::{
    AggKind, BodyId, Const, LocalId, Operand, Place, Program, Proj, Rvalue, StmtKind, TermKind, Ty,
    TyId, TyTable,
};

use super::domain::{AbsVal, FnVal, Key, PathStep, State, Tree};
use crate::factgen::alpha::{self, Alpha, AlphaError, Role, Roots};
use crate::props::ir_props;

/// What the transfer functions read and write besides the state: the IR, the
/// types, and the places of the facts of the component.
pub struct Cx<'a> {
    /// The program.
    pub p: &'a Program,
    /// The types. α adds the instances of generic field types.
    pub tys: &'a mut TyTable,
    /// The facts of the component: α adds its roots and places here.
    pub facts: &'a mut FnFacts,
    /// The roots of the component.
    pub roots: &'a mut Roots,
    /// The summary of each function that a call can run.
    pub sums: &'a super::summary::Summaries,
    /// The blocks of the component that are in a cycle of the CFG.
    pub cycles: &'a super::widen::Cycles,
    /// The handlers of the component: the handled bodies that run now, and
    /// what the runs of each handler found (plan stage F14).
    pub hx: &'a mut super::clause::Handlers,
}

/// The key of local `l` of body `body`: the site local of an upvar local.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if the local does not exist.
pub fn key(p: &Program, body: BodyId, l: LocalId) -> Result<Key, AlphaError> {
    alpha::owner_local(p, body, l)
}

/// The place as a move path: its local and its steps.
///
/// A place is a move path if each projection is a field or a variant. `None`
/// for a place through a dereference, an index,
/// the elements or a split, and for a place at or below a `Kept` capture of
/// a closure body: it is the cell of a variable of the maker (`docs/ir.md`
/// 5.1.7), not a part of the environment.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if the local does not exist.
pub fn move_path(
    p: &Program,
    body: BodyId,
    place: &Place,
) -> Result<Option<(Key, Vec<PathStep>)>, AlphaError> {
    if let Some((_, _, mode)) = alpha::env_capture(p, body, place) {
        if !matches!(
            mode,
            weft_ir::CaptureMode::ByRef | weft_ir::CaptureMode::ByMove
        ) {
            return Ok(None);
        }
    }
    let k = key(p, body, place.local)?;
    let mut path = Vec::new();
    for pr in &place.proj {
        match pr {
            Proj::Field(f) => path.push(PathStep::Field(f.0)),
            Proj::Variant(v) => path.push(PathStep::Variant(v.0)),
            _ => return Ok(None),
        }
    }
    Ok(Some((k, path)))
}

/// The variable of the maker that a whole `Kept` capture `place` names.
///
/// In an instantiated closure body (`docs/ir.md` 6.5) a new value of the
/// capture is a new value of the variable (a strong update), as at an
/// assignment of the variable in the maker.
///
/// # Errors
///
/// The errors of α.
pub fn kept_whole(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    place: &Place,
) -> Result<Option<Key>, AlphaError> {
    if place.proj.len() != 1 || !cx.roots.is_instantiated(body) {
        return Ok(None);
    }
    let Some((_, _, weft_ir::CaptureMode::Kept)) = alpha::env_capture(cx.p, body, place) else {
        return Ok(None);
    };
    let a = alpha(cx, body, st, place)?;
    Ok(match a.places.as_slice() {
        [q] => cx
            .roots
            .path_of(cx.facts, *q)
            .filter(|(_, path)| path.is_empty())
            .map(|(k, _)| k),
        _ => None,
    })
}

/// The places that the references in the value at fact place `at` point
/// into (`docs/ir.md` 6.3).
///
/// For a place of a local, they are the places of its value in the state
/// (of the move path that names it, or of a move path above it). For a
/// place of the pointee of a parameter, they are the wildcard place of the
/// pointees behind the parameter (`*p..`).
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] for a place that no root of the
/// component has.
pub fn held_at(
    p: &Program,
    st: &State,
    facts: &mut FnFacts,
    roots: &mut Roots,
    at: PlaceId,
    field: Option<(weft_ir::AdtId, u32)>,
) -> Result<Vec<PlaceId>, AlphaError> {
    // A place field points into the place that its struct states for it.
    if let Some(sp) = field.and_then(|(a, f)| roots.field_place(a, f)).cloned() {
        let parent = facts.places.get(at.index()).and_then(|i| i.parent);
        if let Some(out) = parent.and_then(|base| field_places(facts, base, &sp)) {
            return Ok(out);
        }
    }
    let root = facts
        .places
        .get(at.index())
        .map(|i| i.root)
        .ok_or_else(|| AlphaError::BadPlace("no fact place".to_string()))?;
    match roots.role(root) {
        Some(Role::Local(_)) => {
            let (k, path) = roots
                .path_of(facts, at)
                .ok_or_else(|| AlphaError::BadPlace("no move path".to_string()))?;
            Ok(st.value(k, &path).flat().refs.into_iter().collect())
        }
        Some(Role::Param(body, i) | Role::Held(body, i)) => {
            let name = param_name(p, body, i);
            let h = roots.held(facts, body, i, &name);
            let mut out = vec![facts.wildcard(h)];
            out.extend(stored_at(facts, st, at));
            Ok(out)
        }
        // A reference in an `rc` object points into a place that each
        // handle of the group can reach: the wildcard place of each field of
        // the group that its type can point into (`Roots::group_targets`),
        // and the places that the body stored there (stage F13).
        Some(Role::Group) => {
            let mut top = at;
            while let Some(up) = facts.places.get(top.index()).and_then(|i| i.parent) {
                top = up;
            }
            let mut out = roots.group_targets(facts, top, at);
            out.extend(stored_at(facts, st, at));
            Ok(out)
        }
        // A reference in a local of the frame of a callee (a value that a
        // closure put there): the frame root ends at the end of the call, so
        // the wildcard place of the root is enough (stage F13).
        Some(Role::Frame(_)) => {
            let mut top = at;
            while let Some(up) = facts.places.get(top.index()).and_then(|i| i.parent) {
                top = up;
            }
            let mut out = vec![facts.wildcard(top)];
            out.extend(stored_at(facts, st, at));
            Ok(out)
        }
        // A reference in the value of a capture points into what the
        // references of the capture point into (the summary of a closure,
        // `docs/ir.md` 6.7), or into a value that the body stored there.
        Some(Role::Capture(b, k)) => {
            let mut out = vec![roots.capture_held_of(p, facts, b, k)];
            out.extend(stored_at(facts, st, at));
            Ok(out)
        }
        Some(Role::CaptureHeld(b, k) | Role::CaptureDeep(b, k)) => {
            let h = roots.capture_deep_of(p, facts, b, k);
            let mut out = vec![facts.wildcard(h)];
            out.extend(stored_at(facts, st, at));
            Ok(out)
        }
        // The cell of a variable holds no reference of its own: the value
        // of the variable has them.
        Some(Role::Cell(_)) => Ok(Vec::new()),
        // A reference in a place of a caller points into a place of a
        // caller.
        Some(Role::Caller) => {
            let c = roots.caller(facts);
            let mut out = vec![facts.wildcard(c)];
            out.extend(stored_at(facts, st, at));
            Ok(out)
        }
        None => Err(AlphaError::BadPlace(
            "a place with no root of the component".to_string(),
        )),
    }
}

/// The places that the references stored in a heap slot that overlaps the
/// fact place `at` can point into (`docs/ir.md` 6.6): a value that the body
/// puts behind a reference parameter, and reads back later (a loop reads in
/// the next iteration what the iteration before stored). A place below a
/// wildcard place counts as its base.
fn stored_at(facts: &FnFacts, st: &State, at: PlaceId) -> Vec<PlaceId> {
    if st.behind().is_empty() {
        return Vec::new();
    }
    let mut out = Vec::new();
    for (q, refs) in st.behind() {
        if slot_overlaps(facts, *q, at) {
            out.extend(refs.iter().copied());
        }
    }
    out
}

/// The function values stored in a heap slot that overlaps the fact place
/// `at` (stage F13, [`stored_at`]).
fn stored_fns_at(facts: &FnFacts, st: &State, at: PlaceId) -> BTreeSet<FnVal> {
    let mut out = BTreeSet::new();
    for (q, fns) in st.behind_fns() {
        if slot_overlaps(facts, *q, at) {
            out.extend(fns.iter().cloned());
        }
    }
    out
}

/// True if the heap slot of place `q` overlaps the fact place `at`: one is
/// at or below the other, and a place below a wildcard place counts as its
/// base.
pub fn slot_overlaps(facts: &FnFacts, q: PlaceId, at: PlaceId) -> bool {
    let norm = |p: PlaceId| facts.wild_base(p).unwrap_or(p);
    let below = |x: PlaceId, y: PlaceId| {
        let mut cur = Some(x);
        while let Some(c) = cur {
            if c == y {
                return true;
            }
            cur = facts.places.get(c.index()).and_then(|i| i.parent);
        }
        false
    };
    let (a, b) = (norm(at), norm(q));
    below(a, b) || below(b, a)
}

/// Each place of `places` that no local of the component owns gets the
/// references `refs` and the function values `fns` in its heap slot (a weak
/// update, `docs/ir.md` 6.6; function values from stage F13).
fn store_heap(
    facts: &FnFacts,
    roots: &Roots,
    st: &mut State,
    places: &[PlaceId],
    refs: &[PlaceId],
    fns: &BTreeSet<FnVal>,
) {
    if refs.is_empty() && fns.is_empty() {
        return;
    }
    for &q in places {
        if roots.path_of(facts, q).is_none() {
            st.store_behind(q, refs.iter().copied());
            st.store_fns_behind(q, fns.iter().cloned());
        }
    }
}

/// The places of the stated place `sp` of a place field (in terms of
/// `self`), for the struct at fact place `base`. `None` for a stated place
/// that is not in terms of `self` alone.
fn field_places(
    facts: &mut FnFacts,
    base: PlaceId,
    sp: &crate::program::SigPlace,
) -> Option<Vec<PlaceId>> {
    use crate::program::{SigRoot, SigStep};
    if sp.root != SigRoot::Param(0) {
        return None;
    }
    let mut q = base;
    for s in &sp.steps {
        q = match s {
            SigStep::Step(step, text) => facts.child(q, *step, text),
            SigStep::Wild => facts.wildcard(q),
            SigStep::Held | SigStep::Seg { .. } => return None,
        };
    }
    Some(vec![q])
}

/// The text of parameter `i` of body `body`: its name.
pub fn param_name(p: &Program, body: BodyId, i: u32) -> String {
    p.bodies
        .get(body.index())
        .and_then(|b| {
            b.params
                .get(i as usize)
                .and_then(|l| b.locals.get(l.index()))
        })
        .and_then(|d| d.name.clone())
        .unwrap_or_else(|| format!("parameter {i}"))
}

/// α of `place` of body `body` in state `st`: a `Deref(Ref)` gives the
/// places that the reference points into ([`held_at`]).
///
/// # Errors
///
/// The errors of [`alpha::alpha_with`] and of [`held_at`].
pub fn alpha(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    place: &Place,
) -> Result<Alpha, AlphaError> {
    let p = cx.p;
    alpha::alpha_with(
        p,
        cx.tys,
        cx.facts,
        cx.roots,
        body,
        place,
        &mut |facts, roots, at, field| held_at(p, st, facts, roots, at, field),
    )
}

/// The type of `place` of body `body`.
fn place_ty(cx: &mut Cx<'_>, body: BodyId, place: &Place) -> Result<TyId, AlphaError> {
    alpha::place_ty(cx.p, cx.tys, body, place)
        .ok_or_else(|| AlphaError::BadPlace(format!("{place:?} has no type")))
}

/// The value at `place` of body `body` in state `st`, with no move.
///
/// A move path gives its tree. Another place (through a pointer, an element)
/// gives the places that its references point into, and a linear part from
/// its type.
///
/// # Errors
///
/// The errors of α.
pub fn place_value(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    place: &Place,
) -> Result<Tree, AlphaError> {
    if let Some((k, path)) = move_path(cx.p, body, place)? {
        return Ok(st.value(k, &path));
    }
    // A `Kept` capture of an instantiated closure is the variable of the
    // maker: its value in the state (the closure body runs with the values
    // of the maker, `docs/ir.md` 6.5).
    if let Some((_, _, weft_ir::CaptureMode::Kept)) = alpha::env_capture(cx.p, body, place) {
        if cx.roots.is_instantiated(body) && !place.has_deref() {
            let a = alpha(cx, body, st, place)?;
            let paths: Option<Vec<(Key, Vec<PathStep>)>> = a
                .places
                .iter()
                .map(|&q| cx.roots.path_of(cx.facts, q))
                .collect();
            if let Some(paths) = paths.filter(|ps| !ps.is_empty()) {
                let mut v = AbsVal::none();
                for (k, path) in paths {
                    v.join(&st.value(k, &path).flat());
                }
                return Ok(Tree::leaf(v));
            }
        }
    }
    let t = place_ty(cx, body, place)?;
    let props = ir_props(cx.tys, t);
    let mut v = AbsVal::of_type(props.linear);
    // A function value through a pointer or in an element: the values that
    // the places can hold (stage F12, `docs/ir.md` 6.6).
    if crate::props::ir_has_fns(cx.tys, t) {
        let a = alpha(cx, body, st, place)?;
        // A place in an `rc` object: the function values of the handles on
        // the way (an `Rc.new` of a value with a closure gives the handle
        // the closure), not a value that the analysis does not know (stage
        // F13).
        let mut by_handle = BTreeSet::new();
        let mut handle_refs = Vec::new();
        for &h in &a.handles {
            let Some(holder) = cx.facts.places.get(h.index()).and_then(|i| i.parent) else {
                continue;
            };
            let fs = fns_at(cx, st, holder);
            if has_closure(&fs) {
                handle_refs.extend(held_at(cx.p, st, cx.facts, cx.roots, holder, None)?);
            }
            by_handle.extend(fs);
        }
        for &at in &a.places {
            let group = cx
                .facts
                .places
                .get(at.index())
                .is_some_and(|i| matches!(cx.roots.role(i.root), Some(Role::Group)));
            if group && !a.handles.is_empty() {
                if !props.holds_refs {
                    v.refs.extend(handle_refs.iter().copied());
                }
                v.fns.extend(by_handle.iter().cloned());
                let slot = stored_fns_at(cx.facts, st, at);
                if !props.holds_refs && has_closure(&slot) {
                    let stored = stored_at(cx.facts, st, at);
                    // A closure in an `rc` object that points into the group
                    // can point into the object itself: the copy depends on
                    // the handles on the way, as a reference through them
                    // (class H-RC1 of the review of stage F13: `h.f = d.f;
                    // d = newh()` frees the object that the closure reads).
                    let into_group = stored.iter().any(|r| {
                        cx.facts
                            .places
                            .get(r.index())
                            .is_some_and(|i| matches!(cx.roots.role(i.root), Some(Role::Group)))
                    });
                    if into_group {
                        v.refs.extend(a.handles.iter().copied());
                    }
                    v.refs.extend(stored);
                }
                v.fns.extend(slot);
                continue;
            }
            let fs = fns_of_role(cx, st, at);
            // The places that the environments of the closures there point
            // into (hole H2 of the review of the ABC preview: `fs[0]`). The
            // environment of a value of a caller is the place of the caller.
            if !props.holds_refs && has_closure(&fs) {
                v.refs
                    .extend(held_at(cx.p, st, cx.facts, cx.roots, at, None)?);
            }
            v.fns.extend(fs);
            // A place that no local owns: the values of its heap slot, with
            // the references that the store put there (stage F13).
            if cx.roots.path_of(cx.facts, at).is_none() {
                let slot = stored_fns_at(cx.facts, st, at);
                if !props.holds_refs && has_closure(&slot) {
                    v.refs.extend(stored_at(cx.facts, st, at));
                }
                v.fns.extend(slot);
            }
        }
    }
    if props.holds_refs {
        let a = alpha(cx, body, st, place)?;
        let field = match place.proj.split_last() {
            Some((Proj::Field(f), base)) => {
                let base = Place {
                    local: place.local,
                    proj: base.to_vec(),
                };
                match alpha::place_ty(cx.p, cx.tys, body, &base).and_then(|t| cx.tys.try_get(t)) {
                    Some(Ty::Adt(a, _)) => Some((*a, f.0)),
                    _ => None,
                }
            }
            _ => None,
        };
        for &at in &a.places {
            v.refs
                .extend(held_at(cx.p, st, cx.facts, cx.roots, at, field)?);
        }
    }
    Ok(Tree::leaf(v))
}

/// The value of operand `op` of body `body` in state `st`. The move of a
/// `move` operand is not done here ([`moves`]).
///
/// # Errors
///
/// The errors of α.
pub fn operand(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    op: &Operand,
) -> Result<Tree, AlphaError> {
    match op {
        Operand::Copy(q) | Operand::Move(q) => place_value(cx, body, st, q),
        Operand::Const(Const::Fn(f, targs)) => {
            if let Some(why) = crate::factgen::checks::item_value(cx.sums, cx.tys, *f, targs) {
                return Err(AlphaError::Later(why));
            }
            let mut v = AbsVal::plain();
            v.fns.insert(FnVal::Item(*f, targs.clone()));
            Ok(Tree::leaf(v))
        }
        Operand::Const(_) => Ok(Tree::leaf(AbsVal::plain())),
    }
}

/// True if the definition of struct or enum type `t` is linear.
fn declared_linear(tys: &TyTable, t: TyId) -> bool {
    match tys.try_get(t) {
        Some(Ty::Adt(a, _)) => tys.adts().get(a.index()).is_some_and(|d| d.linear),
        _ => false,
    }
}

/// True if `t` is an enum type.
fn is_enum(tys: &TyTable, t: TyId) -> bool {
    match tys.try_get(t) {
        Some(Ty::Adt(a, _)) => tys
            .adts()
            .get(a.index())
            .is_some_and(|d| matches!(d.kind, AdtKind::Enum(_))),
        _ => false,
    }
}

/// The value of rvalue `rv` of body `body` in state `st`.
///
/// # Errors
///
/// The errors of α.
pub fn rvalue(cx: &mut Cx<'_>, body: BodyId, st: &State, rv: &Rvalue) -> Result<Tree, AlphaError> {
    match rv {
        Rvalue::Use(op) => operand(cx, body, st, op),
        Rvalue::Ref(q) => {
            let a = alpha(cx, body, st, q)?;
            Ok(Tree::leaf(AbsVal::refs(
                a.places.iter().chain(&a.handles).copied(),
            )))
        }
        Rvalue::Binary(..)
        | Rvalue::Unary(..)
        | Rvalue::Len(_)
        | Rvalue::Discriminant(_)
        | Rvalue::Concat(_)
        | Rvalue::Iter(weft_ir::IterSource::Range(..)) => Ok(Tree::leaf(AbsVal::plain())),
        Rvalue::Aggregate(kind, ops) => aggregate(cx, body, st, kind, ops),
        Rvalue::Iter(weft_ir::IterSource::Elems(q)) => iter_value(cx, body, st, q),
    }
}

/// The value of an iterator over the elements `q` (`docs/ir.md` 5.14): it
/// points into the places of the elements and into the handle places on
/// the way, as a borrow of `q`. It is `@ uniq` if the value of the local of
/// `q` is (RT18).
///
/// # Errors
///
/// The errors of α.
fn iter_value(cx: &mut Cx<'_>, body: BodyId, st: &State, q: &Place) -> Result<Tree, AlphaError> {
    let a = alpha(cx, body, st, q)?;
    let mut v = AbsVal::refs(a.places.iter().chain(&a.handles).copied());
    v.uniq = st.value(key(cx.p, body, q.local)?, &[]).flat().uniq;
    Ok(Tree::leaf(v))
}

/// The value that `IterNext` gives to `dest` from the iterator at `iter`.
///
/// An element of a type that can hold a reference is a reference into the
/// elements (the places of the iterator, and its `@ uniq` mode); a scalar
/// element is a copy (`docs/ir.md` 5.14).
///
/// # Errors
///
/// The errors of α.
pub fn next_value(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    iter: &Place,
    dest: &Place,
) -> Result<Tree, AlphaError> {
    let t = place_ty(cx, body, dest)?;
    if !ir_props(cx.tys, t).holds_refs {
        return Ok(Tree::leaf(AbsVal::plain()));
    }
    let it = place_value(cx, body, st, iter)?.flat();
    let mut v = AbsVal::refs(it.refs);
    v.uniq = it.uniq;
    Ok(Tree::leaf(v))
}

/// `IterNext(iter, dest)`: `dest` gets the next element ([`next_value`]).
/// The `done` edge gets the same state: the block there ends `dest`.
///
/// # Errors
///
/// The errors of α.
fn iter_next(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    iter: &Place,
    dest: &Place,
) -> Result<(), AlphaError> {
    let v = next_value(cx, body, st, iter, dest)?;
    bind_result(cx, body, st, &[], dest, v)
}

/// The value of an aggregate: the values of its operands as its parts.
fn aggregate(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    kind: &AggKind,
    ops: &[Operand],
) -> Result<Tree, AlphaError> {
    let mut parts = Vec::with_capacity(ops.len());
    for op in ops {
        parts.push(operand(cx, body, st, op)?);
    }
    let fields = |parts: Vec<Tree>| {
        let mut t = Tree::leaf(AbsVal::plain());
        for (i, x) in parts.into_iter().enumerate() {
            t.kids
                .insert(PathStep::Field(u32::try_from(i).unwrap_or(u32::MAX)), x);
        }
        t
    };
    match kind {
        AggKind::Tuple => Ok(fields(parts)),
        AggKind::Struct(t) => {
            let mut out = fields(parts);
            out.top.linear = declared_linear(cx.tys, *t);
            out.top.empty = !out.top.linear;
            Ok(out)
        }
        AggKind::Variant(t, v) => {
            let payload = fields(parts);
            let mut out = Tree::leaf(AbsVal::of_type(declared_linear(cx.tys, *t)));
            if is_enum(cx.tys, *t) {
                out.kids.insert(PathStep::Variant(v.0), payload);
            }
            Ok(out)
        }
        AggKind::Array | AggKind::Vec => {
            let mut v = AbsVal::plain();
            for x in &parts {
                v.join(&x.flat());
            }
            Ok(Tree::leaf(v))
        }
        AggKind::Closure(c) => closure_value(cx, body, *c, &parts),
    }
}

/// The value of a closure aggregate of closure `c` in body `body`, with the
/// values `parts` of its operands (`docs/ir.md` 5.22, 6.6): the closure
/// itself, the cell root of the variable of each `ByRef` capture (a move of
/// the variable does not end the cell, O3-11), and what each `ByMove`
/// capture holds. A `Kept` capture shares the cell of the variable: no
/// reference points into it (V13), so it adds no place; a call reads the
/// variable.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] for a closure that does not exist.
fn closure_value(
    cx: &mut Cx<'_>,
    body: BodyId,
    c: weft_ir::ClosureId,
    parts: &[Tree],
) -> Result<Tree, AlphaError> {
    let p = cx.p;
    let decl = p
        .closures
        .get(c.index())
        .ok_or_else(|| AlphaError::BadPlace(format!("no closure c{}", c.0)))?;
    let mut v = AbsVal::plain();
    v.fns.insert(FnVal::Closure(c));
    for (cap, part) in decl.captures.iter().zip(parts) {
        match cap.mode {
            weft_ir::CaptureMode::ByRef => {
                let owner = if cap.source.proj.is_empty() {
                    let k = key(p, body, cap.source.local)?;
                    let env = p
                        .bodies
                        .get(k.0.index())
                        .and_then(|b| b.locals.get(k.1.index()))
                        .is_some_and(|d| d.kind == weft_ir::LocalKind::Env);
                    (!env).then_some(k)
                } else {
                    None
                };
                match owner {
                    Some(k) => {
                        v.refs.insert(cx.roots.cell(p, cx.tys, cx.facts, k)?);
                    }
                    // A capture of a capture of the maker: the place that
                    // the reference of the maker points into.
                    None => v.refs.extend(part.flat().refs),
                }
            }
            weft_ir::CaptureMode::ByMove => {
                let f = part.flat();
                v.refs.extend(f.refs);
                // A function value that the closure owns: the closure runs
                // it through its value (stage F12), so the value of the
                // closure can be it too (a call of the closure applies it).
                v.fns.extend(f.fns);
                v.caps.extend(f.caps);
                v.tasks.extend(f.tasks);
                v.linear |= f.linear;
            }
            // A `Kept` capture shares the cell of its variable: no
            // reference points into the cell, but the closure can read the
            // references in the value (stage F12: a closure that leaves its
            // maker, or a closure that another closure gives back, holds
            // them).
            weft_ir::CaptureMode::Kept => v.refs.extend(part.flat().refs),
            weft_ir::CaptureMode::Cap | weft_ir::CaptureMode::Kont => {}
        }
    }
    v.empty = !v.linear;
    Ok(Tree::leaf(v))
}

/// The whole locals that rvalue `rv` moves into its value, with the steps
/// of their place in the value: `move t` as the value, or as a part of a
/// tuple, a struct or a variant.
pub fn moved_wholes(rv: &Rvalue) -> Vec<(Vec<PathStep>, LocalId)> {
    let whole = |op: &Operand| match op {
        Operand::Move(q) if q.proj.is_empty() => Some(q.local),
        _ => None,
    };
    let field = |i: usize| PathStep::Field(u32::try_from(i).unwrap_or(u32::MAX));
    match rv {
        Rvalue::Use(op) => whole(op).map(|l| (Vec::new(), l)).into_iter().collect(),
        Rvalue::Aggregate(AggKind::Tuple | AggKind::Struct(_), ops) => ops
            .iter()
            .enumerate()
            .filter_map(|(i, op)| whole(op).map(|l| (vec![field(i)], l)))
            .collect(),
        Rvalue::Aggregate(AggKind::Variant(_, v), ops) => ops
            .iter()
            .enumerate()
            .filter_map(|(i, op)| whole(op).map(|l| (vec![PathStep::Variant(v.0), field(i)], l)))
            .collect(),
        _ => Vec::new(),
    }
}

/// The operands of rvalue `rv`.
pub fn rvalue_operands(rv: &Rvalue) -> Vec<&Operand> {
    match rv {
        Rvalue::Use(o) | Rvalue::Unary(_, _, o) => vec![o],
        Rvalue::Binary(_, _, a, b) | Rvalue::Iter(weft_ir::IterSource::Range(a, b)) => vec![a, b],
        Rvalue::Aggregate(_, os) | Rvalue::Concat(os) => os.iter().collect(),
        Rvalue::Ref(_)
        | Rvalue::Len(_)
        | Rvalue::Discriminant(_)
        | Rvalue::Iter(weft_ir::IterSource::Elems(_)) => Vec::new(),
    }
}

/// After the operands `ops` of a node: each `move` of a move path leaves
/// no value there.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if a local does not exist.
pub fn moves<'o>(
    p: &Program,
    body: BodyId,
    st: &mut State,
    ops: impl IntoIterator<Item = &'o Operand>,
) -> Result<(), AlphaError> {
    for op in ops {
        if let Operand::Move(q) = op {
            if let Some((k, path)) = move_path(p, body, q)? {
                st.clear(k, &path);
            }
        }
    }
    Ok(())
}

/// The transfer of a statement.
///
/// # Errors
///
/// The errors of α, and [`AlphaError::Later`] for a construct of a later
/// stage.
pub fn stmt(cx: &mut Cx<'_>, body: BodyId, st: &mut State, s: &StmtKind) -> Result<(), AlphaError> {
    match s {
        StmtKind::Live(l) => live(cx.p, body, st, *l),
        StmtKind::Dead(l) => dead(cx.p, body, st, *l),
        StmtKind::Assign(p, rv) => assign(cx, body, st, p, rv),
        StmtKind::Drop(p) => drop_place(cx.p, body, st, p),
        StmtKind::Consume(p) => consume(cx.p, body, st, p),
        StmtKind::Uninit(p) => uninit(cx.p, body, st, p),
        StmtKind::Bounds(p, i) => bounds(cx.p, body, st, p, i),
        StmtKind::Mention(p) => mention(cx.p, body, st, p),
        StmtKind::Print(ops) => print(cx.p, body, st, ops),
        StmtKind::UnwindValue(p, _) => unwind_value(cx.p, body, st, p),
        StmtKind::UnwindKont(l) => unwind_kont(cx.p, body, st, *l),
    }
}

/// `Live(l)`: a new variable with no value.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if the local does not exist.
pub fn live(p: &Program, body: BodyId, st: &mut State, l: LocalId) -> Result<(), AlphaError> {
    st.clear(key(p, body, l)?, &[]);
    Ok(())
}

/// `Dead(l)`: the local has no value after its end, but a variable that a
/// closure keeps (`Kept`) keeps its last value.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if the local does not exist.
pub fn dead(p: &Program, body: BodyId, st: &mut State, l: LocalId) -> Result<(), AlphaError> {
    // A closure that keeps the variable (`Kept`) reads its last value when
    // it runs after the end of the variable (a closure that a loop makes
    // from a local of the loop body).
    let kept = p.closures.iter().any(|c| {
        c.maker == body
            && c.captures.iter().any(|cap| {
                cap.mode == weft_ir::CaptureMode::Kept
                    && cap.source.proj.is_empty()
                    && cap.source.local == l
            })
    });
    if !kept {
        st.clear(key(p, body, l)?, &[]);
    }
    Ok(())
}

/// `Assign(place, rv)`: the value of `rv`, the moves, then the new value.
///
/// The moves of the operands come after their values. A move path gets the
/// value (a strong update). A place through a pointer or an element joins
/// the value into the move path of each local that it can be (a weak
/// update).
///
/// # Errors
///
/// The errors of α and of [`rvalue`].
pub fn assign(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    place: &Place,
    rv: &Rvalue,
) -> Result<(), AlphaError> {
    let v = rvalue(cx, body, st, rv)?;
    let dest = match move_path(cx.p, body, place)? {
        Some(d) => Some(d),
        None => kept_whole(cx, body, st, place)?.map(|k| (k, Vec::new())),
    };
    let a = if dest.is_some() {
        None
    } else {
        Some(alpha(cx, body, st, place)?)
    };
    // The holes of a whole local that moves go with its value.
    let mut carried: Vec<Vec<PathStep>> = Vec::new();
    for (steps, l) in moved_wholes(rv) {
        let k = key(cx.p, body, l)?;
        for h in st.holes_below(k, &[]) {
            carried.push(steps.iter().copied().chain(h).collect());
        }
    }
    moves(cx.p, body, st, rvalue_operands(rv))?;
    if let Some((k, path)) = dest {
        st.write(k, &path, v);
        for h in carried {
            let at: Vec<PathStep> = path.iter().copied().chain(h).collect();
            st.add_hole(k, &at);
        }
        return Ok(());
    }
    let flat = Tree::leaf(v.flat());
    let targets: BTreeSet<(Key, Vec<PathStep>)> = a
        .iter()
        .flat_map(|a| a.places.iter())
        .filter_map(|&q| cx.roots.path_of(cx.facts, q))
        .collect();
    for (k, path) in targets {
        st.add(k, &path, &flat);
    }
    if let Some(a) = &a {
        let refs: Vec<PlaceId> = flat.top.refs.iter().copied().collect();
        store_heap(cx.facts, cx.roots, st, &a.places, &refs, &flat.top.fns);
    }
    Ok(())
}

/// `Drop(p)`: the old value behind a pointer goes away. The state does not
/// change: the `Assign` after it gives the new value.
///
/// # Errors
///
/// None at stage F3.
pub const fn drop_place(
    _p: &Program,
    _body: BodyId,
    _st: &mut State,
    _place: &Place,
) -> Result<(), AlphaError> {
    Ok(())
}

/// `Consume(p)`: the linear value at `p` is finished. The move path has no
/// value after it.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if the local does not exist.
pub fn consume(p: &Program, body: BodyId, st: &mut State, place: &Place) -> Result<(), AlphaError> {
    if let Some((k, path)) = move_path(p, body, place)? {
        st.clear(k, &path);
    }
    Ok(())
}

/// `Uninit(p)`: the move path has no value.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if the local does not exist.
pub fn uninit(p: &Program, body: BodyId, st: &mut State, place: &Place) -> Result<(), AlphaError> {
    if let Some((k, path)) = move_path(p, body, place)? {
        st.clear(k, &path);
    }
    Ok(())
}

/// `Bounds(q, i)`: a read. Only a `move` of the index changes the state.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if a local does not exist.
pub fn bounds(
    p: &Program,
    body: BodyId,
    st: &mut State,
    _place: &Place,
    i: &Operand,
) -> Result<(), AlphaError> {
    moves(p, body, st, [i])
}

/// `Mention(q)`: no change.
///
/// # Errors
///
/// None.
pub const fn mention(
    _p: &Program,
    _body: BodyId,
    _st: &mut State,
    _place: &Place,
) -> Result<(), AlphaError> {
    Ok(())
}

/// `Print(ops)`: a read of each operand. A `move` operand moves.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if a local does not exist.
pub fn print(p: &Program, body: BodyId, st: &mut State, ops: &[Operand]) -> Result<(), AlphaError> {
    moves(p, body, st, ops)
}

/// `UnwindValue(p, a)`: the unwinder finishes the value; the `Dead` after it
/// ends the local.
///
/// # Errors
///
/// None.
pub const fn unwind_value(
    _p: &Program,
    _body: BodyId,
    _st: &mut State,
    _place: &Place,
) -> Result<(), AlphaError> {
    Ok(())
}

/// `UnwindKont(k)`: no change in this component.
///
/// # Errors
///
/// None.
pub const fn unwind_kont(
    _p: &Program,
    _body: BodyId,
    _st: &mut State,
    _k: LocalId,
) -> Result<(), AlphaError> {
    Ok(())
}

/// The transfer of terminator `t` of block `block`, on its normal edges.
///
/// # Errors
///
/// Returns [`AlphaError::Later`] for a terminator that runs another body or
/// a task with no summary yet (stages F6 and later).
pub fn term(
    cx: &mut Cx<'_>,
    body: BodyId,
    block: weft_ir::BlockId,
    st: &mut State,
    t: &TermKind,
) -> Result<(), AlphaError> {
    match t {
        TermKind::Goto(_) => goto(st),
        TermKind::Switch { on, .. } => switch(cx.p, body, st, on),
        TermKind::Return => ret(st),
        TermKind::Unreachable | TermKind::UnwindExit => Ok(()),
        TermKind::Assert { cond, .. } => moves(cx.p, body, st, [cond]),
        TermKind::Call {
            callee: weft_ir::Callee::Fn(f, targs),
            args,
            dest,
            ..
        } => {
            let before = super::clause::runs_clauses(cx, body, t).then(|| st.clone());
            call(cx, body, block, st, *f, targs, args, dest)?;
            super::clause::call_clauses(cx, (body, block), before.as_ref(), st, t)
        }
        TermKind::Call {
            callee: weft_ir::Callee::Value(f),
            args,
            dest,
            ..
        } => {
            call_value(cx, body, block, st, f, args, dest)?;
            super::clause::call_clauses(cx, (body, block), None, st, t)
        }
        TermKind::Perform {
            cap: weft_ir::CapOperand::Row(e),
            op,
            args,
            dest,
            ..
        } => perform_row(cx, body, st, *e, *op, args, dest),
        TermKind::Perform {
            cap: weft_ir::CapOperand::Local(cap),
            op,
            args,
            dest,
            ..
        } => super::clause::perform_local(cx, body, st, (cap, *op, args), dest),
        TermKind::Resume {
            kont, arg, dest, ..
        } => super::clause::resume(cx, body, st, (kont, arg, dest)),
        TermKind::IterNext { iter, dest, .. } => iter_next(cx, body, st, iter, dest),
        TermKind::Handle { handler, dest, .. } => {
            super::clause::handle(cx, body, st, *handler, dest)
        }
        TermKind::Scope { .. }
        | TermKind::ScopeWait { .. }
        | TermKind::Spawn { .. }
        | TermKind::Join { .. }
        | TermKind::Detach { .. }
        | TermKind::Fork { .. } => Err(AlphaError::Later("a task (stage F18)")),
    }
}

/// `Goto`: no change.
///
/// # Errors
///
/// None.
pub const fn goto(_st: &mut State) -> Result<(), AlphaError> {
    Ok(())
}

/// `Switch`: a read of its operand; a `move` operand moves.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if a local does not exist.
pub fn switch(p: &Program, body: BodyId, st: &mut State, on: &Operand) -> Result<(), AlphaError> {
    moves(p, body, st, [on])
}

/// `Return`: no change; the frame ends.
///
/// # Errors
///
/// None.
pub const fn ret(_st: &mut State) -> Result<(), AlphaError> {
    Ok(())
}

/// The id of the run node of the terminator of block `block` of body
/// `body`: the splits and the one-place instances of a call are its own.
pub const fn run_inst(body: BodyId, block: weft_ir::BlockId) -> u32 {
    body.0.saturating_mul(1 << 16).saturating_add(block.0)
}

/// What a `Call` of the function item `f` with the type arguments `targs`
/// gives: σ, the value of the result, the places that it changes, and the
/// values that go behind its reference arguments.
pub struct CallOut {
    /// σ of the run node.
    pub sigma: super::apply::Sigma,
    /// The summary of the callee.
    pub summary: super::summary::Summary,
    /// The value of the result.
    pub ret: Tree,
    /// The places that the call changes, with their callee root indexes.
    pub muts: Vec<(PlaceId, u32)>,
    /// The values that go behind the reference arguments that the call
    /// changes.
    pub stores: Vec<(PlaceId, Vec<PlaceId>)>,
    /// The summaries of the function values that the callee runs (part
    /// `runs`, stage F12).
    pub apps: Vec<Applied>,
    /// The function values that the callee puts into places of the caller
    /// (part `put_fns`, stage F13). Their references are in `stores`.
    pub put_fns: Vec<(PlaceId, BTreeSet<FnVal>)>,
}

/// The run node of a `Call` of function item `f` of block `block`, in state
/// `st` before it (`docs/ir.md` 6.7).
///
/// # Errors
///
/// Returns [`AlphaError::Later`] if `f` has no summary yet, and the errors of
/// σ.
#[allow(clippy::too_many_arguments)]
pub fn call_out(
    cx: &mut Cx<'_>,
    body: BodyId,
    block: weft_ir::BlockId,
    st: &State,
    f: weft_ir::FnId,
    targs: &[TyId],
    args: &[Operand],
    dest: &Place,
) -> Result<CallOut, AlphaError> {
    let sums = cx.sums;
    let p = cx.p;
    let summary = sums.get(f).map_err(AlphaError::Later)?.clone();
    let decl = p
        .fns
        .get(f.index())
        .ok_or_else(|| AlphaError::BadPlace(format!("no function f{}", f.0)))?;
    let inst = run_inst(body, block);
    let mut sigma = super::apply::sigma(cx, body, st, decl, targs, args, inst)?;
    sigma.cyclic = cx.cycles.has(body, block);
    // A clause that the call runs can get a reference into a local of the
    // callee (plan stage F15, `clause::given`).
    let gives = summary.gives_frame
        && p.body(body)
            .and_then(|b| b.blocks.get(block.index()))
            .is_some_and(|blk| {
                super::clause::call_handlers(cx, body, &blk.term.kind)
                    .iter()
                    .any(|&h| super::clause::gives_refs(p, cx.tys, h))
            });
    if summary.ret_in_frame() || gives {
        sigma.frame = Some(cx.roots.frame(cx.facts, inst, &decl.name));
    }
    sigma.local_ops = p
        .body(body)
        .and_then(|b| b.blocks.get(block.index()))
        .is_some_and(|blk| crate::factgen::frames::row_local(p, cx.tys, sums, &blk.term.kind));
    let ret_ty = place_ty(cx, body, dest)?;
    let ret = super::apply::ret_value(cx, &summary, &sigma, ret_ty)?;
    let muts = super::apply::muts(cx, &summary, &sigma)?;
    let mut stores = super::apply::stores(cx, &summary, &sigma, &muts)?;
    // The function values that the callee runs, and the function values of
    // the result (stage F12).
    let r = Run0 {
        body,
        block,
        inst,
        st,
    };
    // The values that the callee puts into places of the caller (stage F13).
    let (put_refs, put_fns) =
        put_values(cx, r, &summary, &sigma, Given::Args(args), &mut |_, _| {
            Ok((BTreeSet::from([FnVal::Unknown]), BTreeSet::new()))
        })?;
    stores.extend(put_refs);
    let mut apps = Apps::default();
    let given = Given::Args(args);
    apply_runs(
        cx,
        r,
        &summary.runs,
        &sigma,
        &mut |cx, run| param_fns(cx, r, run, given),
        0,
        &mut apps,
    )?;
    let mut fs = ret_fns(cx, r, &summary, given, &mut |_, _| {
        Ok((BTreeSet::from([FnVal::Unknown]), BTreeSet::new()))
    })?;
    // A result of a type parameter can be a function value of an argument
    // (`Box.new(f)`, `v.pop()`).
    if crate::props::ir_has_fns(cx.tys, ret_ty) && cx.tys.mentions_param(decl.ret) {
        for a in args {
            fs.0.extend(reach_fns(cx, body, st, a)?);
            fs.1.extend(reach_refs(cx, body, st, a)?);
        }
    }
    let ret = with_fns(cx, ret, ret_ty, fs);
    Ok(CallOut {
        sigma,
        summary,
        ret,
        muts,
        stores,
        apps: apps.out,
        put_fns,
    })
}

/// The changes of the states of the summaries `apps` that a run node
/// applies: the values that go into places of the caller, a linear value
/// in a changed place, the new value of each captured variable that a
/// closure rebinds.
///
/// `fns`: an argument of the run node can hold a linear value. A function
/// item puts only the values of its arguments into the places of the caller
/// (a function value behind a reference stays with the old pipeline), so
/// the summary of an item gives a linear closure to a place only with
/// `fns`. A closure and code of a caller can make one.
fn apply_apps(cx: &Cx<'_>, st: &mut State, apps: &[Applied], fns: bool) {
    for app in apps {
        let fns = fns || app.kind != super::apply::RunKind::Item;
        for (q, refs) in &app.stores {
            if let Some((k, path)) = cx.roots.path_of(cx.facts, *q) {
                st.add(k, &path, &Tree::leaf(AbsVal::refs(refs.iter().copied())));
            } else {
                st.store_behind(*q, refs.iter().copied());
            }
        }
        apply_put_fns(cx, st, &app.put_fns);
        let changed: Vec<PlaceId> = app.muts.iter().map(|(q, _)| *q).collect();
        for (k, path) in can_get_linear_with(cx, &changed, fns) {
            st.add(k, &path, &Tree::leaf(AbsVal::of_type(true)));
        }
        for (k, v) in &app.rebinds {
            st.write(*k, &[], v.clone());
        }
    }
}

/// A run node with the arguments `args` that changes the places `changed`
/// can put a function value of an argument there (`v.push(f)`): each move
/// path of such a place whose local can hold a function value gets the
/// function values of the arguments (a weak update).
///
/// A place that no local owns gets the values in its heap slot (stage F13).
///
/// # Errors
///
/// The errors of α.
fn store_fns(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    args: &[Operand],
    changed: &[PlaceId],
) -> Result<(), AlphaError> {
    let mut fns = BTreeSet::new();
    // The places that the environments of the function values point into:
    // the stored value holds them (hole H2 of the review of the ABC preview:
    // `fs.push(mk())`).
    let mut refs = BTreeSet::new();
    // An argument that points to a place that can hold a function value:
    // the callee can store one behind it.
    let mut behind = false;
    for a in args {
        if let Operand::Copy(q) | Operand::Move(q) = a {
            let t = place_ty(cx, body, q)?;
            if crate::props::ir_has_fns(cx.tys, t) {
                if is_ref_ty(cx.tys, t) || ir_props(cx.tys, t).holds_refs {
                    behind = true;
                }
                if !is_ref_ty(cx.tys, t) {
                    let v = operand(cx, body, st, a)?.flat();
                    fns.extend(v.fns);
                    refs.extend(v.refs);
                }
            }
        }
        if let Operand::Const(Const::Fn(f, t)) = a {
            fns.insert(FnVal::Item(*f, t.clone()));
        }
    }
    if fns.is_empty() {
        return Ok(());
    }
    for &q in changed {
        match cx.roots.path_of(cx.facts, q) {
            Some((k, path)) => {
                let holds =
                    cx.p.bodies
                        .get(k.0.index())
                        .and_then(|b| b.locals.get(k.1.index()))
                        .is_some_and(|d| crate::props::ir_has_fns(cx.tys, d.ty));
                if holds {
                    let mut v = AbsVal::none();
                    v.fns.clone_from(&fns);
                    v.refs.clone_from(&refs);
                    st.add(k, &path, &Tree::leaf(v));
                }
            }
            // A place that no local owns (behind a reference, in an `rc`
            // object): its heap slot gets the values (stage F13).
            None if behind => {
                st.store_fns_behind(q, fns.iter().cloned());
                st.store_behind(q, refs.iter().copied());
            }
            None => {}
        }
    }
    Ok(())
}

/// True if `t` is a reference type.
fn is_ref_ty(tys: &TyTable, t: TyId) -> bool {
    matches!(tys.try_get(t), Some(Ty::Ref(_)))
}

/// `Call` of a function item: the summary of the callee. The values that go
/// behind its reference arguments join into the move paths that they name
/// (a weak update); the moved arguments leave no value; the result binds to
/// `dest`.
///
/// # Errors
///
/// The errors of [`call_out`] and of α.
#[allow(clippy::too_many_arguments)]
fn call(
    cx: &mut Cx<'_>,
    body: BodyId,
    block: weft_ir::BlockId,
    st: &mut State,
    f: weft_ir::FnId,
    targs: &[TyId],
    args: &[Operand],
    dest: &Place,
) -> Result<(), AlphaError> {
    let fns = args_linear(cx, body, st, args)?;
    let out = call_out(cx, body, block, st, f, targs, args, dest)?;
    for (q, refs) in &out.stores {
        if let Some((k, path)) = cx.roots.path_of(cx.facts, *q) {
            st.add(k, &path, &Tree::leaf(AbsVal::refs(refs.iter().copied())));
        } else {
            st.store_behind(*q, refs.iter().copied());
        }
    }
    apply_put_fns(cx, st, &out.put_fns);
    let mut changed: Vec<PlaceId> = out.muts.iter().map(|(q, _)| *q).collect();
    for (k, path) in can_get_linear_with(cx, &changed, fns) {
        st.add(k, &path, &Tree::leaf(AbsVal::of_type(true)));
    }
    apply_apps(cx, st, &out.apps, fns);
    changed.extend(out.apps.iter().flat_map(|a| a.muts.iter().map(|(q, _)| *q)));
    store_fns(cx, body, st, args, &changed)?;
    bind_result(cx, body, st, args, dest, out.ret)
}

/// The most levels of values that a run node applies through the runs of
/// the values that it runs (`f` runs `g`, which runs `h`). Each value applies
/// one time at a run node, so a chain costs one application for each
/// closure (Q3-2); a deeper chain stays with the old pipeline.
const RUN_DEPTH: usize = 64;

/// How a run node gives the arguments to a function value that it runs.
#[derive(Clone, Copy, Debug)]
pub enum Given<'o> {
    /// The operands of the call.
    Args(&'o [Operand]),
    /// A callee runs the value with arguments that the run node does not
    /// know: each parameter gets these places (the places that the callee
    /// gives to the run, part `runs`). The flag says if code of a caller
    /// there can resume more than once (the row of its function type).
    Opaque(&'o [PlaceId], bool),
}

impl Given<'_> {
    /// The places of a run, `None` for the arguments of a call.
    fn places(&self) -> Option<Vec<PlaceId>> {
        match self {
            Given::Args(_) => None,
            Given::Opaque(ps, _) => Some(ps.to_vec()),
        }
    }
}

/// A run of a function value of the interface (a parameter or a capture):
/// the summary of the body gets it (part `runs`).
#[derive(Clone, Debug)]
pub struct RunOf {
    /// The parameter, or the capture.
    pub param: u32,
    /// True for a capture of a closure.
    pub capture: bool,
    /// True for a run of a result of a run of the parameter
    /// (`FnVal::ParamResult`).
    pub result: bool,
    /// The places that the run node gives to the run.
    pub places: Vec<PlaceId>,
    /// Code of a caller there can resume more than once (the row of the
    /// function type of the value).
    pub multi: bool,
    /// The run can be on another thread (code of a caller, ADR 0006).
    pub task: bool,
    /// The block of the run node: a path to a `Return` that does not pass a
    /// run node can return with no run (`Run::maybe`).
    pub block: weft_ir::BlockId,
    /// The run node can end with no run: a callee runs the value on some
    /// paths only (its run is `maybe`), or code of a caller gets it. Its
    /// block does not count as a block that runs the value (hole H5b of the
    /// second review of the ABC preview).
    pub maybe: bool,
}

/// One summary that a run node of a function value applies (`docs/ir.md`
/// 6.7): of a value that the callee can be, or of a value that such a
/// value runs (part `runs`).
#[derive(Clone, Debug)]
pub struct Applied {
    /// The kind of the run node.
    pub kind: super::apply::RunKind,
    /// The name of the callee, for the diagnostics.
    pub name: String,
    /// σ of the run node.
    pub sigma: super::apply::Sigma,
    /// The summary.
    pub summary: super::summary::Summary,
    /// The value of the result, for a value of the callee itself.
    pub ret: Option<Tree>,
    /// The places that the run changes, with their callee root indexes.
    pub muts: Vec<(PlaceId, u32)>,
    /// The references that go into places of the caller (a weak update):
    /// the part `stores` of an item, and the part `puts` of a closure.
    pub stores: Vec<(PlaceId, Vec<PlaceId>)>,
    /// The captured variables that the run gives a whole new value (part
    /// `rebinds`): the key of the variable and its new value.
    pub rebinds: Vec<(Key, Tree)>,
    /// The variables that the run uses (part `uses`): the index of each
    /// `Kept` and `ByRef` capture and its source, in the body of its maker.
    pub uses: Vec<(u32, BodyId, Place)>,
    /// The places of `once` values that the run moves: the source of a
    /// capture that holds a `once` closure and that the run calls.
    pub once: Vec<(BodyId, Place)>,
    /// The values of the arguments of a run (part `runs`) that hold a `once`
    /// closure: the run moves them, and a run again uses them (W0502).
    pub once_args: Vec<(BodyId, Operand)>,
    /// The run happens again at the `Ret` node (a value that runs another
    /// value `Many` times, OR3).
    pub again: bool,
    /// With `again`: the run happens one time, at the `Main` node or at the
    /// `Ret` node (a body that runs two values can run them in each order).
    /// A `once` value runs once then (no W0502: `fn both(f, g) { f(); g() }`
    /// with one `once` closure, stage F12-fix3 finding (a)).
    pub order: bool,
    /// The run happens at the `Ret` node, after the parts of the summary of
    /// the run node (a value that a callee runs: the callee can change a
    /// place before it runs the value, which then reads a reference into
    /// it).
    pub late: bool,
    /// A run of a function value of the interface: code of a caller here,
    /// and an entry of the part `runs` of the summary of the body.
    pub run: Option<RunOf>,
    /// The summary is code of a caller (map N2): the value that the caller
    /// gives applies its own aborts where the caller runs it.
    pub code: bool,
    /// The places that code of a caller can change through the environment
    /// of the function value (the wildcard places of the references of the
    /// value): `lends_mut` and `reads_at` at the node.
    pub lends: Vec<PlaceId>,
    /// The function values that the run puts into places of the caller
    /// (part `put_fns`, stage F13). Their references are in `stores`.
    pub put_fns: Vec<(PlaceId, BTreeSet<FnVal>)>,
    /// The places that code of a caller can read and that the body can
    /// name: the places behind the parameters of the body and the `rc`
    /// groups that their types reach (`reads_at` at the node; the summary
    /// oracle found them, `docs/ir.md` 8.5).
    pub reads: Vec<PlaceId>,
}

/// What a `Call` of a function value gives: the summaries that it applies
/// and the value of the result.
#[derive(Clone, Debug)]
pub struct ValueOut {
    /// The summaries, the values of the callee first.
    pub apps: Vec<Applied>,
    /// The value of the result: the join of the results of the values of the
    /// callee.
    pub ret: Tree,
    /// The callee can be a `once` closure: the call moves it (W0502 at a
    /// second call, also through a copy of the local, B12-fn-once).
    pub once: bool,
}

/// True if body `body` is a closure body whose facts are in the terms of
/// its interface: the summary of the closure (`super::summarize::closure`).
pub fn in_interface(cx: &Cx<'_>, body: BodyId) -> bool {
    cx.p.closure_of(body).is_some() && !cx.roots.is_instantiated(body)
}

/// The function values that a value at fact place `at` can be (`docs/ir.md` 6.6).
///
/// They are the values of the move path of a local that holds the place, a value of a parameter
/// (`FnVal::Param`) or of a capture (`FnVal::Capture`) for a place of the interface, the
/// values of the variable of the cell of a `ByRef` capture, and [`FnVal::Unknown`] for
/// another place (a place of a caller, of an `rc` object, of a callee frame). A place
/// that no local owns also gives the values of its heap slot (stage F13).
pub fn fns_at(cx: &Cx<'_>, st: &State, at: PlaceId) -> BTreeSet<FnVal> {
    let mut out = fns_of_role(cx, st, at);
    // A place that no local owns: the values that the body stored in its
    // heap slot too (stage F13).
    if !st.behind_fns().is_empty() && cx.roots.path_of(cx.facts, at).is_none() {
        out.extend(stored_fns_at(cx.facts, st, at));
    }
    out
}

/// The function values at fact place `at` by the role of its root
/// ([`fns_at`], with no heap slot).
fn fns_of_role(cx: &Cx<'_>, st: &State, at: PlaceId) -> BTreeSet<FnVal> {
    let mut out = BTreeSet::new();
    let Some(root) = cx.facts.places.get(at.index()).map(|i| i.root) else {
        out.insert(FnVal::Unknown);
        return out;
    };
    match cx.roots.role(root) {
        Some(Role::Local(_)) => match cx.roots.path_of(cx.facts, at) {
            Some((k, path)) => out.extend(st.value(k, &path).flat().fns),
            None => {
                out.insert(FnVal::Unknown);
            }
        },
        // A place behind a parameter whose type cannot hold a function
        // value gives none (`world: &World` with no function field). In a
        // closure body, parameter 0 is the environment.
        Some(Role::Param(b, i) | Role::Held(b, i)) => {
            let closure = cx.p.closure_of(b).is_some();
            let ty =
                cx.p.bodies
                    .get(b.index())
                    .and_then(|body| body.params.get(i as usize))
                    .and_then(|&l| cx.p.bodies.get(b.index())?.local(l))
                    .map(|d| d.ty);
            let may_hold =
                ty.is_none_or(|t| crate::props::ir_has_fns(cx.tys, t) || cx.tys.mentions_param(t));
            if may_hold && !(closure && i == 0) {
                out.insert(FnVal::Param(if closure { i - 1 } else { i }));
            }
        }
        Some(Role::Capture(_, k) | Role::CaptureHeld(_, k) | Role::CaptureDeep(_, k)) => {
            out.insert(FnVal::Capture(k));
        }
        Some(Role::Cell(k)) => out.extend(st.value(k, &[]).flat().fns),
        _ => {
            out.insert(FnVal::Unknown);
        }
    }
    out
}

/// The inner types `T` of the `Rc<T>` handles that a value of type `t` can
/// hold or reach: through its parts, its references and the type arguments
/// of its containers (stage F13). A function value in an `rc` object that a
/// callee reads is a value that a handle of an argument reaches.
pub(crate) fn rc_inners(tys: &mut TyTable, t: TyId) -> Vec<TyId> {
    use weft_ir::ty::AdtKind;
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();
    let mut work = vec![t];
    while let Some(x) = work.pop() {
        if !seen.insert(x) || seen.len() > 256 {
            continue;
        }
        if let Some((weft_ir::ty::Lang::Rc, args)) = tys.lang(x) {
            out.extend(args.first().copied());
        }
        match tys.try_get(x).cloned() {
            Some(Ty::Tuple(ts)) => work.extend(ts),
            Some(Ty::Array(y, _) | Ty::Slice(y) | Ty::Ref(y)) => work.push(y),
            Some(Ty::Adt(a, args)) => {
                let kind = tys.adts().get(a.index()).map(|d| d.kind.clone());
                match kind {
                    Some(AdtKind::Struct(fs)) => {
                        for f in fs {
                            work.push(crate::irbuild::subst(tys, f.ty, &args));
                        }
                    }
                    Some(AdtKind::Enum(vs)) => {
                        for v in vs {
                            for f in v.fields {
                                work.push(crate::irbuild::subst(tys, f, &args));
                            }
                        }
                    }
                    Some(AdtKind::Extern { .. }) | None => work.extend(args),
                }
            }
            _ => {}
        }
    }
    out.sort();
    out.dedup();
    out
}

/// The function values, and the places of their environments, that the
/// body stored in the `rc` objects that a value of type `t` can reach
/// ([`rc_inners`], the heap slots of the group roots, stage F13).
fn rc_stored(cx: &mut Cx<'_>, st: &State, t: TyId) -> (BTreeSet<FnVal>, BTreeSet<PlaceId>) {
    let mut fns = BTreeSet::new();
    let mut refs = BTreeSet::new();
    if st.behind_fns().is_empty() {
        return (fns, refs);
    }
    for inner in rc_inners(cx.tys, t) {
        let g = cx.roots.group(cx.tys, cx.facts, inner);
        let slot = stored_fns_at(cx.facts, st, g);
        if !slot.is_empty() {
            refs.extend(stored_at(cx.facts, st, g));
        }
        fns.extend(slot);
    }
    (fns, refs)
}

/// The function values that a callee can run through the value of operand
/// `op` of body `body` in state `st`: the values that it is, and the values
/// behind its references (two levels).
///
/// # Errors
///
/// The errors of α.
pub fn reach_fns(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    op: &Operand,
) -> Result<BTreeSet<FnVal>, AlphaError> {
    let ty = match op {
        Operand::Copy(q) | Operand::Move(q) => Some(place_ty(cx, body, q)?),
        Operand::Const(_) => None,
    };
    let v = operand(cx, body, st, op)?.flat();
    let mut out = v.fns;
    let Some(t) = ty.filter(|&t| crate::props::ir_has_fns(cx.tys, t)) else {
        return Ok(out);
    };
    // The values that the body stored in an `rc` object that a handle of the
    // value reaches (stage F13).
    out.extend(rc_stored(cx, st, t).0);
    let mut level: Vec<PlaceId> = v.refs.into_iter().collect();
    for _ in 0..2 {
        let mut next = Vec::new();
        for &r in &level {
            out.extend(fns_at(cx, st, r));
            if let Ok(h) = held_at(cx.p, st, cx.facts, cx.roots, r, None) {
                next.extend(h);
            }
        }
        next.sort();
        next.dedup();
        level = next;
    }
    Ok(out)
}

/// The places that a run node gives to code of a caller with the arguments
/// `args`: the places that the references of each argument point into (the
/// places of a reference argument). The run gets what the references there
/// point into too (`super::apply::opaque_sigma`).
///
/// # Errors
///
/// The errors of α.
fn given_places(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    args: &[Operand],
) -> Result<Vec<PlaceId>, AlphaError> {
    let mut out = Vec::new();
    for a in args {
        let v = operand(cx, body, st, a)?.flat();
        out.extend(v.refs.iter().copied());
    }
    out.sort();
    out.dedup();
    Ok(out)
}

/// The applications of one run node: the summaries in order, and the value
/// that each one is for. A value applies one time as a value of the callee
/// (with the arguments of the call) and one time for each set of places
/// that a run gives it: a value can be both, and two runs can give it other
/// places (follow-up F13.2: a closure that a callee made holds the values
/// that it runs in its own value).
#[derive(Default)]
struct Apps {
    /// The summaries.
    out: Vec<Applied>,
    /// The last summary of each value that the node applies.
    seen: std::collections::HashMap<FnVal, usize>,
    /// Each value that the node applies, with `None` for a value of the
    /// callee (`Given::Args`) and the places of a run (`Given::Opaque`).
    modes: BTreeSet<(FnVal, Option<Vec<PlaceId>>)>,
    /// Each value that the node asks to apply, in order, also a value that
    /// it applied before (a value applies one time, so `seen` does not show
    /// a second run of it). [`apply_runs`] finds a value that two runs reach
    /// with it (class H-ORD of the final check of group C: `both(h, || h())`).
    reached: Vec<FnVal>,
}

/// The run node of a `Call` of the function value `callee` of block `block`
/// of body `body`, in state `st` before it (`docs/ir.md` 6.7).
///
/// The value can be function items, closures of the component, closures
/// that a callee made, and function values of the interface or that the
/// analysis does not know (code of a caller, map N2). Each one applies its
/// summary, and the values that it runs apply theirs (part `runs`).
///
/// # Errors
///
/// Returns [`AlphaError::Later`] for a construct of a later stage, and the
/// errors of σ.
#[allow(clippy::too_many_arguments)]
pub fn value_out(
    cx: &mut Cx<'_>,
    body: BodyId,
    block: weft_ir::BlockId,
    st: &State,
    callee: &Operand,
    args: &[Operand],
    dest: &Place,
) -> Result<ValueOut, AlphaError> {
    let ret_ty = place_ty(cx, body, dest)?;
    let mut fns = operand(cx, body, st, callee)?.flat().fns;
    // A local that holds no value here (it moved): the call stops with a
    // fault at run time, and the use of the local is W0302 or W0502. No
    // closure runs.
    if let Operand::Copy(q) | Operand::Move(q) = callee {
        if fns.is_empty() && q.proj.is_empty() && !st.may_hold(key(cx.p, body, q.local)?) {
            return Ok(ValueOut {
                apps: Vec::new(),
                ret: Tree::leaf(AbsVal::of_type(ir_props(cx.tys, ret_ty).linear)),
                once: false,
            });
        }
    }
    // A value that the analysis does not follow is code of a caller.
    if fns.is_empty() {
        fns.insert(FnVal::Unknown);
    }
    let inst = run_inst(body, block);
    let mut apps = Apps::default();
    let mut ret: Option<Tree> = None;
    for fv in &fns {
        let start = apps.out.len();
        apply_value(
            cx,
            Run0 {
                body,
                block,
                inst,
                st,
            },
            fv,
            (callee, body),
            Given::Args(args),
            Some(ret_ty),
            0,
            &mut apps,
        )?;
        if let Some(r) = apps.out.get(start).and_then(|a| a.ret.clone()) {
            ret = Some(match ret {
                Some(t) => Tree::leaf(t.flat().joined(&r.flat())),
                None => r,
            });
        }
    }
    let once = fns.iter().any(|fv| once_value(cx.p, fv));
    Ok(ValueOut {
        apps: apps.out,
        ret: ret.unwrap_or_else(|| Tree::leaf(AbsVal::plain())),
        once,
    })
}

/// True if a call of the function value `fv` moves it: a closure that is
/// `once` (it moves a capture that is not plain data, or it holds a `once`
/// value).
pub fn once_value(p: &Program, fv: &FnVal) -> bool {
    match fv {
        FnVal::Closure(c) | FnVal::Made(c) => p.closures.get(c.index()).is_some_and(|d| d.once),
        FnVal::Item(..)
        | FnVal::Param(_)
        | FnVal::ParamResult(_)
        | FnVal::Capture(_)
        | FnVal::Unknown => false,
    }
}

/// The run node: its body, block, id, and the state before it.
#[derive(Clone, Copy)]
struct Run0<'s> {
    /// The body of the node.
    body: BodyId,
    /// The block of the node.
    block: weft_ir::BlockId,
    /// The id of the node.
    inst: u32,
    /// The state before the node.
    st: &'s State,
}

/// The parameter types, the result type and the row of the function type of
/// operand `callee` of body `body`.
fn fn_type(
    cx: &mut Cx<'_>,
    body: BodyId,
    callee: &Operand,
) -> (Vec<TyId>, Option<TyId>, Option<Vec<weft_ir::EffectId>>) {
    let t = match callee {
        Operand::Copy(q) | Operand::Move(q) => place_ty(cx, body, q).ok(),
        Operand::Const(_) => None,
    };
    match t.and_then(|t| cx.tys.try_get(t)) {
        Some(Ty::Fn(f)) => (f.params.clone(), Some(f.ret), f.row.clone()),
        _ => (Vec::new(), None, None),
    }
}

/// σ of a run with `given`: the arguments of the call, or the places that a
/// callee gives to each parameter of the types `params`.
///
/// # Errors
///
/// The errors of σ.
fn given_sigma(
    cx: &mut Cx<'_>,
    r: Run0<'_>,
    params: &[(TyId, TyId)],
    given: Given<'_>,
) -> Result<super::apply::Sigma, AlphaError> {
    match given {
        Given::Args(args) => {
            let n = args.len().min(params.len());
            super::apply::sigma_with(
                cx,
                r.body,
                r.st,
                params.get(..n).unwrap_or(&[]),
                args,
                r.inst,
            )
        }
        Given::Opaque(places, _) => {
            Ok(super::apply::opaque_sigma(cx, r.st, params, places, r.inst))
        }
    }
}

/// The function values of the result of a run of summary `sum` with
/// `given` (part `ret`, stage F12): an item and a closure that a callee made
/// as they are, the values of a parameter (of an argument), and the values
/// of a capture (`capture`).
///
/// # Errors
///
/// The errors of α.
fn ret_fns(
    cx: &mut Cx<'_>,
    r: Run0<'_>,
    sum: &super::summary::Summary,
    given: Given<'_>,
    capture: &mut CaptureValues<'_>,
) -> Result<(BTreeSet<FnVal>, BTreeSet<PlaceId>), AlphaError> {
    rets_fns(cx, r, &sum.ret.fns, given, capture)
}

/// The function values `rets` of a summary in the terms of run node `r`
/// ([`ret_fns`]): the values of the result, or the values that the body
/// puts into a place of the caller (part `put_fns`, stage F13), with the
/// places that their environments point into.
///
/// # Errors
///
/// The errors of α.
fn rets_fns(
    cx: &mut Cx<'_>,
    r: Run0<'_>,
    rets: &[super::summary::RetFn],
    given: Given<'_>,
    capture: &mut CaptureValues<'_>,
) -> Result<(BTreeSet<FnVal>, BTreeSet<PlaceId>), AlphaError> {
    use super::summary::RetFn;
    let mut out = BTreeSet::new();
    let mut refs = BTreeSet::new();
    for f in rets {
        match f {
            RetFn::Item(g, t) => {
                out.insert(FnVal::Item(*g, t.clone()));
            }
            RetFn::Made(c) => {
                out.insert(FnVal::Made(*c));
            }
            RetFn::Param(i) => match given {
                Given::Args(args) => match args.get(*i as usize) {
                    Some(a) => {
                        let reach = reach_fns(cx, r.body, r.st, a)?;
                        for fv in &reach {
                            refs.extend(result_refs(cx, r, fv, (a, r.body), 0)?);
                        }
                        out.extend(with_results(cx, r, reach)?);
                        refs.extend(reach_refs(cx, r.body, r.st, a)?);
                    }
                    None => {
                        out.insert(FnVal::Unknown);
                    }
                },
                Given::Opaque(..) => {
                    out.insert(FnVal::Unknown);
                }
            },
            // The value of the capture again, and what its runs give back,
            // with the places that their environments point into (hole N1
            // of the second review of the ABC preview: `|| mk()`).
            RetFn::Capture(k) => {
                let (vals, rs) = capture(cx, *k)?;
                out.extend(with_results(cx, r, vals)?);
                refs.extend(rs);
            }
            RetFn::Unknown => {
                out.insert(FnVal::Unknown);
            }
        }
    }
    Ok((out, refs))
}

/// The values that a run node with σ `sigma` puts into places of the caller
/// for the parts `puts` and `put_fns` of summary `sum` (stage F13): the
/// references for each place (they join the part `stores`), and the
/// function values for each place.
///
/// # Errors
///
/// The errors of σ and of α.
fn put_values(
    cx: &mut Cx<'_>,
    r: Run0<'_>,
    sum: &super::summary::Summary,
    sigma: &super::apply::Sigma,
    given: Given<'_>,
    capture: &mut CaptureValues<'_>,
) -> Result<PutValues, AlphaError> {
    let mut stores = Vec::new();
    let mut fns_out = Vec::new();
    for (into, refs) in &sum.puts {
        // The references flow from the values of the arguments, with the
        // handles on the way (as the part `stores`, `apply::flow_refs`).
        let mut rs = Vec::new();
        for x in refs {
            rs.extend(super::apply::vplaces(cx, sigma, x)?);
        }
        rs.sort();
        rs.dedup();
        if rs.is_empty() {
            continue;
        }
        for q in super::apply::iplaces(cx, sigma, into)? {
            stores.push((q, rs.clone()));
        }
    }
    for (into, rets) in &sum.put_fns {
        let (fns, refs) = rets_fns(cx, r, rets, given, capture)?;
        if fns.is_empty() {
            continue;
        }
        let rs: Vec<PlaceId> = refs.into_iter().collect();
        for q in super::apply::iplaces(cx, sigma, into)? {
            if !rs.is_empty() {
                stores.push((q, rs.clone()));
            }
            fns_out.push((q, fns.clone()));
        }
    }
    Ok((stores, fns_out))
}

/// The values of [`put_values`]: the references, and the function values,
/// that go into each place of the caller.
type PutValues = (
    Vec<(PlaceId, Vec<PlaceId>)>,
    Vec<(PlaceId, BTreeSet<FnVal>)>,
);

/// Each place `q` of `put_fns` gets its function values: a weak update of
/// the move path of a local, or of the heap slot of a place that no local
/// owns (stage F13).
fn apply_put_fns(cx: &Cx<'_>, st: &mut State, put_fns: &[(PlaceId, BTreeSet<FnVal>)]) {
    for (q, fns) in put_fns {
        match cx.roots.path_of(cx.facts, *q) {
            Some((k, path)) => {
                let mut v = AbsVal::none();
                v.fns.clone_from(fns);
                st.add(k, &path, &Tree::leaf(v));
            }
            None => {
                st.store_fns_behind(*q, fns.iter().cloned());
            }
        }
    }
}

/// Adds the function values `fns` and the places `refs` of their
/// environments to the top of the result `t` of type `ret_ty`, if the type
/// can hold a function value.
fn with_fns(
    cx: &Cx<'_>,
    mut t: Tree,
    ret_ty: TyId,
    (fns, refs): (BTreeSet<FnVal>, BTreeSet<PlaceId>),
) -> Tree {
    if crate::props::ir_has_fns(cx.tys, ret_ty) {
        t.top.fns.extend(fns);
        t.top.refs.extend(refs);
    }
    t
}

/// True if the function values `fns` hold a closure of the program (a
/// closure of the component, or one that a callee made).
fn has_closure(fns: &BTreeSet<FnVal>) -> bool {
    fns.iter()
        .any(|f| matches!(f, FnVal::Closure(_) | FnVal::Made(_)))
}

/// The places that the environments of the closures that operand `op`
/// reaches point into.
///
/// Operand `op` is of body `body` in state `st` ([`reach_fns`]): the
/// references of a value of a type with a function part, and the
/// references at each place behind its references that holds a function
/// value (two levels). A function value that goes through a call (`id(f)`)
/// keeps them (hole H2 of the review of the ABC preview).
///
/// # Errors
///
/// The errors of α.
pub fn reach_refs(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    op: &Operand,
) -> Result<BTreeSet<PlaceId>, AlphaError> {
    let mut out = BTreeSet::new();
    let ty = match op {
        Operand::Copy(q) | Operand::Move(q) => place_ty(cx, body, q)?,
        Operand::Const(_) => return Ok(out),
    };
    if !crate::props::ir_has_fns(cx.tys, ty) {
        return Ok(out);
    }
    let v = operand(cx, body, st, op)?.flat();
    if !is_ref_ty(cx.tys, ty) {
        out.extend(v.refs.iter().copied());
    }
    // The environments of the values in an `rc` object that the value
    // reaches (stage F13).
    out.extend(rc_stored(cx, st, ty).1);
    let mut level: Vec<PlaceId> = v.refs.into_iter().collect();
    for _ in 0..2 {
        let mut next = Vec::new();
        for &r in &level {
            let held = held_at(cx.p, st, cx.facts, cx.roots, r, None).unwrap_or_default();
            if has_closure(&fns_of_role(cx, st, r)) {
                out.extend(held.iter().copied());
            } else if cx.roots.path_of(cx.facts, r).is_none()
                && has_closure(&stored_fns_at(cx.facts, st, r))
            {
                // A closure in a heap slot: the references that its store
                // put there (stage F13).
                out.extend(stored_at(cx.facts, st, r));
            }
            next.extend(held);
        }
        next.sort();
        next.dedup();
        level = next;
    }
    Ok(out)
}

/// The values of the variables whose cell roots are among the places `refs`.
///
/// A closure value points into the cell of each variable that it captures
/// `ByRef`. The result is the places of the values of these variables in
/// state `st`, and the places that the references in their values point
/// into. A closure that a callee made, and code of a caller, change and read a
/// `ByRef` capture through the cell: that is the current value of the
/// variable where they run (`docs/ir.md` 6.3; hole N1 of the second review
/// of the ABC preview).
///
/// # Errors
///
/// The errors of α.
pub fn cell_values<'r>(
    cx: &mut Cx<'_>,
    st: &State,
    refs: impl IntoIterator<Item = &'r PlaceId>,
) -> Result<(Vec<PlaceId>, Vec<PlaceId>), AlphaError> {
    let mut keys = Vec::new();
    for &q in refs {
        let Some(root) = cx.facts.places.get(q.index()).map(|i| i.root) else {
            continue;
        };
        if let Some(Role::Cell(k)) = cx.roots.role(root) {
            keys.push(k);
        }
    }
    keys.sort();
    keys.dedup();
    let mut places = Vec::new();
    let mut held = Vec::new();
    for (b, l) in keys {
        let place = Place {
            local: l,
            proj: Vec::new(),
        };
        places.extend(alpha(cx, b, st, &place)?.places);
        held.extend(place_value(cx, b, st, &place)?.flat().refs);
    }
    places.sort();
    places.dedup();
    held.sort();
    held.dedup();
    Ok((places, held))
}

/// The reason for a function value that code of a caller can run as a task.
const TASK_RUN: &str =
    "a function value that changes places or holds a nonportable value, and that code of a caller can run on another thread (stage F18)";

/// True if code of a caller that runs the function value `fv` on another
/// thread at the same time can race (ADR 0006: W0401, W0403, W0405 of the
/// old lowering): the value changes or lends a place, or a capture holds a
/// nonportable value or is a reference to a variable.
fn task_unsafe(cx: &mut Cx<'_>, fv: &FnVal) -> bool {
    let sum = match fv {
        FnVal::Closure(c) | FnVal::Made(c) => {
            let p = cx.p;
            let Some(decl) = p.closures.get(c.index()) else {
                return true;
            };
            for (k, cap) in decl.captures.iter().enumerate() {
                if cap.mode == weft_ir::CaptureMode::ByRef {
                    return true;
                }
                let k = u32::try_from(k).unwrap_or(u32::MAX);
                let nonportable = alpha::capture_ty(p, cx.tys, *c, k)
                    .is_none_or(|t| ir_props(cx.tys, t).nonportable);
                if nonportable {
                    return true;
                }
            }
            cx.sums.closure(*c).ok()
        }
        FnVal::Item(f, _) => cx.sums.get(*f).ok(),
        FnVal::Param(_) | FnVal::ParamResult(_) | FnVal::Capture(_) | FnVal::Unknown => {
            return false
        }
    };
    sum.is_none_or(|s| !s.muts.is_empty() || !s.lends.is_empty() || !s.puts.is_empty())
}

/// The function values of a capture of a closure ([`ret_fns`]).
/// They are the function values and the places that their environments
/// point into.
type CaptureValues<'a> =
    dyn FnMut(&mut Cx<'_>, u32) -> Result<(BTreeSet<FnVal>, BTreeSet<PlaceId>), AlphaError> + 'a;

/// The function values of a run, the operand that holds them and its body.
type RunSource = (BTreeSet<FnVal>, Operand, BodyId);

/// The function values of each run of a summary ([`apply_runs`]).
type RunValues<'a> =
    dyn FnMut(&mut Cx<'_>, &super::summary::Run) -> Result<Option<RunSource>, AlphaError> + 'a;

/// Applies the runs `runs` of a summary with σ `sigma` at run node `r`
/// (part `runs`): each function value that the parameter or the capture
/// holds applies its summary with the places of the run (`run.args`). `of`
/// gives the values of a parameter (`false`) or of a capture (`true`).
///
/// # Errors
///
/// The errors of [`apply_value`].
#[allow(clippy::too_many_arguments)]
fn apply_runs(
    cx: &mut Cx<'_>,
    r: Run0<'_>,
    runs: &[super::summary::Run],
    sigma: &super::apply::Sigma,
    of: &mut RunValues<'_>,
    depth: usize,
    apps: &mut Apps,
) -> Result<(), AlphaError> {
    // A body that runs two values can run them in each order: each run can
    // come after the other one. A run of a parameter and a run of its
    // result are one value and the values that it gives back: the body runs
    // the result after the run that gives it.
    let keys: BTreeSet<(u32, bool)> = runs.iter().map(|x| (x.param, x.capture)).collect();
    let two = keys.len() > 1;
    // The values that the runs of each key reach, also through the values
    // that a value runs (`Apps::reached`).
    let mut reached: BTreeMap<(u32, bool), BTreeSet<FnVal>> = BTreeMap::new();
    for run in runs {
        let first = apps.reached.len();
        let many = run.many || two;
        let Some((fns, src, src_body)) = of(cx, run)? else {
            continue;
        };
        let mut places = Vec::new();
        for a in &run.args {
            places.extend(super::apply::iplaces(cx, sigma, a)?);
        }
        places.sort();
        places.dedup();
        // The other arguments of the call: the callee can keep references
        // into them across the run (`Sigma::others`).
        let mut others = Vec::new();
        for (i, a) in sigma.args.iter().enumerate() {
            if !run.capture && i == run.param as usize {
                continue;
            }
            let given = if a.is_empty() {
                sigma.values.get(i).map_or(&[][..], Vec::as_slice)
            } else {
                a.as_slice()
            };
            others.extend(given.iter().copied());
            others.extend(sigma.helds.get(i).into_iter().flatten().copied());
        }
        others.sort();
        others.dedup();
        let env: Vec<PlaceId> = sigma
            .cap_helds
            .iter()
            .chain(&sigma.cap_deeps)
            .flatten()
            .chain(&sigma.env)
            .copied()
            .collect();
        for g in &fns {
            if run.task && task_unsafe(cx, g) {
                return Err(AlphaError::Later(TASK_RUN));
            }
            let start = apps.out.len();
            let fresh = !apps.modes.contains(&(g.clone(), Some(places.clone())));
            apply_value(
                cx,
                r,
                g,
                (&src, src_body),
                Given::Opaque(&places, run.multi),
                None,
                depth + 1,
                apps,
            )?;
            for a in apps.out.iter_mut().skip(start) {
                a.kind = super::apply::RunKind::Run;
                a.late = true;
                a.sigma.others.clone_from(&others);
                // A value that the closure runs through a capture changes
                // the places of the environment through the environment.
                if run.capture {
                    a.sigma.env.extend(env.iter().copied());
                }
                // A run that the callee does on some paths only: each run
                // that it gives is on some paths only too (hole H5b of the
                // second review of the ABC preview: `outer(f) { maybe(f) }`).
                if run.maybe {
                    if let Some(x) = a.run.as_mut() {
                        x.maybe = true;
                    }
                }
            }
            // A capture that holds a `once` value moves at the run of the
            // closure (`Applied::once`); a value of a parameter moves here.
            if fresh && !run.capture && once_value(cx.p, g) {
                if let Some(a) = apps.out.get_mut(start) {
                    a.once_args.push((src_body, src.clone()));
                }
            }
            if many {
                match (fresh, apps.seen.get(g)) {
                    // A run of the value and of each value that it runs
                    // happens again. With two values and one run of each
                    // (`!run.many`), it happens one time, in either order.
                    // An app that is already `again` runs two times inside
                    // the value (`both(|| { h(); h() }, g)`): it keeps its
                    // flags (class H-ORD of the final check of group C).
                    (true, _) => {
                        for a in apps.out.iter_mut().skip(start) {
                            if !a.again {
                                a.again = true;
                                a.order = !run.many;
                            }
                        }
                    }
                    // The same value runs a second time.
                    (false, Some(&k)) => {
                        if let Some(a) = apps.out.get_mut(k) {
                            a.again = true;
                            a.order = false;
                        }
                    }
                    _ => {}
                }
            }
        }
        let key = (run.param, run.capture);
        let got = apps.reached.get(first..).unwrap_or_default();
        reached.entry(key).or_default().extend(got.iter().cloned());
    }
    // A value that the runs of two keys reach runs two times
    // (`both(h, || h())`, `both(|| h(), || h())`): its app happens again,
    // not in one order only. An item has no `once` part to lose.
    if two {
        let mut keys_of: BTreeMap<&FnVal, usize> = BTreeMap::new();
        for vals in reached.values() {
            for v in vals {
                *keys_of.entry(v).or_default() += 1;
            }
        }
        for (v, n) in keys_of {
            if n < 2 || matches!(v, FnVal::Item(..)) {
                continue;
            }
            if let Some(a) = apps.seen.get(v).and_then(|&k| apps.out.get_mut(k)) {
                a.again = true;
                a.order = false;
            }
        }
    }
    Ok(())
}

/// The places that code of a caller can read and that body `body` can
/// name: the wildcard place of the interface root of each parameter (what
/// the parameter points into, and what the references behind it point
/// into), and the wildcard place of each `rc` group that a parameter type
/// reaches. A function value of a caller can point into each of them (the
/// four summary-oracle rows of stage F12-fix3, and FO-A3b of the review of
/// stage F13: `let g = h.f; g()` reads `Hook.data[]`).
///
/// # Errors
///
/// The errors of α.
fn caller_reads(cx: &mut Cx<'_>, body: BodyId) -> Result<Vec<PlaceId>, AlphaError> {
    let mut out = super::unknown::param_places(cx, body)?;
    let tys: Vec<TyId> =
        cx.p.bodies
            .get(body.index())
            .map(|b| {
                b.params
                    .iter()
                    .filter_map(|l| b.locals.get(l.index()).map(|d| d.ty))
                    .collect()
            })
            .unwrap_or_default();
    for t in tys {
        for inner in rc_inners(cx.tys, t) {
            let g = cx.roots.group(cx.tys, cx.facts, inner);
            out.push(cx.facts.wildcard(g));
        }
    }
    out.sort();
    out.dedup();
    Ok(out)
}

/// Applies the function value `fv` at the run node `r`: its summary, and the
/// summary of each value that it runs, at depth `depth`. `callee` is the
/// operand of the value; `ret_ty` is the type of the result of a value of
/// the callee itself (`None` for a run that a summary gives). The summaries
/// go to `apps`, the value itself first. A value applies one time at a run
/// node.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn apply_value(
    cx: &mut Cx<'_>,
    r: Run0<'_>,
    fv: &FnVal,
    (callee, cb): (&Operand, BodyId),
    given: Given<'_>,
    ret_ty: Option<TyId>,
    depth: usize,
    apps: &mut Apps,
) -> Result<(), AlphaError> {
    use super::summary::{IPlace, IRoot};
    if depth > RUN_DEPTH {
        return Err(AlphaError::Later(
            "a chain of function values that run each other deeper than 64 (stage F12)",
        ));
    }
    apps.reached.push(fv.clone());
    if !apps.modes.insert((fv.clone(), given.places())) {
        return Ok(());
    }
    apps.seen.insert(fv.clone(), apps.out.len());
    let p = cx.p;
    let (body, st) = (r.body, r.st);
    match fv {
        FnVal::Unknown | FnVal::Param(_) | FnVal::ParamResult(_) | FnVal::Capture(_) => {
            let (params, fn_ret, row) = fn_type(cx, cb, callee);
            let fn_ret = ret_ty.or(fn_ret).unwrap_or_else(|| cx.tys.unit());
            let pairs: Vec<(TyId, TyId)> = params.iter().map(|&t| (t, t)).collect();
            let (summary, sigma) = match given {
                Given::Args(_) => {
                    let summary =
                        super::unknown::code_of_caller(cx.tys, &params, fn_ret, row.as_deref());
                    (summary, given_sigma(cx, r, &pairs, given)?)
                }
                Given::Opaque(_, multi) => {
                    // The parameters of the value are not known: one
                    // parameter stands for each place that the run gets.
                    let any = cx.tys.unit();
                    let t = cx.tys.intern(Ty::Ref(any));
                    let mut summary =
                        super::unknown::code_of_caller(cx.tys, &[t], fn_ret, row.as_deref());
                    summary.multi = multi;
                    summary.unknown_multi = multi;
                    (summary, given_sigma(cx, r, &[(t, t)], given)?)
                }
            };
            // The environment of the value: what its references point into.
            let env: Vec<PlaceId> = match given {
                // A value of a caller next to a closure in one value (a slot
                // that holds the value of the caller and a closure that the
                // body stored there): the references of the value are the
                // environment of the closure, which its own run applies. The
                // value of the caller has the places of a caller (false
                // positive FP-S2 of the review of stage F13: `let o = s.o`).
                Given::Args(_)
                    if !matches!(fv, FnVal::Unknown)
                        && operand(cx, cb, st, callee)?
                            .flat()
                            .fns
                            .iter()
                            .any(|f| matches!(f, FnVal::Closure(_) | FnVal::Made(_))) =>
                {
                    Vec::new()
                }
                Given::Args(_) => {
                    let v = operand(cx, cb, st, callee)?.flat();
                    // The cell of a variable that a closure captures `ByRef`
                    // stands for the value of the variable too.
                    let (cells, held) = cell_values(cx, st, &v.refs)?;
                    v.refs
                        .iter()
                        .chain(&cells)
                        .chain(&held)
                        .map(|&q| cx.facts.wildcard(q))
                        .collect()
                }
                Given::Opaque(..) => Vec::new(),
            };
            let mut ret = match ret_ty {
                Some(t) => {
                    let mut v = super::apply::ret_value(cx, &summary, &sigma, t)?;
                    if ir_props(cx.tys, t).holds_refs || crate::props::ir_has_fns(cx.tys, t) {
                        v.top.refs.extend(env.iter().copied());
                    }
                    Some(v)
                }
                None => None,
            };
            let run = match (fv, given) {
                (
                    FnVal::Param(i) | FnVal::ParamResult(i) | FnVal::Capture(i),
                    Given::Args(args),
                ) => Some(RunOf {
                    param: *i,
                    capture: matches!(fv, FnVal::Capture(_)),
                    result: matches!(fv, FnVal::ParamResult(_)),
                    places: given_places(cx, body, st, args)?,
                    multi: summary.multi,
                    task: false,
                    block: r.block,
                    maybe: false,
                }),
                (
                    FnVal::Param(i) | FnVal::ParamResult(i) | FnVal::Capture(i),
                    Given::Opaque(ps, _),
                ) => Some(RunOf {
                    param: *i,
                    capture: matches!(fv, FnVal::Capture(_)),
                    result: matches!(fv, FnVal::ParamResult(_)),
                    places: ps.to_vec(),
                    multi: summary.multi,
                    task: false,
                    block: r.block,
                    maybe: false,
                }),
                _ => None,
            };
            // The code can run each function value that the arguments
            // reach, more than once, and give the result one of them.
            let mut reach = BTreeSet::new();
            let mut reach_at = BTreeSet::new();
            if let Given::Args(args) = given {
                for a in args {
                    reach.extend(reach_fns(cx, body, st, a)?);
                    reach_at.extend(reach_refs(cx, body, st, a)?);
                }
            }
            if let (Some(t), Some(rt)) = (ret.take(), ret_ty) {
                let mut fs = reach.clone();
                // The result of a run of a value of the interface: a value
                // that the run of the value of the caller gives (part
                // `runs`: the caller applies the results too, part `ret`
                // gives them back). The caller knows these values, so the
                // result is not `Unknown` (second review of the ABC
                // preview: `Unknown` there made code of a caller change the
                // environment of each closure that the result reaches).
                // A run of a value of a parameter gives a result of it
                // (`FnVal::ParamResult`): a run of the result is not a run of
                // the parameter again.
                fs.insert(match fv {
                    FnVal::Param(i) | FnVal::ParamResult(i) => FnVal::ParamResult(*i),
                    other => other.clone(),
                });
                ret = Some(with_fns(cx, t, rt, (fs, reach_at)));
            }
            let name = match callee {
                Operand::Copy(q) | Operand::Move(q) => p
                    .bodies
                    .get(cb.index())
                    .and_then(|b| b.locals.get(q.local.index()))
                    .and_then(|d| d.name.clone())
                    .unwrap_or_else(|| "the function value".to_string()),
                Operand::Const(_) => "the function value".to_string(),
            };
            let multi = summary.multi;
            apps.out.push(Applied {
                kind: super::apply::RunKind::Unknown,
                name,
                sigma,
                summary,
                ret,
                muts: Vec::new(),
                stores: Vec::new(),
                rebinds: Vec::new(),
                uses: Vec::new(),
                once: Vec::new(),
                once_args: Vec::new(),
                again: false,
                order: false,
                late: false,
                run,
                code: true,
                lends: env,
                put_fns: Vec::new(),
                reads: caller_reads(cx, body)?,
            });
            let places = match given {
                Given::Args(args) => {
                    let mut ps = given_places(cx, body, st, args)?;
                    let c = cx.roots.caller(cx.facts);
                    ps.push(cx.facts.wildcard(c));
                    ps
                }
                Given::Opaque(ps, _) => ps.to_vec(),
            };
            for g in &reach {
                if matches!(g, FnVal::Unknown) {
                    continue;
                }
                // Code of a caller can run the value on another thread at
                // the same time (ADR 0006): the facts of a task are stage
                // F18.
                if task_unsafe(cx, g) {
                    return Err(AlphaError::Later(TASK_RUN));
                }
                let start = apps.out.len();
                apply_value(
                    cx,
                    r,
                    g,
                    (callee, cb),
                    Given::Opaque(&places, multi),
                    None,
                    depth + 1,
                    apps,
                )?;
                for a in apps.out.iter_mut().skip(start) {
                    a.again = true;
                    a.kind = super::apply::RunKind::Run;
                    // Code of a caller can drop the value with no run.
                    if let Some(r) = a.run.as_mut() {
                        r.task = true;
                        r.maybe = true;
                    }
                }
            }
            // The code can run a `once` value of an argument more than once:
            // the run moves the argument, and the run again uses it (W0502).
            if let Given::Args(args) = given {
                for a in args {
                    let once = reach_fns(cx, body, st, a)?
                        .into_iter()
                        .find(|g| once_value(p, g));
                    let at = once.and_then(|g| apps.seen.get(&g).copied());
                    if let Some(app) = at.and_then(|k| apps.out.get_mut(k)) {
                        app.once_args.push((body, a.clone()));
                    }
                }
            }
            Ok(())
        }
        FnVal::Item(f, targs) => {
            let summary = cx.sums.get(*f).map_err(AlphaError::Later)?.clone();
            let decl = p
                .fns
                .get(f.index())
                .ok_or_else(|| AlphaError::BadPlace(format!("no function f{}", f.0)))?;
            if decl.intrinsic.is_some() {
                return Err(AlphaError::Later(
                    "a call of `sim.run` or `with_timeout` as a value (stage F19)",
                ));
            }
            let pairs: Vec<(TyId, TyId)> = decl
                .params
                .iter()
                .map(|&t| (t, crate::irbuild::subst(cx.tys, t, targs)))
                .collect();
            let mut sigma = given_sigma(cx, r, &pairs, given)?;
            sigma.cyclic = cx.cycles.has(body, r.block);
            if summary.ret_in_frame() {
                sigma.frame = Some(cx.roots.frame(cx.facts, r.inst, &decl.name));
            }
            let ret = match ret_ty {
                Some(t) => {
                    let v = super::apply::ret_value(cx, &summary, &sigma, t)?;
                    let fs = ret_fns(cx, r, &summary, given, &mut |_, _| {
                        Ok((BTreeSet::from([FnVal::Unknown]), BTreeSet::new()))
                    })?;
                    Some(with_fns(cx, v, t, fs))
                }
                None => None,
            };
            let muts = super::apply::muts(cx, &summary, &sigma)?;
            let mut stores = super::apply::stores(cx, &summary, &sigma, &muts)?;
            let (put_refs, put_fns) = put_values(cx, r, &summary, &sigma, given, &mut |_, _| {
                Ok((BTreeSet::from([FnVal::Unknown]), BTreeSet::new()))
            })?;
            stores.extend(put_refs);
            let name = decl
                .name
                .rsplit('.')
                .next()
                .unwrap_or(&decl.name)
                .to_string();
            let runs = summary.runs.clone();
            apps.out.push(Applied {
                kind: super::apply::RunKind::Item,
                name,
                sigma: sigma.clone(),
                summary,
                ret,
                muts,
                stores,
                rebinds: Vec::new(),
                uses: Vec::new(),
                once: Vec::new(),
                once_args: Vec::new(),
                again: false,
                order: false,
                late: false,
                run: None,
                code: false,
                lends: Vec::new(),
                put_fns,
                reads: Vec::new(),
            });
            apply_runs(
                cx,
                r,
                &runs,
                &sigma,
                &mut |cx, run| param_fns(cx, r, run, given),
                depth,
                apps,
            )
        }
        FnVal::Closure(c) | FnVal::Made(c) => {
            let made = matches!(fv, FnVal::Made(_));
            let summary = cx.sums.closure(*c).map_err(AlphaError::Later)?.clone();
            let decl = p
                .closures
                .get(c.index())
                .ok_or_else(|| AlphaError::BadPlace(format!("no closure c{}", c.0)))?;
            let mut sigma = if made {
                super::apply::made_sigma(cx, body, st, *c, (callee, cb), given, r.inst)?
            } else {
                super::apply::closure_sigma(cx, body, st, *c, (callee, cb), given, r.inst)?
            };
            sigma.cyclic = cx.cycles.has(body, r.block);
            if summary.ret_in_frame() {
                sigma.frame = Some(cx.roots.frame(cx.facts, r.inst, "the closure"));
            }
            let ret = match ret_ty {
                Some(t) => {
                    let v = super::apply::ret_value(cx, &summary, &sigma, t)?;
                    let callee_v = operand(cx, cb, st, callee)?.flat();
                    let mut callee_refs = callee_v.refs.clone();
                    callee_refs.extend(reach_refs(cx, cb, st, callee)?);
                    let fs = ret_fns(cx, r, &summary, given, &mut |cx, k| {
                        let fns = capture_fns(cx, r, *c, k, made, &callee_v.fns)?;
                        let refs = capture_refs(cx, r, *c, k, made, &callee_refs)?;
                        Ok((fns, refs))
                    })?;
                    Some(with_fns(cx, v, t, fs))
                }
                None => None,
            };
            let muts = super::apply::muts(cx, &summary, &sigma)?;
            // The new value of each capture that the body rebinds on each
            // path: a whole local of the maker gets it (a strong update).
            let mut rebinds = Vec::new();
            let mut whole: Vec<u32> = Vec::new();
            for &k in summary.rebinds.iter().filter(|_| !made) {
                let Some(cap) = decl.captures.get(k as usize) else {
                    continue;
                };
                if !cap.source.proj.is_empty()
                    || alpha::env_capture(p, decl.maker, &cap.source).is_some()
                {
                    continue;
                }
                let key = key(p, decl.maker, cap.source.local)?;
                let ty = p
                    .bodies
                    .get(key.0.index())
                    .and_then(|b| b.locals.get(key.1.index()))
                    .map(|d| d.ty);
                let mut v = AbsVal::of_type(ty.is_some_and(|t| ir_props(cx.tys, t).linear));
                let root = IPlace::root(IRoot::Capture(k));
                if ty.is_some_and(|t| crate::props::ir_has_fns(cx.tys, t)) {
                    // The values that the body puts into the capture (part
                    // `put_fns`), else a value that the analysis does not know
                    // (follow-up F13.2: `let set = || { g = grow }; set();
                    // g(w)` runs `grow`, not code of a caller).
                    let put = summary
                        .put_fns
                        .iter()
                        .find(|(into, _)| *into == root)
                        .map(|(_, rets)| rets.clone());
                    match put {
                        Some(rets) => {
                            let callee_v = operand(cx, cb, st, callee)?.flat();
                            let mut callee_refs = callee_v.refs.clone();
                            callee_refs.extend(reach_refs(cx, cb, st, callee)?);
                            let (fns, _) = rets_fns(cx, r, &rets, given, &mut |cx, j| {
                                let fns = capture_fns(cx, r, *c, j, made, &callee_v.fns)?;
                                let refs = capture_refs(cx, r, *c, j, made, &callee_refs)?;
                                Ok((fns, refs))
                            })?;
                            v.fns.extend(fns);
                            if v.fns.is_empty() {
                                v.fns.insert(FnVal::Unknown);
                            }
                        }
                        None => {
                            v.fns.insert(FnVal::Unknown);
                        }
                    }
                }
                for (into, refs) in &summary.puts {
                    if *into == root {
                        for r in refs {
                            v.refs.extend(super::apply::iplaces(cx, &sigma, r)?);
                        }
                    }
                }
                whole.push(k);
                rebinds.push((key, Tree::leaf(v)));
            }
            // The other values that the body puts into a place of the caller
            // (a weak update).
            let mut stores = Vec::new();
            for (into, refs) in &summary.puts {
                if let IRoot::Capture(k) = into.root {
                    if into.steps.is_empty() && whole.contains(&k) {
                        continue;
                    }
                }
                let mut rs = Vec::new();
                for r in refs {
                    rs.extend(super::apply::iplaces(cx, &sigma, r)?);
                }
                rs.sort();
                rs.dedup();
                if rs.is_empty() {
                    continue;
                }
                for q in super::apply::iplaces(cx, &sigma, into)? {
                    stores.push((q, rs.clone()));
                }
            }
            let uses: Vec<(u32, BodyId, Place)> = if made {
                Vec::new()
            } else {
                summary
                    .uses
                    .iter()
                    .filter_map(|&k| decl.captures.get(k as usize).map(|c| (k, c)))
                    .filter(|(_, cap)| {
                        matches!(
                            cap.mode,
                            weft_ir::CaptureMode::Kept | weft_ir::CaptureMode::ByRef
                        )
                    })
                    .map(|(k, cap)| (k, decl.maker, cap.source.clone()))
                    .collect()
            };
            // The function values that the body puts into places of the
            // caller (stage F13): a capture gives the values of its source.
            let mut put_fns = Vec::new();
            if !summary.put_fns.is_empty() {
                let callee_v = operand(cx, cb, st, callee)?.flat();
                let mut callee_refs = callee_v.refs.clone();
                callee_refs.extend(reach_refs(cx, cb, st, callee)?);
                for (into, rets) in &summary.put_fns {
                    let (fns, _) = rets_fns(cx, r, rets, given, &mut |cx, k| {
                        let fns = capture_fns(cx, r, *c, k, made, &callee_v.fns)?;
                        let refs = capture_refs(cx, r, *c, k, made, &callee_refs)?;
                        Ok((fns, refs))
                    })?;
                    if fns.is_empty() {
                        continue;
                    }
                    for q in super::apply::iplaces(cx, &sigma, into)? {
                        put_fns.push((q, fns.clone()));
                    }
                }
            }
            let runs = summary.runs.clone();
            let first = apps.out.len();
            apps.out.push(Applied {
                kind: super::apply::RunKind::Closure,
                name: "the closure".to_string(),
                sigma: sigma.clone(),
                summary,
                ret,
                muts,
                stores,
                rebinds,
                uses,
                once: Vec::new(),
                once_args: Vec::new(),
                again: false,
                order: false,
                late: false,
                run: None,
                code: false,
                lends: Vec::new(),
                put_fns,
                reads: Vec::new(),
            });
            // A closure that a callee made holds the values that it runs in
            // its own value: a run of a capture runs each value of the callee
            // with the places of the run (follow-up F13.2: they are known
            // values of the body, not code of a caller). A capture that runs
            // more than once makes each run happen again.
            if made {
                if runs.iter().any(|x| x.capture && x.many) {
                    for a in &mut apps.out {
                        a.again = true;
                    }
                }
                let held = operand(cx, cb, st, callee)?.flat().fns;
                return apply_runs(
                    cx,
                    r,
                    &runs,
                    &sigma,
                    &mut |cx, run| {
                        if run.capture {
                            Ok(Some((
                                made_held(cx.p, *c, run.param, &held),
                                callee.clone(),
                                cb,
                            )))
                        } else {
                            param_fns(cx, r, run, given)
                        }
                    },
                    depth,
                    apps,
                );
            }
            let maker = decl.maker;
            apply_runs(
                cx,
                r,
                &runs,
                &sigma,
                &mut |cx, run| {
                    if !run.capture {
                        return param_fns(cx, r, run, given);
                    }
                    let Some(cap) = decl.captures.get(run.param as usize) else {
                        return Ok(None);
                    };
                    if cap.mode == weft_ir::CaptureMode::ByMove {
                        // The closure owns the value: the value of the
                        // closure holds it.
                        let mut fns = operand(cx, cb, st, callee)?.flat().fns;
                        fns.remove(&FnVal::Closure(*c));
                        let mut fns = with_results(cx, r, fns)?;
                        fns.remove(&FnVal::Closure(*c));
                        return Ok(Some((fns, callee.clone(), cb)));
                    }
                    // The values of the capture, and the values that their
                    // runs give back: the summary has a run of the capture
                    // for each run of a result of a run of it (hole N1 of
                    // the second review of the ABC preview: `|| run(mk())`).
                    let src = Operand::Copy(cap.source.clone());
                    let fns = reach_fns(cx, maker, st, &src)?;
                    let fns = with_results(cx, r, fns)?;
                    Ok(Some((fns, src, maker)))
                },
                depth,
                apps,
            )?;
            // A `once` value that the closure runs through a capture moves.
            for (k, cap) in decl.captures.iter().enumerate() {
                let k = u32::try_from(k).unwrap_or(u32::MAX);
                if !runs.iter().any(|x| x.capture && x.param == k) {
                    continue;
                }
                let v = place_value(cx, maker, st, &cap.source)?.flat();
                if v.fns.iter().any(|g| once_value(p, g)) {
                    if let Some(a) = apps.out.get_mut(first) {
                        a.once.push((maker, cap.source.clone()));
                    }
                }
            }
            Ok(())
        }
    }
}

/// The function values that capture `k` of closure `c` holds, for a closure
/// that a callee made and gave back as the value `held` (follow-up F13.2).
///
/// The value of a made closure holds the values of its `Kept` captures
/// (`summarize::fn_parts_of` puts them into the part `ret` of the maker): each
/// value of `held` but the closure itself. The values of another capture are
/// not in the value: code of a caller ([`FnVal::Unknown`]) stands for them.
/// A closure that is not in `held` is the result of a run of a value of
/// `held` (`with_results`): the values that it holds are not known there.
fn made_held(
    p: &Program,
    c: weft_ir::ClosureId,
    k: u32,
    held: &BTreeSet<FnVal>,
) -> BTreeSet<FnVal> {
    if !held.contains(&FnVal::Made(c)) {
        return BTreeSet::from([FnVal::Unknown]);
    }
    let mut out: BTreeSet<FnVal> = held
        .iter()
        .filter(|f| **f != FnVal::Made(c))
        .cloned()
        .collect();
    let kept = p
        .closures
        .get(c.index())
        .and_then(|d| d.captures.get(k as usize))
        .is_some_and(|cap| cap.mode == weft_ir::CaptureMode::Kept);
    if !kept || out.is_empty() {
        out.insert(FnVal::Unknown);
    }
    out
}

/// The function values of parameter `run.param` of a run with `given`, and
/// the operand that holds them: the values that the argument reaches.
///
/// # Errors
///
/// The errors of α.
fn param_fns(
    cx: &mut Cx<'_>,
    r: Run0<'_>,
    run: &super::summary::Run,
    given: Given<'_>,
) -> Result<Option<RunSource>, AlphaError> {
    match given {
        Given::Args(args) => {
            let Some(a) = args.get(run.param as usize) else {
                return Ok(None);
            };
            let reach = reach_fns(cx, r.body, r.st, a)?;
            let fns = if run.result {
                results_of(cx, r, &reach)?
            } else {
                with_results(cx, r, reach)?
            };
            Ok(Some((fns, a.clone(), r.body)))
        }
        Given::Opaque(..) => Ok(Some((
            BTreeSet::from([FnVal::Unknown]),
            Operand::Const(Const::Unit),
            r.body,
        ))),
    }
}

/// The function values `fns` and the function values that their runs give
/// back (part `ret`): a callee that runs a value of a parameter can run its
/// result too (`ap(|| || ..)`). A closure of the body that gives back a
/// capture gives the values of the capture at run node `r` (a chain of
/// closures that give back closures). Each value counts one time; a chain
/// longer than [`RESULT_DEPTH`] stays with the old pipeline. A value that
/// gives back the value of a parameter is code of a caller here.
///
/// # Errors
///
/// The errors of α, and [`AlphaError::Later`] for a longer chain.
fn with_results(
    cx: &mut Cx<'_>,
    r: Run0<'_>,
    mut fns: BTreeSet<FnVal>,
) -> Result<BTreeSet<FnVal>, AlphaError> {
    use super::summary::RetFn;
    let mut level = fns.clone();
    for _ in 0..RESULT_DEPTH {
        let mut next = BTreeSet::new();
        for f in &level {
            let sum = match f {
                FnVal::Closure(c) | FnVal::Made(c) => cx.sums.closure(*c).ok().cloned(),
                FnVal::Item(g, _) => cx.sums.get(*g).ok().cloned(),
                _ => None,
            };
            let Some(sum) = sum else {
                continue;
            };
            for rf in &sum.ret.fns {
                match (rf, f) {
                    (RetFn::Item(g, t), _) => {
                        next.insert(FnVal::Item(*g, t.clone()));
                    }
                    (RetFn::Made(c), _) => {
                        next.insert(FnVal::Made(*c));
                    }
                    (RetFn::Capture(k), FnVal::Closure(c)) => {
                        next.extend(capture_fns(cx, r, *c, *k, false, &BTreeSet::new())?);
                    }
                    _ => {
                        next.insert(FnVal::Unknown);
                    }
                }
            }
        }
        next.retain(|f| !fns.contains(f));
        if next.is_empty() {
            return Ok(fns);
        }
        fns.extend(next.iter().cloned());
        level = next;
    }
    Err(AlphaError::Later(
        "a chain of function values that give back function values (stage F13)",
    ))
}

/// The values that runs of the function values `fns` give back, not the
/// values themselves (a run of `FnVal::ParamResult` in a callee): what a
/// closure or an item gives back (part `ret`, [`with_results`]); a run of a
/// value of a parameter of this body gives a result of it again; a value
/// that the analysis does not know gives a value that it does not know.
///
/// # Errors
///
/// The errors of [`with_results`].
fn results_of(
    cx: &mut Cx<'_>,
    r: Run0<'_>,
    fns: &BTreeSet<FnVal>,
) -> Result<BTreeSet<FnVal>, AlphaError> {
    let mut out = BTreeSet::new();
    let mut known = BTreeSet::new();
    for f in fns {
        match f {
            FnVal::Param(i) | FnVal::ParamResult(i) => {
                out.insert(FnVal::ParamResult(*i));
            }
            FnVal::Capture(_) | FnVal::Unknown => {
                out.insert(f.clone());
            }
            FnVal::Item(..) | FnVal::Closure(_) | FnVal::Made(_) => {
                known.insert(f.clone());
            }
        }
    }
    let all = with_results(cx, r, known.clone())?;
    out.extend(all.into_iter().filter(|f| !known.contains(f)));
    Ok(out)
}

/// The most levels of [`with_results`].
const RESULT_DEPTH: usize = 16;

/// The function values of capture `k` of closure `c` at run node `r`: the
/// values that its source in the maker reaches; for a closure that a callee
/// made, the values of the callee (`callee`) and code of a caller.
///
/// # Errors
///
/// The errors of α.
fn capture_fns(
    cx: &mut Cx<'_>,
    r: Run0<'_>,
    c: weft_ir::ClosureId,
    k: u32,
    made: bool,
    callee: &BTreeSet<FnVal>,
) -> Result<BTreeSet<FnVal>, AlphaError> {
    if made {
        let mut out: BTreeSet<FnVal> = callee
            .iter()
            .filter(|f| **f != FnVal::Made(c))
            .cloned()
            .collect();
        out.insert(FnVal::Unknown);
        return Ok(out);
    }
    let p = cx.p;
    let Some(decl) = p.closures.get(c.index()) else {
        return Ok(BTreeSet::from([FnVal::Unknown]));
    };
    match decl.captures.get(k as usize) {
        Some(cap) if cap.mode != weft_ir::CaptureMode::ByMove => {
            reach_fns(cx, decl.maker, r.st, &Operand::Copy(cap.source.clone()))
        }
        _ => Ok(BTreeSet::from([FnVal::Unknown])),
    }
}

/// The places that the environments of the function values of capture `k`
/// of closure `c` at run node `r` point into ([`capture_fns`]): what the
/// source of a `Kept` or `ByRef` capture in the maker reaches
/// ([`reach_refs`]); for a `ByMove` capture and for a closure that a callee
/// made, the places of the closure value itself (`callee`): it holds the
/// value of the capture.
///
/// # Errors
///
/// The errors of α.
fn capture_refs(
    cx: &mut Cx<'_>,
    r: Run0<'_>,
    c: weft_ir::ClosureId,
    k: u32,
    made: bool,
    callee: &BTreeSet<PlaceId>,
) -> Result<BTreeSet<PlaceId>, AlphaError> {
    let p = cx.p;
    let cap = p
        .closures
        .get(c.index())
        .and_then(|d| d.captures.get(k as usize).map(|cap| (d.maker, cap)));
    match cap {
        Some((maker, cap)) if !made && cap.mode != weft_ir::CaptureMode::ByMove => {
            let src = Operand::Copy(cap.source.clone());
            let mut out = reach_refs(cx, maker, r.st, &src)?;
            for fv in reach_fns(cx, maker, r.st, &src)? {
                out.extend(result_refs(cx, r, &fv, (&src, maker), 0)?);
            }
            Ok(out)
        }
        _ => Ok(callee.clone()),
    }
}

/// The places that the result of a run of the function value `fv` with no
/// arguments points into, if its result can be a closure that its body
/// makes (part `ret`): the environment of that closure (for example a
/// reference that the maker takes before it makes the closure). A value
/// that gives back a capture gives what a run of the capture gives back
/// ([`RESULT_DEPTH`] levels). `callee` is the operand that holds `fv` and
/// its body.
///
/// A closure that a maker gives back holds these places where a closure
/// or a callee gives back the result of a run of the maker (`|| mk()`,
/// `give(mk)`): hole of class N1 of the third review of the ABC preview
/// (`n1c/c05`, the made closure reads a reference that the maker took).
///
/// # Errors
///
/// The errors of σ and of α.
fn result_refs(
    cx: &mut Cx<'_>,
    r: Run0<'_>,
    fv: &FnVal,
    (callee, cb): (&Operand, BodyId),
    depth: usize,
) -> Result<BTreeSet<PlaceId>, AlphaError> {
    use super::summary::RetFn;
    let mut out = BTreeSet::new();
    let (FnVal::Closure(c) | FnVal::Made(c)) = fv else {
        return Ok(out);
    };
    if depth > RESULT_DEPTH {
        return Ok(out);
    }
    let Ok(summary) = cx.sums.closure(*c).cloned() else {
        return Ok(out);
    };
    if summary.ret.fns.is_empty() {
        return Ok(out);
    }
    let p = cx.p;
    let Some(decl) = p.closures.get(c.index()) else {
        return Ok(out);
    };
    let Some(cb_decl) = p.bodies.get(decl.body.index()) else {
        return Ok(out);
    };
    // A run with arguments is code of a caller in the body that runs it:
    // its result points into its wildcard places there.
    if cb_decl.params.len() > 1 {
        return Ok(out);
    }
    let Some(ret_ty) = cb_decl.locals.first().map(|d| d.ty) else {
        return Ok(out);
    };
    let sigma = if matches!(fv, FnVal::Made(_)) {
        super::apply::made_sigma(cx, r.body, r.st, *c, (callee, cb), Given::Args(&[]), r.inst)?
    } else {
        super::apply::closure_sigma(cx, r.body, r.st, *c, (callee, cb), Given::Args(&[]), r.inst)?
    };
    let v = super::apply::ret_value(cx, &summary, &sigma, ret_ty)?;
    v.places(&mut out);
    if matches!(fv, FnVal::Made(_)) {
        return Ok(out);
    }
    for rf in &summary.ret.fns {
        let RetFn::Capture(k) = rf else { continue };
        let Some(cap) = decl.captures.get(*k as usize) else {
            continue;
        };
        if cap.mode == weft_ir::CaptureMode::ByMove {
            continue;
        }
        let src = Operand::Copy(cap.source.clone());
        for g in reach_fns(cx, decl.maker, r.st, &src)? {
            out.extend(result_refs(cx, r, &g, (&src, decl.maker), depth + 1)?);
        }
    }
    Ok(out)
}

/// True if `place` of body `body` holds a `once` value.
///
/// A `once` value is a closure that moves a capture: the mode of its local
/// (`docs/ir.md` 5.22). A call of such a value moves it, also through a copy
/// of the local (B12-fn-once).
pub fn once_source(p: &Program, body: BodyId, place: &Place) -> bool {
    if !place.proj.is_empty() {
        return false;
    }
    let Ok(k) = key(p, body, place.local) else {
        return false;
    };
    p.bodies
        .get(k.0.index())
        .and_then(|b| b.locals.get(k.1.index()))
        .is_some_and(|d| d.props.once && d.kind != weft_ir::LocalKind::Env)
}

/// `Call` of a function value (stage F11): the summaries of the values that
/// the callee can be ([`value_out`]). The values that go into places of the
/// caller join there (a weak update); each captured variable that a closure
/// rebinds gets its new value; the moved arguments leave no value; the
/// result binds to `dest`.
///
/// # Errors
///
/// The errors of [`value_out`] and of α.
#[allow(clippy::too_many_arguments)]
fn call_value(
    cx: &mut Cx<'_>,
    body: BodyId,
    block: weft_ir::BlockId,
    st: &mut State,
    callee: &Operand,
    args: &[Operand],
    dest: &Place,
) -> Result<(), AlphaError> {
    let fns = args_linear(cx, body, st, args)?;
    let out = value_out(cx, body, block, st, callee, args, dest)?;
    apply_apps(cx, st, &out.apps, fns);
    let changed: Vec<PlaceId> = out
        .apps
        .iter()
        .flat_map(|a| a.muts.iter().map(|(q, _)| *q))
        .collect();
    store_fns(cx, body, st, args, &changed)?;
    bind_result(cx, body, st, args, dest, out.ret)
}

/// True if an argument of `args` can hold a linear value in state `st`.
///
/// # Errors
///
/// The errors of α.
fn args_linear(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    args: &[Operand],
) -> Result<bool, AlphaError> {
    for op in args {
        if operand(cx, body, st, op)?.flat().linear {
            return Ok(true);
        }
    }
    Ok(false)
}

/// The move paths of the places `changed` that can get a linear value.
///
/// A run node changes the places `changed`. The type of the local of such
/// a move path can hold a linear value. The callee can put a linear value into such a place and keep the
/// old value (`Vec.push`), so the local can hold a linear value after the
/// node, also if it held none before (an empty `Vec`).
pub fn can_get_linear(cx: &Cx<'_>, changed: &[PlaceId]) -> Vec<(Key, Vec<PathStep>)> {
    can_get_linear_with(cx, changed, true)
}

/// [`can_get_linear`] with the flag `fns`.
///
/// A local whose type has a function part, and cannot hold a linear value
/// by its type, counts only with `fns` (a linear closure can go there:
/// review of the ABC preview, false positive FP1).
pub fn can_get_linear_with(
    cx: &Cx<'_>,
    changed: &[PlaceId],
    fns: bool,
) -> Vec<(Key, Vec<PathStep>)> {
    let mut out: Vec<(Key, Vec<PathStep>)> = Vec::new();
    for &q in changed {
        let Some((k, path)) = cx.roots.path_of(cx.facts, q) else {
            continue;
        };
        // A local whose type has a function part can get a linear closure
        // (stage F11): the closure is linear by its value, not by its type.
        let linear =
            cx.p.bodies
                .get(k.0.index())
                .and_then(|b| b.locals.get(k.1.index()))
                .is_some_and(|d| {
                    crate::props::ir_maybe_linear(cx.tys, d.ty)
                        || (fns && crate::props::ir_has_fns(cx.tys, d.ty))
                });
        if linear && !out.contains(&(k, path.clone())) {
            out.push((k, path));
        }
    }
    out
}

/// `Perform` through the capability of a caller: an operation of a caller
/// (`super::unknown`). The moved arguments leave no value; the result binds
/// to `dest`.
///
/// # Errors
///
/// The errors of [`super::unknown::op_of_caller`] and of α.
#[allow(clippy::too_many_arguments)]
fn perform_row(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    e: weft_ir::EffectId,
    op: weft_ir::OpIdx,
    args: &[Operand],
    dest: &Place,
) -> Result<(), AlphaError> {
    let out = super::unknown::op_of_caller(cx, body, st, e, op, args)?;
    let lent: Vec<PlaceId> = out.args.iter().flatten().copied().collect();
    for (k, path) in can_get_linear(cx, &lent) {
        st.add(k, &path, &Tree::leaf(AbsVal::of_type(true)));
    }
    bind_result(cx, body, st, args, dest, out.ret)
}

/// The result `ret` of a run node as a value of the type of `dest`.
///
/// A type that holds no reference and no function value gets none. The
/// values of a run can be more than one function value, and their results
/// join (`with_results` keeps the maker too), so the `()` result of `g()`
/// could point into the environment of a closure that a maker gives back
/// (the W0204 class of the third review of the ABC preview).
///
/// # Errors
///
/// The errors of α.
pub fn typed_result(
    cx: &mut Cx<'_>,
    body: BodyId,
    dest: &Place,
    mut ret: Tree,
) -> Result<Tree, AlphaError> {
    let t = place_ty(cx, body, dest)?;
    let pr = ir_props(cx.tys, t);
    // A function value holds its environment, so a type with a function
    // part keeps its references.
    if !pr.generic && !pr.holds_refs && !pr.callable && !crate::props::ir_has_fns(cx.tys, t) {
        ret.map_refs(&mut |r| {
            let had = !r.is_empty();
            r.clear();
            had
        });
        no_fns(&mut ret);
    }
    Ok(ret)
}

/// Removes the function values of each part of `t`.
fn no_fns(t: &mut Tree) {
    t.top.fns.clear();
    for k in t.kids.values_mut() {
        no_fns(k);
    }
}

/// The result `ret` of a run node with the arguments `args` binds to
/// `dest`: the moved arguments leave no value, then a move path gets the
/// value (a strong update), and another place joins it (a weak update).
///
/// # Errors
///
/// The errors of α.
pub(crate) fn bind_result(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    args: &[Operand],
    dest: &Place,
    ret: Tree,
) -> Result<(), AlphaError> {
    let ret = typed_result(cx, body, dest, ret)?;
    let target = match move_path(cx.p, body, dest)? {
        Some(d) => Some(d),
        None => kept_whole(cx, body, st, dest)?.map(|k| (k, Vec::new())),
    };
    let a = if target.is_some() {
        None
    } else {
        Some(alpha(cx, body, st, dest)?)
    };
    moves(cx.p, body, st, args)?;
    if let Some((k, path)) = target {
        st.write(k, &path, ret);
        return Ok(());
    }
    let flat = Tree::leaf(ret.flat());
    let targets: BTreeSet<(Key, Vec<PathStep>)> = a
        .iter()
        .flat_map(|a| a.places.iter())
        .filter_map(|&q| cx.roots.path_of(cx.facts, q))
        .collect();
    for (k, path) in targets {
        st.add(k, &path, &flat);
    }
    if let Some(a) = &a {
        let refs: Vec<PlaceId> = flat.top.refs.iter().copied().collect();
        store_heap(cx.facts, cx.roots, st, &a.places, &refs, &flat.top.fns);
    }
    Ok(())
}
