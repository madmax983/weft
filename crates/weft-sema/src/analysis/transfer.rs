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

use std::collections::BTreeSet;

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
/// Returns [`AlphaError::Later`] for a reference in an `rc` object (stored
/// values, stage F13), and [`AlphaError::BadPlace`] for a place that no root
/// of the component has.
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
        Some(Role::Group) => Err(AlphaError::Later(
            "a reference in an `rc` object (stored values, stage F13)",
        )),
        Some(Role::Frame(_)) => Err(AlphaError::Later(
            "a reference in a local of a callee (stage F14)",
        )),
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
    let a = norm(at);
    let mut out = Vec::new();
    for (q, refs) in st.behind() {
        let b = norm(*q);
        if below(a, b) || below(b, a) {
            out.extend(refs.iter().copied());
        }
    }
    out
}

/// Each place of `places` that no local of the component owns gets the
/// references `refs` in its heap slot (a weak update, `docs/ir.md` 6.6).
fn store_heap(
    facts: &FnFacts,
    roots: &Roots,
    st: &mut State,
    places: &[PlaceId],
    refs: &[PlaceId],
) {
    if refs.is_empty() {
        return;
    }
    for &q in places {
        if roots.path_of(facts, q).is_none() {
            st.store_behind(q, refs.iter().copied());
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
                v.caps.extend(f.caps);
                v.tasks.extend(f.tasks);
                v.linear |= f.linear;
            }
            weft_ir::CaptureMode::Kept | weft_ir::CaptureMode::Cap | weft_ir::CaptureMode::Kont => {
            }
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

/// `Dead(l)`: the local has no value after its end.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if the local does not exist.
pub fn dead(p: &Program, body: BodyId, st: &mut State, l: LocalId) -> Result<(), AlphaError> {
    st.clear(key(p, body, l)?, &[]);
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
        store_heap(cx.facts, cx.roots, st, &a.places, &refs);
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
        } => call(cx, body, block, st, *f, targs, args, dest),
        TermKind::Call {
            callee: weft_ir::Callee::Value(f),
            args,
            dest,
            ..
        } => call_value(cx, body, block, st, f, args, dest),
        TermKind::Perform {
            cap: weft_ir::CapOperand::Row(e),
            op,
            args,
            dest,
            ..
        } => perform_row(cx, body, st, *e, *op, args, dest),
        TermKind::Perform { .. } => Err(AlphaError::Later(
            "a perform through a capability of a handler (stage F14)",
        )),
        TermKind::Resume { .. } => Err(AlphaError::Later("a continuation (stage F16)")),
        TermKind::IterNext { iter, dest, .. } => iter_next(cx, body, st, iter, dest),
        TermKind::Handle { .. } => Err(AlphaError::Later("a handler (stage F14)")),
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
    if summary.ret_in_frame() {
        sigma.frame = Some(cx.roots.frame(cx.facts, inst, &decl.name));
    }
    let ret_ty = place_ty(cx, body, dest)?;
    let ret = super::apply::ret_value(cx, &summary, &sigma, ret_ty)?;
    let muts = super::apply::muts(cx, &summary, &sigma)?;
    let stores = super::apply::stores(cx, &summary, &sigma, &muts)?;
    Ok(CallOut {
        sigma,
        summary,
        ret,
        muts,
        stores,
    })
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
    let out = call_out(cx, body, block, st, f, targs, args, dest)?;
    for (q, refs) in &out.stores {
        if let Some((k, path)) = cx.roots.path_of(cx.facts, *q) {
            st.add(k, &path, &Tree::leaf(AbsVal::refs(refs.iter().copied())));
        } else {
            st.store_behind(*q, refs.iter().copied());
        }
    }
    let changed: Vec<PlaceId> = out.muts.iter().map(|(q, _)| *q).collect();
    for (k, path) in can_get_linear(cx, &changed) {
        st.add(k, &path, &Tree::leaf(AbsVal::of_type(true)));
    }
    bind_result(cx, body, st, args, dest, out.ret)
}

/// The most closures that a run node applies through the captures that run
/// each other (`f` runs `g`, which runs `h`): a deeper chain is a later
/// stage (F12).
const RUN_DEPTH: usize = 8;

/// One summary that a run node of a function value applies (`docs/ir.md`
/// 6.7): of a value that the callee can be, or of a value that such a
/// closure runs through a capture (part `runs`).
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
    /// The variables that the run uses (part `uses`): the source of each
    /// `Kept` and `ByRef` capture, in the body of its maker.
    pub uses: Vec<(BodyId, Place)>,
    /// The places of `once` values that the run moves: the source of a
    /// capture that holds a `once` closure and that the run calls.
    pub once: Vec<(BodyId, Place)>,
    /// The run happens again at the `Ret` node (a capture that the closure
    /// runs `Many` times, OR3).
    pub again: bool,
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
}

/// True if body `body` is a closure body whose facts are in the terms of
/// its interface: the summary of the closure (`super::summarize::closure`).
pub fn in_interface(cx: &Cx<'_>, body: BodyId) -> bool {
    cx.p.closure_of(body).is_some() && !cx.roots.is_instantiated(body)
}

/// The run node of a `Call` of the function value `callee` of block `block`
/// of body `body`, in state `st` before it (`docs/ir.md` 6.7).
///
/// The value can be function items and closures of the component: each one
/// applies its summary, and a closure also applies the summary of each
/// value that it runs through a capture (part `runs`). In the summary of a
/// closure body, a call of a capture is in the part `runs`: it applies
/// nothing here.
///
/// # Errors
///
/// Returns [`AlphaError::Later`] for a value that the analysis does not
/// know (a parameter, a field, the result of a call: stage F12), and the
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
    if let Operand::Copy(q) | Operand::Move(q) = callee {
        if q.proj.len() == 1
            && alpha::env_capture(cx.p, body, q).is_some()
            && in_interface(cx, body)
        {
            // The summary of the closure has the run (`runs`): the run node
            // of the closure applies the value of the capture.
            let props = ir_props(cx.tys, ret_ty);
            if props.holds_refs || cx.tys.mentions_fn(ret_ty) {
                return Err(AlphaError::Later(
                    "a run of a captured function value with a reference in its result (stage F12)",
                ));
            }
            for a in args {
                let t = match a {
                    Operand::Copy(x) | Operand::Move(x) => place_ty(cx, body, x)?,
                    Operand::Const(_) => continue,
                };
                if ir_props(cx.tys, t).holds_refs || cx.tys.mentions_fn(t) {
                    return Err(AlphaError::Later(
                        "a run of a captured function value with a reference argument (stage F12)",
                    ));
                }
            }
            return Ok(ValueOut {
                apps: Vec::new(),
                ret: Tree::leaf(AbsVal::of_type(props.linear)),
            });
        }
    }
    let fns = operand(cx, body, st, callee)?.flat().fns;
    let inst = run_inst(body, block);
    let mut apps = Vec::new();
    let mut ret: Option<Tree> = None;
    if fns.is_empty() {
        return Err(AlphaError::Later(
            "a call of a function value that the body does not know (stage F12)",
        ));
    }
    for fv in &fns {
        let start = apps.len();
        apply_value(
            cx,
            body,
            block,
            st,
            fv,
            callee,
            args,
            Some(ret_ty),
            inst,
            0,
            &mut apps,
        )?;
        if let Some(r) = apps.get(start).and_then(|a| a.ret.clone()) {
            ret = Some(match ret {
                Some(t) => Tree::leaf(t.flat().joined(&r.flat())),
                None => r,
            });
        }
    }
    Ok(ValueOut {
        apps,
        ret: ret.unwrap_or_else(|| Tree::leaf(AbsVal::plain())),
    })
}

/// Applies the function value `fv` at the run node `inst` of body `body`
/// (state `st`): its summary, and for a closure the summary of each value
/// that it runs through a capture, at depth `depth`. `ret_ty` is the type of
/// the result of a value of the callee itself (`None` for a run through a
/// capture). The summaries go to `out`, the value itself first.
#[allow(clippy::too_many_arguments)]
fn apply_value(
    cx: &mut Cx<'_>,
    body: BodyId,
    block: weft_ir::BlockId,
    st: &State,
    fv: &FnVal,
    callee: &Operand,
    args: &[Operand],
    ret_ty: Option<TyId>,
    inst: u32,
    depth: usize,
    out: &mut Vec<Applied>,
) -> Result<(), AlphaError> {
    use super::summary::{IPlace, IRoot};
    if depth > RUN_DEPTH {
        return Err(AlphaError::Later(
            "a chain of closures that run each other deeper than eight (stage F12)",
        ));
    }
    let p = cx.p;
    match fv {
        FnVal::Unknown => Err(AlphaError::Later(
            "a call of a function value that the body does not know (stage F12)",
        )),
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
            let mut sigma = super::apply::sigma(cx, body, st, decl, targs, args, inst)?;
            sigma.cyclic = cx.cycles.has(body, block);
            if summary.ret_in_frame() {
                sigma.frame = Some(cx.roots.frame(cx.facts, inst, &decl.name));
            }
            let ret = match ret_ty {
                Some(t) => Some(super::apply::ret_value(cx, &summary, &sigma, t)?),
                None => None,
            };
            let muts = super::apply::muts(cx, &summary, &sigma)?;
            let stores = super::apply::stores(cx, &summary, &sigma, &muts)?;
            let name = decl
                .name
                .rsplit('.')
                .next()
                .unwrap_or(&decl.name)
                .to_string();
            out.push(Applied {
                kind: super::apply::RunKind::Item,
                name,
                sigma,
                summary,
                ret,
                muts,
                stores,
                rebinds: Vec::new(),
                uses: Vec::new(),
                once: Vec::new(),
                again: false,
            });
            Ok(())
        }
        FnVal::Closure(c) => {
            let summary = cx.sums.closure(*c).map_err(AlphaError::Later)?.clone();
            let decl = p
                .closures
                .get(c.index())
                .ok_or_else(|| AlphaError::BadPlace(format!("no closure c{}", c.0)))?;
            let mut sigma = super::apply::closure_sigma(cx, body, st, *c, callee, args, inst)?;
            sigma.cyclic = cx.cycles.has(body, block);
            if summary.ret_in_frame() {
                sigma.frame = Some(cx.roots.frame(cx.facts, inst, "the closure"));
            }
            let ret = match ret_ty {
                Some(t) => Some(super::apply::ret_value(cx, &summary, &sigma, t)?),
                None => None,
            };
            let muts = super::apply::muts(cx, &summary, &sigma)?;
            // The new value of each capture that the body rebinds on each
            // path: a whole local of the maker gets it (a strong update).
            let mut rebinds = Vec::new();
            let mut whole: Vec<u32> = Vec::new();
            for &k in &summary.rebinds {
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
                if ty.is_some_and(|t| cx.tys.mentions_fn(t)) {
                    v.fns.insert(FnVal::Unknown);
                }
                let root = IPlace::root(IRoot::Capture(k));
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
            let uses: Vec<(BodyId, Place)> = summary
                .uses
                .iter()
                .filter_map(|&k| decl.captures.get(k as usize))
                .filter(|cap| {
                    matches!(
                        cap.mode,
                        weft_ir::CaptureMode::Kept | weft_ir::CaptureMode::ByRef
                    )
                })
                .map(|cap| (decl.maker, cap.source.clone()))
                .collect();
            let runs = summary.runs.clone();
            out.push(Applied {
                kind: super::apply::RunKind::Closure,
                name: "the closure".to_string(),
                sigma,
                summary,
                ret,
                muts,
                stores,
                rebinds,
                uses,
                once: Vec::new(),
                again: false,
            });
            // Each value that the closure runs through a capture: the value
            // of the variable of the capture at the run node.
            for run in runs.iter().filter(|r| r.capture) {
                let Some(cap) = decl.captures.get(run.param as usize) else {
                    continue;
                };
                if cap.mode != weft_ir::CaptureMode::Kept {
                    return Err(AlphaError::Later(
                        "a run of a function value that a closure owns (stage F12)",
                    ));
                }
                let v = place_value(cx, decl.maker, st, &cap.source)?.flat();
                if v.fns.is_empty() {
                    return Err(AlphaError::Later(
                        "a run of a captured function value that the body does not know (stage F12)",
                    ));
                }
                let src = Operand::Copy(cap.source.clone());
                let once = once_source(p, decl.maker, &cap.source);
                for g in &v.fns {
                    let start = out.len();
                    apply_value(
                        cx,
                        decl.maker,
                        block,
                        st,
                        g,
                        &src,
                        &[],
                        None,
                        inst,
                        depth + 1,
                        out,
                    )?;
                    if let Some(first) = out.get_mut(start) {
                        if once {
                            first.once.push((decl.maker, cap.source.clone()));
                        }
                    }
                    if run.many {
                        for a in out.iter_mut().skip(start) {
                            a.again = true;
                        }
                    }
                }
            }
            Ok(())
        }
    }
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
    let out = value_out(cx, body, block, st, callee, args, dest)?;
    for app in &out.apps {
        for (q, refs) in &app.stores {
            if let Some((k, path)) = cx.roots.path_of(cx.facts, *q) {
                st.add(k, &path, &Tree::leaf(AbsVal::refs(refs.iter().copied())));
            } else {
                st.store_behind(*q, refs.iter().copied());
            }
        }
        let changed: Vec<PlaceId> = app.muts.iter().map(|(q, _)| *q).collect();
        for (k, path) in can_get_linear(cx, &changed) {
            st.add(k, &path, &Tree::leaf(AbsVal::of_type(true)));
        }
        for (k, v) in &app.rebinds {
            st.write(*k, &[], v.clone());
        }
    }
    bind_result(cx, body, st, args, dest, out.ret)
}

/// The move paths of the places `changed` that can get a linear value.
///
/// A run node changes the places `changed`. The type of the local of such
/// a move path can hold a linear value. The callee can put a linear value into such a place and keep the
/// old value (`Vec.push`), so the local can hold a linear value after the
/// node, also if it held none before (an empty `Vec`).
pub fn can_get_linear(cx: &Cx<'_>, changed: &[PlaceId]) -> Vec<(Key, Vec<PathStep>)> {
    let mut out: Vec<(Key, Vec<PathStep>)> = Vec::new();
    for &q in changed {
        let Some((k, path)) = cx.roots.path_of(cx.facts, q) else {
            continue;
        };
        let linear =
            cx.p.bodies
                .get(k.0.index())
                .and_then(|b| b.locals.get(k.1.index()))
                .is_some_and(|d| crate::props::ir_maybe_linear(cx.tys, d.ty));
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

/// The result `ret` of a run node with the arguments `args` binds to
/// `dest`: the moved arguments leave no value, then a move path gets the
/// value (a strong update), and another place joins it (a weak update).
///
/// # Errors
///
/// The errors of α.
fn bind_result(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    args: &[Operand],
    dest: &Place,
    ret: Tree,
) -> Result<(), AlphaError> {
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
        store_heap(cx.facts, cx.roots, st, &a.places, &refs);
    }
    Ok(())
}
