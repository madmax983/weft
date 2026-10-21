//! The transfer functions of the analysis (`docs/ir.md` 6.6).
//!
//! There is one function for each statement kind and for each terminator
//! kind that stage F3 knows (`Switch`, `Goto`, `Return`, and the terminators
//! with no effect on the state). A terminator that runs another body applies
//! its summary: it comes with stage F5, so [`term`] gives
//! [`AlphaError::Later`] for it.
//!
//! - `Ref(q)` gives `refs = α(q)` and the handle places of each `Deref(Rc)`
//!   on `q`.
//! - `Use(copy q)` gives the value at `q`, with the structure of its move
//!   paths. `Use(move q)` gives it too, and then `q` has no value.
//! - An aggregate gives the values of its operands as its parts.
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
}

/// The key of local `l` of body `body`: the site local of an upvar local.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if the local does not exist.
pub fn key(p: &Program, body: BodyId, l: LocalId) -> Result<Key, AlphaError> {
    alpha::owner_local(p, body, l)
}

/// The place as a move path: its local and its steps, if each projection is
/// a field or a variant. `None` for a place through a dereference, an index,
/// the elements or a split.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if the local does not exist.
pub fn move_path(
    p: &Program,
    body: BodyId,
    place: &Place,
) -> Result<Option<(Key, Vec<PathStep>)>, AlphaError> {
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
) -> Result<Vec<PlaceId>, AlphaError> {
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
            Ok(vec![facts.wildcard(h)])
        }
        Some(Role::Group) => Err(AlphaError::Later(
            "a reference in an `rc` object (stored values, stage F13)",
        )),
        None => Err(AlphaError::BadPlace(
            "a place with no root of the component".to_string(),
        )),
    }
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
        &mut |facts, roots, at| held_at(p, st, facts, roots, at),
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
    let t = place_ty(cx, body, place)?;
    let props = ir_props(cx.tys, t);
    let mut v = AbsVal::of_type(props.linear);
    if props.holds_refs {
        let a = alpha(cx, body, st, place)?;
        for &at in &a.places {
            v.refs.extend(held_at(cx.p, st, cx.facts, cx.roots, at)?);
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
/// The errors of α, and [`AlphaError::Later`] for a closure aggregate
/// (stage F11) and an iterator (stage F10).
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
        | Rvalue::Concat(_) => Ok(Tree::leaf(AbsVal::plain())),
        Rvalue::Aggregate(kind, ops) => aggregate(cx, body, st, kind, ops),
        Rvalue::Iter(_) => Err(AlphaError::Later("an iterator (stage F10)")),
    }
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
        AggKind::Closure(_) => Err(AlphaError::Later("a closure (stage F11)")),
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
    let dest = move_path(cx.p, body, place)?;
    let a = if dest.is_some() {
        None
    } else {
        Some(alpha(cx, body, st, place)?)
    };
    moves(cx.p, body, st, rvalue_operands(rv))?;
    if let Some((k, path)) = dest {
        st.write(k, &path, v);
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

/// The transfer of a terminator, on its normal edges.
///
/// # Errors
///
/// Returns [`AlphaError::Later`] for a terminator that runs another body or
/// a task (stages F5 and later).
pub fn term(cx: &mut Cx<'_>, body: BodyId, st: &mut State, t: &TermKind) -> Result<(), AlphaError> {
    match t {
        TermKind::Goto(_) => goto(st),
        TermKind::Switch { on, .. } => switch(cx.p, body, st, on),
        TermKind::Return => ret(st),
        TermKind::Unreachable | TermKind::UnwindExit => Ok(()),
        TermKind::Assert { cond, .. } => moves(cx.p, body, st, [cond]),
        TermKind::Call { .. } | TermKind::Perform { .. } | TermKind::Resume { .. } => {
            Err(AlphaError::Later("a call (summaries, stage F5)"))
        }
        TermKind::IterNext { .. } => Err(AlphaError::Later("an iterator (stage F10)")),
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
