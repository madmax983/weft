//! The templates of the instructions (`docs/ir.md` 6.4).
//!
//! Each statement kind and each terminator phase has one function here. A
//! template reads the state of the analysis before its node (`crate::analysis`)
//! and writes the facts of the node. No other code writes node facts: the
//! relations with no node come from the declarations (`super::decls`), and
//! the edges come from the node table (`super::nodes`).
//!
//! Stage F4 has the templates of the statements, of the operands, and of the
//! terminators that run no other body: `Goto`, `Switch`, `Return`,
//! `Unreachable`, `UnwindExit` and `Assert`. Stage F5 adds the phases of a
//! `Call` of a function item ([`call`]): `Main`, `Ret` and `FrameEnd`, with
//! the summary of the callee (`crate::analysis::apply`). The rules of a reference
//! fragment (a borrow, a copy of a reference, a read and a write through a
//! reference) are pure functions in `super::kernel`.
//!
//! Notation of the comments: `n` is the node; `v(q)` are the variables of the
//! move paths that overlap place `q` (`S` of the base, the `H` and `U`
//! variables at, above or below the move path of `q`), and of the index
//! locals of `q`.

use std::collections::BTreeMap;

use weft_facts::{FnFacts, NodeId, PlaceId, RefKind, RefSite, Span, VarId};
use weft_ir::ty::AdtKind;
use weft_ir::{
    BodyId, LocalId, LocalKind, Operand, Place, Program, Proj, Rvalue, StmtKind, TermKind, Ty,
    TyId, TyTable, UnwindAction,
};

use super::alpha::{Alpha, AlphaError, Roots};
use super::kernel::{self, Access, Frag};
use super::vars::{PartKind, VarKey, Vars};
use crate::analysis::transfer::{self, Cx};
use crate::analysis::{Key, PathStep, State, Tree};
use crate::irbuild::subst;
use crate::props::ir_props;

/// The result of a template.
pub type R = Result<(), AlphaError>;

/// What the templates of one body read and write.
pub struct Em<'a> {
    /// The program.
    pub p: &'a Program,
    /// The program of the analysis: the place fields of the structs.
    pub sema: &'a crate::Program,
    /// The types.
    pub tys: &'a mut TyTable,
    /// The facts of the component.
    pub facts: &'a mut FnFacts,
    /// The roots of the component.
    pub roots: &'a mut Roots,
    /// The variables of the component.
    pub vars: &'a Vars,
    /// The body of the nodes.
    pub body: BodyId,
    /// The node is on a cleanup path.
    pub cleanup: bool,
    /// The places that the signature states for a returned reference, if it
    /// states them.
    pub ret_places: Option<&'a [PlaceId]>,
    /// The `@ uniq` mode of each value of each variable, so far: the meet.
    pub uniq: &'a mut BTreeMap<VarId, bool>,
    /// The local whose `S` the accesses of the node do not use: a pattern
    /// moves its parts one at a time, and its later parts are not a use of
    /// a moved value (the old lowering moves the whole value once).
    pub skip_s: Option<Key>,
    /// The summary of each function that a call can run.
    pub sums: &'a crate::analysis::Summaries,
    /// The references that the body puts behind a reference parameter or
    /// into an `rc` object (the W0204 store check, `docs/ir.md` 6.9).
    pub stored: Vec<Stored>,
}

/// References that a node puts into a place that a caller keeps: behind a
/// reference parameter, or into an `rc` object.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stored {
    /// The place that gets the references.
    pub into: PlaceId,
    /// The places that the references point into.
    pub refs: Vec<PlaceId>,
    /// The span of the node.
    pub span: Span,
}

/// The span of the facts for an IR span.
const fn span(s: weft_ir::Span) -> Span {
    Span { lo: s.lo, hi: s.hi }
}

/// The steps of a move path, if each projection is a field or a variant.
fn steps(proj: &[Proj]) -> Option<Vec<PathStep>> {
    proj.iter()
        .map(|p| match p {
            Proj::Field(f) => Some(PathStep::Field(f.0)),
            Proj::Variant(v) => Some(PathStep::Variant(v.0)),
            _ => None,
        })
        .collect()
}

/// The projections of `place` up to the first one that is not a field or a
/// variant: the move path of the local that the place starts in.
fn move_prefix(place: &Place) -> &[Proj] {
    let end = place
        .proj
        .iter()
        .position(|p| !matches!(p, Proj::Field(_) | Proj::Variant(_)))
        .unwrap_or(place.proj.len());
    place.proj.get(..end).unwrap_or(&[])
}

/// The projections of `place` up to the first one that is not a field, a
/// variant or a dereference of a `Box`: the path that the local owns, with
/// the boxed values in it.
fn owned_prefix(place: &Place) -> &[Proj] {
    let end = place
        .proj
        .iter()
        .position(|p| {
            !matches!(
                p,
                Proj::Field(_) | Proj::Variant(_) | Proj::Deref(weft_ir::DerefKind::Box)
            )
        })
        .unwrap_or(place.proj.len());
    place.proj.get(..end).unwrap_or(&[])
}

/// True if `a` is a prefix of `b` (or equal to it).
fn is_prefix<T: PartialEq>(a: &[T], b: &[T]) -> bool {
    a.len() <= b.len() && a.iter().zip(b).all(|(x, y)| x == y)
}

impl Em<'_> {
    /// The context of the transfer functions.
    const fn cx(&mut self) -> Cx<'_> {
        Cx {
            p: self.p,
            tys: self.tys,
            facts: self.facts,
            roots: self.roots,
            sums: self.sums,
        }
    }

    /// The key of local `l` of the body.
    fn key(&self, l: LocalId) -> Result<Key, AlphaError> {
        transfer::key(self.p, self.body, l)
    }

    /// `S` of the local with key `k`.
    fn s_var(&self, k: Key) -> Option<VarId> {
        self.vars.get(&VarKey::S(k.0, k.1))
    }

    /// True if the local with key `k` is a source local: a variable of the
    /// program or a parameter.
    fn source_local(&self, k: Key) -> bool {
        self.p
            .bodies
            .get(k.0.index())
            .and_then(|b| b.locals.get(k.1.index()))
            .is_some_and(|d| matches!(d.kind, LocalKind::User | LocalKind::Param(_)))
    }

    /// α of `place` with the state `st`.
    fn alpha(&mut self, st: &State, place: &Place) -> Result<Alpha, AlphaError> {
        let body = self.body;
        transfer::alpha(&mut self.cx(), body, st, place)
    }

    /// The type of `place`.
    fn place_ty(&mut self, place: &Place) -> Option<TyId> {
        super::alpha::place_ty(self.p, self.tys, self.body, place)
    }

    /// The variables `v(q)` of `place`: `S` of its base, the `H` and `U`
    /// variables that overlap its move path, and `S` of its index locals.
    fn vars_of(&self, place: &Place) -> Result<Vec<VarId>, AlphaError> {
        self.vars_with(place, true)
    }

    /// The variables `v(q)` of `place`; with `unset` false, with no `U`
    /// variable (a move of a whole value that does not read its place
    /// fields).
    fn vars_with(&self, place: &Place, unset: bool) -> Result<Vec<VarId>, AlphaError> {
        let k = self.key(place.local)?;
        let mut out: Vec<VarId> = if self.skip_s == Some(k) {
            Vec::new()
        } else {
            self.s_var(k).into_iter().collect()
        };
        let prefix = move_prefix(place);
        // A place field of a boxed value is a path through `Deref(Box)`
        // (`docs/ir.md` 5.8): a `U` variable compares with the owned path.
        let owned = owned_prefix(place);
        for (kind, proj, v) in self.vars.parts_of(k.0, k.1) {
            if *kind == PartKind::U && !unset {
                continue;
            }
            let at = if *kind == PartKind::U { owned } else { prefix };
            if is_prefix(proj, at) || is_prefix(at, proj) {
                out.push(*v);
            }
        }
        for pr in &place.proj {
            if let Proj::Index(i) = pr {
                out.extend(self.s_var(self.key(*i)?));
            }
        }
        out.sort();
        out.dedup();
        Ok(out)
    }

    /// What a template knows about an access of `place` in state `st`.
    /// With `root`, the access reads the root of a source local.
    fn access(
        &mut self,
        st: &State,
        place: &Place,
        root: bool,
    ) -> Result<(Access, Alpha), AlphaError> {
        let a = self.alpha(st, place)?;
        let mut ptrs = a.ptrs.clone();
        for pr in &place.proj {
            if let Proj::Index(i) = pr {
                ptrs.push(self.root_of(*i)?);
            }
        }
        let k = self.key(place.local)?;
        let root = if root && self.source_local(k) {
            Some(self.root_of(place.local)?)
        } else {
            None
        };
        // The variables of each pointer local on the path (`docs/ir.md` 6.4,
        // operands): a pointer in a place of another local is a use of that
        // local.
        let mut vars = self.vars_of(place)?;
        for &q in &a.ptrs {
            vars.extend(self.owner_vars(q, k));
        }
        vars.sort();
        vars.dedup();
        let acc = Access {
            vars,
            places: a.places.clone(),
            ptrs,
            root,
        };
        Ok((acc, a))
    }

    /// The variables of the move path of the local that owns fact place
    /// `q`, if it is not the local with key `base`: `S` of the local, and the
    /// `H` and `U` variables at, above or below the path.
    fn owner_vars(&self, q: PlaceId, base: Key) -> Vec<VarId> {
        let Some((k, path)) = self.roots.path_of(self.facts, q) else {
            return Vec::new();
        };
        if k == base {
            return Vec::new();
        }
        let mut out: Vec<VarId> = if self.skip_s == Some(k) {
            Vec::new()
        } else {
            self.s_var(k).into_iter().collect()
        };
        for (_, proj, v) in self.vars.parts_of(k.0, k.1) {
            if let Some(s) = steps(proj) {
                if is_prefix(&s, &path) || is_prefix(&path, &s) {
                    out.push(*v);
                }
            }
        }
        out
    }

    /// The root place of the value of local `l`.
    fn root_of(&mut self, l: LocalId) -> Result<PlaceId, AlphaError> {
        self.roots.local(self.p, self.tys, self.facts, self.body, l)
    }

    /// Puts the facts of fragment `f` at node `n`.
    fn apply(&mut self, n: NodeId, f: Frag) {
        let facts = &mut *self.facts;
        facts.uses.extend(f.uses.into_iter().map(|v| (v, n)));
        facts.reads_at.extend(f.reads.into_iter().map(|p| (n, p)));
        facts
            .mutates_at
            .extend(f.mutates.into_iter().map(|p| (n, p)));
        facts.points_into.extend(f.points_into);
        facts
            .writes_via
            .extend(f.writes_via.into_iter().map(|v| (n, v)));
    }

    /// The `H` variables of the local with key `k` at or below the move path
    /// `path`, with their paths relative to `path`.
    fn h_below(&self, k: Key, path: &[PathStep]) -> Vec<(Vec<PathStep>, VarId)> {
        let mut out = Vec::new();
        for (kind, proj, v) in self.vars.parts_of(k.0, k.1) {
            if *kind != PartKind::H {
                continue;
            }
            if let Some(s) = steps(proj) {
                if is_prefix(path, &s) {
                    out.push((s.get(path.len()..).unwrap_or(&[]).to_vec(), *v));
                }
            }
        }
        out
    }

    /// The facts of a new value `v` of the move path `path` of the local
    /// with key `k`: `points_into` of each `H` variable at or below the path,
    /// with the places of its part. The places of the parts with no `H`
    /// variable go to `whole` (`S(l)`, or the variable above the path).
    fn give_value(&mut self, k: Key, path: &[PathStep], v: &Tree, whole: Option<VarId>) {
        let hs = self.h_below(k, path);
        let all: Vec<&[PathStep]> = hs.iter().map(|(p, _)| p.as_slice()).collect();
        for (rel, var) in &hs {
            let deeper: Vec<&[PathStep]> = hs
                .iter()
                .filter(|(o, _)| o.len() > rel.len() && is_prefix(rel, o))
                .filter_map(|(o, _)| o.get(rel.len()..))
                .collect();
            let refs = v.get(rel).flat_without(&deeper).refs;
            let frag = kernel::copy_ref(&[*var], &refs.into_iter().collect::<Vec<_>>());
            self.facts.points_into.extend(frag.points_into);
        }
        if let Some(w) = whole {
            let refs = v.flat_without(&all).refs;
            let frag = kernel::copy_ref(&[w], &refs.into_iter().collect::<Vec<_>>());
            self.facts.points_into.extend(frag.points_into);
        }
    }

    /// Meets the `@ uniq` mode of a new value of `var`.
    fn meet_uniq(&mut self, var: VarId, uniq: bool) {
        let m = self.uniq.entry(var).or_insert(true);
        *m &= uniq;
    }
}

/// True if a part of type `t` other than the part at `proj` can hold a
/// linear value: the rest of a value after a move of the part (the R3a
/// encoding, `rest_linear`).
fn rest_linear(tys: &mut TyTable, t: TyId, proj: &[Proj]) -> bool {
    let Some((first, rest)) = proj.split_first() else {
        return false;
    };
    let others = |tys: &TyTable, ts: &[TyId], i: usize| {
        ts.iter()
            .enumerate()
            .any(|(j, &x)| j != i && ir_props(tys, x).linear)
    };
    match (tys.try_get(t).cloned(), first) {
        (Some(Ty::Tuple(ts)), Proj::Field(f)) => {
            let i = f.index();
            others(tys, &ts, i) || ts.get(i).is_some_and(|&x| rest_linear(tys, x, rest))
        }
        (Some(Ty::Adt(a, args)), Proj::Field(f)) => {
            let Some(d) = tys.adts().get(a.index()).cloned() else {
                return true;
            };
            match &d.kind {
                AdtKind::Struct(fs) => {
                    let ts: Vec<TyId> = fs.iter().map(|x| subst(tys, x.ty, &args)).collect();
                    let i = f.index();
                    d.linear
                        || others(tys, &ts, i)
                        || ts.get(i).is_some_and(|&x| rest_linear(tys, x, rest))
                }
                _ => ir_props(tys, t).linear,
            }
        }
        (Some(Ty::Adt(a, args)), Proj::Variant(v)) => {
            let Some(d) = tys.adts().get(a.index()).cloned() else {
                return true;
            };
            match &d.kind {
                AdtKind::Enum(vs) => {
                    let ts: Vec<TyId> = vs
                        .get(v.index())
                        .map(|x| x.fields.iter().map(|&y| subst(tys, y, &args)).collect())
                        .unwrap_or_default();
                    d.linear
                        || match rest.split_first() {
                            Some((Proj::Field(k), more)) => {
                                let i = k.index();
                                others(tys, &ts, i)
                                    || ts.get(i).is_some_and(|&x| rest_linear(tys, x, more))
                            }
                            _ => false,
                        }
                }
                _ => ir_props(tys, t).linear,
            }
        }
        _ => ir_props(tys, t).linear,
    }
}

// ------------------------------------------------------------ operands

/// An operand at node `n`.
///
/// `copy q` and `move q` use `v(q)` and the
/// variables of the pointer locals of `q`, read α of `q`, the pointer places
/// and the root of a source local. A `move` of a value that is not plain
/// data also moves the base local: `moved_at(S(l), n)`, and for a part
/// `moved_part(α(q), n)` and `rest_linear(S(l), n)` if another part can
/// hold a linear value.
///
/// # Errors
///
/// The errors of α.
pub fn operand(em: &mut Em<'_>, n: NodeId, st: &State, op: &Operand) -> R {
    operand_in(em, n, st, op, false)
}

/// An operand at node `n`. With `relocate`, a `move` of a whole local
/// gives the value with its place fields to the destination (a value that a
/// construction built in place, or the result of the body): it does not
/// read the place fields. A `!Move` value does not read them either: its
/// move is W0604.
fn operand_in(em: &mut Em<'_>, n: NodeId, st: &State, op: &Operand, relocate: bool) -> R {
    operand_moves(em, n, st, op, relocate, true)
}

/// An operand at node `n`, as [`operand_in`]. With `moves` false, a `move`
/// does not move the base local at `n`: a callee that holds the argument
/// moves it at the `Ret` node of the call.
fn operand_moves(
    em: &mut Em<'_>,
    n: NodeId,
    st: &State,
    op: &Operand,
    relocate: bool,
    moves: bool,
) -> R {
    match op {
        Operand::Const(_) => Ok(()),
        Operand::Copy(q) => {
            let (mut a, al) = em.access(st, q, true)?;
            copied_refs(em, q, &al, &mut a)?;
            em.apply(n, kernel::read(&a));
            Ok(())
        }
        Operand::Move(q) => {
            let (mut a, al) = em.access(st, q, true)?;
            copied_refs(em, q, &al, &mut a)?;
            let ty = em.place_ty(q);
            let immovable = ty.is_some_and(|t| ir_props(em.tys, t).immovable);
            if relocate || immovable {
                a.vars = em.vars_with(q, false)?;
            }
            em.apply(n, kernel::read(&a));
            let plain = ty.is_some_and(|t| !em.tys.not_copy(t));
            if !plain && moves {
                moved(em, n, st, q, &al)?;
            }
            Ok(())
        }
    }
}

/// A read of the value at `q` through a pointer that copies references out
/// of a place of another local, or a borrow of such a place (R3RT2,
/// `docs/ir.md` 5.13): the access uses the variables of the move paths that
/// own the places, as an access of the local itself does.
fn copied_refs(em: &mut Em<'_>, q: &Place, al: &Alpha, a: &mut Access) -> R {
    if !q.has_deref() {
        return Ok(());
    }
    let holds = em
        .place_ty(q)
        .is_some_and(|t| ir_props(em.tys, t).holds_refs);
    if !holds {
        return Ok(());
    }
    let base = em.key(q.local)?;
    for &p in &al.places {
        a.vars.extend(em.owner_vars(p, base));
    }
    a.vars.sort();
    a.vars.dedup();
    Ok(())
}

/// The move of the value at `q` at node `n` (a `move` operand or a
/// `Consume`): `moved_at` of the base local, and for a part `moved_part` and
/// `rest_linear`. The rest of the local is linear if the type of another
/// part can hold a linear value and the state says that the rest of the
/// value can (a part that moved before holds nothing).
fn moved(em: &mut Em<'_>, n: NodeId, st: &State, q: &Place, al: &Alpha) -> R {
    let k = em.key(q.local)?;
    let Some(s) = em.s_var(k) else {
        return Ok(());
    };
    em.facts.moved_at.push((s, n));
    if !q.proj.is_empty() {
        em.facts
            .moved_part
            .extend(al.places.iter().map(|&m| (m, n)));
        let t = super::alpha::place_ty(em.p, em.tys, em.body, &Place::local(q.local));
        let by_type = t.is_some_and(|t| rest_linear(em.tys, t, &q.proj));
        let by_state = match steps(move_prefix(q)) {
            Some(path) if !path.is_empty() => {
                st.value(k, &[]).flat_without(&[path.as_slice()]).linear
            }
            _ => true,
        };
        if by_type && by_state {
            em.facts.rest_linear.push((s, n));
        }
    }
    Ok(())
}

// ------------------------------------------------------------ statements

/// The template of statement `s` at node `n`, with the state `st` before
/// it. `pair` is the drop pair variable of a `Drop` right before an
/// `Assign`, or of the `Drop` itself.
///
/// # Errors
///
/// The errors of α, and [`AlphaError::Later`] for a construct of a later
/// stage.
pub fn stmt(em: &mut Em<'_>, n: NodeId, st: &State, s: &StmtKind, pair: Option<VarId>) -> R {
    match s {
        StmtKind::Live(l) => live(em, n, *l),
        StmtKind::Dead(l) => dead(em, n, *l),
        StmtKind::Assign(p, rv) => assign(em, n, st, p, rv, pair),
        StmtKind::Drop(p) => drop_place(em, n, st, p, pair),
        StmtKind::Consume(p) => consume(em, n, st, p),
        StmtKind::Uninit(p) => uninit(em, n, p),
        StmtKind::Bounds(p, i) => bounds(em, n, st, p, i),
        StmtKind::Mention(p) => mention(em, n, st, p),
        StmtKind::Print(ops) => print(em, n, st, ops),
        StmtKind::UnwindValue(p, a) => unwind_value(em, n, p, a),
        StmtKind::UnwindKont(k) => unwind_kont(em, n, *k),
    }
}

/// `Live(l)`: no fact but the edge. The first value after it writes
/// nothing (`assign`).
///
/// # Errors
///
/// None.
pub const fn live(_em: &mut Em<'_>, _n: NodeId, _l: LocalId) -> R {
    Ok(())
}

/// `Dead(l)`: the end of the variables of `l`.
///
/// It gives `scope_end` of `S(l)`, of each `H` and `U` variable of `l` and of
/// `C(l)` on a normal path, and `unwound_at` in place of `scope_end` on a
/// cleanup path. A value that is not plain data ends here too.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if the local does not exist.
pub fn dead(em: &mut Em<'_>, n: NodeId, l: LocalId) -> R {
    let k = em.key(l)?;
    let vars = em.vars;
    let vs = em
        .s_var(k)
        .into_iter()
        .chain(vars.parts_of(k.0, k.1).iter().map(|(_, _, v)| *v))
        .chain(vars.get(&VarKey::C(k.0, k.1)));
    let rel = if em.cleanup {
        &mut em.facts.unwound_at
    } else {
        &mut em.facts.scope_end
    };
    rel.extend(vs.map(|v| (v, n)));
    Ok(())
}

/// `Assign(p, rv)`: the operands of `rv` (a borrow uses its place and reads
/// its pointers; `Len` and `Discriminant` read their place), then the
/// destination:
///
/// - a whole local `l`: `rebound_at` of `S(l)` and of each `H` and `U`
///   variable of `l`; `points_into` of the places of the value (each `H`
///   variable gets the places of its part); `empty_at(S(l))` if the value
///   has no linear part; `mutates_at(n, root(l))` if `l` is a source local
///   that can hold a value before `n`. The first value after `Live` or
///   `Uninit` writes nothing.
/// - a part of `l`: `uses(S(l))`; `rebound_at` and `points_into` of the `H`
///   variables at or below the part; `rebound_at` of the `U` variables at
///   or below it; `mutates_at(n, α(p))`; `overwrites(S(l))` if the part can
///   hold a linear value.
/// - an element of `l`: as a part, with `points_into` of the variable
///   above it (a weak definition).
/// - a place through a reference: the write rule of the kernel
///   (`mutates_at`, the pointers, `writes_via`); a weak definition of each
///   local that the place can be; the end of the drop pair `pair`.
///
/// A reference into a place field of a `!Move` struct gives `ref_at` and
/// `ref_in` (W0605), and so does a reference in a place field of a struct
/// literal (`ref_at` only).
///
/// # Errors
///
/// The errors of α and of the analysis.
pub fn assign(
    em: &mut Em<'_>,
    n: NodeId,
    st: &State,
    place: &Place,
    rv: &Rvalue,
    pair: Option<VarId>,
) -> R {
    let ret_local = em.p.bodies.get(em.body.index()).map(|b| b.ret);
    let to_result = place.proj.is_empty() && Some(place.local) == ret_local;
    let wholes = transfer::moved_wholes(rv);
    let relocates = |em: &Em<'_>, l: LocalId| {
        to_result || em.key(l).is_ok_and(|k| em.vars.built_in_place(k.0, k.1))
    };
    for op in transfer::rvalue_operands(rv) {
        let relocate = match op {
            Operand::Move(q) if q.proj.is_empty() => relocates(em, q.local),
            _ => false,
        };
        operand_in(em, n, st, op, relocate)?;
        if let Operand::Const(weft_ir::Const::Fn(f, _)) = op {
            let sim =
                em.p.fns
                    .get(f.index())
                    .is_some_and(|d| d.intrinsic == Some(weft_ir::Intrinsic::SimRun));
            if sim {
                em.facts.sim_run_at.push(n);
            }
        }
    }
    match rv {
        Rvalue::Ref(q) => {
            let (mut a, al) = em.access(st, q, false)?;
            // A borrow of a place that holds references, through a pointer,
            // uses the references there (R3RT2: a binding by reference).
            copied_refs(em, q, &al, &mut a)?;
            let (f, _) = kernel::borrow(&a, &al.handles);
            em.apply(n, f);
        }
        Rvalue::Len(q) | Rvalue::Discriminant(q) => {
            let (a, _) = em.access(st, q, true)?;
            em.apply(n, kernel::read(&a));
        }
        Rvalue::Aggregate(weft_ir::AggKind::Struct(t), ops) => literal_fields(em, st, n, *t, ops)?,
        _ => {}
    }
    let body = em.body;
    let v = transfer::rvalue(&mut em.cx(), body, st, rv)?;
    let dest = transfer::move_path(em.p, body, place)?;
    match &dest {
        Some((k, path)) if path.is_empty() => whole(em, n, st, *k, &v),
        Some((k, path)) => part(em, n, st, *k, place, path, &v)?,
        None if !place.has_deref() => element(em, n, st, place, &v)?,
        None => through(em, n, st, place, &v)?,
    }
    if let Some(d) = pair {
        em.facts.scope_end.push((d, n));
    }
    // The place fields of a value built in place go with it: a place field
    // with no value has no value in the destination.
    if dest.is_some() {
        for (steps_in, t) in wholes {
            if relocates(em, t) && !to_result {
                relocate(em, n, st, place, &steps_in, t)?;
            }
        }
    }
    place_field(em, st, n, place, &v)?;
    Ok(())
}

/// The place fields of the whole local `t` that moves to `place` (at the
/// steps `steps_in` of the value): each `U` variable of `t` whose place can
/// have no value gives `unset_at` of the `U` variable of the destination,
/// in place of its `rebound_at`.
fn relocate(
    em: &mut Em<'_>,
    n: NodeId,
    st: &State,
    place: &Place,
    steps_in: &[PathStep],
    t: LocalId,
) -> R {
    let tk = em.key(t)?;
    let dk = em.key(place.local)?;
    let us: Vec<Vec<Proj>> = em
        .vars
        .parts_of(tk.0, tk.1)
        .iter()
        .filter(|(kind, _, _)| *kind == PartKind::U)
        .map(|(_, r, _)| r.clone())
        .collect();
    for r in us {
        let unset = steps(&r).is_none_or(|rs| !st.must_hold(tk, &rs));
        if !unset {
            continue;
        }
        let mut proj = place.proj.clone();
        proj.extend(steps_in.iter().map(|s| match s {
            PathStep::Field(i) => Proj::Field(weft_ir::FieldIdx(*i)),
            PathStep::Variant(v) => Proj::Variant(weft_ir::VariantIdx(*v)),
        }));
        proj.extend(r);
        let key = VarKey::U(dk.0, Place { local: dk.1, proj });
        if let Some(u) = em.vars.get(&key) {
            em.facts.rebound_at.retain(|x| *x != (u, n));
            em.facts.unset_at.push((u, n));
        }
    }
    Ok(())
}

/// The destination of an `Assign` is the whole local with key `k`.
fn whole(em: &mut Em<'_>, n: NodeId, st: &State, k: Key, v: &Tree) {
    let s = em.s_var(k);
    let flat = v.flat();
    if let Some(s) = s {
        em.facts.rebound_at.push((s, n));
        if flat.empty {
            em.facts.empty_at.push((s, n));
        }
        em.meet_uniq(s, flat.uniq);
    }
    em.facts
        .rebound_at
        .extend(em.vars.parts_of(k.0, k.1).iter().map(|(_, _, v)| (*v, n)));
    em.give_value(k, &[], v, s);
    if em.source_local(k) && st.may_hold(k) {
        if let Ok(r) = em.roots.local(em.p, em.tys, em.facts, k.0, k.1) {
            em.facts.mutates_at.push((n, r));
        }
    }
}

/// The destination of an `Assign` is the part `path` of the local with key
/// `k`.
fn part(
    em: &mut Em<'_>,
    n: NodeId,
    st: &State,
    k: Key,
    place: &Place,
    path: &[PathStep],
    v: &Tree,
) -> R {
    let s = em.s_var(k);
    if let Some(s) = s {
        em.facts.uses.push((s, n));
    }
    em.facts.rebound_at.extend(
        em.vars
            .parts_of(k.0, k.1)
            .iter()
            .filter(|(_, proj, _)| steps(proj).is_some_and(|x| is_prefix(path, &x)))
            .map(|(_, _, v)| (*v, n)),
    );
    // The places of a part with no variable of its own go to the variable
    // above it: no `rebound_at`, the other parts keep their places.
    let above = em
        .h_below(k, &[])
        .into_iter()
        .filter(|(p, _)| p.len() < path.len() && is_prefix(p, path))
        .max_by_key(|(p, _)| p.len())
        .map(|(_, v)| v)
        .or(s);
    em.give_value(k, path, v, above);
    let al = em.alpha(st, place)?;
    em.facts
        .mutates_at
        .extend(al.places.iter().map(|&m| (n, m)));
    if let (Some(s), Some(t)) = (s, em.place_ty(place)) {
        if ir_props(em.tys, t).linear {
            em.facts.overwrites.push((s, n));
        }
    }
    Ok(())
}

/// The destination of an `Assign` is an element of a local (an index or
/// the elements, with no dereference).
fn element(em: &mut Em<'_>, n: NodeId, st: &State, place: &Place, v: &Tree) -> R {
    let (a, _) = em.access(st, place, false)?;
    let k = em.key(place.local)?;
    let s = em.s_var(k);
    let prefix = steps(move_prefix(place)).unwrap_or_default();
    let holder = em
        .h_below(k, &[])
        .into_iter()
        .filter(|(p, _)| is_prefix(p, &prefix))
        .max_by_key(|(p, _)| p.len())
        .map(|(_, v)| v)
        .or(s);
    let refs: Vec<PlaceId> = v.flat().refs.into_iter().collect();
    let mut f = Frag {
        uses: a.vars.clone(),
        reads: a.ptrs.clone(),
        mutates: a.places,
        ..Frag::default()
    };
    if let Some(h) = holder {
        f.extend(kernel::copy_ref(&[h], &refs));
    }
    em.apply(n, f);
    if let (Some(s), Some(t)) = (s, em.place_ty(place)) {
        if ir_props(em.tys, t).linear {
            em.facts.overwrites.push((s, n));
        }
    }
    Ok(())
}

/// The destination of an `Assign` goes through a reference.
fn through(em: &mut Em<'_>, n: NodeId, st: &State, place: &Place, v: &Tree) -> R {
    let (mut a, al) = em.access(st, place, false)?;
    // A store into a path that the local owns through a `Box` gives the
    // place fields at or below it a value: the store does not read them.
    if owned_prefix(place).len() == place.proj.len() {
        let k = em.key(place.local)?;
        let given: Vec<VarId> = em
            .vars
            .parts_of(k.0, k.1)
            .iter()
            .filter(|(kind, proj, _)| *kind == PartKind::U && is_prefix(&place.proj, proj))
            .map(|(_, _, v)| *v)
            .collect();
        a.vars.retain(|v| !given.contains(v));
        em.facts
            .rebound_at
            .extend(given.into_iter().map(|u| (u, n)));
    }
    // `writes_via`: the first dereference is of a whole local that holds one
    // reference to one place.
    let one = match place.proj.first() {
        Some(Proj::Deref(weft_ir::DerefKind::Ref)) => {
            let k = em.key(place.local)?;
            let refs = st.value(k, &[]).flat().refs;
            match (refs.len(), refs.first(), em.s_var(k)) {
                (1, Some(&d), Some(s)) if em.facts.wild_base(d).is_none() => Some((s, d)),
                _ => None,
            }
        }
        _ => None,
    };
    let facts = &*em.facts;
    let below = |m: PlaceId, d: PlaceId| {
        let mut cur = Some(m);
        while let Some(c) = cur {
            if c == d {
                return true;
            }
            cur = facts.places.get(c.index()).and_then(|i| i.parent);
        }
        false
    };
    let f = kernel::write_through(&a, one, &below);
    em.apply(n, f);
    // A store of a reference into a local through a pointer: a weak
    // definition of the variable of the place (no `rebound_at`).
    let refs: Vec<PlaceId> = v.flat().refs.into_iter().collect();
    if refs.is_empty() {
        return Ok(());
    }
    // A self-reference field has its own check (W0605).
    let self_ref = field_place(em, st, place)?.is_some();
    let sp = em.facts.node(n).span;
    for &q in &al.places {
        store(em, q, &refs, sp, !self_ref);
    }
    Ok(())
}

/// The references `refs` go into place `q` at a node with span `span`. A
/// place of a local: a weak definition of the variable of the place (no
/// `rebound_at`). A place that a caller keeps (behind a reference
/// parameter, in an `rc` object): with `check`, the W0204 store check gets
/// it ([`Stored`]).
fn store(em: &mut Em<'_>, q: PlaceId, refs: &[PlaceId], span: Span, check: bool) {
    let Some((k, path)) = em.roots.path_of(em.facts, q) else {
        if check {
            em.stored.push(Stored {
                into: q,
                refs: refs.to_vec(),
                span,
            });
        }
        return;
    };
    let holder = em
        .h_below(k, &[])
        .into_iter()
        .filter(|(p, _)| is_prefix(p, &path))
        .max_by_key(|(p, _)| p.len())
        .map(|(_, v)| v)
        .or_else(|| em.s_var(k));
    if let Some(h) = holder {
        let frag = kernel::copy_ref(&[h], refs);
        em.facts.points_into.extend(frag.points_into);
    }
}

/// The stated place of the place field that `place` names, if `place` is a
/// place field of a struct: the places of the field in terms of the place
/// of the struct, and the text.
fn field_place(
    em: &mut Em<'_>,
    st: &State,
    place: &Place,
) -> Result<Option<(Vec<PlaceId>, String)>, AlphaError> {
    let Some((Proj::Field(f), base)) = place.proj.split_last() else {
        return Ok(None);
    };
    let base = Place {
        local: place.local,
        proj: base.to_vec(),
    };
    let Some(t) = em.place_ty(&base) else {
        return Ok(None);
    };
    let Some(Ty::Adt(a, _)) = em.tys.try_get(t).cloned() else {
        return Ok(None);
    };
    let Some(sp) = sema_field_place(em.sema, a, f.index()) else {
        return Ok(None);
    };
    let bases = vec![em.alpha(st, &base)?.places];
    let allowed = super::decls::subst(em.p, em.tys, em.facts, em.roots, &sp, &bases);
    Ok(Some((allowed, sp.text)))
}

/// The stated place of field `i` of definition `a` of the analysis.
fn sema_field_place(
    sema: &crate::Program,
    a: weft_ir::AdtId,
    i: usize,
) -> Option<crate::program::SigPlace> {
    let d = sema.adts.get(a.index())?;
    match &d.kind {
        crate::program::AdtKind::Struct(fs) => fs.get(i).and_then(|f| f.place.clone()),
        _ => None,
    }
}

/// The places of `refs` that a stated place can hold: not a handle place.
fn named_refs(em: &Em<'_>, refs: impl IntoIterator<Item = PlaceId>) -> Vec<PlaceId> {
    refs.into_iter()
        .filter(|&r| !em.roots.is_handle(r))
        .collect()
}

/// W0605: a reference into place field `place` of a `!Move` struct must be
/// inside the stated place of the field (`ref_at`, `ref_in`, on a node with
/// no edges that only `ref_outside` reads).
fn place_field(em: &mut Em<'_>, st: &State, n: NodeId, place: &Place, v: &Tree) -> R {
    let Some((allowed, text)) = field_place(em, st, place)? else {
        return Ok(());
    };
    let refs = named_refs(em, v.flat().refs);
    if refs.is_empty() {
        return Ok(());
    }
    let sp = em.facts.node(n).span;
    let m = em.facts.add_node(sp, "field", String::new());
    em.facts.ref_in.extend(allowed.into_iter().map(|d| (m, d)));
    em.facts.ref_at.extend(refs.into_iter().map(|r| (m, r)));
    em.facts.ref_sites.push(RefSite {
        node: m,
        kind: RefKind::Field,
        needs: text,
    });
    Ok(())
}

/// W0605 for a struct literal: a reference in a place field of the literal
/// has no stated place of the body (`ref_at` with no `ref_in`): the struct
/// has no place yet.
fn literal_fields(em: &mut Em<'_>, st: &State, n: NodeId, t: TyId, ops: &[Operand]) -> R {
    let Some(Ty::Adt(a, _)) = em.tys.try_get(t).cloned() else {
        return Ok(());
    };
    let names: Vec<(usize, String)> = match em.sema.adts.get(a.index()).map(|d| &d.kind) {
        Some(crate::program::AdtKind::Struct(fs)) => fs
            .iter()
            .enumerate()
            .filter(|(_, f)| f.place.is_some())
            .map(|(i, f)| (i, f.name.clone()))
            .collect(),
        _ => return Ok(()),
    };
    for (i, name) in names {
        let Some(op) = ops.get(i) else {
            continue;
        };
        let body = em.body;
        let v = transfer::operand(&mut em.cx(), body, st, op)?;
        let refs = named_refs(em, v.flat().refs);
        if refs.is_empty() {
            continue;
        }
        let needs = sema_field_place(em.sema, a, i).map_or_else(String::new, |p| p.text);
        let sp = em.facts.node(n).span;
        let m = em.facts.add_node(sp, "field", String::new());
        em.facts.ref_at.extend(refs.into_iter().map(|r| (m, r)));
        em.facts.ref_sites.push(RefSite {
            node: m,
            kind: RefKind::Literal { field: name },
            needs,
        });
    }
    Ok(())
}

/// `Drop(p)`: the old value of a place behind a pointer goes away.
///
/// It uses and reads the pointers of `p`, and binds the drop pair `pair`
/// (with the props of the old value). The pair ends at the `Assign` after
/// it.
///
/// # Errors
///
/// The errors of α.
pub fn drop_place(em: &mut Em<'_>, n: NodeId, st: &State, place: &Place, pair: Option<VarId>) -> R {
    let (a, _) = em.access(st, place, false)?;
    em.apply(
        n,
        Frag {
            uses: a.vars,
            reads: a.ptrs,
            ..Frag::default()
        },
    );
    if let Some(d) = pair {
        em.facts.rebound_at.push((d, n));
    }
    Ok(())
}

/// `Consume(p)`: the linear value at `p` is finished.
///
/// It moves the base local; a part is a move of a part (`moved_part`,
/// `rest_linear`), as a `move` operand. It is not a use: the parts of the
/// value moved before it (a pattern binds them), so a use would be a use
/// after a move.
///
/// # Errors
///
/// The errors of α.
pub fn consume(em: &mut Em<'_>, n: NodeId, st: &State, place: &Place) -> R {
    let al = em.alpha(st, place)?;
    moved(em, n, st, place, &al)
}

/// `Uninit(p)`: `unset_at(S(l))` for a whole local, `unset_at(U(p))` for a
/// place field path.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if the local does not exist.
pub fn uninit(em: &mut Em<'_>, n: NodeId, place: &Place) -> R {
    let k = em.key(place.local)?;
    let v = if place.proj.is_empty() {
        em.s_var(k)
    } else {
        em.vars.get(&VarKey::U(
            k.0,
            Place {
                local: k.1,
                proj: place.proj.clone(),
            },
        ))
    };
    if let Some(v) = v {
        em.facts.unset_at.push((v, n));
    }
    Ok(())
}

/// `Bounds(q, i)`: a read of `q` (the length and the buffer) and the
/// operand `i`.
///
/// # Errors
///
/// The errors of α.
pub fn bounds(em: &mut Em<'_>, n: NodeId, st: &State, place: &Place, i: &Operand) -> R {
    let (a, _) = em.access(st, place, true)?;
    em.apply(n, kernel::read(&a));
    operand(em, n, st, i)
}

/// `Mention(q)`: `uses` of `v(q)` and of the pointer locals; no read.
///
/// # Errors
///
/// The errors of α.
pub fn mention(em: &mut Em<'_>, n: NodeId, st: &State, place: &Place) -> R {
    let (a, _) = em.access(st, place, false)?;
    em.apply(n, kernel::mention(&a));
    Ok(())
}

/// `Print(ops)`: the operands; an operand that holds a reference reads
/// through it (`reads_at` of the places of its value).
///
/// # Errors
///
/// The errors of α.
pub fn print(em: &mut Em<'_>, n: NodeId, st: &State, ops: &[Operand]) -> R {
    for op in ops {
        operand(em, n, st, op)?;
        let body = em.body;
        let v = transfer::operand(&mut em.cx(), body, st, op)?;
        let refs = named_refs(em, v.flat().refs);
        em.apply(n, kernel::read_through(&refs));
    }
    Ok(())
}

/// `UnwindValue(p, a)`: `unwound_at` of `S(l)` and of the variables below
/// `p`. An `OnAbort` action applies the summary of the function (stage F7).
///
/// # Errors
///
/// Returns [`AlphaError::Later`] for an `OnAbort` action.
pub fn unwind_value(em: &mut Em<'_>, n: NodeId, place: &Place, a: &UnwindAction) -> R {
    if let UnwindAction::OnAbort(_) = a {
        return Err(AlphaError::Later("an `on abort` function (stage F7)"));
    }
    let k = em.key(place.local)?;
    let prefix = move_prefix(place);
    let vars = em.vars;
    let vs = em.s_var(k).into_iter().chain(
        vars.parts_of(k.0, k.1)
            .iter()
            .filter(|(_, proj, _)| is_prefix(prefix, proj))
            .map(|(_, _, v)| *v),
    );
    em.facts.unwound_at.extend(vs.map(|v| (v, n)));
    Ok(())
}

/// `UnwindKont(k)`: the edge only. The frames of the continuation unwind in
/// the component where they live.
///
/// # Errors
///
/// None.
pub const fn unwind_kont(_em: &mut Em<'_>, _n: NodeId, _k: LocalId) -> R {
    Ok(())
}

// ----------------------------------------------------------- terminators

/// The template of terminator `t` at its node `n` (phase `Main`), with the
/// state `st` before it. `origin` is the span of the terminator.
///
/// # Errors
///
/// The errors of α, and [`AlphaError::Later`] for a terminator of a later
/// stage.
pub fn term(em: &mut Em<'_>, n: NodeId, st: &State, t: &TermKind, origin: weft_ir::Span) -> R {
    match t {
        TermKind::Goto(_) => goto(em, n),
        TermKind::Unreachable => unreachable(em, n),
        TermKind::UnwindExit => unwind_exit(em, n),
        TermKind::Switch { on, .. } => switch(em, n, st, on),
        TermKind::Return => ret(em, n, st, origin),
        TermKind::Assert { cond, .. } => assert(em, n, st, cond),
        TermKind::Call { .. } => Err(AlphaError::BadPlace(
            "a call needs the nodes of its phases (`call`)".to_string(),
        )),
        _ => Err(AlphaError::Later(
            "a terminator that runs another body (stages F14 and later)",
        )),
    }
}

/// `Goto`: the edge only.
///
/// # Errors
///
/// None.
pub const fn goto(_em: &mut Em<'_>, _n: NodeId) -> R {
    Ok(())
}

/// `Unreachable`: the edge only.
///
/// # Errors
///
/// None.
pub const fn unreachable(_em: &mut Em<'_>, _n: NodeId) -> R {
    Ok(())
}

/// `UnwindExit`: the edge only.
///
/// # Errors
///
/// None.
pub const fn unwind_exit(_em: &mut Em<'_>, _n: NodeId) -> R {
    Ok(())
}

/// `Switch`: its operand.
///
/// # Errors
///
/// The errors of α.
pub fn switch(em: &mut Em<'_>, n: NodeId, st: &State, on: &Operand) -> R {
    operand(em, n, st, on)
}

/// `Return`: `uses(S(_0), n)` and of the `H` variables of `_0`.
///
/// So a reference in `_0` into a local that the frame end freed is
/// `error(_0, Return)`. If the signature states the returned places, a node
/// with no edges gets `ref_at` of the places of `_0` that are not locals
/// and `ref_in` of the stated places (W0204).
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if the body has no `_0`.
pub fn ret(em: &mut Em<'_>, n: NodeId, st: &State, origin: weft_ir::Span) -> R {
    let b =
        em.p.bodies
            .get(em.body.index())
            .ok_or_else(|| AlphaError::BadPlace("no body".to_string()))?;
    let k = em.key(b.ret)?;
    let vars = em.vars;
    let vs = em.s_var(k).into_iter().chain(
        vars.parts_of(k.0, k.1)
            .iter()
            .filter(|(kind, _, _)| *kind == PartKind::H)
            .map(|(_, _, v)| *v),
    );
    em.facts.uses.extend(vs.map(|v| (v, n)));
    let Some(allowed) = em.ret_places else {
        return Ok(());
    };
    let refs: Vec<PlaceId> = named_refs(em, st.value(k, &[]).flat().refs)
        .into_iter()
        .filter(|&r| !super::decls::is_local_root(em.facts, r))
        .collect();
    if refs.is_empty() {
        return Ok(());
    }
    let allowed = allowed.to_vec();
    let m = em.facts.add_node(span(origin), "return", String::new());
    let needs: Vec<String> = allowed
        .iter()
        .map(|&d| em.facts.place(d).display.clone())
        .collect();
    em.facts.ref_in.extend(allowed.into_iter().map(|d| (m, d)));
    em.facts.ref_at.extend(refs.into_iter().map(|r| (m, r)));
    em.facts.ref_sites.push(RefSite {
        node: m,
        kind: RefKind::Return { env: None },
        needs: needs.join(" | "),
    });
    Ok(())
}

/// `Assert`: its operand and `may_abort(n)`. A failed `assert` ends the
/// task: the abort goes past the function (no local handler spares a
/// variable, so no `spared_at`).
///
/// # Errors
///
/// The errors of α.
pub fn assert(em: &mut Em<'_>, n: NodeId, st: &State, cond: &Operand) -> R {
    operand(em, n, st, cond)?;
    em.facts.may_abort.push(n);
    Ok(())
}

/// The entry of a function body: each parameter binds.
///
/// It gives `rebound_at` of each parameter, with the places of its value
/// (`points_into`) and `empty_at` if it has no linear part. The `H` and `U`
/// variables of a parameter bind too.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if a parameter does not exist.
pub fn entry(em: &mut Em<'_>, n: NodeId, params: &[(LocalId, Tree)]) -> R {
    for (l, v) in params {
        let k = em.key(*l)?;
        let flat = v.flat();
        let s = em.s_var(k);
        if let Some(s) = s {
            em.facts.rebound_at.push((s, n));
            if flat.empty {
                em.facts.empty_at.push((s, n));
            }
            em.meet_uniq(s, flat.uniq);
            let refs: Vec<PlaceId> = flat.refs.iter().copied().collect();
            let f = kernel::copy_ref(&[s], &refs);
            em.facts.points_into.extend(f.points_into);
        }
        let parts: Vec<(PartKind, VarId)> = em
            .vars
            .parts_of(k.0, k.1)
            .iter()
            .map(|(kind, _, v)| (*kind, *v))
            .collect();
        for (kind, var) in parts {
            em.facts.rebound_at.push((var, n));
            if kind == PartKind::H {
                let refs: Vec<PlaceId> = flat.refs.iter().copied().collect();
                let f = kernel::copy_ref(&[var], &refs);
                em.facts.points_into.extend(f.points_into);
            }
        }
    }
    Ok(())
}

// ------------------------------------------------------------------ calls

/// The nodes of a `Call` (`docs/ir.md` 6.2).
#[derive(Clone, Debug)]
pub struct CallNodes {
    /// The node `Main`.
    pub main: NodeId,
    /// The node `Ret`, if the call returns.
    pub ret: Option<NodeId>,
    /// The node `FrameEnd` of the normal path.
    pub frame_end: Option<NodeId>,
    /// The node `FrameEnd(d)` of the path of each abort.
    pub aborts: Vec<NodeId>,
}

/// True if type `t` names type parameter `j`.
fn mentions_index(tys: &TyTable, t: TyId, j: u32, depth: usize) -> bool {
    if depth > 32 {
        return true;
    }
    let deep = |x: &TyId| mentions_index(tys, *x, j, depth + 1);
    match tys.try_get(t) {
        Some(Ty::Param(i)) => *i == j,
        Some(Ty::Tuple(ts) | Ty::Adt(_, ts)) => ts.iter().any(deep),
        Some(Ty::Ref(x) | Ty::Slice(x) | Ty::Array(x, _) | Ty::Iter(x)) => deep(x),
        Some(Ty::Cont(a, b)) => deep(a) || deep(b),
        Some(Ty::Fn(f)) => f.params.iter().any(deep) || deep(&f.ret),
        _ => false,
    }
}

/// The span of operand `op` of a call with span `at`: the origin of its
/// temporary, or the span of the call.
fn operand_span(em: &Em<'_>, op: &Operand, at: Span) -> Span {
    let local = match op {
        Operand::Copy(q) | Operand::Move(q) if q.proj.is_empty() => Some(q.local),
        _ => None,
    };
    local
        .and_then(|l| {
            em.p.bodies
                .get(em.body.index())
                .and_then(|b| b.locals.get(l.index()))
        })
        .filter(|d| matches!(d.kind, LocalKind::Temp(_)))
        .map_or(at, |d| span(d.origin.span))
}

/// The local that a receiver argument reaches through: `r` for a receiver
/// `&(*r).q` (a temporary that the body borrows through `r`) or `copy r`,
/// where `r` is a reference.
fn receiver_ref(em: &Em<'_>, op: &Operand) -> Option<LocalId> {
    let (Operand::Copy(q) | Operand::Move(q)) = op else {
        return None;
    };
    if !q.proj.is_empty() {
        return None;
    }
    let b = em.p.bodies.get(em.body.index())?;
    let d = b.locals.get(q.local.index())?;
    let place = if matches!(d.kind, LocalKind::Temp(_)) {
        b.blocks
            .iter()
            .flat_map(|blk| &blk.stmts)
            .find_map(|s| match &s.kind {
                StmtKind::Assign(
                    dest,
                    Rvalue::Ref(p) | Rvalue::Use(Operand::Copy(p) | Operand::Move(p)),
                ) if dest.local == q.local && dest.proj.is_empty() => Some(p.clone()),
                _ => None,
            })?
    } else {
        q.clone()
    };
    let is_ref = |l: LocalId| {
        b.locals
            .get(l.index())
            .is_some_and(|d| matches!(em.tys.try_get(d.ty), Some(Ty::Ref(_))))
    };
    match place.proj.first() {
        None if is_ref(place.local) => Some(place.local),
        Some(Proj::Deref(weft_ir::DerefKind::Ref)) => Some(place.local),
        _ => None,
    }
}

/// `writes_via` at a method call (`docs/ir.md` 6.4, QA6): the callee
/// changes only places below its receiver, and the receiver reaches through
/// a local `r` of type `&X` (with no reference in `X`). If each place that the
/// node changes is at or below a place that `r` points into, the node
/// gets `writes_via(n, S(r))`.
fn via_receiver(
    em: &mut Em<'_>,
    n: NodeId,
    st: &State,
    args: &[Operand],
    only_self: bool,
    changed: &[(PlaceId, u32)],
) -> R {
    if !only_self || changed.is_empty() {
        return Ok(());
    }
    let Some(r) = args.first().and_then(|op| receiver_ref(em, op)) else {
        return Ok(());
    };
    let ty = em.place_ty(&Place::local(r));
    let one = ty
        .and_then(|t| match em.tys.try_get(t) {
            Some(Ty::Ref(x)) => Some(*x),
            _ => None,
        })
        .is_some_and(|x| !ir_props(em.tys, x).holds_refs);
    if !one {
        return Ok(());
    }
    let k = em.key(r)?;
    let Some(s) = em.s_var(k) else {
        return Ok(());
    };
    let refs = st.value(k, &[]).flat().refs;
    let facts = &*em.facts;
    let below = |p: PlaceId| {
        let mut at = Some(p);
        while let Some(q) = at {
            if refs.contains(&q) {
                return true;
            }
            at = facts.places.get(q.index()).and_then(|i| i.parent);
        }
        false
    };
    if changed.iter().all(|&(m, _)| below(m)) {
        em.facts.writes_via.push((n, s));
    }
    Ok(())
}

/// The value `v` binds to the destination `dest` of a node `n`, as the
/// destination of an `Assign` ([`assign`]).
fn bind_dest(em: &mut Em<'_>, n: NodeId, st: &State, dest: &Place, v: &Tree) -> R {
    let body = em.body;
    match transfer::move_path(em.p, body, dest)? {
        Some((k, path)) if path.is_empty() => whole(em, n, st, k, v),
        Some((k, path)) => part(em, n, st, k, dest, &path, v)?,
        None if !dest.has_deref() => element(em, n, st, dest, v)?,
        None => through(em, n, st, dest, v)?,
    }
    place_field(em, st, n, dest, v)
}

/// A `Call` of a function item: its nodes `Main`, `Ret` and `FrameEnd`
/// (`docs/ir.md` 6.4), with the summary of the callee (`docs/ir.md` 6.7).
///
/// - `Main`: the operands; the parts of the summary that act at the call
///   (`crate::analysis::apply::main`); `writes_via` at a method call whose
///   callee changes only places below its receiver; the binding of the
///   callee frame root and of a value that the callee drops.
/// - `Ret`: the result binds to `dest`; each argument that the callee holds
///   moves here (part `holds`); the values that go behind a reference
///   argument (part `stores`); a value that the callee drops ends here
///   (W0601).
/// - `FrameEnd`: the callee frame root ends, on the normal path and on the
///   path of each abort.
///
/// # Errors
///
/// Returns [`AlphaError::Later`] for a call of a function value or of a
/// function with no summary yet, and the errors of α.
pub fn call(
    em: &mut Em<'_>,
    nodes: &CallNodes,
    st: &State,
    block: weft_ir::BlockId,
    t: &TermKind,
    origin: weft_ir::Span,
) -> R {
    let TermKind::Call {
        callee: weft_ir::Callee::Fn(f, targs),
        args,
        dest,
        ..
    } = t
    else {
        return Err(AlphaError::Later("a call of a function value (stage F12)"));
    };
    let body = em.body;
    let out = transfer::call_out(&mut em.cx(), body, block, st, *f, targs, args, dest)?;
    let sum = &out.summary;
    let p = em.p;
    let decl = p
        .fns
        .get(f.index())
        .ok_or_else(|| AlphaError::BadPlace(format!("no function f{}", f.0)))?;
    let callee = decl
        .name
        .rsplit('.')
        .next()
        .unwrap_or(decl.name.as_str())
        .to_string();
    let main = nodes.main;
    let at = span(origin);
    // An argument of a type parameter that the callee holds moves at `Ret`.
    let held: Vec<bool> = (0..args.len())
        .map(|i| {
            decl.params
                .get(i)
                .is_some_and(|&t| sum.holds.iter().any(|&j| mentions_index(em.tys, t, j, 0)))
        })
        .collect();
    let mut spans = Vec::new();
    let mut bases = Vec::new();
    for (i, op) in args.iter().enumerate() {
        let moves = !held.get(i).copied().unwrap_or(false);
        // A value that the call builds in place (`Box.new(Frame { .. })`,
        // `docs/ir.md` 5.36) goes to the callee with its place fields: the
        // call does not read them. The result gets them (the `Uninit`
        // after the call).
        let relocate = match op {
            Operand::Move(q) if q.proj.is_empty() => em
                .key(q.local)
                .is_ok_and(|k| em.vars.built_in_place(k.0, k.1)),
            _ => false,
        };
        operand_moves(em, main, st, op, relocate, moves)?;
        spans.push(operand_span(em, op, at));
        bases.push(match op {
            Operand::Copy(q) | Operand::Move(q) => em.alpha(st, q)?.places,
            Operand::Const(_) => Vec::new(),
        });
    }
    let site = crate::analysis::apply::Site {
        callee: &callee,
        spans,
        bases,
    };
    let changed = crate::analysis::apply::main(
        &mut em.cx(),
        main,
        sum,
        &out.sigma,
        &site,
        crate::analysis::apply::RunKind::Item,
    )?;
    via_receiver(em, main, st, args, sum.only_self, &changed)?;
    let places: Vec<PlaceId> = changed.iter().map(|(q, _)| *q).collect();
    gets_linear(em, main, st, &places);
    // The callee frame root: a local of the callee that the result points
    // into.
    let frame = out.sigma.frame.map(|r| {
        let v = em.facts.add_var(weft_facts::VarInfo::plain(
            format!("a local of `{callee}`"),
            weft_facts::VarKind::Temp,
            at,
            String::new(),
        ));
        em.facts.owner.push((r, v));
        em.facts.rebound_at.push((v, main));
        v
    });
    // A value that the callee drops: a linear type argument goes away at the
    // call (W0601).
    let mut drops = Vec::new();
    for &j in &sum.drops {
        let Some(&targ) = targs.get(j as usize) else {
            continue;
        };
        let props = ir_props(em.tys, targ);
        if !props.linear {
            continue;
        }
        let mut info = weft_facts::VarInfo::plain(
            callee.clone(),
            weft_facts::VarKind::Dropped,
            at,
            em.tys.show(targ),
        );
        info.linear = true;
        info.has_on_abort = props.on_abort;
        let v = em.facts.add_var(info);
        em.facts.rebound_at.push((v, main));
        drops.push(v);
    }
    if let Some(r) = nodes.ret {
        held_refs(em, r, st, args)?;
        bind_dest(em, r, st, dest, &out.ret)?;
        for (i, op) in args.iter().enumerate() {
            let (true, Operand::Move(q)) = (held.get(i).copied().unwrap_or(false), op) else {
                continue;
            };
            let plain = em.place_ty(q).is_some_and(|t| !em.tys.not_copy(t));
            if plain {
                continue;
            }
            let vs = em.vars_of(q)?;
            em.facts.uses.extend(vs.into_iter().map(|v| (v, r)));
            let al = em.alpha(st, q)?;
            moved(em, r, st, q, &al)?;
        }
        for (q, refs) in &out.stores {
            store(em, *q, refs, at, true);
        }
        em.facts.scope_end.extend(drops.iter().map(|&v| (v, r)));
    }
    if let (Some(fe), Some(v)) = (nodes.frame_end, frame) {
        em.facts.scope_end.push((v, fe));
    }
    for &a in &nodes.aborts {
        em.facts.scope_end.extend(frame.map(|v| (v, a)));
        em.facts.unwound_at.extend(drops.iter().map(|&v| (v, a)));
    }
    Ok(())
}

/// A `Perform` through the capability of a caller: an operation of a caller
/// (`crate::analysis::unknown`, map N1). Its nodes are `Main` and `Ret`
/// (`docs/ir.md` 6.2).
///
/// - `Main`: the operands; `reads_at`, `call_arg`, `lends_mut` and
///   `call_mut` of the places of each reference argument (the clause gets
///   them and can change them, W0312 compares them); `call_arg` of the
///   places of the references of a by-value argument; `reads_at` and
///   `lends_mut` of the places of the callers; `escapes_at` of the effect;
///   `may_abort`; `multi_at` for a `multi` operation.
/// - `Ret`: the result binds to `dest`.
///
/// # Errors
///
/// Returns [`AlphaError::Later`] for a perform through a capability of a
/// local handler (stage F14), and the errors of α.
pub fn perform(em: &mut Em<'_>, nodes: &CallNodes, st: &State, t: &TermKind) -> R {
    let TermKind::Perform {
        cap: weft_ir::CapOperand::Row(e),
        op,
        args,
        dest,
        ..
    } = t
    else {
        return Err(AlphaError::Later(
            "a perform through a capability of a handler (stage F14)",
        ));
    };
    let body = em.body;
    let out = crate::analysis::unknown::op_of_caller(&mut em.cx(), body, st, *e, *op, args)?;
    let n = nodes.main;
    for op in args {
        operand_moves(em, n, st, op, false, true)?;
    }
    for (i, ps) in out.args.iter().enumerate() {
        let root = crate::body::roots::param(i);
        for &p in ps {
            em.facts.reads_at.push((n, p));
            em.facts.call_arg.push((n, p, root));
            em.facts.lends_mut.push((n, p));
            em.facts.call_mut.push((n, p, root));
        }
    }
    for (i, ps) in out.values.iter().enumerate() {
        let root = crate::body::roots::fn_arg(i);
        em.facts.call_arg.extend(ps.iter().map(|&p| (n, p, root)));
    }
    let lent: Vec<PlaceId> = out.args.iter().flatten().copied().collect();
    gets_linear(em, n, st, &lent);
    em.facts.reads_at.push((n, out.caller));
    em.facts.lends_mut.push((n, out.caller));
    em.facts.escapes_at.push((n, out.effect.clone()));
    em.facts.may_abort.push(n);
    if out.multi {
        em.facts.multi_at.push(n);
    }
    if let Some(r) = nodes.ret {
        held_refs(em, r, st, args)?;
        bind_dest(em, r, st, dest, &out.ret)?;
    }
    Ok(())
}

/// A run node `n` that changes the places `changed` (the callee, or a clause
/// of a caller, can put a linear value there and keep the old value, as
/// `Vec.push`): a local that can hold a linear value and holds none in the
/// state `st` before the node gets `overwrites(S(l), n)`, so its linear value
/// is live after the node (W0601 at its end). A local that can hold one
/// already is live: the node is no overwrite of it.
fn gets_linear(em: &mut Em<'_>, n: NodeId, st: &State, changed: &[PlaceId]) {
    let keys: Vec<Key> = transfer::can_get_linear(&em.cx(), changed)
        .into_iter()
        .map(|(k, _)| k)
        .collect();
    let mut done: Vec<Key> = Vec::new();
    for k in keys {
        if done.contains(&k) {
            continue;
        }
        done.push(k);
        if !st.value(k, &[]).flat().empty {
            continue;
        }
        if let Some(v) = em.s_var(k) {
            em.facts.overwrites.push((v, n));
        }
    }
}

/// The callee (or the clause) holds each reference argument until it
/// returns: at the `Ret` node `r`, `uses` of each argument of plain data
/// that holds a reference into a value that another argument moves at
/// `Main` (`f(&v[0], v)`). The move frees the value, so the reference that
/// the callee holds is invalid (W0301 at the call). A reference into a place
/// that the call only changes is the W0312 check (`call_mut`, `call_arg`).
///
/// # Errors
///
/// The errors of α.
fn held_refs(em: &mut Em<'_>, r: NodeId, st: &State, args: &[Operand]) -> R {
    let mut moved: Vec<PlaceId> = Vec::new();
    for op in args {
        let Operand::Move(q) = op else { continue };
        let plain = em.place_ty(q).is_some_and(|t| !em.tys.not_copy(t));
        if !plain {
            moved.extend(em.alpha(st, q)?.places);
        }
    }
    if moved.is_empty() {
        return Ok(());
    }
    let body = em.body;
    for op in args {
        let (Operand::Copy(q) | Operand::Move(q)) = op else {
            continue;
        };
        let Some(t) = em.place_ty(q) else { continue };
        if em.tys.not_copy(t) || !ir_props(em.tys, t).holds_refs {
            continue;
        }
        let refs = transfer::operand(&mut em.cx(), body, st, op)?.flat().refs;
        let hit = refs
            .iter()
            .any(|&p| moved.iter().any(|&m| overlap(em.facts, p, m)));
        if hit {
            let vs = em.vars_of(q)?;
            em.facts.uses.extend(vs.into_iter().map(|v| (v, r)));
        }
    }
    Ok(())
}

/// True if fact place `a` is at or below `b`, or `b` at or below `a`.
fn overlap(facts: &FnFacts, a: PlaceId, b: PlaceId) -> bool {
    let below = |x: PlaceId, y: PlaceId| {
        let mut at = Some(x);
        while let Some(p) = at {
            if p == y {
                return true;
            }
            at = facts.places.get(p.index()).and_then(|i| i.parent);
        }
        false
    };
    below(a, b) || below(b, a)
}
