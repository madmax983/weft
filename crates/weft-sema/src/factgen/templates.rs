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
//! `Unreachable`, `UnwindExit` and `Assert`. The rules of a reference
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
        for (kind, proj, v) in self.vars.parts_of(k.0, k.1) {
            if *kind == PartKind::U && !unset {
                continue;
            }
            if is_prefix(proj, prefix) || is_prefix(prefix, proj) {
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
        let acc = Access {
            vars: self.vars_of(place)?,
            places: a.places.clone(),
            ptrs,
            root,
        };
        Ok((acc, a))
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
    match op {
        Operand::Const(_) => Ok(()),
        Operand::Copy(q) => {
            let (a, _) = em.access(st, q, true)?;
            em.apply(n, kernel::read(&a));
            Ok(())
        }
        Operand::Move(q) => {
            let (mut a, al) = em.access(st, q, true)?;
            let ty = em.place_ty(q);
            let immovable = ty.is_some_and(|t| ir_props(em.tys, t).immovable);
            if relocate || immovable {
                a.vars = em.vars_with(q, false)?;
            }
            em.apply(n, kernel::read(&a));
            let plain = ty.is_some_and(|t| !em.tys.not_copy(t));
            if !plain {
                moved(em, n, st, q, &al)?;
            }
            Ok(())
        }
    }
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
            let (a, al) = em.access(st, q, false)?;
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
    let (a, al) = em.access(st, place, false)?;
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
    for &q in &al.places {
        let Some((k, path)) = em.roots.path_of(em.facts, q) else {
            continue;
        };
        let holder = em
            .h_below(k, &[])
            .into_iter()
            .filter(|(p, _)| is_prefix(p, &path))
            .max_by_key(|(p, _)| p.len())
            .map(|(_, v)| v)
            .or_else(|| em.s_var(k));
        if let Some(h) = holder {
            let frag = kernel::copy_ref(&[h], &refs);
            em.facts.points_into.extend(frag.points_into);
        }
    }
    Ok(())
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
        _ => Err(AlphaError::Later(
            "a terminator that runs another body (stages F5 and later)",
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
