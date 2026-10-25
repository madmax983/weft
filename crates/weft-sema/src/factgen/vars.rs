//! The variables of a component (`docs/ir.md` 6.3).
//!
//! - `S(l)`: the owner variable of each local with storage of each body of
//!   the component (also a temporary, a by-value parameter, `_0`, a
//!   capability, a continuation, a scope capability and a task result). An
//!   upvar local uses the variable of its site local, and the environment of a
//!   closure body has no variable (it is an interface root).
//! - `H(l.q)`: each move path that the body assigns on its own and whose type
//!   can hold a reference, a function value, a capability or a task. Each
//!   value of the part gets a variable of its own (`super::holders`); this
//!   variable is the first.
//! - `U(l.q)`: each place field path that can have no value (an `Uninit` of a
//!   projected place).
//! - `C(x)`: the cell of each local that a closure captures `ByRef`.
//! - `E(c, k)`: each `ByMove` capture `k` of a closure body: the value in the
//!   environment. It binds at the entry of the closure body, and a move of
//!   the capture moves it (stage F11). The environment local has no `S`
//!   variable: its captures are apart.
//! - `D(n)`: the drop pair of each `Drop` statement: the old value of the
//!   place behind a pointer. It binds at the `Drop` and ends at the `Assign`
//!   after it (W0601 for a linear old value).
//! - `W(b, v)`: the variant test of base place `b` for variant `v`, for each
//!   `Discriminant(b)` of the body and each variant `v` that a place of the
//!   body reads through `(b as v)`. It binds at each test, points into the
//!   variant place, and each access through the step uses it (`docs/ir.md`
//!   6.3): a new value of `b` between the test and a late read (a receiver
//!   place, 5.19) makes the read W0301.
//! - `N(t, b, v)`: the variant `v` of base `b` that the target of an
//!   assignment names, for an assignment whose value starts with temporary
//!   `t` (5.6, 5.7). It binds at `Live(t)` and the write of the target uses
//!   it: a value that gives `b` a new value is W0301.
//!
//! The flags come from the properties of the local ([`weft_ir::Props`]; for a
//! local of a function type the builder joins the modes of the closures that
//! the old analysis gives it). `immovable` is off for an `in_place` local
//! (`docs/ir.md` 5.36). `once_var` also holds for a task handle, a task
//! result, a scope capability and a `once` continuation. `uniq` is the `@ uniq`
//! property of the local; the analysis (stage F3) makes it "each value is
//! `@ uniq`".

use std::collections::{HashMap, HashSet};

use weft_facts::{FnFacts, Span, VarId, VarInfo, VarKind};
use weft_ir::ty::{AdtKind, Lang, TyProp};
use weft_ir::{
    BlockId, BodyId, BodyKind, CaptureMode, IterSource, LocalDecl, LocalId, LocalKind, Operand,
    Place, Program, Proj, Rvalue, StmtKind, TempKind, TermKind, Ty, TyId, TyTable,
};

use super::alpha::{local_text, owner_local, path_text, path_ty, place_ty};
use crate::analysis::transfer::rvalue_operands;
use crate::props::ir_props;

/// The key of a variable.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum VarKey {
    /// `S(l)`: the owner of the value of local `l` of a body.
    S(BodyId, LocalId),
    /// `H(l.q)`: a part of a local that the body assigns on its own.
    H(BodyId, Place),
    /// `U(l.q)`: a place field path that can have no value.
    U(BodyId, Place),
    /// `C(x)`: the cell of a local that a closure captures by reference.
    C(BodyId, LocalId),
    /// `E(c, k)`: the value of `ByMove` capture `k` in the environment of
    /// closure body `c`.
    E(BodyId, u32),
    /// `D(n)`: the drop pair of the `Drop` statement `at` of a block.
    D(BodyId, BlockId, u32),
    /// `W(b, v)`: the test of variant `v` of the value at base place `b`.
    W(BodyId, Place, u32),
    /// `N(t, b, v)`: variant `v` of base place `b` in the target of an
    /// assignment whose value starts with the temporary `t`.
    N(BodyId, LocalId, Place, u32),
}

/// The temporaries of the borrows of the `ByRef` captures of the closure
/// aggregates of the bodies `comp`: each operand `move t` of a `ByRef`
/// capture.
fn capture_refs(p: &Program, comp: &[BodyId]) -> HashSet<(BodyId, LocalId)> {
    let mut out = HashSet::new();
    for &bid in comp {
        let Some(b) = p.bodies.get(bid.index()) else {
            continue;
        };
        for blk in &b.blocks {
            for s in &blk.stmts {
                let StmtKind::Assign(_, Rvalue::Aggregate(weft_ir::AggKind::Closure(c), ops)) =
                    &s.kind
                else {
                    continue;
                };
                let Some(decl) = p.closures.get(c.index()) else {
                    continue;
                };
                for (cap, op) in decl.captures.iter().zip(ops) {
                    if let (CaptureMode::ByRef, Operand::Move(t)) = (cap.mode, op) {
                        if t.proj.is_empty() {
                            out.insert((bid, t.local));
                        }
                    }
                }
            }
        }
    }
    out
}

/// The variant steps of `place`: for each `Variant(v)` step, its base place
/// (the projections before it) and `v`.
pub fn variant_steps(place: &Place) -> Vec<(Place, u32)> {
    place
        .proj
        .iter()
        .enumerate()
        .filter_map(|(j, pr)| match pr {
            Proj::Variant(v) => Some((
                Place {
                    local: place.local,
                    proj: place
                        .proj
                        .get(..j)
                        .map(<[Proj]>::to_vec)
                        .unwrap_or_default(),
                },
                v.0,
            )),
            _ => None,
        })
        .collect()
}

/// The place `base` with the step `Variant(v)` after it.
pub fn variant_place(base: &Place, v: u32) -> Place {
    let mut proj = base.proj.clone();
    proj.push(Proj::Variant(weft_ir::VariantIdx(v)));
    Place {
        local: base.local,
        proj,
    }
}

/// The place of operand `o`, if it has one.
const fn op(o: &Operand) -> Option<&Place> {
    match o {
        Operand::Copy(q) | Operand::Move(q) => Some(q),
        Operand::Const(_) => None,
    }
}

/// The places that the statements and the terminators of a body access
/// (not the places that `Uninit` and `UnwindValue` name: they read no
/// value).
fn accessed(b: &weft_ir::Body) -> Vec<&Place> {
    let mut out: Vec<&Place> = Vec::new();
    for blk in &b.blocks {
        for s in &blk.stmts {
            match &s.kind {
                StmtKind::Assign(dest, rv) => {
                    out.push(dest);
                    out.extend(rvalue_operands(rv).into_iter().filter_map(op));
                    match rv {
                        Rvalue::Ref(q)
                        | Rvalue::Len(q)
                        | Rvalue::Discriminant(q)
                        | Rvalue::Iter(IterSource::Elems(q)) => out.push(q),
                        _ => {}
                    }
                }
                StmtKind::Drop(q) | StmtKind::Consume(q) | StmtKind::Mention(q) => out.push(q),
                StmtKind::Bounds(q, i) => {
                    out.push(q);
                    out.extend(op(i));
                }
                StmtKind::Print(ops) => out.extend(ops.iter().filter_map(op)),
                _ => {}
            }
        }
        let t = &blk.term.kind;
        match t {
            TermKind::Switch { on, .. } => out.extend(op(on)),
            TermKind::Call { callee, args, .. } => {
                if let weft_ir::Callee::Value(c) = callee {
                    out.extend(op(c));
                }
                out.extend(args.iter().filter_map(op));
            }
            TermKind::Perform { args, .. } => out.extend(args.iter().filter_map(op)),
            TermKind::Resume { kont, arg, .. } => {
                out.push(kont);
                out.extend(op(arg));
            }
            TermKind::ScopeWait { scope, .. } => out.push(scope),
            TermKind::Spawn { scope, task, .. } => {
                out.extend(op(scope));
                out.extend(op(task));
            }
            TermKind::Join { task, .. } | TermKind::Detach { task, .. } => out.extend(op(task)),
            TermKind::Fork { branches, .. } => out.extend(branches.iter().filter_map(op)),
            TermKind::Assert { cond, .. } => out.extend(op(cond)),
            TermKind::IterNext { iter, .. } => out.push(iter),
            _ => {}
        }
        out.extend(term_dest(t));
    }
    out
}

/// A variable of a part: its kind, the projections of the part, and the
/// variable.
pub type PartVar = (PartKind, Vec<Proj>, VarId);

/// An `N` variable of a value temporary: the base place, the variant and the
/// variable.
pub type NamedVar = (Place, u32, VarId);

/// The kind of a variable of a part ([`Vars::parts_of`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PartKind {
    /// `H(l.q)`: the references of a part.
    H,
    /// `U(l.q)`: a place field path that can have no value.
    U,
}

/// The variables of one component.
#[derive(Clone, Debug, Default)]
pub struct Vars {
    /// The variable of each key.
    ids: HashMap<VarKey, VarId>,
    /// The keys, in the order of the variables.
    order: Vec<VarKey>,
    /// The `H` and `U` variables of each local, with their projections.
    parts: HashMap<(BodyId, LocalId), Vec<PartVar>>,
    /// The locals whose value a construction builds in place: an `in_place`
    /// local, a temporary that gets an aggregate (`into` writes it into its
    /// destination, `docs/ir.md` 5.36), and a temporary that gets the result
    /// of a call (5.17).
    in_place: HashSet<(BodyId, LocalId)>,
    /// The `W` variables of each tested base place: the variant and the
    /// variable.
    tested: HashMap<(BodyId, Place), Vec<(u32, VarId)>>,
    /// The `N` variables of each value temporary: the base, the variant and
    /// the variable.
    named: HashMap<(BodyId, LocalId), Vec<NamedVar>>,
    /// The temporaries of the borrows of `ByRef` captures
    /// ([`Vars::is_capture_ref`]).
    capture_refs: HashSet<(BodyId, LocalId)>,
}

/// The span of the facts for an IR span.
const fn span(s: weft_ir::Span) -> Span {
    Span { lo: s.lo, hi: s.hi }
}

/// True if a value of type `t` is a task handle.
fn is_task(tys: &TyTable, t: TyId) -> bool {
    matches!(tys.lang(t), Some((Lang::Task, _)))
}

/// The name of the variable of `_0` of a body of kind `kind`: the
/// diagnostics name the frame by it (`docs/ir.md` 6.9). `None` for another
/// local.
fn result_text(kind: &BodyKind, d: &LocalDecl) -> Option<String> {
    if d.kind != LocalKind::Return {
        return None;
    }
    let text = match kind {
        BodyKind::Fn(_) | BodyKind::Test(_) => "the result",
        BodyKind::Closure(_) => "the closure result",
        BodyKind::Handled(_) => "handled body value",
        BodyKind::Scope(_) => "scope body value",
        BodyKind::Clause(..) => "clause value",
    };
    Some(text.to_string())
}

/// The kind of the variable of a local.
fn var_kind(tys: &TyTable, d: &LocalDecl) -> VarKind {
    match d.kind {
        LocalKind::Return => VarKind::Result,
        LocalKind::Param(_) => VarKind::Param,
        LocalKind::Temp(TempKind::Value) => VarKind::BlockValue,
        LocalKind::Temp(_) => VarKind::Temp,
        LocalKind::Iterator => VarKind::Iterator,
        LocalKind::Kont(_) => VarKind::Continuation,
        LocalKind::TaskResult(_) => VarKind::Task,
        _ if is_task(tys, d.ty) => VarKind::Task,
        _ => VarKind::Local,
    }
}

/// True if a value of type `t` can hold a reference, a function value, a
/// capability or a task (through fields too).
fn holds_values(tys: &TyTable, t: TyId, depth: usize) -> bool {
    let Some(ty) = tys.try_get(t) else {
        return false;
    };
    if depth > 32 {
        return true;
    }
    let deep = |x: TyId| holds_values(tys, x, depth + 1);
    match ty {
        // A type parameter can be any of them.
        Ty::Ref(_)
        | Ty::Slice(_)
        | Ty::Fn(_)
        | Ty::Cap(_)
        | Ty::Cont(..)
        | Ty::Scope
        | Ty::Param(_) => true,
        Ty::Adt(a, args) => tys.adts().get(a.index()).is_some_and(|d| {
            if matches!(d.lang, Some(Lang::Task | Lang::Scope)) {
                return true;
            }
            let carried = [TyProp::Refs, TyProp::Fns].iter().any(|p| {
                let row = d.row(*p);
                row.always
                    || row
                        .params
                        .iter()
                        .any(|&j| args.get(j as usize).is_some_and(|&x| deep(x)))
            });
            // A task in a field: the property rows do not say it.
            let task_field = match &d.kind {
                AdtKind::Struct(fs) => fs.iter().any(|f| is_task(tys, f.ty)),
                AdtKind::Enum(vs) => vs.iter().flat_map(|v| &v.fields).any(|&x| is_task(tys, x)),
                AdtKind::Extern { .. } => false,
            };
            carried || task_field || args.iter().any(|&x| deep(x))
        }),
        Ty::Tuple(ts) => ts.iter().any(|&x| deep(x)),
        Ty::Array(x, _) | Ty::Iter(x) => deep(*x),
        Ty::Unit | Ty::Bool | Ty::Never | Ty::Int(_) => false,
    }
}

/// True if `place` is a move path below its local: a projection with no
/// `Deref`, no index and no split (a part that the local owns).
fn is_part(place: &Place) -> bool {
    !place.proj.is_empty()
        && place
            .proj
            .iter()
            .all(|p| matches!(p, Proj::Field(_) | Proj::Variant(_)))
}

/// The locals of the bodies `comp` whose value a construction builds in
/// place: each `in_place` local, each temporary that gets an aggregate, and
/// each temporary that gets the result of a call.
fn built_in_place(p: &Program, comp: &[BodyId]) -> HashSet<(BodyId, LocalId)> {
    let mut out = HashSet::new();
    for &bid in comp {
        let Some(b) = p.bodies.get(bid.index()) else {
            continue;
        };
        for (i, d) in b.locals.iter().enumerate() {
            if d.in_place {
                out.insert((bid, LocalId(u32::try_from(i).unwrap_or(u32::MAX))));
            }
        }
        let temp = |dest: &Place| {
            dest.proj.is_empty()
                && b.locals
                    .get(dest.local.index())
                    .is_some_and(|d| matches!(d.kind, LocalKind::Temp(_)))
        };
        for blk in &b.blocks {
            for s in &blk.stmts {
                if let StmtKind::Assign(dest, weft_ir::Rvalue::Aggregate(..)) = &s.kind {
                    if temp(dest) {
                        out.insert((bid, dest.local));
                    }
                }
            }
            // A call writes its result into its destination, with the place
            // fields that have no value (`docs/ir.md` 5.17).
            if let TermKind::Call { dest, .. } = &blk.term.kind {
                if temp(dest) {
                    out.insert((bid, dest.local));
                }
            }
        }
    }
    out
}

/// The locals of the bodies `comp` that a call takes as a whole: `move l`
/// as an argument. The callee can move the value (`Vec.push` moves it when
/// its buffer grows), unless the builder builds it in place (`in_place`).
fn call_args(p: &Program, comp: &[BodyId]) -> HashSet<(BodyId, LocalId)> {
    let mut out = HashSet::new();
    for &bid in comp {
        let Some(b) = p.bodies.get(bid.index()) else {
            continue;
        };
        for blk in &b.blocks {
            if let TermKind::Call { args, .. } = &blk.term.kind {
                for a in args {
                    if let weft_ir::Operand::Move(q) = a {
                        if q.proj.is_empty() {
                            out.insert((bid, q.local));
                        }
                    }
                }
            }
        }
    }
    out
}

/// The place that a terminator writes, if it writes one.
const fn term_dest(t: &TermKind) -> Option<&Place> {
    match t {
        TermKind::Call { dest, .. }
        | TermKind::Perform { dest, .. }
        | TermKind::Resume { dest, .. }
        | TermKind::Handle { dest, .. }
        | TermKind::Scope { dest, .. }
        | TermKind::Join { dest, .. }
        | TermKind::Fork { dest, .. }
        | TermKind::IterNext { dest, .. } => Some(dest),
        TermKind::Spawn { dest, .. } => dest.as_ref(),
        _ => None,
    }
}

impl Vars {
    /// Makes the variables of the bodies `comp` of a component in `facts`, in
    /// this order: `S` of each local of each body, then `H`, `U` and `C`.
    pub fn build(p: &Program, tys: &mut TyTable, facts: &mut FnFacts, comp: &[BodyId]) -> Self {
        let mut v = Self {
            in_place: built_in_place(p, comp),
            ..Self::default()
        };
        let to_callee = call_args(p, comp);
        for &bid in comp {
            let Some(b) = p.bodies.get(bid.index()) else {
                continue;
            };
            for (li, d) in b.locals.iter().enumerate() {
                if matches!(d.kind, LocalKind::Upvar(_) | LocalKind::Env) {
                    continue;
                }
                let l = LocalId(u32::try_from(li).unwrap_or(u32::MAX));
                let task = is_task(tys, d.ty);
                let once = d.props.once
                    || task
                    || matches!(
                        d.kind,
                        LocalKind::TaskResult(_) | LocalKind::ScopeCap | LocalKind::Kont(false)
                    );
                let info = VarInfo {
                    name: result_text(&b.kind, d).unwrap_or_else(|| local_text(tys, d)),
                    kind: var_kind(tys, d),
                    span: span(d.origin.span),
                    ty: tys.show(d.ty),
                    linear: d.props.linear,
                    has_on_abort: d.props.linear && d.props.on_abort,
                    once,
                    // A value built in place does not move, unless a call
                    // that does not build it in place takes it (W0604).
                    immovable: d.props.immovable
                        && !d.in_place
                        && (!v.in_place.contains(&(bid, l)) || to_callee.contains(&(bid, l))),
                    uniq: d.props.uniq,
                    nonportable: d.props.nonportable,
                    callable: d.props.callable,
                };
                v.add(facts, VarKey::S(bid, l), info);
            }
        }
        for &bid in comp {
            v.parts(p, tys, facts, bid);
        }
        v.relocated(p, tys, facts, comp);
        v.cells(p, tys, facts, comp);
        v.env_values(p, tys, facts, comp);
        v.capture_refs = capture_refs(p, comp);
        for &bid in comp {
            v.drop_pairs(p, tys, facts, bid);
        }
        for &bid in comp {
            v.variant_tests(p, tys, facts, bid);
        }
        v
    }

    /// Adds the `W` and `N` variables of body `bid`.
    fn variant_tests(&mut self, p: &Program, tys: &mut TyTable, facts: &mut FnFacts, bid: BodyId) {
        let Some(b) = p.bodies.get(bid.index()) else {
            return;
        };
        // The first test of each base place.
        let mut tests: HashMap<&Place, weft_ir::Span> = HashMap::new();
        for blk in &b.blocks {
            for s in &blk.stmts {
                if let StmtKind::Assign(_, Rvalue::Discriminant(q)) = &s.kind {
                    tests.entry(q).or_insert(s.origin.span);
                }
            }
        }
        let mut new: Vec<(VarKey, VarInfo)> = Vec::new();
        for q in accessed(b) {
            for (base, v) in variant_steps(q) {
                let Some(&sp) = tests.get(&base) else {
                    continue;
                };
                let key = VarKey::W(bid, base.clone(), v);
                if self.ids.contains_key(&key) || new.iter().any(|(k, _)| *k == key) {
                    continue;
                }
                let ty = place_ty(p, tys, bid, &base).map_or_else(String::new, |t| tys.show(t));
                let mut info = Self::plain(
                    format!("variant test of `{}`", path_text(p, tys, bid, &base)),
                    span(sp),
                    ty,
                );
                info.kind = VarKind::Temp;
                new.push((key, info));
            }
        }
        // The target of an assignment: `p = move t`, and `t2 := Op(copy p,
        // move t)` of a compound assignment.
        let temp = |l: &LocalId| {
            b.locals
                .get(l.index())
                .is_some_and(|d| matches!(d.kind, LocalKind::Temp(_)))
        };
        for blk in &b.blocks {
            for s in &blk.stmts {
                let (StmtKind::Assign(target, Rvalue::Use(Operand::Move(t)))
                | StmtKind::Assign(
                    _,
                    Rvalue::Binary(_, _, Operand::Copy(target), Operand::Move(t)),
                )) = &s.kind
                else {
                    continue;
                };
                if !t.proj.is_empty() || !temp(&t.local) {
                    continue;
                }
                for (base, v) in variant_steps(target) {
                    let key = VarKey::N(bid, t.local, base.clone(), v);
                    if self.ids.contains_key(&key) || new.iter().any(|(k, _)| *k == key) {
                        continue;
                    }
                    let named = variant_place(&base, v);
                    let ty = place_ty(p, tys, bid, &base).map_or_else(String::new, |t| tys.show(t));
                    let mut info = Self::plain(
                        format!("assigned place `{}`", path_text(p, tys, bid, &named)),
                        span(s.origin.span),
                        ty,
                    );
                    info.kind = VarKind::Temp;
                    new.push((key, info));
                }
            }
        }
        for (key, info) in new {
            self.add(facts, key, info);
        }
    }

    /// The `W` variable of each variant step of `place` of body `body`
    /// that has one.
    pub fn tests_of(&self, body: BodyId, place: &Place) -> Vec<VarId> {
        variant_steps(place)
            .into_iter()
            .filter_map(|(base, v)| self.get(&VarKey::W(body, base, v)))
            .collect()
    }

    /// The `N` variables of body `body` for the assignment whose value
    /// starts with temporary `t`: the base, the variant and the variable.
    pub fn named_by(&self, body: BodyId, t: LocalId) -> &[NamedVar] {
        self.named.get(&(body, t)).map_or(&[], Vec::as_slice)
    }

    /// The `W` variables of body `body` that the test of base place `base`
    /// binds: the variant and the variable.
    pub fn tested_at(&self, body: BodyId, base: &Place) -> &[(u32, VarId)] {
        self.tested
            .get(&(body, base.clone()))
            .map_or(&[], Vec::as_slice)
    }

    /// The `N` variable of each variant step of `target` for the assignment
    /// whose value starts with temporary `t`.
    pub fn named_of(&self, body: BodyId, t: LocalId, target: &Place) -> Vec<VarId> {
        variant_steps(target)
            .into_iter()
            .filter_map(|(base, v)| self.get(&VarKey::N(body, t, base, v)))
            .collect()
    }

    /// True if a construction builds the value of local `l` of body `body`
    /// in place: a move of the whole local into its destination does not
    /// move the value, and the place fields of the value go with it.
    pub fn built_in_place(&self, body: BodyId, l: LocalId) -> bool {
        self.in_place.contains(&(body, l))
    }

    /// Adds the `U` variables of the place fields that a move of a value
    /// built in place gives its destination: `d = Wrap { move t, .. }` with
    /// `U(t.1)` gives `U(d.0.1)`. A chain of such moves gives a variable at
    /// each step.
    fn relocated(&mut self, p: &Program, tys: &mut TyTable, facts: &mut FnFacts, comp: &[BodyId]) {
        // Each round adds the variables of one more step of a chain.
        for _ in 0..=comp.len().saturating_add(16) {
            let mut new: Vec<(VarKey, VarInfo)> = Vec::new();
            for &bid in comp {
                let Some(b) = p.bodies.get(bid.index()) else {
                    continue;
                };
                for blk in &b.blocks {
                    for s in &blk.stmts {
                        let StmtKind::Assign(dest, rv) = &s.kind else {
                            continue;
                        };
                        if !is_part(dest) && !dest.proj.is_empty() {
                            continue;
                        }
                        let Ok((db, dl)) = owner_local(p, bid, dest.local) else {
                            continue;
                        };
                        for (steps, t) in crate::analysis::transfer::moved_wholes(rv) {
                            let Ok((tb, tl)) = owner_local(p, bid, t) else {
                                continue;
                            };
                            if !self.in_place.contains(&(tb, tl)) {
                                continue;
                            }
                            for (kind, r, _) in self.parts_of(tb, tl) {
                                if *kind != PartKind::U {
                                    continue;
                                }
                                let mut proj = dest.proj.clone();
                                proj.extend(steps.iter().map(|s| match s {
                                    crate::analysis::PathStep::Field(i) => {
                                        Proj::Field(weft_ir::FieldIdx(*i))
                                    }
                                    crate::analysis::PathStep::Variant(v) => {
                                        Proj::Variant(weft_ir::VariantIdx(*v))
                                    }
                                }));
                                proj.extend(r.iter().cloned());
                                let place = Place { local: dl, proj };
                                let key = VarKey::U(db, place.clone());
                                if self.ids.contains_key(&key) {
                                    continue;
                                }
                                let ty = path_ty(p, tys, db, &place)
                                    .map_or_else(String::new, |t| tys.show(t));
                                let info = Self::plain(
                                    path_text(p, tys, db, &place),
                                    span(s.origin.span),
                                    ty,
                                );
                                new.push((key, info));
                            }
                        }
                    }
                }
            }
            if new.is_empty() {
                return;
            }
            for (k, info) in new {
                self.add(facts, k, info);
            }
        }
    }

    /// Adds the drop pair variable of each `Drop` statement of body `bid`.
    /// It has the flags of the type of the place: the old value can be
    /// linear.
    fn drop_pairs(&mut self, p: &Program, tys: &mut TyTable, facts: &mut FnFacts, bid: BodyId) {
        let Some(b) = p.bodies.get(bid.index()) else {
            return;
        };
        for (bi, blk) in b.blocks.iter().enumerate() {
            for (si, s) in blk.stmts.iter().enumerate() {
                let StmtKind::Drop(place) = &s.kind else {
                    continue;
                };
                let block = BlockId(u32::try_from(bi).unwrap_or(u32::MAX));
                let at = u32::try_from(si).unwrap_or(u32::MAX);
                let ty = place_ty(p, tys, bid, place);
                let props = ty.map(|t| ir_props(tys, t)).unwrap_or_default();
                let mut info = Self::plain(
                    format!("the old value of `{}`", path_text(p, tys, bid, place)),
                    span(s.origin.span),
                    ty.map_or_else(String::new, |t| tys.show(t)),
                );
                info.kind = VarKind::Temp;
                info.linear = props.linear;
                info.has_on_abort = props.linear && props.on_abort;
                info.once = props.linear;
                self.add(facts, VarKey::D(bid, block, at), info);
            }
        }
    }

    /// The `H` and `U` variables of local `l` of body `body` (the owner
    /// local, not an upvar), with the projections of their parts.
    pub fn parts_of(&self, body: BodyId, l: LocalId) -> &[PartVar] {
        self.parts.get(&(body, l)).map_or(&[], Vec::as_slice)
    }

    /// The `H` variable of each part of the component: the key of its
    /// owner local, its move path and its variable.
    pub fn holder_parts(
        &self,
    ) -> Vec<(crate::analysis::Key, Vec<crate::analysis::PathStep>, VarId)> {
        let mut out = Vec::new();
        for key in &self.order {
            let VarKey::H(b, pl) = key else {
                continue;
            };
            let Some(v) = self.ids.get(key) else {
                continue;
            };
            let steps: Option<Vec<crate::analysis::PathStep>> = pl
                .proj
                .iter()
                .map(|pr| match pr {
                    Proj::Field(f) => Some(crate::analysis::PathStep::Field(f.0)),
                    Proj::Variant(x) => Some(crate::analysis::PathStep::Variant(x.0)),
                    _ => None,
                })
                .collect();
            if let Some(steps) = steps {
                out.push(((*b, pl.local), steps, *v));
            }
        }
        out
    }

    /// Adds the variable `info` with the key `key`, if the key has none.
    fn add(&mut self, facts: &mut FnFacts, key: VarKey, info: VarInfo) {
        if self.ids.contains_key(&key) {
            return;
        }
        let id = facts.add_var(info);
        match &key {
            VarKey::H(b, pl) => self.parts.entry((*b, pl.local)).or_default().push((
                PartKind::H,
                pl.proj.clone(),
                id,
            )),
            VarKey::U(b, pl) => self.parts.entry((*b, pl.local)).or_default().push((
                PartKind::U,
                pl.proj.clone(),
                id,
            )),
            VarKey::W(b, base, v) => self
                .tested
                .entry((*b, base.clone()))
                .or_default()
                .push((*v, id)),
            VarKey::N(b, t, base, v) => {
                self.named
                    .entry((*b, *t))
                    .or_default()
                    .push((base.clone(), *v, id));
            }
            _ => {}
        }
        self.ids.insert(key.clone(), id);
        self.order.push(key);
    }

    /// A variable with no flags, for a part or a cell.
    const fn plain(name: String, sp: Span, ty: String) -> VarInfo {
        VarInfo {
            name,
            kind: VarKind::Local,
            span: sp,
            ty,
            linear: false,
            has_on_abort: false,
            once: false,
            immovable: false,
            uniq: false,
            nonportable: false,
            callable: false,
        }
    }

    /// Adds the `H` and `U` variables of body `bid`.
    fn parts(&mut self, p: &Program, tys: &mut TyTable, facts: &mut FnFacts, bid: BodyId) {
        let Some(b) = p.bodies.get(bid.index()) else {
            return;
        };
        let mut writes: Vec<(&Place, weft_ir::Span)> = Vec::new();
        let mut unset: Vec<(&Place, weft_ir::Span)> = Vec::new();
        for blk in &b.blocks {
            for s in &blk.stmts {
                match &s.kind {
                    StmtKind::Assign(place, _) => writes.push((place, s.origin.span)),
                    StmtKind::Uninit(place) if !place.proj.is_empty() => {
                        unset.push((place, s.origin.span));
                    }
                    _ => {}
                }
            }
            if let Some(dest) = term_dest(&blk.term.kind) {
                writes.push((dest, blk.term.origin.span));
            }
        }
        for (place, sp) in writes {
            if !is_part(place) {
                continue;
            }
            let Some(t) = path_ty(p, tys, bid, place) else {
                continue;
            };
            if !holds_values(tys, t, 0) {
                continue;
            }
            let Ok((ob, ol)) = owner_local(p, bid, place.local) else {
                continue;
            };
            let key = VarKey::H(
                ob,
                Place {
                    local: ol,
                    proj: place.proj.clone(),
                },
            );
            if self.ids.contains_key(&key) {
                continue;
            }
            // Each value of the part gets a variable of its own: this one is
            // the first (`super::holders`). The name is that of the part
            // holders of the old lowering.
            let mut info = Self::plain(
                format!("value in `{}`", path_text(p, tys, bid, place)),
                span(sp),
                tys.show(t),
            );
            info.kind = VarKind::Temp;
            self.add(facts, key, info);
        }
        for (place, sp) in unset {
            let Ok((ob, ol)) = owner_local(p, bid, place.local) else {
                continue;
            };
            let key = VarKey::U(
                ob,
                Place {
                    local: ol,
                    proj: place.proj.clone(),
                },
            );
            if self.ids.contains_key(&key) {
                continue;
            }
            let ty = path_ty(p, tys, bid, place).map_or_else(String::new, |t| tys.show(t));
            let info = Self::plain(path_text(p, tys, bid, place), span(sp), ty);
            self.add(facts, key, info);
        }
    }

    /// Adds the `C` variable of each local of the component that a closure
    /// of the component captures `ByRef`.
    fn cells(&mut self, p: &Program, tys: &TyTable, facts: &mut FnFacts, comp: &[BodyId]) {
        for c in &p.closures {
            if !comp.contains(&c.maker) {
                continue;
            }
            for cap in &c.captures {
                if cap.mode != CaptureMode::ByRef || !cap.source.proj.is_empty() {
                    continue;
                }
                let Ok((ob, ol)) = owner_local(p, c.maker, cap.source.local) else {
                    continue;
                };
                let Some(d) = p
                    .bodies
                    .get(ob.index())
                    .and_then(|b| b.locals.get(ol.index()))
                else {
                    continue;
                };
                if d.kind == LocalKind::Env {
                    continue;
                }
                let mut info = Self::plain(
                    format!("{} (cell)", local_text(tys, d)),
                    span(d.origin.span),
                    tys.show(d.ty),
                );
                info.kind = var_kind(tys, d);
                self.add(facts, VarKey::C(ob, ol), info);
            }
        }
    }

    /// True if local `l` of body `body` is the temporary of the borrow of a
    /// `ByRef` capture: the operand `move t` of a closure aggregate, with
    /// `t := &x` (`docs/ir.md` 5.22).
    pub fn is_capture_ref(&self, body: BodyId, l: LocalId) -> bool {
        self.capture_refs.contains(&(body, l))
    }

    /// Adds the `E` variable of each `ByMove` capture of each closure body
    /// of the component: the flags come from the type of the capture.
    fn env_values(&mut self, p: &Program, tys: &mut TyTable, facts: &mut FnFacts, comp: &[BodyId]) {
        for &bid in comp {
            let Some((c, decl)) = p.closure_of(bid) else {
                continue;
            };
            let origin = p
                .bodies
                .get(bid.index())
                .map_or_else(weft_ir::Span::default, |b| b.origin.span);
            for (k, cap) in decl.captures.iter().enumerate() {
                if cap.mode != CaptureMode::ByMove {
                    continue;
                }
                let k = u32::try_from(k).unwrap_or(u32::MAX);
                let Some(t) = super::alpha::capture_ty(p, tys, c, k) else {
                    continue;
                };
                let props = ir_props(tys, t);
                let mut info = Self::plain(
                    super::alpha::capture_name(p, c, k),
                    span(origin),
                    tys.show(t),
                );
                info.linear = props.linear;
                info.has_on_abort = props.linear && props.on_abort;
                info.once = props.once || is_task(tys, t);
                info.nonportable = props.nonportable;
                // A move of the capture in the body moves the value again.
                info.immovable = props.immovable;
                self.add(facts, VarKey::E(bid, k), info);
            }
        }
    }

    /// The variable of `key`, if it has one.
    pub fn get(&self, key: &VarKey) -> Option<VarId> {
        self.ids.get(key).copied()
    }

    /// The keys, in the order of the variables.
    pub fn keys(&self) -> impl Iterator<Item = &VarKey> {
        self.order.iter()
    }

    /// The number of variables.
    pub fn len(&self) -> usize {
        self.order.len()
    }

    /// True if the component has no variable.
    pub fn is_empty(&self) -> bool {
        self.order.is_empty()
    }
}
