//! The variables of a component (`docs/ir.md` 6.3).
//!
//! - `S(l)`: the owner variable of each local with storage of each body of
//!   the component (also a temporary, a by-value parameter, `_0`, a
//!   capability, a continuation, a scope capability and a task result). An
//!   upvar local uses the variable of its site local, and the environment of a
//!   closure body has no variable (it is an interface root).
//! - `H(l.q)`: each move path that the body assigns on its own and whose type
//!   can hold a reference, a function value, a capability or a task.
//! - `U(l.q)`: each place field path that can have no value (an `Uninit` of a
//!   projected place).
//! - `C(x)`: the cell of each local that a closure captures `ByRef`.
//!
//! The flags come from the properties of the local ([`weft_ir::Props`]; for a
//! local of a function type the builder joins the modes of the closures that
//! the old analysis gives it). `immovable` is off for an `in_place` local
//! (`docs/ir.md` 5.36). `once_var` also holds for a task handle, a task
//! result, a scope capability and a `once` continuation. `uniq` is the `@ uniq`
//! property of the local; the analysis (stage F3) makes it "each value is
//! `@ uniq`".

use std::collections::HashMap;

use weft_facts::{FnFacts, Span, VarId, VarInfo, VarKind};
use weft_ir::ty::{AdtKind, Lang, TyProp};
use weft_ir::{
    BodyId, CaptureMode, LocalDecl, LocalId, LocalKind, Place, Program, Proj, StmtKind, TempKind,
    TermKind, Ty, TyId, TyTable,
};

use super::alpha::{local_text, owner_local, path_text, path_ty};

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
}

/// The variables of one component.
#[derive(Clone, Debug, Default)]
pub struct Vars {
    /// The variable of each key.
    ids: HashMap<VarKey, VarId>,
    /// The keys, in the order of the variables.
    order: Vec<VarKey>,
}

/// The span of the facts for an IR span.
const fn span(s: weft_ir::Span) -> Span {
    Span { lo: s.lo, hi: s.hi }
}

/// True if a value of type `t` is a task handle.
fn is_task(tys: &TyTable, t: TyId) -> bool {
    matches!(tys.lang(t), Some((Lang::Task, _)))
}

/// The kind of the variable of a local.
fn var_kind(tys: &TyTable, d: &LocalDecl) -> VarKind {
    match d.kind {
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
        let mut v = Self::default();
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
                    name: local_text(tys, d),
                    kind: var_kind(tys, d),
                    span: span(d.origin.span),
                    ty: tys.show(d.ty),
                    linear: d.props.linear,
                    has_on_abort: d.props.linear && d.props.on_abort,
                    once,
                    immovable: d.props.immovable && !d.in_place,
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
        v.cells(p, tys, facts, comp);
        v
    }

    /// Adds the variable `info` with the key `key`, if the key has none.
    fn add(&mut self, facts: &mut FnFacts, key: VarKey, info: VarInfo) {
        if self.ids.contains_key(&key) {
            return;
        }
        let id = facts.add_var(info);
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
            let info = Self::plain(path_text(p, tys, bid, place), span(sp), tys.show(t));
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
                let info = Self::plain(
                    format!("{} (cell)", local_text(tys, d)),
                    span(d.origin.span),
                    tys.show(d.ty),
                );
                self.add(facts, VarKey::C(ob, ol), info);
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
