//! Cleanup chains (`docs/ir.md` 5.1.6, 5.28).
//!
//! Each terminator that can abort gets the cleanup chain of the frame at
//! its point. The chain finishes each value that has a cell there, in the
//! order of V16:
//!
//! ```text
//! UnwindKont(k); Dead(k)                    // a clause: the continuation first
//! [UnwindValue(_0, a)]; Dead(_0)            // only after `_0` gets its value
//! [UnwindValue(t, a)]; Dead(t) ...          // the temporaries, the newest first
//! [UnwindValue(l, a)]; Dead(l) ...          // the other locals, the highest first
//! Dead(_0)                                  // `_0` with no value
//! [UnwindValue(p, a)]; Dead(p) ...          // the parameters, the last first
//! Goto(unwind_exit)
//! ```
//!
//! A value that is not plain data gets `UnwindValue` before its `Dead`.
//! Plain data gets only its `Dead`, but for the scope capability of a scope
//! body: its `UnwindValue(s, Drop)` cancels and joins the tasks of the
//! scope. The action comes from the type
//! ([`Builder::unwind_parts`]).
//!
//! Two chains with the same suffix share the blocks of the suffix: the
//! block that finishes local `l` and goes on to block `b` is one block. So
//! the blocks grow with the number of locals, not with the number of
//! terminators.

use std::collections::HashMap;
use std::rc::Rc;

use weft_ir::ty::{AdtKind, Lang};
use weft_ir::{
    BlockId, DerefKind, FieldIdx, LocalId, LocalKind, Origin, Place, Proj, StmtKind, TempKind,
    TermKind, Ty, TyId, UnwindAction, VariantIdx,
};
use weft_syntax::ast::Span;

use super::{id_of, Builder, Draft, RET};
use crate::program::ItemRef;

/// The number of parts above which a value gets one action for the whole
/// value.
const LIMIT: usize = 64;

/// The depth of the parts below which the walk of a type stops: the walk
/// gives one action for the part at that depth.
const DEPTH: usize = 16;

/// The parts of a value that the unwinder finishes one by one: the path of
/// each part below the value, and its action.
pub(super) type UnwindParts = Rc<[(Vec<Proj>, UnwindAction)]>;

/// The actions of the full types of one body, by type.
pub(super) type UnwindTable = HashMap<TyId, UnwindParts>;

impl Builder<'_> {
    /// Returns the cleanup block of an abort at the current point
    /// (`docs/ir.md` 5.1.6): the chain of the frame, in the order of V16.
    ///
    /// The locals of each class (temporaries, other locals) are a stack over
    /// the scopes: a scope gets new locals of a class only while no scope
    /// inside it holds that class, so the locals of an inner scope are
    /// newer. So the chain of a class is the locals of each scope, from the
    /// outermost, in order. Each scope keeps its part of the chain
    /// ([`super::ChainPart`]), and a later chain adds only the new locals:
    /// the cost of a chain is the number of scopes and the new locals, not
    /// the number of locals.
    pub(super) fn cleanup(&mut self, origin: Origin) -> BlockId {
        let valued = self.ret_value;
        let mut next = self.chain_base(valued, origin);
        for class in [0, 1] {
            for si in 0..self.scopes.len() {
                let Some(s) = self.scopes.get_mut(si) else {
                    continue;
                };
                let mut part = std::mem::take(&mut s.chain[class]);
                // The new locals of the scope that are of the class.
                for &l in s.locals.get(part.seen..).unwrap_or_default() {
                    if Some(l) == self.kont {
                        continue;
                    }
                    let of = match self.locals.get(l.index()).map(|d| d.kind) {
                        // A promoted temporary holds plain data: the
                        // unwinder has nothing to finish, and its `Live`
                        // may not have run (`docs/ir.md` 5.10).
                        Some(LocalKind::Temp(TempKind::Promoted)) => continue,
                        Some(LocalKind::Temp(_)) => 1,
                        // The capability of a handled body and the scope
                        // capability end with the parameters.
                        Some(LocalKind::Param(_) | LocalKind::Cap(_) | LocalKind::ScopeCap) => {
                            continue
                        }
                        _ => 0,
                    };
                    if of == class {
                        part.members.push(l);
                    }
                }
                part.seen = s.locals.len();
                let (start, mut head) = match part.built {
                    Some((below, n)) if below == next => (n, part.head),
                    _ => (0, next),
                };
                for &l in part.members.get(start..).unwrap_or_default() {
                    head = self.chain_node(l, head, origin);
                }
                part.built = Some((next, part.members.len()));
                part.head = head;
                next = head;
                if let Some(s) = self.scopes.get_mut(si) {
                    s.chain[class] = part;
                }
            }
        }
        if valued {
            next = self.chain_node(RET, next, origin);
        }
        if let Some(k) = self.kont {
            next = self.chain_node(k, next, origin);
        }
        BlockId(id_of(next))
    }

    /// Returns the cleanup block that finishes local `l` and goes to block
    /// `next`: `UnwindValue` of each part that the unwinder finishes, then
    /// `Dead(l)`. For the continuation of a clause it is `UnwindKont(l);
    /// Dead(l)`.
    fn chain_node(&mut self, l: LocalId, next: usize, origin: Origin) -> usize {
        if let Some(&b) = self.chains.get(&(l, next)) {
            return b;
        }
        let mut stmts = Vec::new();
        if Some(l) == self.kont {
            stmts.push(StmtKind::UnwindKont(l));
        } else {
            self.finish_value(l, &mut stmts);
        }
        stmts.push(StmtKind::Dead(l));
        let b = self.cleanup_block(stmts, origin);
        if let Some(d) = self.blocks.get_mut(b) {
            d.term = Some(weft_ir::Term {
                kind: TermKind::Goto(BlockId(id_of(next))),
                origin,
            });
        }
        self.chains.insert((l, next), b);
        b
    }

    /// Returns the last block of each cleanup chain: `Dead(_0)` if `_0` has
    /// no value (`valued` is false), then the capability of a handled body
    /// and the parameters, from the last.
    /// With no terminator it goes to the unwind exit.
    fn chain_base(&mut self, valued: bool, origin: Origin) -> usize {
        let i = usize::from(valued);
        if let Some(b) = self.chain_base.get(i).copied().flatten() {
            return b;
        }
        let mut stmts = Vec::new();
        if !valued {
            stmts.push(StmtKind::Dead(RET));
        }
        let params: Vec<LocalId> = self
            .params
            .iter()
            .copied()
            .chain(self.cap_params.iter().map(|(_, l)| *l))
            .rev()
            .collect();
        for p in params {
            // The environment of a closure outlives the run: it does not end.
            let env = self.locals.get(p.index()).map(|d| d.kind) == Some(LocalKind::Env);
            if Some(p) == self.kont || env {
                continue;
            }
            self.finish_value(p, &mut stmts);
            stmts.push(StmtKind::Dead(p));
        }
        let b = self.cleanup_block(stmts, origin);
        if let Some(slot) = self.chain_base.get_mut(i) {
            *slot = Some(b);
        }
        b
    }

    /// Adds a cleanup block with statements `stmts`. With no terminator it
    /// goes to the unwind exit (`Builder::finish`).
    fn cleanup_block(&mut self, stmts: Vec<StmtKind>, origin: Origin) -> usize {
        let b = self.blocks.len();
        self.blocks.push(Draft {
            stmts: stmts
                .into_iter()
                .map(|kind| weft_ir::Stmt { kind, origin })
                .collect(),
            term: None,
            live: false,
            cleanup: true,
        });
        b
    }

    /// Adds to `out` the `UnwindValue` statements that finish the value of
    /// local `l` (`docs/ir.md` 5.1.6). Plain data needs none. A value with
    /// no linear part gets `Drop`. A value with linear parts gets the
    /// actions of its parts ([`Self::unwind_parts`]). The properties of the
    /// local decide when the type cannot (a function value is a closure
    /// whose properties come from the analysis).
    fn finish_value(&mut self, l: LocalId, out: &mut Vec<StmtKind>) {
        let Some(d) = self.locals.get(l.index()) else {
            return;
        };
        // The scope capability is plain data, but its `UnwindValue` cancels
        // the tasks of the scope and waits for them (5.1.6).
        if d.kind == LocalKind::ScopeCap {
            out.push(StmtKind::UnwindValue(Place::local(l), UnwindAction::Drop));
            return;
        }
        // A plain-data value needs no `UnwindValue`. A local of a function
        // type that can hold a linear closure gets one (its `copy` comes from
        // its type, its `linear` from the analysis: `irbuild/mod.rs`).
        if d.props.copy && !d.props.linear {
            return;
        }
        let (ty, props) = (d.ty, d.props);
        let parts = self.unwind_parts(ty);
        if parts.is_empty() {
            let a = if props.linear && !props.on_abort {
                UnwindAction::Fault
            } else {
                UnwindAction::Drop
            };
            out.push(StmtKind::UnwindValue(Place::local(l), a));
            return;
        }
        for (proj, a) in parts.iter() {
            let place = Place {
                local: l,
                proj: proj.clone(),
            };
            out.push(StmtKind::UnwindValue(place, a.clone()));
        }
    }

    /// Returns the parts of a value of type `t` that the unwinder finishes
    /// one by one, with the action of each (`docs/ir.md` 5.1.6), in field
    /// order (`extract_linear` of the interpreter). Empty for a type with no
    /// linear part: the value drops as a whole.
    ///
    /// - A type that declares `on abort = f` gets `OnAbort(f)` for the
    ///   whole value: `f` finishes its linear parts.
    /// - A linear type with no `on abort` gets `Fault`: W0602 rejects each
    ///   program that can reach it. A linear extern type whose runtime has
    ///   `on abort` (a task handle) gets `Drop`, or `Fault` if a type
    ///   argument has a linear part with no `on abort`.
    /// - Another type gives the parts of its fields, of its tuple parts, of
    ///   the payloads of its variants (`(p as V).k`: the unwinder finishes
    ///   the payload only if the value has the variant), and of the target
    ///   of a `Box`. The elements of an array or of a `Vec` get one action
    ///   (`p[]`) if the element type has one action for the whole value.
    /// - A part that the walk does not follow (a recursive type, an `Rc`, a
    ///   very deep or a very wide type) gets one action for the whole part:
    ///   `Fault` if a linear part in it has no `on abort`, else `Drop`.
    ///
    /// A type parameter is not linear here: the instance decides at run
    /// time, so its value gets `Drop`.
    pub(super) fn unwind_parts(&mut self, t: TyId) -> UnwindParts {
        if let Some(p) = self.unwinds.get(&t) {
            return Rc::clone(p);
        }
        let mut out = Vec::new();
        let mut path = Vec::new();
        let mut stack = Vec::new();
        self.walk_parts(t, &mut path, &mut stack, &mut out);
        if out.len() > LIMIT {
            out = vec![(Vec::new(), self.whole_action(t))];
        }
        let parts: UnwindParts = out.into();
        self.unwinds.insert(t, Rc::clone(&parts));
        parts
    }

    /// Returns the action for a value of type `t` as a whole: `Fault` if a
    /// linear part of it has no `on abort`, else `Drop`.
    fn whole_action(&self, t: TyId) -> UnwindAction {
        if self.props(t).on_abort {
            UnwindAction::Drop
        } else {
            UnwindAction::Fault
        }
    }

    /// Adds to `out` the parts of the part at `path` of type `t`
    /// ([`Self::unwind_parts`]). `stack` has the types of the parts above
    /// it.
    fn walk_parts(
        &mut self,
        t: TyId,
        path: &mut Vec<Proj>,
        stack: &mut Vec<TyId>,
        out: &mut Vec<(Vec<Proj>, UnwindAction)>,
    ) {
        if out.len() > LIMIT || !self.props(t).linear {
            return;
        }
        let whole = self.whole_action(t);
        let Some(ty) = self.tys.try_get(t).cloned() else {
            out.push((path.clone(), whole));
            return;
        };
        if let Ty::Adt(a, _) = &ty {
            let Some(decl) = self.tys.adts().get(a.index()) else {
                out.push((path.clone(), whole));
                return;
            };
            if let Some(name) = decl.on_abort.clone() {
                let action = self
                    .on_abort_fn(*a, &name)
                    .map_or(UnwindAction::Fault, UnwindAction::OnAbort);
                out.push((path.clone(), action));
                return;
            }
            if decl.linear || decl.has_on_abort {
                out.push((path.clone(), whole));
                return;
            }
        }
        if stack.len() >= DEPTH || stack.contains(&t) {
            out.push((path.clone(), whole));
            return;
        }
        stack.push(t);
        match ty {
            Ty::Tuple(ts) => {
                for (i, x) in ts.into_iter().enumerate() {
                    path.push(Proj::Field(FieldIdx(id_of(i))));
                    self.walk_parts(x, path, stack, out);
                    path.pop();
                }
            }
            Ty::Adt(a, args) => self.walk_adt(a, &args, whole, path, stack, out),
            Ty::Array(x, _) => self.walk_elems(x, whole, path, stack, out),
            _ => out.push((path.clone(), whole)),
        }
        stack.pop();
    }

    /// [`Self::walk_parts`] for a definition `a` with type arguments `args`
    /// that has no `on abort` and is not linear itself. `whole` is the
    /// action for the value as a whole.
    fn walk_adt(
        &mut self,
        a: weft_ir::AdtId,
        args: &[TyId],
        whole: UnwindAction,
        path: &mut Vec<Proj>,
        stack: &mut Vec<TyId>,
        out: &mut Vec<(Vec<Proj>, UnwindAction)>,
    ) {
        let Some(decl) = self.tys.adts().get(a.index()) else {
            out.push((path.clone(), whole));
            return;
        };
        match (decl.kind.clone(), decl.lang) {
            (AdtKind::Struct(fs), _) => {
                for (i, f) in fs.iter().enumerate() {
                    let fty = super::unset::subst(self.tys, f.ty, args);
                    path.push(Proj::Field(FieldIdx(id_of(i))));
                    self.walk_parts(fty, path, stack, out);
                    path.pop();
                }
            }
            (AdtKind::Enum(vs), _) => {
                for (v, var) in vs.iter().enumerate() {
                    for (k, &x) in var.fields.iter().enumerate() {
                        let fty = super::unset::subst(self.tys, x, args);
                        path.push(Proj::Variant(VariantIdx(id_of(v))));
                        path.push(Proj::Field(FieldIdx(id_of(k))));
                        self.walk_parts(fty, path, stack, out);
                        path.pop();
                        path.pop();
                    }
                }
            }
            (_, Some(Lang::Box)) => match args.first() {
                Some(&x) => {
                    path.push(Proj::Deref(DerefKind::Box));
                    self.walk_parts(x, path, stack, out);
                    path.pop();
                }
                None => out.push((path.clone(), whole)),
            },
            (_, Some(Lang::Vec)) => match args.first() {
                Some(&x) => self.walk_elems(x, whole, path, stack, out),
                None => out.push((path.clone(), whole)),
            },
            _ => out.push((path.clone(), whole)),
        }
    }

    /// [`Self::walk_parts`] for the elements of type `x` of an array or a
    /// `Vec`: one action for all elements (`p[]`) if the element type has
    /// one action for the whole value, else `whole` for the buffer.
    fn walk_elems(
        &mut self,
        x: TyId,
        whole: UnwindAction,
        path: &[Proj],
        stack: &mut Vec<TyId>,
        out: &mut Vec<(Vec<Proj>, UnwindAction)>,
    ) {
        let mut inner = Vec::new();
        let mut here = Vec::new();
        self.walk_parts(x, &mut here, stack, &mut inner);
        match inner.as_slice() {
            [(p, a)] if p.is_empty() => {
                // The place `p[]` has the type `[x]` (V8).
                self.tys.intern(Ty::Slice(x));
                let mut p = path.to_vec();
                p.push(Proj::Elems);
                out.push((p, a.clone()));
            }
            [] => {}
            _ => out.push((path.to_vec(), whole)),
        }
    }

    /// Returns the function of the program that the `on abort = name` of
    /// definition `a` names, if the name finds a function (else W0101).
    fn on_abort_fn(&mut self, a: weft_ir::AdtId, name: &str) -> Option<weft_ir::FnId> {
        let prog = &self.d.a.program;
        let module = prog.adts.get(a.index())?.module;
        let Some(ItemRef::Fn(f)) = prog.lookup(module, name) else {
            return None;
        };
        self.fn_id(f, Span { lo: 0, hi: 0 }).ok()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use weft_ir::{
        BlockId, IntTy, LocalDecl, LocalId, LocalKind, Place, StmtKind, TempKind, TermKind, Ty,
        TyTable, UnwindAction,
    };
    use weft_syntax::ast::Span;

    use super::super::unset::PlaceFields;
    use super::super::{Builder, Decls, ScopeKind};
    use crate::thir::Tables;

    /// Runs `f` on a builder of a body whose `_0` is not plain data
    /// (`[u64; 2]`), with a frame scope.
    fn with_builder(f: impl FnOnce(&mut Builder<'_>)) {
        let Ok(a) = crate::analyze_source("", crate::Options::default()) else {
            panic!("the empty program does not analyze");
        };
        let t = Tables::default();
        let mut tys = TyTable::new();
        let u64 = tys.intern(Ty::Int(IntTy::U64));
        let ret = tys.intern(Ty::Array(u64, 2));
        let mut fields = PlaceFields::new(&tys);
        let (mut fns, mut decls) = (BTreeMap::new(), Vec::new());
        let mut pending = super::super::closure::Pending::default();
        let d = Decls {
            a: &a,
            fns: &mut fns,
            items: &mut decls,
            cap_envs: &mut Vec::new(),
            pending: &mut pending,
        };
        let span = Span { lo: 0, hi: 1 };
        let mut b = Builder::new(&t, &mut tys, &mut fields, d, 0, ret, span);
        b.open(ScopeKind::Frame, span);
        f(&mut b);
    }

    /// Adds a local of kind `kind` and type `u64` to the innermost scope.
    fn local(b: &mut Builder<'_>, kind: LocalKind) -> LocalId {
        let ty = b.tys.intern(Ty::Int(IntTy::U64));
        let props = b.props(ty);
        let origin = b.origin(Span { lo: 0, hi: 1 }, None);
        let l = b.add_local(LocalDecl {
            ty,
            kind,
            name: None,
            props,
            in_place: false,
            origin,
        });
        if let Some(s) = b.scopes.last_mut() {
            s.locals.push(l);
        }
        l
    }

    /// Returns the statements of the chain that starts at block `from`.
    fn chain(b: &Builder<'_>, from: BlockId) -> Vec<StmtKind> {
        let mut v = Vec::new();
        let mut cur = Some(from.index());
        while let Some(c) = cur {
            let Some(d) = b.blocks.get(c) else { break };
            assert!(d.cleanup);
            v.extend(d.stmts.iter().map(|s| s.kind.clone()));
            cur = match d.term.as_ref().map(|t| &t.kind) {
                Some(TermKind::Goto(t)) => Some(t.index()),
                _ => None,
            };
        }
        v
    }

    #[test]
    fn the_value_of_the_frame_is_first_only_after_it_gets_one() {
        with_builder(|b| {
            let p = local(b, LocalKind::Param(0));
            b.params.push(p);
            let x = local(b, LocalKind::User);
            b.open(ScopeKind::Stmt, Span { lo: 0, hi: 1 });
            let t = local(b, LocalKind::Temp(TempKind::Operand));
            let origin = b.origin(Span { lo: 0, hi: 1 }, None);
            let before = b.cleanup(origin);
            assert_eq!(
                chain(b, before),
                [
                    StmtKind::Dead(t),
                    StmtKind::Dead(x),
                    StmtKind::Dead(LocalId(0)),
                    StmtKind::Dead(p),
                ]
            );
            b.ret_value = true;
            let after = b.cleanup(origin);
            assert_eq!(
                chain(b, after),
                [
                    StmtKind::UnwindValue(Place::local(LocalId(0)), UnwindAction::Drop),
                    StmtKind::Dead(LocalId(0)),
                    StmtKind::Dead(t),
                    StmtKind::Dead(x),
                    StmtKind::Dead(p),
                ]
            );
        });
    }

    #[test]
    fn the_continuation_of_a_clause_is_first() {
        with_builder(|b| {
            let p = local(b, LocalKind::Param(0));
            b.params.push(p);
            let k = local(b, LocalKind::Kont(true));
            b.kont = Some(k);
            let x = local(b, LocalKind::User);
            let origin = b.origin(Span { lo: 0, hi: 1 }, None);
            let head = b.cleanup(origin);
            assert_eq!(
                chain(b, head),
                [
                    StmtKind::UnwindKont(k),
                    StmtKind::Dead(k),
                    StmtKind::Dead(x),
                    StmtKind::Dead(LocalId(0)),
                    StmtKind::Dead(p),
                ]
            );
        });
    }
}
