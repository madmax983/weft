//! Calls, method calls, performs, `print` and `assert` (`docs/ir.md` 5.18,
//! 5.19, 5.20, 5.26, 5.33, 5.34), and the cleanup block of a terminator that
//! can abort (5.1.6).
//!
//! The arguments run in the order of the parameters: the THIR gives the
//! argument of each parameter (`CallInfo::args`, ADR 0009). So named
//! arguments run in parameter order. Each argument is an operand that is read
//! where it is written (choice A, 5.1.1). A method receiver is a place first;
//! the call reads it after the arguments. Each call passes the lexical
//! capability environment (`CapArgs::Lexical`, 5.1.8).

use weft_ir::{
    BlockId, Callee, LocalId, LocalKind, OpIdx, Operand, Origin, Place, Rvalue, StmtKind, TempKind,
    TermKind, Ty, TyId,
};
use weft_syntax::ast::{Arg, Expr, ExprKind, Span};

use super::{id_of, unsupported, Builder, Construct, Draft, R, RET};
use crate::thir::{self, Builtin, CallInfo, Recv, RecvMode};

/// The parts of a call expression: the receiver of a method call, the
/// arguments and the trailing block.
type Parts<'e> = (Option<&'e Expr>, &'e [Arg], Option<&'e Expr>);

/// Returns the receiver, the arguments and the trailing block of call `e`.
fn parts(e: &Expr) -> Option<Parts<'_>> {
    match &e.kind {
        ExprKind::Call { args, trailing, .. } => Some((None, args, trailing.as_deref())),
        ExprKind::MethodCall {
            receiver,
            args,
            trailing,
            ..
        } => Some((Some(receiver), args, trailing.as_deref())),
        _ => None,
    }
}

impl Builder<'_> {
    /// Writes the value of call or method call `e` into `dest` (`docs/ir.md`
    /// 5.18, 5.19). The THIR callee gives the form: a call of a function
    /// item, a perform, a struct or a variant constructor, or `print`.
    pub(super) fn call_into(&mut self, e: &Expr, dest: Place) -> R<()> {
        let t = self.t;
        if self.sim_run(e) {
            // The THIR has no call entry for `sim.run`: plan stage B11.
            return unsupported(Construct::Intrinsic, e.span);
        }
        let (Some((receiver, args, trailing)), Some(info)) = (parts(e), t.call.get(&e.id)) else {
            return unsupported(Construct::NoThir, e.span);
        };
        if let thir::Callee::Item { item, .. } = &info.callee {
            // `sim.run` and `with_timeout` are for plan stage B11: a call of
            // `sim.run` can leave out an argument.
            let id = self.fn_id(*item, e.span)?;
            if self
                .d
                .items
                .get(id.index())
                .is_some_and(|d| d.intrinsic.is_some())
            {
                return unsupported(Construct::Intrinsic, e.span);
            }
        }
        let slots = slots(info, args, trailing, e.span)?;
        match &info.callee {
            thir::Callee::Item { item, targs } => {
                let recv = match (info.recv, receiver) {
                    (Some(r), Some(x)) => Some((r, x)),
                    (None, _) => None,
                    (Some(_), None) => return unsupported(Construct::NoThir, e.span),
                };
                self.item_call(e, *item, targs, recv, &slots, &dest)
            }
            thir::Callee::Op { effect, op } => self.perform_into(e, *effect, *op, &slots, dest),
            thir::Callee::Struct { .. } => self.positional_into(e, &slots, dest),
            thir::Callee::Variant { variant, .. } => self.variant_into(e, *variant, &slots, dest),
            thir::Callee::Builtin(Builtin::Print) => self.print_into(e, &slots, dest),
            thir::Callee::Builtin(_) => unsupported(Construct::Task, e.span),
            thir::Callee::Value(_) => unsupported(Construct::FnValueCall, e.span),
            thir::Callee::Resume(_) => unsupported(Construct::Handle, e.span),
        }
    }

    /// Returns true if `e` is a call `sim.run(..)`: a method `run` on the
    /// standard module `sim`.
    fn sim_run(&self, e: &Expr) -> bool {
        let ExprKind::MethodCall {
            receiver, method, ..
        } = &e.kind
        else {
            return false;
        };
        method.name == "run"
            && matches!(self.t.res.get(&receiver.id),
                Some(thir::Res::Mod(m)) if super::is_sim(self.d.a, *m))
    }

    /// Lowers a call of function item `f` with type arguments `targs`
    /// (`docs/ir.md` 5.18, 5.19, 5.20):
    ///
    /// ```text
    /// f(x, y)   =>  tx := <x>; ty := <y>; dest = call f<T..>(move tx, move ty)
    /// r.m(a)    =>  <place r>; ta := <a>; tr := &<place r>; dest = call m(move tr, move ta)
    /// ```
    ///
    /// The arguments run in the order of the parameters. The receiver is a
    /// place first, and the call reads it after the arguments (p7, p8). So no
    /// argument of a method call skips its temporary. A `!Move` value built
    /// for a parameter of its own type, or for `Box.new` and `Rc.new`, is
    /// built in place (5.36).
    fn item_call(
        &mut self,
        e: &Expr,
        f: crate::FnId,
        targs: &[TyId],
        recv: Option<(Recv, &Expr)>,
        slots: &[&Expr],
        dest: &Place,
    ) -> R<()> {
        let id = self.fn_id(f, e.span)?;
        let Some(decl) = self.d.items.get(id.index()) else {
            return unsupported(Construct::NoThir, e.span);
        };
        let first = usize::from(recv.is_some());
        let params: Vec<TyId> = decl.params.iter().skip(first).copied().collect();
        let boxes = self.builds_in_place(f);
        let base = match recv {
            Some((r, x)) => Some((r, x, self.receiver_place(x)?)),
            None => None,
        };
        let skips = self.skips(slots);
        let mut ops = Vec::with_capacity(slots.len() + first);
        for (i, (a, skip)) in slots.iter().zip(skips).enumerate() {
            let own = params.get(i).is_some_and(|&p| self.props(p).immovable);
            ops.push(self.operand_in(a, base.is_none() && skip, boxes || own)?);
        }
        if let Some((r, x, p)) = base {
            let op = self.read_receiver(r.mode, p, x)?;
            ops.insert(0, op);
        }
        let aborts = self.call_can_abort(f, id);
        let origin = self.origin(e.span, Some(e.id));
        let unwind = aborts.then(|| self.cleanup(origin));
        let next = self.new_block();
        self.terminate(
            TermKind::Call {
                callee: Callee::Fn(id, targs.to_vec()),
                args: ops,
                dest: dest.clone(),
                caps: self.cap_args(),
                next: Some(BlockId(id_of(next))),
                unwind,
            },
            origin,
        );
        self.enter(next);
        // A call result is built in place: its place fields have no value
        // (`docs/ir.md` 5.17, ADR 0007).
        let ty = self.ty(e)?;
        self.unset_fields(dest, ty, &[], origin);
        Ok(())
    }

    /// Returns, for each operand of `parts`, true if no later operand can run
    /// code: then a place operand can skip its temporary (`docs/ir.md`
    /// 5.1.1). One pass from the end, so the cost is linear.
    pub(super) fn skips(&self, parts: &[&Expr]) -> Vec<bool> {
        let mut v = vec![true; parts.len()];
        let mut inert = true;
        for (i, x) in parts.iter().enumerate().rev() {
            if let Some(s) = v.get_mut(i) {
                *s = inert;
            }
            inert = inert && self.inert(x);
        }
        v
    }

    /// Evaluates the receiver `x` of a method call to a place (`docs/ir.md`
    /// 5.19): its own place, or a `Receiver` temporary for a value.
    fn receiver_place(&mut self, x: &Expr) -> R<Place> {
        if let Some(p) = self.as_place(x)? {
            return Ok(p);
        }
        let ty = self.ty(x)?;
        let origin = self.origin(x.span, Some(x.id));
        let t = self.temp(ty, TempKind::Receiver, origin);
        self.value_into(x, Place::local(t))?;
        Ok(Place::local(t))
    }

    /// Reads the receiver at place `p` (the place of `x`) for the call, after
    /// the arguments (`docs/ir.md` 5.19). `self` by reference borrows the
    /// place (`tr := &p`), or passes a reference as it is. `self` by value
    /// copies plain data and moves another value.
    fn read_receiver(&mut self, mode: RecvMode, p: Place, x: &Expr) -> R<Operand> {
        let ty = self.value_ty(x)?;
        match mode {
            RecvMode::Borrow => {
                let origin = self.origin(x.span, Some(x.id));
                let rty = self.tys.intern(Ty::Ref(ty));
                let t = self.temp(rty, TempKind::Receiver, origin);
                self.assign(Place::local(t), Rvalue::Ref(p), origin);
                Ok(Operand::Move(Place::local(t)))
            }
            RecvMode::Ref | RecvMode::Value | RecvMode::Deref => self.read_place(p, ty, x),
        }
    }

    /// Returns the function of the program for function `f` of the analysis.
    /// A function with no body of its own (an extern function of the
    /// prelude) gets its declaration at its first call.
    fn fn_id(&mut self, f: crate::FnId, span: Span) -> R<weft_ir::FnId> {
        if let Some(&id) = self.d.fns.get(&f) {
            return Ok(id);
        }
        let (decl, ok) = super::fn_decl(self.d.a, self.tys, f);
        if !ok {
            return unsupported(Construct::NoThir, span);
        }
        let id = weft_ir::FnId(id_of(self.d.items.len()));
        self.d.items.push(decl);
        self.d.fns.insert(f, id);
        Ok(id)
    }

    /// Returns true if a call of function `f` (`id` in the program) can abort
    /// by its kind (`docs/ir.md` 5.18, V10): each function but an extern
    /// function with an empty stated row and no run-time meaning.
    fn call_can_abort(&self, f: crate::FnId, id: weft_ir::FnId) -> bool {
        let external = self
            .d
            .a
            .program
            .fns
            .get(f.index())
            .is_some_and(|def| def.decl.body.is_none());
        let quiet = self.d.items.get(id.index()).is_some_and(|d| {
            d.intrinsic.is_none() && d.stated_row.as_ref().is_some_and(Vec::is_empty)
        });
        !(external && quiet)
    }

    /// Returns true if function `f` builds its argument in place on the heap:
    /// `Box.new` and `Rc.new` of the prelude (`docs/ir.md` 5.32).
    fn builds_in_place(&self, f: crate::FnId) -> bool {
        let prog = &self.d.a.program;
        prog.fns.get(f.index()).is_some_and(|def| {
            let owner = def
                .owner
                .and_then(|a| prog.adts.get(a.index()))
                .map(|a| a.name.as_str());
            def.is_std && def.name == "new" && matches!(owner, Some("Box" | "Rc"))
        })
    }

    /// Lowers a perform of operation `op` of effect `effect` (`docs/ir.md`
    /// 5.26):
    ///
    /// ```text
    /// op(a, b)  =>  ta := <a>; tb := <b>; dest = perform cap.op(move ta, move tb)
    /// ```
    ///
    /// The capability comes from the capability environment (5.1.8).
    fn perform_into(
        &mut self,
        e: &Expr,
        effect: weft_ir::EffectId,
        op: u32,
        slots: &[&Expr],
        dest: Place,
    ) -> R<()> {
        let mut ops = Vec::with_capacity(slots.len());
        for (a, skip) in slots.iter().zip(self.skips(slots)) {
            ops.push(self.operand(a, skip)?);
        }
        let origin = self.origin(e.span, Some(e.id));
        let unwind = Some(self.cleanup(origin));
        let next = self.new_block();
        self.terminate(
            TermKind::Perform {
                cap: self.cap_of(effect),
                op: OpIdx(op),
                args: ops,
                dest,
                next: BlockId(id_of(next)),
                unwind,
            },
            origin,
        );
        self.enter(next);
        Ok(())
    }

    /// Lowers `print(a, b)` (`docs/ir.md` 5.33):
    ///
    /// ```text
    /// print(a, b)  =>  ta := <a>; tb := <b>; Print(copy ta, copy tb); dest = ()
    /// ```
    ///
    /// Each operand is read where it is written (N2). A value that is not
    /// plain data is borrowed, not moved. So each operand is plain data or a
    /// reference, and `Print` copies it.
    fn print_into(&mut self, e: &Expr, slots: &[&Expr], dest: Place) -> R<()> {
        let mut ops = Vec::with_capacity(slots.len());
        for (a, skip) in slots.iter().zip(self.skips(slots)) {
            ops.push(match self.read_operand(a, skip)? {
                Operand::Move(p) => Operand::Copy(p),
                op => op,
            });
        }
        let origin = self.origin(e.span, Some(e.id));
        self.push(StmtKind::Print(ops), origin);
        self.assign(dest, Rvalue::Use(super::expr::unit()), origin);
        Ok(())
    }

    /// Lowers `assert c` (`docs/ir.md` 5.33): `Assert(c) -> [next, unwind: C]`.
    /// A condition that is a place or a constant is the operand itself.
    pub(super) fn assert_stmt(&mut self, c: &Expr, span: Span) -> R<()> {
        let cond = self.operand(c, true)?;
        let origin = self.origin(span, None);
        let unwind = Some(self.cleanup(origin));
        let next = self.new_block();
        self.terminate(
            TermKind::Assert {
                cond,
                next: BlockId(id_of(next)),
                unwind,
            },
            origin,
        );
        self.enter(next);
        Ok(())
    }

    /// Returns the cleanup block of an abort at the current point (`docs/ir.md`
    /// 5.1.6): the `Dead` of each local that has a cell, in the order of V16
    /// (the temporaries from the newest, the other locals from the highest
    /// index, `_0`, the parameters), then the unwind exit.
    ///
    /// Two chains with the same suffix share the blocks of the suffix: the
    /// block that ends local `l` and goes on to block `b` is one block. So
    /// the blocks grow with the number of locals, not with the number of
    /// terminators. Plan stage B8 adds the values (`UnwindValue`) and the
    /// value of `_0`.
    ///
    /// The locals of each class are a stack over the scopes: a scope gets
    /// new locals of a class only while no scope inside it holds that class,
    /// so the locals of an inner scope are newer. So the chain of a class is
    /// the locals of each scope, from the outermost, in order. Each scope
    /// keeps its part of the chain ([`super::ChainPart`]), and a later chain
    /// adds only the new locals: the cost of a chain is the number of scopes
    /// and the new locals, not the number of locals.
    pub(super) fn cleanup(&mut self, origin: Origin) -> BlockId {
        let mut next = self.chain_base(origin);
        for class in [0, 1] {
            for si in 0..self.scopes.len() {
                let Some(s) = self.scopes.get_mut(si) else {
                    continue;
                };
                let mut part = std::mem::take(&mut s.chain[class]);
                // The new locals of the scope that are of the class.
                for &l in s.locals.get(part.seen..).unwrap_or_default() {
                    let of = match self.locals.get(l.index()).map(|d| d.kind) {
                        Some(LocalKind::Temp(_)) => 1,
                        Some(LocalKind::Param(_)) => continue,
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
        BlockId(id_of(next))
    }

    /// Returns the cleanup block that ends local `l` and goes to block
    /// `next`.
    fn chain_node(&mut self, l: LocalId, next: usize, origin: Origin) -> usize {
        if let Some(&b) = self.chains.get(&(l, next)) {
            return b;
        }
        let b = self.cleanup_block(&[l], origin);
        if let Some(d) = self.blocks.get_mut(b) {
            d.term = Some(weft_ir::Term {
                kind: TermKind::Goto(BlockId(id_of(next))),
                origin,
            });
        }
        self.chains.insert((l, next), b);
        b
    }

    /// Returns the last block of each cleanup chain: `Dead(_0)` and the
    /// parameters, then the unwind exit.
    fn chain_base(&mut self, origin: Origin) -> usize {
        if let Some(b) = self.chain_base {
            return b;
        }
        let mut ends = vec![RET];
        ends.extend(self.params.iter().rev().copied());
        let b = self.cleanup_block(&ends, origin);
        self.chain_base = Some(b);
        b
    }

    /// Adds a cleanup block with `Dead` of each of `ends`. With no
    /// terminator it goes to the unwind exit (`Builder::finish`).
    fn cleanup_block(&mut self, ends: &[LocalId], origin: Origin) -> usize {
        let b = self.blocks.len();
        self.blocks.push(Draft {
            stmts: ends
                .iter()
                .map(|&l| weft_ir::Stmt {
                    kind: StmtKind::Dead(l),
                    origin,
                })
                .collect(),
            term: None,
            live: false,
            cleanup: true,
        });
        b
    }

    /// Writes `Uninit` of each place field of the value of type `ty` at
    /// `dest` that is built in place (`docs/ir.md` 5.17, ADR 0007), but for
    /// the fields `given` of the top struct.
    pub(super) fn unset_fields(&mut self, dest: &Place, ty: TyId, given: &[u32], origin: Origin) {
        for path in self.fields.of(self.tys, ty).iter() {
            if let Some(weft_ir::Proj::Field(f)) = path.proj.first() {
                if given.contains(&f.0) {
                    continue;
                }
            }
            let mut p = dest.clone();
            p.proj.extend(path.proj.iter().cloned());
            self.push(StmtKind::Uninit(p), origin);
        }
    }
}

/// Returns the argument expression of each parameter of call `info`, in the
/// order of the parameters (ADR 0009): an argument, or the trailing block.
/// A parameter with no argument is an error of `typeck` (W0103).
fn slots<'e>(
    info: &CallInfo,
    args: &'e [Arg],
    trailing: Option<&'e Expr>,
    span: Span,
) -> R<Vec<&'e Expr>> {
    let mut v = Vec::with_capacity(info.args.len());
    for s in &info.args {
        let k = s.map(|k| k as usize);
        let x = match k {
            Some(k) if k < args.len() => args.get(k).map(|a| &a.value),
            Some(k) if k == args.len() => trailing,
            _ => None,
        };
        match x {
            Some(x) => v.push(x),
            None => return unsupported(Construct::NoThir, span),
        }
    }
    Ok(v)
}
