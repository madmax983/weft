//! Functions, blocks, statements and patterns.

use super::{
    ast, block_tail, effects, AssignOp, Block, EffectSig, ExprKind, FnId, Frame, Jump, LVal,
    LoopFrame, Lower, Lowered, NodeId, Pattern, PlaceId, RootKind, SigPlace, SigRoot, SigStep,
    Span, StepKind, Stmt, StmtKind, Ty, Val, VarId, VarKind,
};
use std::collections::BTreeSet;
use std::fmt::Write as _;

impl Lower<'_> {
    /// Lowers a function body.
    pub fn lower_fn(mut self, id: FnId) -> Lowered {
        let def = &self.prog.fns[id];
        let sig = self.sigs[id].clone();
        self.self_fn = Some(id);
        self.ret_ty = sig.ret.clone();
        let Some(body) = def.decl.body.clone() else {
            return self.finish(EffectSig::default());
        };
        let entry = self.start(def.span, "entry");
        let mut bases: Vec<Vec<PlaceId>> = Vec::new();
        let mut param_locals = Vec::new();
        for p in &sig.params {
            let l = self.new_local(&p.name, VarKind::Param, p.span, p.ty.clone(), p.uniq);
            param_locals.push(l);
            let base = if p.ty.is_ref() {
                if p.place.is_some() {
                    Vec::new()
                } else {
                    vec![self.facts.add_root(&p.name, RootKind::Param)]
                }
            } else {
                let r = self.facts.add_root(&p.name, RootKind::Local);
                self.set_root(l, r);
                vec![r]
            };
            bases.push(base);
        }
        for (i, p) in sig.params.iter().enumerate() {
            if let Some(pl) = &p.place {
                bases[i] = self.subst_place(pl, &bases.clone(), 0);
            }
        }
        for (i, p) in sig.params.iter().enumerate() {
            let l = param_locals[i];
            let refs = if p.ty.is_ref() {
                bases[i].clone()
            } else {
                Vec::new()
            };
            let v = Val {
                ty: p.ty.clone(),
                refs,
                uniq: p.uniq,
                fn_param: matches!(p.ty, Ty::Fn(_)).then_some((0, i)),
                ..Val::default()
            };
            self.assign_local(l, &v, entry);
            if p.shared {
                self.facts.shared_root.extend(bases[i].iter().copied());
            }
        }
        if sig.declared {
            self.facts.has_signature = true;
            for m in &sig.effects.muts {
                let ps = self.subst_place(m, &bases, 0);
                self.facts.declared_mut.extend(ps);
            }
            self.facts.declared_effect = effects::close(&sig.effects.named).into_iter().collect();
        }
        let exit = self.facts.add_node(def.span, "exit", String::new());
        self.jumps.push(Jump::Function { exit: Some(exit) });
        self.frames.push(Frame {
            names: Vec::new(),
            barrier: None,
        });
        // The temporaries of the value of the body live until the return.
        self.open_stmt();
        let v = self.block_inner(&body);
        let tail_span = body.stmts.last().map_or(body.span, |s| s.span);
        if self.cur.is_some() {
            self.finish_return(&v, tail_span);
        }
        self.stmt_temps.pop();
        self.flush(block_tail(&body));
        self.end_frame(body.span);
        if let Some(c) = self.cur {
            self.facts.cfg_edge.push((c, exit));
        }
        self.cur = Some(exit);
        self.frames.pop();
        // Parameters go out of scope at the exit.
        for &l in &param_locals {
            let var = self.locals[l].var;
            self.facts.scope_end.push((var, exit));
        }
        self.jumps.pop();
        self.apply_stored();
        let eff = self.summary_to_sig(&bases);
        let fdef = &self.prog.fns[id];
        if fdef.is_pub && !sig.declared && !eff.is_empty() && !fdef.decl.is_extern {
            let text = Self::effect_text(&eff);
            self.err(
                "W0701",
                format!(
                    "public function `{}` must state its effects: `/ {text}`",
                    fdef.name
                ),
                fdef.decl.name.span,
            );
        }
        self.finish(eff)
    }

    /// Lowers a test body. Tests have no signature and may install root handlers.
    pub fn lower_test(mut self, body: &Block, span: Span) -> Lowered {
        self.in_test = true;
        self.jumps.push(Jump::Function { exit: None });
        let _ = self.start(span, "test");
        self.open_stmt();
        let v = self.block(body);
        self.stmt_temps.pop();
        self.drop_value(&v, span);
        self.flush(block_tail(body));
        self.apply_stored();
        let eff = self.summary_to_sig(&[]);
        self.finish(eff)
    }

    fn finish(mut self, eff: EffectSig) -> Lowered {
        // Show the types of the locals as the whole body inferred them.
        for i in 0..self.locals.len() {
            let ty = self.locals[i].ty.clone();
            let shown = self.show(&ty);
            let var = self.locals[i].var;
            self.facts.vars[var.index()].ty = shown;
        }
        let declared: BTreeSet<String> = if self.facts.has_signature {
            self.facts.declared_effect.iter().cloned().collect()
        } else {
            effects::close(&eff.named)
        };
        for h in &mut self.facts.handlers {
            h.forwards = h.forwards || declared.contains(&h.effect);
        }
        self.facts.normalize();
        let unit = self.prog.mods[self.module].unit;
        for d in &mut self.diags {
            d.unit = unit;
        }
        Lowered {
            facts: self.facts,
            effects: eff,
            diags: self.diags,
        }
    }

    /// Text form of an effect row.
    pub(super) fn effect_text(e: &EffectSig) -> String {
        let mut parts: Vec<String> = Vec::new();
        if !e.muts.is_empty() {
            let ps: Vec<&str> = e.muts.iter().map(|m| m.text.as_str()).collect();
            parts.push(format!("mut({})", ps.join(", ")));
        }
        parts.extend(e.named.iter().map(|n| n.to_lowercase()));
        parts.join(", ")
    }

    /// Converts the body summary into a signature row in terms of parameters.
    ///
    /// A closure keeps the capabilities of the place where it is made, so the row
    /// also has the effects and the mutations of each closure that the body
    /// makes, also one that it returns or stores and does not call.
    fn summary_to_sig(&self, bases: &[Vec<PlaceId>]) -> EffectSig {
        let sum = &self.sums[0];
        let mut out = EffectSig {
            named: sum.escapes.clone(),
            passthrough: sum.passthrough.clone(),
            lent: self.lent_sig(bases),
            ret: self.ret_sig(bases),
            stores: sum.stores.clone(),
            reaches: !self.reaches.is_empty(),
            reach_given: self.reach_sig(bases),
            multi: self.unknown_multi,
            ..EffectSig::default()
        };
        let mut changed: Vec<PlaceId> = sum.muts.iter().copied().collect();
        for c in &self.closures {
            out.named.extend(c.escapes.iter().cloned());
            changed.extend(c.muts.iter().copied().filter(|&m| {
                let r = self.root_place(m);
                !c.param_roots.contains_key(&r) && !c.own_roots.contains(&self.facts.place(m).root)
            }));
        }
        let mut muts: Vec<SigPlace> = Vec::new();
        for m in changed {
            // `mut(p..)` is equal to `mut(p)`: a mutation anywhere below `p` is one of `p`.
            let base = self.facts.wild_base(m).unwrap_or(m);
            let Some(sp) = self.sig_place(base, bases) else {
                continue;
            };
            if !muts.contains(&sp) {
                muts.push(sp);
            }
        }
        // Keep only places that no other place covers.
        let covered = |a: &SigPlace, b: &SigPlace| {
            a.root == b.root
                && b.steps.len() < a.steps.len()
                && a.steps[..b.steps.len()] == b.steps[..]
        };
        let keep: Vec<SigPlace> = muts
            .iter()
            .filter(|a| !muts.iter().any(|b| covered(a, b)))
            .cloned()
            .collect();
        out.muts = keep;
        out
    }

    /// Returns the steps of place `p` from its root, each with its text, so that a
    /// caller shows the place as the body names it. A split side becomes an element step.
    pub(super) fn sig_steps(&self, p: PlaceId) -> Vec<SigStep> {
        let mut out = Vec::new();
        let mut at = p;
        while let Some(parent) = self.facts.place(at).parent {
            let info = self.facts.place(at);
            if let Some(&s) = info.steps.last() {
                let step = if let StepKind::Seg { .. } = s.kind {
                    let elem = weft_facts::Step {
                        kind: StepKind::Elem,
                        unstable: s.unstable,
                    };
                    SigStep::Step(elem, "[]".into())
                } else {
                    let text = info
                        .display
                        .get(self.facts.place(parent).display.len()..)
                        .unwrap_or("");
                    SigStep::Step(s, text.to_string())
                };
                out.push(step);
            }
            at = parent;
        }
        out.reverse();
        out
    }

    fn finish_return(&mut self, v: &Val, span: Span) {
        let ret = self.ret_ty.clone();
        // A returned function value: its caller can call it later.
        if let Ty::Fn(f) = self.inf.shallow(&ret) {
            let info = self.fn_info(v);
            self.rets.push((info, f.effects.clone()));
        }
        if matches!(ret, Ty::Unit) {
            self.drop_value(v, span);
        } else {
            let before = self.diags.len();
            self.unify(&ret, &v.ty, span);
            let typed = self.diags.len() == before;
            self.consume(v, span);
            // An ill-typed value gets no second error for its places.
            if typed {
                self.check_returned_refs(v, span);
            }
        }
    }

    /// A returned reference must be inside the place that the signature states. It
    /// cannot point into a local, a by-value parameter or a temporary of the
    /// function: they go out of scope at the return.
    fn check_returned_refs(&mut self, v: &Val, span: Span) {
        let Some(id) = self.self_fn else { return };
        let sig = self.sigs[id].clone();
        let fname = self.prog.fns[id].name.clone();
        let mut reported = Vec::new();
        let mut rest = Vec::new();
        for &r in &v.refs {
            let root = self.facts.place(r).root;
            if self.facts.roots[root.index()].kind != RootKind::Local {
                rest.push(r);
                continue;
            }
            if reported.contains(&root) {
                continue;
            }
            reported.push(root);
            let by_value = (0..sig.params.len())
                .find(|&i| self.locals[i].root.map(|p| self.facts.place(p).root) == Some(root));
            // The signature check already reports a returned place in a by-value parameter.
            let in_sig = by_value.is_some_and(|i| {
                sig.ret_places
                    .iter()
                    .any(|rp| rp.place.root == SigRoot::Param(i))
            });
            if in_sig {
                continue;
            }
            let by_value = by_value.is_some();
            let name = self.facts.roots[root.index()].name.clone();
            let what = if by_value {
                format!("the by-value parameter `{name}`")
            } else if name == "temporary" {
                "a temporary value".to_string()
            } else {
                format!("the local `{name}`")
            };
            let shown = self.facts.place(r).display.clone();
            let head = if v.summary.is_some() {
                format!("the returned closure captures `{shown}`")
            } else {
                format!("returned reference points into `{shown}`")
            };
            self.err(
                "W0204",
                format!("{head}: {what} of `{fname}` goes out of scope at the return"),
                span,
            );
        }
        if sig.ret_places.is_empty() || rest.is_empty() {
            return;
        }
        let bases: Vec<Vec<PlaceId>> = (0..sig.params.len())
            .map(|i| {
                self.locals
                    .get(i)
                    .map(|l| l.refs.clone())
                    .unwrap_or_default()
            })
            .collect();
        let bases: Vec<Vec<PlaceId>> = sig
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| {
                if p.ty.is_ref() {
                    bases[i].clone()
                } else {
                    self.locals[i].root.into_iter().collect()
                }
            })
            .collect();
        let mut allowed = Vec::new();
        for rp in &sig.ret_places {
            allowed.extend(self.subst_place(&rp.place, &bases, 0));
        }
        // The handle places of `Rc` handles are not where the reference points.
        rest.retain(|&r| !self.is_dep(r));
        for &r in &rest {
            if allowed.iter().any(|&a| self.sig_allows(a, r)) {
                continue;
            }
            let (rt, at) = (
                self.facts.place(r).display.clone(),
                self.place_text(&allowed),
            );
            let msg = if allowed.iter().any(|&a| self.below_unstable(a, r)) {
                format!("returned reference points into `{rt}`, which is below `{at}` through an unstable step: state the place, or `{at}..`")
            } else {
                format!("returned reference points into `{rt}`, but the signature says `{at}`")
            };
            self.err("W0204", msg, span);
        }
    }

    // -----------------------------------------------------------------------
    // Blocks
    // -----------------------------------------------------------------------

    pub(super) fn block(&mut self, b: &Block) -> Val {
        self.block_with(b, true)
    }

    /// Lowers a block. With `hold`, it holds a value that points into a local of
    /// the block across the end of the block, so that the end invalidates it.
    pub(super) fn block_with(&mut self, b: &Block, hold: bool) -> Val {
        self.frames.push(Frame {
            names: Vec::new(),
            barrier: None,
        });
        let v = self.block_inner(b);
        let v = self.hand_out(v, b.span);
        let tail = block_tail(b);
        let held = if hold { self.hold_out(&v, tail) } else { None };
        self.end_frame(b.span);
        self.frames.pop();
        if self.use_held(held, tail) {
            Val { var: None, ..v }
        } else {
            v
        }
    }

    /// Holds a value that points into a local of the innermost frame. Call it
    /// before `end_frame`, and give the result to `use_held` after it.
    pub(super) fn hold_out(&mut self, v: &Val, span: Span) -> Option<VarId> {
        let top = self.frames.len() - 1;
        let owned: Vec<PlaceId> = self.frames[top]
            .names
            .iter()
            .filter_map(|&(_, l)| self.locals[l].root)
            .collect();
        let inside = v.refs.iter().any(|&p| {
            let mut at = Some(p);
            while let Some(a) = at {
                if owned.contains(&a) {
                    return true;
                }
                at = self.facts.place(a).parent;
            }
            false
        });
        if inside {
            self.hold_as(v, "block value", VarKind::BlockValue, span)
        } else {
            None
        }
    }

    /// Uses a value that `hold_out` held, after the end of its frame. Returns
    /// true if there is one: the value then no longer stands for its variable.
    pub(super) fn use_held(&mut self, held: Option<VarId>, span: Span) -> bool {
        let Some(var) = held else {
            return false;
        };
        let n = self.emit(span, "block value", String::new());
        self.facts.uses.push((var, n));
        true
    }

    /// Moves a block's value out of the block before its locals go out of scope.
    pub(super) fn hand_out(&mut self, mut v: Val, span: Span) -> Val {
        if let Some(l) = v.local {
            let top = self.frames.len() - 1;
            let local_here = self.frames[top].names.iter().any(|(_, i)| *i == l);
            if local_here && self.cur.is_some() {
                let ty = self.locals[l].ty.clone();
                if !self.is_copy(&ty) {
                    let n = self.emit(span, "block value", String::new());
                    let var = self.locals[l].var;
                    self.move_var(var, n);
                }
                v.var = None;
                v.local = None;
                v.place = None;
            }
        }
        v
    }

    pub(super) fn block_inner(&mut self, b: &Block) -> Val {
        let mut last = Val::default();
        let n = b.stmts.len();
        for (i, s) in b.stmts.iter().enumerate() {
            let is_last = i + 1 == n;
            match &s.kind {
                // The value of the block belongs to the enclosing statement.
                StmtKind::Expr(e) if is_last => last = self.expr(e),
                _ => {
                    self.open_stmt();
                    self.stmt(s);
                    self.close_stmt(s.span);
                    if is_last {
                        last = Val::default();
                        if self.cur.is_none() {
                            last.ty = Ty::Never;
                        }
                    }
                }
            }
        }
        last
    }

    /// Ends the innermost frame: its locals go out of scope.
    pub(super) fn end_frame(&mut self, span: Span) {
        let top = self.frames.len() - 1;
        let names: Vec<usize> = self.frames[top].names.iter().map(|(_, i)| *i).collect();
        if names.is_empty() || self.cur.is_none() {
            return;
        }
        // The closing brace of the block.
        let close = Span::new(span.hi.saturating_sub(1), span.hi);
        let n = self.emit(close, "end of block", String::new());
        for l in names {
            let var = self.locals[l].var;
            self.facts.scope_end.push((var, n));
        }
    }

    /// Ends every frame above `keep`: for `return`, `break` and `continue`. The
    /// temporaries of the statements in these frames go out of scope too.
    pub(super) fn end_frames_above(&mut self, keep: usize, n: NodeId) {
        let mut vars = Vec::new();
        for f in &self.frames[keep..] {
            for (_, l) in &f.names {
                vars.push(self.locals[*l].var);
            }
        }
        for (depth, temps) in &self.stmt_temps {
            if *depth > keep {
                vars.extend(temps.iter().copied());
            }
        }
        for v in vars {
            self.facts.scope_end.push((v, n));
        }
    }

    /// Discards a value. A linear temporary is an error at this point.
    pub(super) fn drop_value(&mut self, v: &Val, span: Span) {
        if v.var.is_some() || v.task.is_some() || self.cur.is_none() {
            return;
        }
        let t = self.inf.resolve(&v.ty);
        if self.is_linear(&t) {
            let info = self.var_info("temporary", VarKind::Temp, span, &t, false);
            let var = self.facts.add_var(info);
            let n = self.emit(span, "drop", String::new());
            self.bind(var, n);
            let d = self.emit(span, "drop", String::new());
            self.facts.scope_end.push((var, d));
        }
    }

    // -----------------------------------------------------------------------
    // Statements
    // -----------------------------------------------------------------------

    fn stmt(&mut self, s: &Stmt) {
        match &s.kind {
            StmtKind::Let { pat, ty, init } => {
                let expected = ty.as_ref().map(|t| self.local_ty(t));
                let v = match init {
                    Some(e) => {
                        let v = self.expr(e);
                        if let Some(t) = &expected {
                            self.unify(t, &v.ty, e.span);
                        }
                        v
                    }
                    None => Val {
                        ty: expected.unwrap_or_else(|| self.inf.fresh()),
                        ..Val::default()
                    },
                };
                if init.is_some() {
                    self.consume(&v, s.span);
                }
                let n = self.emit(s.span, "let", String::new());
                self.bind_pattern(pat, &v, n);
            }
            StmtKind::Expr(e) => {
                let v = self.expr(e);
                self.drop_value(&v, e.span);
            }
            StmtKind::Assign { target, op, value } => self.assign(target, *op, value, s.span),
            StmtKind::Return(e) => {
                let v = e.as_ref().map_or_else(Val::default, |e| self.expr(e));
                match self.jumps.last().cloned() {
                    _ if self.cur.is_none() => {}
                    Some(Jump::Fence(what)) => {
                        self.err("W0315", format!("`return` cannot leave a {what}"), s.span);
                    }
                    Some(Jump::Closure { .. }) => self.closure_return(&v, s.span),
                    Some(Jump::Function { exit }) => {
                        self.finish_return(&v, s.span);
                        let n = self.emit(s.span, "return", String::new());
                        self.end_frames_above(1, n);
                        if let Some(exit) = exit {
                            self.facts.cfg_edge.push((n, exit));
                        }
                    }
                    None => {}
                }
                self.cur = None;
            }
            StmtKind::Break | StmtKind::Continue => {
                let word = if matches!(s.kind, StmtKind::Break) {
                    "break"
                } else {
                    "continue"
                };
                let Some(lf) = self.loops.last().cloned() else {
                    self.err("W0111", "`break` or `continue` outside a loop", s.span);
                    return;
                };
                let fence = self.jumps[lf.jumps.min(self.jumps.len())..]
                    .iter()
                    .find_map(|j| match j {
                        Jump::Fence(what) => Some(*what),
                        _ => None,
                    });
                if let Some(what) = fence {
                    if self.cur.is_some() {
                        self.err("W0315", format!("`{word}` cannot leave a {what}"), s.span);
                    }
                    self.cur = None;
                    return;
                }
                let (target, keep) = if matches!(s.kind, StmtKind::Break) {
                    (lf.exit, lf.frames)
                } else {
                    (lf.header, lf.frames)
                };
                if self.cur.is_some() {
                    let n = self.emit(s.span, "jump", String::new());
                    self.end_frames_above(keep, n);
                    self.facts.cfg_edge.push((n, target));
                }
                self.cur = None;
            }
            StmtKind::While { cond, body } => {
                let header = self.emit(s.span, "while", String::new());
                let mut exit = None;
                self.lower_loop(&mut |me: &mut Self| {
                    // The condition is a statement of its own.
                    me.open_stmt();
                    let c = me.expr(cond);
                    me.unify(&Ty::Bool, &c.ty, cond.span);
                    me.close_stmt(cond.span);
                    let br = me.emit(cond.span, "branch", String::new());
                    let x = me.facts.add_node(s.span, "end while", String::new());
                    me.facts.cfg_edge.push((br, x));
                    me.loop_body(body, header, x);
                    exit = Some(x);
                });
                self.cur = exit;
            }
            StmtKind::Loop(body) => {
                let header = self.emit(s.span, "loop", String::new());
                let exit = self.facts.add_node(s.span, "end loop", String::new());
                self.lower_loop(&mut |me: &mut Self| me.loop_body(body, header, exit));
                // A `loop` that no `break` leaves does not end normally.
                let left = self.facts.cfg_edge.iter().any(|&(_, q)| q == exit);
                self.cur = left.then_some(exit);
            }
            StmtKind::For { pat, iter, body } => self.for_loop(pat, iter, body, s.span),
            StmtKind::Assert(e) => {
                let v = self.expr(e);
                let t = self.deref_ty(&v.ty);
                self.unify(&Ty::Bool, &t, e.span);
                self.emit(e.span, "assert", String::new());
            }
        }
    }

    /// Lowers a loop body: control goes back to `header`, and `break` goes to `exit`.
    fn loop_body(&mut self, body: &Block, header: NodeId, exit: NodeId) {
        self.loops.push(LoopFrame {
            header,
            exit,
            frames: self.frames.len(),
            jumps: self.jumps.len(),
        });
        let v = self.block(body);
        self.drop_value(&v, body.span);
        self.flush(block_tail(body));
        self.loops.pop();
        if let Some(c) = self.cur {
            self.facts.cfg_edge.push((c, header));
        }
    }

    /// Lowers one iteration of a loop with `pass` until the values of the locals
    /// from outside the loop are stable. An iteration starts with the values that
    /// the iterations before it gave: references, function values and tasks. So
    /// when the body gives a local a new value, the body is lowered again from
    /// the loop head, with the old and the new values joined. A chain of locals
    /// needs one more pass for each local. After `MAX_LOOP_PASSES` passes the values
    /// of the last pass stay. A reference that goes deeper in each iteration
    /// (`cur = &cur.next[0]`) then has the places of eight iterations. A deeper
    /// place is below one of them, so a change through an unstable step covers it.
    fn lower_loop(&mut self, pass: &mut dyn FnMut(&mut Self)) {
        const MAX_LOOP_PASSES: usize = 8;
        let outer = self.locals.len();
        let made = (self.facts.roots.len(), self.facts.vars.len());
        let mut passes = 0;
        loop {
            let start = self.carried(outer, made);
            let head = self.clone();
            pass(self);
            passes += 1;
            if passes >= MAX_LOOP_PASSES || self.carried(outer, made) == start {
                return;
            }
            let values: Vec<_> = self.locals[..outer].to_vec();
            self.rewind(head);
            for (l, v) in values.into_iter().enumerate() {
                let var = self.locals[l].var;
                for &p in &v.refs {
                    if !self.locals[l].refs.contains(&p) {
                        self.facts.points_into.push((var, p));
                    }
                }
                let loc = &mut self.locals[l];
                loc.refs = v.refs;
                loc.summary = v.summary;
                loc.fn_param = v.fn_param;
                loc.task = v.task;
                loc.bound = v.bound;
                loc.uniq = v.uniq;
            }
        }
    }

    /// The values of the first `outer` locals that an iteration passes to the next,
    /// as keys that are the same in each pass. `made` is the number of roots and
    /// variables before the loop.
    fn carried(&self, outer: usize, made: (usize, usize)) -> Vec<BTreeSet<String>> {
        self.locals[..outer]
            .iter()
            .map(|loc| {
                let mut key: BTreeSet<String> = loc
                    .refs
                    .iter()
                    .map(|&p| format!("ref {}", self.place_key(p, made.0)))
                    .collect();
                key.extend(loc.task.map(|t| format!("task {t}")));
                let info = super::FnInfo {
                    summary: loc.summary,
                    item: None,
                    param: loc.fn_param,
                };
                key.extend(self.fn_key(&info, made));
                key
            })
            .collect()
    }

    /// A key of place `p` that is the same in each pass of a loop. A root that the
    /// loop makes (index `roots` or more) has its kind and name, and a split has its side.
    fn place_key(&self, p: PlaceId, roots: usize) -> String {
        let info = self.facts.place(p);
        let r = info.root.index();
        let mut key = if r < roots {
            format!("r{r}")
        } else {
            let root = &self.facts.roots[r];
            format!("{:?} {}", root.kind, root.name)
        };
        for s in &info.steps {
            let _ = match s.kind {
                StepKind::Seg { hi, .. } => write!(key, "/seg {hi} {}", s.unstable),
                k => write!(key, "/{k:?} {}", s.unstable),
            };
        }
        key
    }

    /// The keys of what a call of function value `info` does, the same in each pass of a loop.
    fn fn_key(&self, info: &super::FnInfo, made: (usize, usize)) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        out.extend(info.param.map(|p| format!("param {p:?}")));
        let Some(s) = info.summary else {
            return out;
        };
        let sum = &self.closures[s];
        let pk = |p: PlaceId| self.place_key(p, made.0);
        let vk = |v: VarId| {
            if v.index() < made.1 {
                format!("{v}")
            } else {
                self.facts.var(v).name.clone()
            }
        };
        for (tag, ps) in [
            ("mut", &sum.muts),
            ("read", &sum.reads),
            ("lend", &sum.lends),
        ] {
            out.extend(ps.iter().map(|&p| format!("{tag} {}", pk(p))));
        }
        out.extend(sum.ret_refs.iter().map(|&p| format!("ret {}", pk(p))));
        out.extend(
            sum.binds
                .iter()
                .map(|&(l, p)| format!("bind {l} {}", pk(p))),
        );
        out.extend(
            sum.escapes
                .iter()
                .chain(&sum.row)
                .map(|e| format!("effect {e}")),
        );
        out.extend(sum.performs.iter().map(|c| format!("cap {c}")));
        out.extend(sum.passthrough.iter().map(|p| format!("passthrough {p}")));
        out.extend(sum.items.iter().map(|f| format!("item {f}")));
        out.extend(sum.params.iter().map(|p| format!("param {p}")));
        out.extend(sum.stores.iter().map(|p| format!("stores {p}")));
        out.extend(sum.captures.iter().map(|&v| format!("capture {}", vk(v))));
        out.extend(
            sum.moved_captures
                .iter()
                .map(|&v| format!("moved {}", vk(v))),
        );
        out.extend(
            sum.param_roots
                .iter()
                .map(|(&r, k)| format!("root {k} {}", pk(r))),
        );
        out.extend(
            sum.op_args
                .iter()
                .map(|(c, op, pos, p)| format!("op {c} {op:?} {pos:?} {}", pk(*p))),
        );
        out.extend(
            sum.lent
                .iter()
                .map(|(f, pos, p)| format!("lent {f} {pos:?} {}", pk(*p))),
        );
        for (flag, on) in [
            ("abort", sum.may_abort),
            ("multi", sum.multi),
            ("unknown", sum.unknown),
            ("literal", sum.literal),
        ] {
            if on {
                out.insert(flag.to_string());
            }
        }
        out
    }

    /// Goes back to the state `head` at a loop head. The interned tables stay, so
    /// that the values of the pass before stay valid.
    fn rewind(&mut self, head: Self) {
        let roots = std::mem::take(&mut self.facts.roots);
        let places = std::mem::take(&mut self.facts.places);
        let index = std::mem::take(&mut self.facts.place_index);
        let vars = std::mem::take(&mut self.facts.vars);
        let closures = std::mem::take(&mut self.closures);
        let inf = std::mem::take(&mut self.inf);
        let groups = std::mem::take(&mut self.groups);
        let deps = std::mem::take(&mut self.dep_places);
        let split = self.split;
        *self = head;
        self.facts.roots = roots;
        self.facts.places = places;
        self.facts.place_index = index;
        self.facts.vars = vars;
        self.closures = closures;
        self.inf = inf;
        self.groups = groups;
        self.dep_places = deps;
        self.split = split;
    }

    fn for_loop(&mut self, pat: &Pattern, iter: &ast::Expr, body: &Block, span: Span) {
        self.frames.push(Frame {
            names: Vec::new(),
            barrier: None,
        });
        let (elem_val, it_refs) = match &iter.kind {
            ExprKind::Range { lo, hi } => {
                let a = self.expr(lo);
                let b = self.expr(hi);
                self.unify(&a.ty, &b.ty, iter.span);
                (
                    Val {
                        ty: a.ty,
                        ..Val::default()
                    },
                    Vec::new(),
                )
            }
            ExprKind::Index { base, index: None } => self.elem_iter(base, iter.span),
            _ => self.elem_iter(iter, iter.span),
        };
        // The hidden iterator points into the elements. Each iteration uses it.
        let it = if it_refs.is_empty() {
            None
        } else {
            let ty = elem_val.ty.clone();
            let l = self.new_local("{iterator}", VarKind::Iterator, iter.span, ty, false);
            let init = self.emit(iter.span, "iterator", String::new());
            let v = Val {
                ty: elem_val.ty.clone(),
                refs: it_refs,
                ..Val::default()
            };
            self.assign_local(l, &v, init);
            Some(l)
        };
        // Each iteration reads the elements.
        if let Some(l) = it {
            for p in self.split_deps(&self.locals[l].refs.clone()).0 {
                self.read(p);
            }
        }
        let header = self.emit(span, "for", String::new());
        if let Some(l) = it {
            let var = self.locals[l].var;
            self.facts.uses.push((var, header));
        }
        let exit = self.facts.add_node(span, "end for", String::new());
        self.facts.cfg_edge.push((header, exit));
        self.lower_loop(&mut |me: &mut Self| {
            let bindn = me.emit(pat.span(), "for binding", String::new());
            me.bind_pattern(pat, &elem_val, bindn);
            me.loop_body(body, header, exit);
        });
        self.cur = Some(exit);
        self.end_frame(span);
        self.frames.pop();
    }

    /// Returns the element value of `for e in x[]` and the element places.
    fn elem_iter(&mut self, base: &ast::Expr, span: Span) -> (Val, Vec<PlaceId>) {
        let lv = self.place_or_temp(base);
        let t = self.deref_ty(&lv.ty);
        if let Some((step, elem)) = super::elem_step(self.prog, &self.inf.deep(&t)) {
            let mut places: Vec<PlaceId> = match step {
                Some(s) => lv.places.iter().map(|&p| self.child(p, s, "[]")).collect(),
                None => lv.places.clone(),
            };
            // The elements depend on the `Rc` handles on the way.
            places.extend(lv.deps.iter().copied());
            // Copy elements bind by value; other elements bind by reference.
            let v = if self.is_scalar(&elem) {
                Val {
                    ty: elem,
                    ..Val::default()
                }
            } else {
                Val {
                    ty: Ty::Ref(Box::new(elem)),
                    refs: places.clone(),
                    uniq: lv.uniq,
                    ..Val::default()
                }
            };
            (v, places)
        } else {
            let shown = self.show(&t);
            self.err("W0102", format!("cannot iterate over `{shown}`"), span);
            (
                Val {
                    ty: Ty::Error,
                    ..Val::default()
                },
                Vec::new(),
            )
        }
    }

    fn assign(&mut self, target: &ast::Expr, op: AssignOp, value: &ast::Expr, span: Span) {
        // `x = v` on a local rebinds it. `c += v` on a reference writes through
        // it, as the interpreter does: the general path below mutates its places.
        if let ExprKind::Name(id) = &target.kind {
            let local = self.lookup_local(&id.name).filter(|&l| {
                op == AssignOp::Assign
                    || !matches!(self.inf.shallow(&self.locals[l].ty), Ty::Ref(_))
            });
            if let Some(l) = local {
                let v = self.expr(value);
                let lt = self.locals[l].ty.clone();
                if op == AssignOp::Assign {
                    self.unify(&lt, &v.ty, value.span);
                } else {
                    self.use_local(l);
                    self.arith(&lt, &v.ty, value.span);
                }
                self.consume(&v, value.span);
                let n = self.emit(span, &format!("{} =", id.name), String::new());
                if let Some(r) = self.locals[l].root {
                    self.mutate(n, r);
                }
                self.note_capture(l);
                self.assign_local(l, &v, n);
                return;
            }
        }
        let v = self.expr(value);
        let Some(lv) = self.place_expr(target) else {
            self.err(
                "W0112",
                "the left side of an assignment must be a place",
                target.span,
            );
            return;
        };
        // `p op= v` on a place that holds a reference writes through it, as the
        // interpreter does: it mutates what the reference points into.
        let mut places = lv.places.clone();
        if op != AssignOp::Assign && matches!(self.inf.shallow(&lv.ty), Ty::Ref(_)) {
            let through = self
                .field_referents(target)
                .or_else(|| lv.owner.map(|l| self.locals[l].refs.clone()));
            if let Some(ps) = through {
                places = self.split_deps(&ps).0;
            }
        }
        if op == AssignOp::Assign {
            self.unify(&lv.ty, &v.ty, value.span);
        } else {
            for &p in &places {
                self.read(p);
            }
            self.arith(&lv.ty, &v.ty, value.span);
        }
        // A function value in a field or an element: the body does not follow it.
        self.escape(&v);
        self.consume(&v, value.span);
        let detail = format!("mut({})", self.place_text(&places));
        let n = self.emit(span, "assign", detail);
        for &p in &places {
            self.mutate(n, p);
        }
    }

    pub(super) fn arith(&mut self, a: &Ty, b: &Ty, span: Span) {
        let a = self.deref_ty(a);
        let b = self.deref_ty(b);
        self.unify(&a, &b, span);
        let r = self.inf.shallow(&a);
        let ok = matches!(r, Ty::Int(_) | Ty::IntVar(_) | Ty::Error | Ty::Var(_))
            || matches!(r, Ty::Adt(x, _) if Some(x) == self.b.duration || Some(x) == self.b.string);
        if !ok {
            let shown = self.show(&r);
            self.err(
                "W0102",
                format!("arithmetic needs integers, found `{shown}`"),
                span,
            );
        }
    }

    // -----------------------------------------------------------------------
    // Patterns
    // -----------------------------------------------------------------------

    pub(super) fn bind_pattern(&mut self, pat: &Pattern, v: &Val, n: NodeId) {
        match pat {
            Pattern::Bind(id) => {
                let l = self.new_local(&id.name, VarKind::Local, id.span, v.ty.clone(), v.uniq);
                self.assign_local(l, v, n);
            }
            Pattern::Wild(_) | Pattern::Lit(..) => {}
            Pattern::Tuple(ps, span) => {
                let t = self.inf.shallow(&v.ty);
                let tys: Vec<Ty> = match t {
                    Ty::Tuple(ts) if ts.len() == ps.len() => ts,
                    Ty::Ref(inner) => match self.inf.shallow(&inner) {
                        Ty::Tuple(ts) if ts.len() == ps.len() => {
                            ts.into_iter().map(|t| Ty::Ref(Box::new(t))).collect()
                        }
                        _ => {
                            self.err("W0102", "this value is not a tuple of that size", *span);
                            return;
                        }
                    },
                    Ty::Var(_) => {
                        let ts: Vec<Ty> = ps.iter().map(|_| self.inf.fresh()).collect();
                        self.unify(&v.ty, &Ty::Tuple(ts.clone()), *span);
                        ts
                    }
                    _ => {
                        self.err("W0102", "this value is not a tuple of that size", *span);
                        return;
                    }
                };
                for (i, p) in ps.iter().enumerate() {
                    let part = v
                        .parts
                        .as_ref()
                        .and_then(|parts| parts.get(i).cloned())
                        .unwrap_or_else(|| Val {
                            ty: tys[i].clone(),
                            refs: v.refs.clone(),
                            ..Val::default()
                        });
                    let part = Val {
                        ty: tys[i].clone(),
                        ..part
                    };
                    self.bind_pattern(p, &part, n);
                }
            }
            Pattern::Variant { path, fields, span } => {
                // `let S(a, b) = s` destructures a struct and consumes it.
                let Some(adt) = self.adt_by_path(path) else {
                    self.err("W0113", "a variant pattern needs `match`", *span);
                    return;
                };
                let crate::program::AdtKind::Struct(defs) = self.prog.adts[adt].kind.clone() else {
                    self.err("W0113", "a variant pattern needs `match`", *span);
                    return;
                };
                let args: Vec<Ty> = self.prog.adts[adt]
                    .generics
                    .iter()
                    .map(|_| self.inf.fresh())
                    .collect();
                self.unify(&Ty::Adt(adt, args.clone()), &v.ty, *span);
                if defs.len() != fields.len() {
                    self.err(
                        "W0103",
                        format!("`{}` has {} fields", self.prog.adts[adt].name, defs.len()),
                        *span,
                    );
                    return;
                }
                for (p, d) in fields.iter().zip(&defs) {
                    let ft = super::subst(&d.ty, &args);
                    self.bind_pattern(
                        p,
                        &Val {
                            ty: ft,
                            ..Val::default()
                        },
                        n,
                    );
                }
            }
        }
    }

    /// Resolves a type written in a `let`.
    fn local_ty(&mut self, t: &ast::TypeExpr) -> Ty {
        let gens: Vec<String> = self
            .self_fn
            .map(|f| self.sigs[f].generics.clone())
            .unwrap_or_default();
        let module = self.module;

        crate::program::TyResolver {
            prog: self.prog,
            diags: &mut self.diags,
        }
        .resolve(t, module, &gens, None)
    }

    /// Returns the place of an expression, or a fresh temporary root for a value.
    pub(super) fn place_or_temp(&mut self, e: &ast::Expr) -> LVal {
        if let Some(lv) = self.place_expr(e) {
            return lv;
        }
        let v = self.expr(e);
        if let Ty::Ref(inner) = self.inf.shallow(&v.ty) {
            let (places, deps) = self.split_deps(&v.refs);
            return LVal {
                places,
                ty: *inner,
                owner: None,
                through_ref: true,
                uniq: v.uniq,
                deps,
            };
        }
        let r = self.temp_root(e.span, &v.ty);
        LVal {
            places: vec![r],
            ty: v.ty,
            ..LVal::default()
        }
    }

    /// Records a by-value use of a value: copy types are read, other values move.
    pub(super) fn consume(&mut self, v: &Val, span: Span) {
        if self.cur.is_none() {
            return;
        }
        let ty = self.inf.resolve(&v.ty);
        if self.is_copy(&ty) {
            return;
        }
        if let Some(lv) = &v.place {
            if lv.through_ref {
                let shown = self.show(&ty);
                self.err(
                    "W0303",
                    format!("cannot move a `{shown}` out of a borrowed place; borrow it with `&`"),
                    span,
                );
                return;
            }
        }
        let Some(var) = v.var.or_else(|| {
            v.place
                .as_ref()
                .and_then(|p| p.owner)
                .map(|l| self.locals[l].var)
        }) else {
            return;
        };
        let n = self.emit(span, "move", String::new());
        self.move_var(var, n);
        // A move of a part of the owner frees that part only.
        if v.var.is_none() {
            if let Some(lv) = &v.place {
                let root = lv.owner.and_then(|l| self.locals[l].root);
                for &p in &lv.places {
                    if Some(p) != root {
                        self.facts.moved_part.push((p, n));
                    }
                }
            }
        }
    }
}
