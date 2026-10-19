//! Functions, blocks, statements and patterns.

use super::{
    ast, block_tail, effects, AssignOp, Block, EffectSig, ExprKind, FnId, Jump, LVal, LoopFrame,
    Lower, Lowered, NodeId, Pattern, PlaceId, RootKind, SigPlace, SigRoot, SigStep, Span, StepKind,
    Stmt, StmtKind, Ty, Val, VarId, VarKind,
};
use crate::props::Prop;
use std::collections::{BTreeMap, BTreeSet};

impl Lower<'_> {
    /// Lowers a function body.
    pub fn lower_fn(mut self, id: FnId) -> Lowered {
        let def = &self.prog.fns[id];
        let sig = self.sigs[id].clone();
        self.self_fn = Some(id);
        self.generic = !sig.generics.is_empty();
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
                    let r = self.facts.add_root(&p.name, RootKind::Param);
                    let rid = self.facts.place(r).root;
                    self.param_of_root.insert(rid, (0, bases.len()));
                    vec![r]
                }
            } else {
                let r = self.facts.add_root(&p.name, RootKind::Local);
                self.set_root(l, r);
                // A by-value parameter that holds references, such as an
                // `Option<&T>`, points into places of the caller.
                if self.byval_refs(&p.ty) {
                    vec![r, self.facts.add_root(&p.name, RootKind::Param)]
                } else {
                    vec![r]
                }
            };
            bases.push(base);
        }
        // The root parameter of an `in` place first: it can come later in the
        // list, and it can have an `in` place itself.
        for i in crate::program::in_place_order(&sig.params).0 {
            if let Some(pl) = &sig.params[i].place {
                let b = self.subst_place(pl, &bases, 0);
                bases[i] = b;
            }
        }
        self.param_bases = bases.iter().flatten().copied().collect();
        for (i, p) in sig.params.iter().enumerate() {
            let l = param_locals[i];
            let refs = if p.ty.is_ref() {
                bases[i].clone()
            } else {
                bases[i].get(1).copied().into_iter().collect()
            };
            let v = Val {
                ty: p.ty.clone(),
                refs,
                uniq: p.uniq,
                fn_param: matches!(p.ty, Ty::Fn(_)).then_some((0, i)),
                ..Val::default()
            };
            self.assign_local(l, &v, entry);
            // The parameter holds the function values that the caller gives. A
            // value of a type parameter can be one too.
            let generic = super::flow::mentions_param(&p.ty);
            if !matches!(p.ty, Ty::Fn(_)) && (self.has_fn(&p.ty) || generic) {
                self.locals
                    .get_mut(l)
                    .caps
                    .insert(super::caps::param_cap(i));
                self.locals
                    .get_mut(l)
                    .sticky
                    .insert(super::caps::param_cap(i));
            }
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
        self.push_frame(None);
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
        self.pop_frame();
        // Parameters go out of scope at the exit.
        for &l in &param_locals {
            let var = self.locals[l].var;
            self.facts.scope_end.push((var, exit));
        }
        self.jumps.pop();
        self.finish_values();
        self.finish_aborts();
        self.op_refs();
        self.finish_op_env();
        self.check_returns();
        self.check_stored_behind();
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
        // A test is a harness: it can install root handlers, also in a library (W0801).
        self.facts.library = false;
        self.jumps.push(Jump::Function { exit: None });
        let _ = self.start(span, "test");
        self.open_stmt();
        let v = self.block(body);
        self.stmt_temps.pop();
        self.drop_value(&v, span);
        self.flush(block_tail(body));
        self.finish_values();
        self.finish_aborts();
        self.op_refs();
        self.finish_op_env();
        let eff = self.summary_to_sig(&[]);
        self.finish(eff)
    }

    fn finish(mut self, mut eff: EffectSig) -> Lowered {
        self.check_int_lits();
        self.settle_moves();
        self.finish_via_calls();
        // The types of the locals as the whole body inferred them. A local can get
        // its type after its `let`: `let v = Vec.new()` with a later `v.push(x)`.
        // So its flags come from the inferred type too. A local that gets a
        // function type after its `let` is `callable`. A hidden variable gets its
        // flags from its inferred type in the same way.
        let mut maybe: Vec<(VarId, Ty)> = Vec::new();
        for i in 0..self.locals.len() {
            let t = self.inf.resolve(&self.locals[i].ty);
            let shown = self.show(&t);
            let has = |me: &Self, p: Prop| me.local_has_strict(i, p);
            let (linear, no_abort) = (has(&self, Prop::Linear), has(&self, Prop::NoOnAbort));
            let (immovable, nonportable) =
                (has(&self, Prop::Immovable), has(&self, Prop::Nonportable));
            if self.generic && !linear && self.local_has(i, Prop::Linear) {
                maybe.push((self.locals[i].var, t.clone()));
            }
            self.mark_modes(i);
            let var = self.locals[i].var;
            let v = &mut self.facts.vars[var.index()];
            v.ty = shown;
            v.linear = linear;
            v.has_on_abort = !no_abort;
            v.immovable |= immovable;
            v.nonportable |= nonportable;
            v.once |= v.linear;
            v.callable |= matches!(t, Ty::Fn(_));
        }
        for (var, ty) in std::mem::take(&mut self.late_vars) {
            let t = self.inf.resolve(&ty);
            let linear = self.ty_has_strict(&t, Prop::Linear);
            if self.generic && !linear && self.is_linear(&t) {
                maybe.push((var, t.clone()));
            }
            let has_on_abort = self.has_on_abort(&t);
            let v = &mut self.facts.vars[var.index()];
            v.linear = linear;
            v.has_on_abort = has_on_abort;
            v.once |= linear;
            v.callable |= matches!(t, Ty::Fn(_));
        }
        if self.generic {
            eff.drops = self.dropped_params(&maybe);
            eff.holds = self.held_params(&maybe);
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
            work: crate::Work {
                type_steps: self.inf.steps(),
                ..self.work
            },
        }
    }

    /// Drops each move of `Lower::tentative` whose value the body infers to be
    /// plain data: it is a copy.
    fn settle_moves(&mut self) {
        let copies: BTreeSet<(VarId, NodeId)> = std::mem::take(&mut self.tentative)
            .into_iter()
            .filter(|(_, _, t)| self.is_copy(&self.inf.resolve(t)))
            .map(|(v, n, _)| (v, n))
            .collect();
        if copies.is_empty() {
            return;
        }
        let nodes: BTreeSet<NodeId> = copies.iter().map(|&(_, n)| n).collect();
        self.facts.moved_at.retain(|m| !copies.contains(m));
        self.facts.moved_part.retain(|(_, n)| !nodes.contains(n));
    }

    /// Reports W0102 for an integer literal that does not fit the type that the
    /// body infers for it. A literal with no other type is an `i64`.
    fn check_int_lits(&mut self) {
        let lits = std::mem::take(&mut self.int_lits);
        let mut seen = BTreeSet::new();
        for (n, neg, ty, span) in lits {
            let Ty::Int(it) = self.inf.resolve(&ty) else {
                continue;
            };
            if !seen.insert((span.lo, span.hi)) {
                continue;
            }
            let (min, max) = int_range(it);
            let value = if neg { -i128::from(n) } else { i128::from(n) };
            if value < min || value > max {
                let shown = if neg { format!("-{n}") } else { n.to_string() };
                self.err(
                    "W0102",
                    format!("`{shown}` does not fit in `{}`", it.name()),
                    span,
                );
            }
        }
    }

    /// Text form of an effect row.
    pub(super) fn effect_text(e: &EffectSig) -> String {
        let mut parts: Vec<String> = Vec::new();
        if !e.muts.is_empty() {
            let ps: Vec<&str> = e.muts.iter().map(|m| m.text.as_str()).collect();
            parts.push(format!("mut({})", ps.join(", ")));
        }
        parts.extend(e.named.iter().map(|n| effects::in_signature(n)));
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
            named: sum.escapes.to_set(),
            passthrough: sum.passthrough.to_set(),
            lent: self.lent_sig(bases),
            ret: self.ret_sig(bases),
            stores: sum.stores.to_set(),
            reaches: !self.reaches.is_empty(),
            reach_given: self.reach_sig(bases),
            reach_repeats: self.reach_runs.1 || (self.reach_runs.0 > 1 && self.reaches_follow()),
            multi: self.unknown_multi,
            tasks: sum.tasks.to_set(),
            fn_stores: sum.fn_stores.to_set(),
            op_effects: sum.op_effects.to_set(),
            op_fns: sum
                .op_fns
                .iter()
                .filter(|(_, cap, _)| cap.is_none())
                .map(|(p, _, e)| (*p, e.clone()))
                .collect(),
            task_effects: sum.task_effects.to_set(),
            repeats: self.repeats_sig(),
            ..EffectSig::default()
        };
        let mut changed: Vec<PlaceId> = sum.muts.iter().copied().collect();
        // A by-value parameter that holds references stands for the places that
        // its references point into: a change of its own value is local.
        let own: Vec<_> = bases
            .iter()
            .filter(|b| b.len() > 1)
            .filter_map(|b| b.first().map(|&r| self.facts.place(r).root))
            .collect();
        changed.retain(|&m| !own.contains(&self.facts.place(m).root));
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
            let held = |p: &SigPlace| p.steps.first() == Some(&SigStep::Held);
            a.root == b.root
                && held(a) == held(b)
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
                // A wildcard place, also one of one call result, is `..` for a
                // caller: the caller makes its own places.
                let step = if weft_facts::is_wild_step(&s) {
                    SigStep::Wild
                } else if let StepKind::Seg { .. } = s.kind {
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
            // An ill-typed value gets no second error for its places. The check
            // comes after the body: an operation result gets its places there.
            if typed {
                self.returned
                    .push((v.refs.clone(), v.summary.is_some(), span));
            }
        }
    }

    /// A returned reference must be inside the place that the signature states. It
    /// cannot point into a local, a by-value parameter or a temporary of the
    /// function: they go out of scope at the return.
    pub(super) fn check_returned_refs(&mut self, refs: &[PlaceId], closure: bool, span: Span) {
        let Some(id) = self.self_fn else { return };
        let sig = self.sigs[id].clone();
        let fname = self.prog.fns[id].name.clone();
        let mut reported = Vec::new();
        let mut rest = Vec::new();
        for &r in refs {
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
            let head = if closure {
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
            let env = self
                .env_root
                .is_some_and(|e| self.facts.place(e).root == self.facts.place(r).root);
            let msg = if env {
                format!("the returned reference can come from a handler of a caller, which can give a place outside `{at}`")
            } else if allowed.iter().any(|&a| self.below_unstable(a, r)) {
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
        self.push_frame(None);
        let v = self.block_inner(b);
        let v = self.hand_out(v, b.span);
        let tail = block_tail(b);
        let held = if hold { self.hold_out(&v, tail) } else { None };
        self.end_frame(b.span);
        self.pop_frame();
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
            let local_here = self.local_frame(l) == top;
            if local_here && self.cur.is_some() {
                let ty = self.locals[l].ty.clone();
                let copy = self.is_copy(&ty);
                let unknown = copy && self.has_unknown(&ty);
                if !copy || unknown {
                    let n = self.emit(span, "block value", String::new());
                    let var = self.locals[l].var;
                    self.move_var(var, n);
                    if unknown {
                        self.tentative.push((var, n, ty));
                    }
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
        if self.cur.is_none() {
            return;
        }
        // A closure that no local holds: if it moves a linear value, the value is lost.
        if let (Some(var), Some(s), None) = (v.var, v.summary, v.local) {
            if self.closure_is_once(s) && self.closure_linear(s) {
                let d = self.emit(span, "drop", String::new());
                self.facts.scope_end.push((var, d));
            }
            return;
        }
        if v.var.is_some() || !v.tasks.is_empty() {
            return;
        }
        let t = self.inf.resolve(&v.ty);
        if self.may_be_linear(&t) {
            self.drop_linear("temporary", &t, span);
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
                self.check_binders(pat);
                let n = self.emit(s.span, "let", String::new());
                let bound = self.facts.rebound_at.len();
                self.bind_pattern(pat, &v, n);
                // A pattern that reads references out of a local uses the local here.
                self.flush(s.span);
                // `let x: T` with no value declares `x` only (W0304).
                if init.is_none() {
                    let declared: Vec<_> = self.facts.rebound_at.drain(bound..).collect();
                    self.facts.unset_at.extend(declared);
                }
                // A `_` drops its part of the value. A new task handle goes to its scope.
                let fresh_task = !v.tasks.is_empty() && v.local.is_none();
                if init.is_some() && !(fresh_task && matches!(pat, Pattern::Wild(_))) {
                    let whole = matches!(pat, Pattern::Wild(_));
                    for (span, ty) in self.wild_drops(pat, &v.ty) {
                        let name = if whole {
                            self.val_name(&v)
                        } else {
                            "temporary".to_string()
                        };
                        self.drop_linear(&name, &ty, span);
                    }
                }
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
                        self.leave_in_flight(n, self.jumps.len(), 0);
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
                    let st = self.branch_state();
                    let n = self.emit(s.span, "jump", String::new());
                    self.loop_jumps
                        .push((matches!(s.kind, StmtKind::Break), st, n));
                    self.end_frames_above(keep, n);
                    self.leave_in_flight(n, lf.jumps, self.loops.len());
                    self.facts.cfg_edge.push((n, target));
                }
                self.cur = None;
            }
            StmtKind::While { cond, body } => {
                let header = self.emit(s.span, "while", String::new());
                let mut exit = None;
                self.lower_loop(s.span, &mut |me: &mut Self| {
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
                self.lower_loop(s.span, &mut |me: &mut Self| {
                    me.loop_body(body, header, exit);
                });
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
        self.last_loop = Some((header, exit));
    }

    fn for_loop(&mut self, pat: &Pattern, iter: &ast::Expr, body: &Block, span: Span) {
        self.push_frame(None);
        self.iter_uniq = false;
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
        // The hidden iterator points into the elements. Each iteration uses it. It
        // is `@ uniq` if its source is, so it is not `many` either.
        let it = if it_refs.is_empty() {
            None
        } else {
            let ty = elem_val.ty.clone();
            let uniq = self.iter_uniq;
            let l = self.new_local("{iterator}", VarKind::Iterator, iter.span, ty, uniq);
            let init = self.emit(iter.span, "iterator", String::new());
            let v = Val {
                ty: elem_val.ty.clone(),
                refs: it_refs,
                uniq,
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
        self.lower_loop(span, &mut |me: &mut Self| {
            me.check_binders(pat);
            let bindn = me.emit(pat.span(), "for binding", String::new());
            me.bind_pattern(pat, &elem_val, bindn);
            me.loop_body(body, header, exit);
        });
        self.cur = Some(exit);
        self.end_frame(span);
        self.pop_frame();
    }

    /// Returns the element value of `for e in x[]` and the element places.
    fn elem_iter(&mut self, base: &ast::Expr, span: Span) -> (Val, Vec<PlaceId>) {
        let lv = self.place_or_temp(base);
        self.iter_uniq = lv.uniq;
        let t = self.deref_ty(&lv.ty);
        if let Some((step, elem)) = super::elem_step(self.prog, &self.inf.deep(&t)) {
            let mut places: Vec<PlaceId> = match step {
                Some(s) => lv.places.iter().map(|&p| self.child(p, s, "[]")).collect(),
                None => lv.places.clone(),
            };
            // The elements depend on the `Rc` handles on the way. An element that
            // holds references points where they point.
            places.extend(lv.deps.iter().copied());
            if self.holds_refs(&elem) && !self.is_scalar(&elem) {
                let inner = self.held_refs(&lv.places);
                places.extend(inner);
            }
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
        let mark = self.pend_uses.len();
        let Some(lv) = self.place_expr(target) else {
            self.err(
                "W0112",
                "the left side of an assignment must be a place",
                target.span,
            );
            return;
        };
        // A self-reference field of a `!Move` struct can point only into its struct.
        if op == AssignOp::Assign {
            self.check_self_ref(target, &v, value.span);
        }
        // The target does not read the references that the new value replaces.
        if let (AssignOp::Assign, Some(l), false) = (op, lv.owner, lv.through_ref) {
            let replaced: Vec<VarId> = self
                .part_holders
                .iter()
                .filter(|h| h.local == l && self.below_any(&h.places, &lv.places))
                .map(|h| h.var)
                .collect();
            let mut i = mark;
            while i < self.pend_uses.len() {
                if replaced.contains(&self.pend_uses[i]) {
                    self.pend_uses.remove(i);
                } else {
                    i += 1;
                }
            }
        }
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
            self.keep_modes(&v, &lv.ty, value.span);
        } else {
            for &p in &places {
                self.read(p);
            }
            self.arith(&lv.ty, &v.ty, value.span);
        }
        // A reference behind a reference parameter: the caller keeps it. A
        // self-reference field has its own check (W0605).
        if op == AssignOp::Assign
            && lv.through_ref
            && !v.refs.is_empty()
            && self.field_referents(target).is_none()
        {
            for &p in &lv.places {
                self.note_stored_behind(p, &v.refs, value.span);
            }
        }
        // A function value in a field or an element: the body does not follow it.
        self.escape(&v);
        self.store_into(&v, &lv.places);
        if self.has_fn(&v.ty) {
            self.note_fn_store(&lv.places);
        }
        self.consume(&v, value.span);
        // A part of a local that gets a reference points where it points from
        // here on. A hidden variable holds it, and a use of the local uses it.
        // The new value replaces what the part held before, and what each part
        // below it held.
        let holder = match (op, lv.owner, lv.through_ref) {
            (AssignOp::Assign, Some(l), false) => {
                // A holder of the same part with the same places gets the new value.
                let same = self
                    .part_holders
                    .iter()
                    .find(|h| h.local == l && h.places == lv.places && h.refs == v.refs)
                    .map(|h| h.var);
                self.retire_holders(l, &lv.places);
                (!v.refs.is_empty()).then(|| {
                    if let Some(h) = same {
                        self.part_holders.push(super::PartHolder {
                            local: l,
                            places: lv.places.clone(),
                            var: h,
                            refs: v.refs.clone(),
                        });
                        return h;
                    }
                    let name = format!("value in `{}`", self.place_text(&lv.places));
                    let mut info = self.var_info(&name, VarKind::Temp, target.span, &v.ty, v.uniq);
                    info.linear = false;
                    info.has_on_abort = true;
                    let h = self.facts.add_var(info);
                    for &p in &v.refs {
                        self.facts.points_into.push((h, p));
                    }
                    self.part_holders.push(super::PartHolder {
                        local: l,
                        places: lv.places.clone(),
                        var: h,
                        refs: v.refs.clone(),
                    });
                    h
                })
            }
            _ => None,
        };
        // A new value of a linear place drops the old one. Behind a reference the
        // old value is always there: a borrowed place cannot be moved out.
        let old_linear = op == AssignOp::Assign && self.is_linear(&lv.ty);
        let owner = lv.owner.filter(|_| !lv.through_ref);
        if old_linear && owner.is_none() {
            let name = self.place_text(&lv.places);
            self.drop_linear(&name, &lv.ty, target.span);
        }
        let detail = format!("mut({})", self.place_text(&places));
        let n = self.emit(span, "assign", detail);
        // A place field gets its value.
        let set: Vec<VarId> = self
            .unset_places
            .iter()
            .filter(|(p, _)| lv.places.contains(p))
            .map(|&(_, var)| var)
            .collect();
        for var in set.into_iter().chain(holder) {
            self.bind(var, n);
        }
        if let (true, Some(l)) = (old_linear, owner) {
            let var = self.locals[l].var;
            self.facts.overwrites.push((var, n));
        }
        for &p in &places {
            self.mutate(n, p);
        }
        // A write through a reference local at its place or below it leaves the
        // local valid (`writes_via`).
        if let Some(l) = base_name(target)
            .and_then(|id| self.lookup_local(&id.name))
            .filter(|&l| self.writes_through(l, &places))
        {
            let var = self.locals[l].var;
            self.facts.writes_via.push((n, var));
        }
    }

    /// Returns true if local `l` holds one reference and each place of `places` is
    /// at or below a place that it points to now. Then a write of `places` is a
    /// write through `l`, at the one place of `l` or below it.
    fn writes_through(&self, l: usize, places: &[PlaceId]) -> bool {
        self.one_ref_local(l) && self.all_below(places, &self.locals[l].refs)
    }

    /// Returns true if local `l` is a reference to a value with no reference in it.
    pub(super) fn one_ref_local(&self, l: usize) -> bool {
        match self.inf.shallow(&self.locals[l].ty) {
            Ty::Ref(inner) => !self.holds_refs(&inner),
            _ => false,
        }
    }

    /// Returns true if `places` is not empty and each place in it is at or below
    /// a place of `refs`.
    fn all_below(&self, places: &[PlaceId], refs: &[PlaceId]) -> bool {
        !places.is_empty()
            && places.iter().all(|&p| {
                let mut at = Some(p);
                while let Some(q) = at {
                    if refs.contains(&q) {
                        return true;
                    }
                    at = self.facts.place(q).parent;
                }
                false
            })
    }

    /// Gives `writes_via` to the node of each call of `Lower::via_calls`: each
    /// mutation at the node is at or below a place that the local had at the
    /// call, the node performs nothing, and no node of the call gives the local
    /// a new value. All facts of the body are there now, also the changes that a
    /// clause or a stored value adds to a node later.
    fn finish_via_calls(&mut self) {
        let calls = std::mem::take(&mut self.via_calls);
        if calls.is_empty() {
            return;
        }
        let mut muts: BTreeMap<NodeId, Vec<PlaceId>> = BTreeMap::new();
        for &(n, p) in &self.facts.mutates_at {
            muts.entry(n).or_default().push(p);
        }
        let performs: BTreeSet<NodeId> = self.facts.performs_at.iter().map(|&(n, _)| n).collect();
        for c in calls {
            let found = (c.from..self.facts.nodes.len()).find(|&i| {
                let node = &self.facts.nodes[i];
                node.span == c.span && node.label == c.label
            });
            let Some(i) = found else {
                continue;
            };
            let n = NodeId(u32::try_from(i).unwrap_or(u32::MAX));
            let rebound = self
                .facts
                .rebound_at
                .iter()
                .any(|&(v, m)| v == c.var && m.index() >= c.from && m.index() <= i);
            let places = muts.get(&n).map_or(&[][..], Vec::as_slice);
            if !rebound && !performs.contains(&n) && self.all_below(places, &c.refs) {
                self.facts.writes_via.push((n, c.var));
            }
        }
    }

    /// Reports W0605 if `target` is a self-reference field of a `!Move` struct
    /// and value `v` points outside the place that the field states.
    fn check_self_ref(&mut self, target: &ast::Expr, v: &Val, span: Span) {
        let Some(allowed) = self.field_referents(target) else {
            return;
        };
        let (named, _) = self.split_deps(&v.refs);
        for r in named {
            if allowed.iter().any(|&a| self.sig_allows(a, r)) {
                continue;
            }
            let (rt, at) = (
                self.facts.place(r).display.clone(),
                self.place_text(&allowed),
            );
            self.err(
                "W0605",
                format!("this field can point only into `{at}` of its own struct, but the value points into `{rt}`"),
                span,
            );
            return;
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
                let tys: Vec<Ty> = match t.clone() {
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
                // A part behind a reference to a tuple points where the part
                // points, too, if it holds references.
                let behind = matches!(t, Ty::Ref(_));
                let mut refs = v.refs.clone();
                let inner_refs = tys
                    .iter()
                    .any(|t| matches!(self.inf.shallow(t), Ty::Ref(x) if self.holds_refs(&x)));
                if behind && inner_refs {
                    let (named, _) = self.split_deps(&v.refs);
                    refs.extend(self.held_refs(&named));
                }
                for (i, p) in ps.iter().enumerate() {
                    let part = v
                        .parts
                        .as_ref()
                        .and_then(|parts| parts.get(i).cloned())
                        .unwrap_or_else(|| Val {
                            ty: tys[i].clone(),
                            refs: refs.clone(),
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
                    // A field that holds references points where the struct points.
                    let refs = if self.holds_refs(&ft) {
                        v.refs.clone()
                    } else {
                        Vec::new()
                    };
                    self.bind_pattern(
                        p,
                        &Val {
                            ty: ft,
                            refs,
                            ..Val::default()
                        },
                        n,
                    );
                }
            }
        }
    }

    /// Reports W0107 for a name that pattern `pat` binds twice.
    pub(super) fn check_binders(&mut self, pat: &Pattern) {
        fn walk<'a>(p: &'a Pattern, out: &mut Vec<&'a ast::Ident>) {
            match p {
                Pattern::Bind(id) => out.push(id),
                Pattern::Tuple(ps, _) => ps.iter().for_each(|q| walk(q, out)),
                Pattern::Variant { fields, .. } => fields.iter().for_each(|q| walk(q, out)),
                Pattern::Wild(_) | Pattern::Lit(..) => {}
            }
        }
        let mut names = Vec::new();
        walk(pat, &mut names);
        for (i, id) in names.iter().enumerate() {
            if names[..i].iter().any(|o| o.name == id.name) {
                self.err(
                    "W0107",
                    format!("`{}` is bound twice in this pattern", id.name),
                    id.span,
                );
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
            let held = self.val_caps(&v);
            return LVal {
                places,
                ty: *inner,
                owner: None,
                through_ref: true,
                uniq: v.uniq,
                deps,
                held,
            };
        }
        // The temporary goes away at the end of the statement.
        self.drop_value(&v, e.span);
        let r = self.temp_root(e.span, &v.ty);
        // The temporary points where its value points.
        if !v.refs.is_empty() {
            let root = self.facts.place(r).root;
            self.temp_refs.insert(root, v.refs.clone());
        }
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
        // A value whose type is not known yet moves for now: `finish` keeps the
        // move only if the inferred type is not plain data.
        let copy = self.is_copy(&ty);
        let unknown = copy && self.has_unknown(&ty);
        if copy && !unknown {
            return;
        }
        if let Some(lv) = &v.place {
            if lv.through_ref && unknown {
                return;
            }
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
        if unknown {
            self.tentative.push((var, n, v.ty.clone()));
        }
        // A local that moves its whole value holds no task handle after the move.
        if let Some(l) = v.var.and_then(|x| self.local_of(x)) {
            self.locals.set_tasks(l, BTreeSet::new());
        }
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

/// Returns the smallest and the largest value of an integer type.
const fn int_range(t: super::IntTy) -> (i128, i128) {
    use super::IntTy;
    match t {
        IntTy::I8 => (i8::MIN as i128, i8::MAX as i128),
        IntTy::I16 => (i16::MIN as i128, i16::MAX as i128),
        IntTy::I32 => (i32::MIN as i128, i32::MAX as i128),
        IntTy::I64 => (i64::MIN as i128, i64::MAX as i128),
        IntTy::U8 => (0, u8::MAX as i128),
        IntTy::U16 => (0, u16::MAX as i128),
        IntTy::U32 => (0, u32::MAX as i128),
        IntTy::U64 | IntTy::Usize => (0, u64::MAX as i128),
    }
}

/// Returns the name at the base of place expression `e`: `cur` in `cur.next[0].val`.
pub(super) fn base_name(e: &ast::Expr) -> Option<&ast::Ident> {
    match &e.kind {
        ExprKind::Name(id) => Some(id),
        ExprKind::Field { base, .. } | ExprKind::Index { base, .. } => base_name(base),
        _ => None,
    }
}
