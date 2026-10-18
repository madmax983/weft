//! Functions, blocks, statements and patterns.

use super::{
    ast, effects, AssignOp, Block, EffectSig, ExprKind, FnId, Frame, LVal, LoopFrame, Lower,
    Lowered, NodeId, Pattern, PlaceId, RootKind, SigPlace, SigRoot, SigStep, Span, StepKind, Stmt,
    StmtKind, Ty, Val, VarKind,
};
use std::collections::BTreeSet;

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
                self.locals[l].root = Some(r);
                vec![r]
            };
            if matches!(p.ty, Ty::Fn(_)) {
                self.locals[l].fn_param = Some(param_locals.len() - 1);
            }
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
        self.frames.push(Frame {
            names: Vec::new(),
            barrier: None,
        });
        let v = self.block_inner(&body);
        let tail_span = body.stmts.last().map_or(body.span, |s| s.span);
        if self.cur.is_some() {
            self.finish_return(&v, tail_span);
        }
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
        let _ = &self.loops;
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
        let _ = self.start(span, "test");
        let v = self.block(body);
        self.drop_value(&v, span);
        let eff = self.summary_to_sig(&[]);
        self.finish(eff)
    }

    fn finish(mut self, eff: EffectSig) -> Lowered {
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
    fn summary_to_sig(&self, bases: &[Vec<PlaceId>]) -> EffectSig {
        let sum = self.sums[0].clone();
        let mut out = EffectSig {
            named: sum.escapes.clone(),
            passthrough: sum.passthrough.clone(),
            ..EffectSig::default()
        };
        let mut muts: Vec<SigPlace> = Vec::new();
        for &m in &sum.muts {
            let root = self.facts.place(m).root;
            let root_place = self
                .facts
                .places
                .iter()
                .position(|p| p.root == root && p.parent.is_none());
            let Some(rp) = root_place else { continue };
            let rp = PlaceId(u32::try_from(rp).unwrap_or(0));
            let sig_root = if let Some(i) = bases.iter().position(|b| b.first() == Some(&rp)) {
                SigRoot::Param(i)
            } else if let Some((&a, _)) = self.groups.iter().find(|(_, &g)| g == rp) {
                SigRoot::Group(a)
            } else {
                // A place under a parameter with an `in` clause, or a local.
                match bases
                    .iter()
                    .position(|b| b.iter().any(|&bp| self.facts.place(bp).root == root))
                {
                    Some(i) => SigRoot::Param(i),
                    None => continue,
                }
            };
            let info = self.facts.place(m).clone();
            let steps: Vec<SigStep> = info
                .steps
                .iter()
                .map(|s| match s.kind {
                    StepKind::Seg { .. } => SigStep::Step(
                        weft_facts::Step {
                            kind: StepKind::Elem,
                            unstable: s.unstable,
                        },
                        "[]".into(),
                    ),
                    _ => SigStep::Step(*s, String::new()),
                })
                .take(8)
                .collect();
            let sp = SigPlace {
                root: sig_root,
                steps,
                text: info.display.clone(),
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

    fn finish_return(&mut self, v: &Val, span: Span) {
        let ret = self.ret_ty.clone();
        if matches!(ret, Ty::Unit) {
            self.drop_value(v, span);
        } else {
            self.unify(&ret, &v.ty, span);
            self.consume(v, span);
            self.check_returned_refs(v, span);
        }
    }

    /// A returned reference must be inside the place that the signature states.
    fn check_returned_refs(&mut self, v: &Val, span: Span) {
        let Some(id) = self.self_fn else { return };
        let sig = self.sigs[id].clone();
        if sig.ret_places.is_empty() || v.refs.is_empty() {
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
        for &r in &v.refs {
            let ok = allowed.iter().any(|&a| {
                self.facts.place(a).root == self.facts.place(r).root
                    && weft_verified::places::within(
                        &self.facts.place(r).steps,
                        &self.facts.place(a).steps,
                    )
            });
            if !ok {
                let (rt, at) = (
                    self.facts.place(r).display.clone(),
                    self.place_text(&allowed),
                );
                self.err(
                    "W0204",
                    format!("returned reference points into `{rt}`, but the signature says `{at}`"),
                    span,
                );
            }
        }
    }

    // -----------------------------------------------------------------------
    // Blocks
    // -----------------------------------------------------------------------

    pub(super) fn block(&mut self, b: &Block) -> Val {
        self.frames.push(Frame {
            names: Vec::new(),
            barrier: None,
        });
        let v = self.block_inner(b);
        let v = self.hand_out(v, b.span);
        self.end_frame(b.span);
        self.frames.pop();
        v
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

    fn block_inner(&mut self, b: &Block) -> Val {
        let mut last = Val::default();
        let n = b.stmts.len();
        for (i, s) in b.stmts.iter().enumerate() {
            let is_last = i + 1 == n;
            match &s.kind {
                StmtKind::Expr(e) if is_last => last = self.expr(e),
                _ => {
                    self.stmt(s);
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

    /// Ends every frame above `keep`: for `return`, `break` and `continue`.
    fn end_frames_above(&mut self, keep: usize, n: NodeId) {
        let mut vars = Vec::new();
        for f in &self.frames[keep..] {
            for (_, l) in &f.names {
                vars.push(self.locals[*l].var);
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
                if self.cur.is_some() {
                    self.finish_return(&v, s.span);
                    let n = self.emit(s.span, "return", String::new());
                    self.end_frames_above(1, n);
                    // The exit node is node 1 of the function component when it exists.
                    if let Some(exit) = self.exit_node() {
                        self.facts.cfg_edge.push((n, exit));
                    }
                }
                self.cur = None;
            }
            StmtKind::Break | StmtKind::Continue => {
                let Some(lf) = self.loops.last() else {
                    self.err("W0111", "`break` or `continue` outside a loop", s.span);
                    return;
                };
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
                let c = self.expr(cond);
                self.unify(&Ty::Bool, &c.ty, cond.span);
                let br = self.emit(cond.span, "branch", String::new());
                let exit = self.facts.add_node(s.span, "end while", String::new());
                self.facts.cfg_edge.push((br, exit));
                self.loops.push(LoopFrame {
                    header,
                    exit,
                    frames: self.frames.len(),
                });
                let v = self.block(body);
                self.drop_value(&v, body.span);
                self.loops.pop();
                if let Some(c) = self.cur {
                    self.facts.cfg_edge.push((c, header));
                }
                self.cur = Some(exit);
            }
            StmtKind::Loop(body) => {
                let header = self.emit(s.span, "loop", String::new());
                let exit = self.facts.add_node(s.span, "end loop", String::new());
                self.loops.push(LoopFrame {
                    header,
                    exit,
                    frames: self.frames.len(),
                });
                let v = self.block(body);
                self.drop_value(&v, body.span);
                self.loops.pop();
                if let Some(c) = self.cur {
                    self.facts.cfg_edge.push((c, header));
                }
                self.cur = Some(exit);
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

    fn exit_node(&self) -> Option<NodeId> {
        self.facts
            .nodes
            .iter()
            .position(|n| n.label == "exit")
            .map(|i| NodeId(u32::try_from(i).unwrap_or(0)))
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
        let header = self.emit(span, "for", String::new());
        if let Some(l) = it {
            let var = self.locals[l].var;
            self.facts.uses.push((var, header));
        }
        let exit = self.facts.add_node(span, "end for", String::new());
        self.facts.cfg_edge.push((header, exit));
        let bindn = self.emit(pat.span(), "for binding", String::new());
        self.bind_pattern(pat, &elem_val, bindn);
        self.loops.push(LoopFrame {
            header,
            exit,
            frames: self.frames.len(),
        });
        let v = self.block(body);
        self.drop_value(&v, body.span);
        self.loops.pop();
        if let Some(c) = self.cur {
            self.facts.cfg_edge.push((c, header));
        }
        self.cur = Some(exit);
        self.end_frame(span);
        self.frames.pop();
    }

    /// Returns the element value of `for e in x[]` and the element places.
    fn elem_iter(&mut self, base: &ast::Expr, span: Span) -> (Val, Vec<PlaceId>) {
        let lv = self.place_or_temp(base);
        let t = self.deref_ty(&lv.ty);
        if let Some((step, elem)) = super::elem_step(self.prog, &self.inf.resolve(&t)) {
            let places: Vec<PlaceId> = match step {
                Some(s) => lv.places.iter().map(|&p| self.child(p, s, "[]")).collect(),
                None => lv.places.clone(),
            };
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
        // `x = v` on a local rebinds it.
        if let ExprKind::Name(id) = &target.kind {
            if let Some(l) = self.lookup_local(&id.name) {
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
        if op == AssignOp::Assign {
            self.unify(&lv.ty, &v.ty, value.span);
        } else {
            for &p in &lv.places {
                self.read(p);
            }
            self.arith(&lv.ty, &v.ty, value.span);
        }
        self.consume(&v, value.span);
        let detail = format!("mut({})", self.place_text(&lv.places));
        let n = self.emit(span, "assign", detail);
        for &p in &lv.places {
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
        let mut c = crate::program::Collector::for_types(self.prog.clone());
        let gens: Vec<String> = self
            .self_fn
            .map(|f| self.sigs[f].generics.clone())
            .unwrap_or_default();
        let ty = c.resolve_ty(t, self.module, &gens, None);
        self.diags.extend(c.diags);
        ty
    }

    /// Returns the place of an expression, or a fresh temporary root for a value.
    pub(super) fn place_or_temp(&mut self, e: &ast::Expr) -> LVal {
        if let Some(lv) = self.place_expr(e) {
            return lv;
        }
        let v = self.expr(e);
        if let Ty::Ref(inner) = self.inf.shallow(&v.ty) {
            return LVal {
                places: v.refs,
                ty: *inner,
                owner: None,
                through_ref: true,
                uniq: v.uniq,
            };
        }
        let r = self.root("temporary", RootKind::Local);
        LVal {
            places: vec![r],
            ty: v.ty,
            owner: None,
            through_ref: false,
            uniq: false,
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
    }
}
