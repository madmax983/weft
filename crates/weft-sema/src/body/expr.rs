//! Expressions, places, closures, handlers and scopes.

use super::{
    ast, block_tail, effects, elem_step, expr_tail, field_step, AdtKind, BinOp, ContInfo, Deref,
    Expr, ExprKind, FnId, FnTy, Frame, HandlerFrame, HandlerInfo, IntTy, ItemRef, Jump, LVal, Lit,
    Lower, NodeId, PathRef, Pattern, PlaceId, Rc, RootKind, Span, StrPart, Summary, Ty, UnOp, Val,
    VarKind, PRELUDE,
};
use weft_facts::{Step, StepKind};

impl Lower<'_> {
    /// Lowers an expression and returns its value.
    pub(super) fn expr(&mut self, e: &Expr) -> Val {
        match &e.kind {
            ExprKind::Lit(l) => self.lit(l),
            ExprKind::Name(id) => self.name(id, e.span),
            ExprKind::Field { base, name } => {
                if let ExprKind::Lit(Lit::Int(_)) = &base.kind {
                    if matches!(name.name.as_str(), "s" | "ms") {
                        let d = self
                            .b
                            .duration
                            .map_or(Ty::Error, |d| Ty::Adt(d, Vec::new()));
                        return Val {
                            ty: d,
                            ..Val::default()
                        };
                    }
                }
                if let Some(v) = self.path_member(base, name) {
                    return v;
                }
                self.place_value(e)
            }
            ExprKind::Index { .. } => self.place_value(e),
            ExprKind::Call {
                callee,
                args,
                trailing,
            } => self.call(callee, args, trailing.as_deref(), e.span),
            ExprKind::MethodCall {
                receiver,
                method,
                args,
                trailing,
            } => self.method_call(receiver, method, args, trailing.as_deref(), e.span),
            ExprKind::Unary {
                op: UnOp::Ref,
                expr,
            } => self.borrow(expr),
            ExprKind::Unary { op, expr } => {
                let v = self.expr(expr);
                let t = self.deref_ty(&v.ty);
                match op {
                    UnOp::Not => self.unify(&Ty::Bool, &t, expr.span),
                    _ => self.arith(&t, &t, expr.span),
                }
                Val {
                    ty: t,
                    ..Val::default()
                }
            }
            ExprKind::Binary { op, lhs, rhs } => self.binary(*op, lhs, rhs, e.span),
            ExprKind::Range { .. } => {
                self.err("W0114", "a range is only valid in `for`", e.span);
                Val {
                    ty: Ty::Error,
                    ..Val::default()
                }
            }
            ExprKind::Tuple(es) => {
                // Move and hold each part before the next one runs.
                let mut parts: Vec<Val> = Vec::new();
                let mut held = Vec::new();
                for (i, x) in es.iter().enumerate() {
                    let p = self.expr(x);
                    self.consume(&p, x.span);
                    if i + 1 < es.len() {
                        held.extend(self.hold_later(&p, "tuple part", x.span));
                    }
                    parts.push(p);
                }
                self.pend_uses.extend(held);
                let ty = Ty::Tuple(parts.iter().map(|p| p.ty.clone()).collect());
                let refs = parts.iter().flat_map(|p| p.refs.clone()).collect();
                Val {
                    ty,
                    refs,
                    parts: Some(
                        parts
                            .into_iter()
                            .map(|p| Val {
                                var: None,
                                local: None,
                                place: None,
                                ..p
                            })
                            .collect(),
                    ),
                    ..Val::default()
                }
            }
            ExprKind::Array(es) => {
                let t = self.inf.fresh();
                let mut caps = std::collections::BTreeSet::new();
                for x in es {
                    let v = self.expr(x);
                    self.unify(&t, &v.ty, x.span);
                    self.escape(&v);
                    caps.extend(self.val_caps(&v));
                    self.consume(&v, x.span);
                }
                let ty = self.b.vec.map_or(Ty::Error, |v| Ty::Adt(v, vec![t]));
                Val {
                    ty,
                    caps,
                    ..Val::default()
                }
            }
            ExprKind::StructLit { path, fields } => self.struct_lit(path, fields, e.span),
            ExprKind::Closure { params, body } => self.closure(params, body, None, e.span),
            ExprKind::Block(b) => self.block(b),
            ExprKind::If { cond, then, else_ } => {
                self.if_expr(cond, then, else_.as_deref(), e.span)
            }
            ExprKind::Match { scrutinee, arms } => self.match_expr(scrutinee, arms, e.span),
            ExprKind::Handle {
                effect,
                clauses,
                body,
            } => self.handle(effect, clauses, body, e.span),
            ExprKind::Scope { binder, body } => self.scope(binder, body, e.span),
        }
    }

    /// Lowers an expression with an expected type. Array literals and closures use it.
    pub(super) fn expr_with(&mut self, e: &Expr, expected: Option<&Ty>) -> Val {
        match (&e.kind, expected.map(|t| self.inf.shallow(t))) {
            (ExprKind::Array(es), Some(Ty::Array(elem, n))) => {
                let mut caps = std::collections::BTreeSet::new();
                for x in es {
                    let v = self.expr(x);
                    self.unify(&elem, &v.ty, x.span);
                    self.escape(&v);
                    caps.extend(self.val_caps(&v));
                    self.consume(&v, x.span);
                }
                if u64::try_from(es.len()).ok() != Some(n) {
                    self.err(
                        "W0102",
                        format!("expected an array of {n} elements, found {}", es.len()),
                        e.span,
                    );
                }
                Val {
                    ty: Ty::Array(elem, n),
                    caps,
                    ..Val::default()
                }
            }
            (ExprKind::Closure { params, body }, Some(Ty::Fn(f))) => {
                self.closure(params, body, Some(&f), e.span)
            }
            _ => self.expr(e),
        }
    }

    /// `Enum.Variant` and `module.function` used as values.
    fn path_member(&mut self, base: &Expr, name: &ast::Ident) -> Option<Val> {
        match self.path_ref(base)? {
            PathRef::Adt(a) => {
                if let AdtKind::Enum(vs) = &self.prog.adts[a].kind {
                    if let Some(vi) = vs.iter().position(|v| v.name == name.name) {
                        if vs[vi].fields.is_empty() {
                            let args: Vec<Ty> = self.prog.adts[a]
                                .generics
                                .iter()
                                .map(|_| self.inf.fresh())
                                .collect();
                            return Some(Val {
                                ty: Ty::Adt(a, args),
                                ..Val::default()
                            });
                        }
                    }
                }
                let n = self.prog.adts[a].name.clone();
                self.err(
                    "W0104",
                    format!("`{n}` has no unit variant `{}`", name.name),
                    name.span,
                );
                Some(Val {
                    ty: Ty::Error,
                    ..Val::default()
                })
            }
            PathRef::Mod(m) => {
                if let Some(ItemRef::Fn(f)) = self.prog.lookup_in(m, &name.name) {
                    Some(self.item_value(f, name.span))
                } else {
                    self.err(
                        "W0104",
                        format!("no item `{}` in this module", name.name),
                        name.span,
                    );
                    Some(Val {
                        ty: Ty::Error,
                        ..Val::default()
                    })
                }
            }
            PathRef::Effect(_) => {
                self.err(
                    "W0105",
                    "an effect is not a value; call one of its operations",
                    name.span,
                );
                Some(Val {
                    ty: Ty::Error,
                    ..Val::default()
                })
            }
        }
    }

    fn lit(&mut self, l: &Lit) -> Val {
        let ty = match l {
            Lit::Int(_) => self.inf.fresh_int(),
            Lit::Bool(_) => Ty::Bool,
            Lit::Unit => Ty::Unit,
            Lit::Str(parts) => {
                for p in parts {
                    if let StrPart::Interp(e) = p {
                        let _ = self.expr(e);
                    }
                }
                self.b.string.map_or(Ty::Error, |s| Ty::Adt(s, Vec::new()))
            }
        };
        Val {
            ty,
            ..Val::default()
        }
    }

    fn name(&mut self, id: &ast::Ident, span: Span) -> Val {
        if let Some(l) = self.lookup_local(&id.name) {
            self.use_local(l);
            let loc = self.locals[l].clone();
            // A reference used as a value reads the places that it points into.
            if matches!(self.inf.shallow(&loc.ty), Ty::Ref(_)) {
                for &p in &loc.refs {
                    self.read(p);
                }
            }
            let place = if loc.ty.is_ref() {
                None
            } else {
                loc.root.map(|r| LVal {
                    places: vec![r],
                    ty: loc.ty.clone(),
                    owner: Some(l),
                    through_ref: false,
                    uniq: loc.uniq,
                    deps: Vec::new(),
                })
            };
            return Val {
                ty: loc.ty.clone(),
                refs: loc.refs.clone(),
                var: Some(loc.var),
                local: Some(l),
                uniq: loc.uniq,
                summary: loc.summary,
                task: loc.task,
                parts: None,
                place,
                fn_param: loc.fn_param,
                item: None,
                caps: loc.caps,
            };
        }
        if let Some(ItemRef::Fn(f)) = self.prog.lookup(self.module, &id.name) {
            self.item_value(f, span)
        } else {
            if let Some(v) = self.unit_variant(&id.name) {
                return v;
            }
            self.err("W0101", format!("unknown name `{}`", id.name), span);
            Val {
                ty: Ty::Error,
                ..Val::default()
            }
        }
    }

    /// A function item used as a value.
    fn item_value(&mut self, f: FnId, span: Span) -> Val {
        // A call through the value can install the root handlers of `sim.run`.
        if self.is_sim_run(f) && self.library && !self.in_test {
            self.err(
                "W0802",
                "only binaries and tests can install root handlers (`sim.run`)",
                span,
            );
        }
        let sig = &self.sigs[f];
        let targs: Vec<Ty> = sig.generics.iter().map(|_| self.inf.fresh()).collect();
        let ty = Ty::Fn(Rc::new(FnTy {
            params: sig
                .params
                .iter()
                .map(|p| super::subst(&p.ty, &targs))
                .collect(),
            ret: super::subst(&sig.ret, &targs),
            effects: Some(effects::close(&sig.effects.named).into_iter().collect()),
            summary: None,
            item: Some(f),
        }));
        Val {
            ty,
            item: Some(f),
            ..Val::default()
        }
    }

    /// Returns true for the test harness `sim.run` of the prelude.
    pub(super) fn is_sim_run(&self, f: FnId) -> bool {
        let def = &self.prog.fns[f];
        def.is_std && def.path == "run" && self.prog.mods[def.module].name == "sim"
    }

    fn unit_variant(&mut self, name: &str) -> Option<Val> {
        let &(adt, vi) = self.prog.variants.get(name)?.first()?;
        let AdtKind::Enum(vs) = &self.prog.adts[adt].kind else {
            return None;
        };
        if !vs[vi].fields.is_empty() {
            return None;
        }
        let args: Vec<Ty> = self.prog.adts[adt]
            .generics
            .iter()
            .map(|_| self.inf.fresh())
            .collect();
        Some(Val {
            ty: Ty::Adt(adt, args),
            ..Val::default()
        })
    }

    /// Resolves a path that names a module, a type or an effect.
    pub(super) fn path_ref(&self, e: &Expr) -> Option<PathRef> {
        match &e.kind {
            ExprKind::Name(id) => {
                if self.lookup_local(&id.name).is_some() {
                    return None;
                }
                match self.prog.lookup(self.module, &id.name) {
                    Some(ItemRef::Mod(m)) => Some(PathRef::Mod(m)),
                    Some(ItemRef::Adt(a)) => Some(PathRef::Adt(a)),
                    Some(ItemRef::Effect(x)) => Some(PathRef::Effect(x)),
                    _ => {
                        let names = effects::canonical(self.prog, self.module, &id.name)?;
                        if names.len() != 1 {
                            return None;
                        }
                        self.prog
                            .effect_named(PRELUDE, &names[0])
                            .map(PathRef::Effect)
                    }
                }
            }
            ExprKind::Field { base, name } => match self.path_ref(base)? {
                PathRef::Mod(m) => match self.prog.lookup_in(m, &name.name)? {
                    ItemRef::Mod(s) => Some(PathRef::Mod(s)),
                    ItemRef::Adt(a) => Some(PathRef::Adt(a)),
                    ItemRef::Effect(x) => Some(PathRef::Effect(x)),
                    ItemRef::Fn(_) => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    // -----------------------------------------------------------------------
    // Places
    // -----------------------------------------------------------------------

    /// Returns the place that an expression names, if it names one.
    pub(super) fn place_expr(&mut self, e: &Expr) -> Option<LVal> {
        match &e.kind {
            ExprKind::Name(id) => {
                let l = self.lookup_local(&id.name)?;
                self.use_local(l);
                let loc = self.locals[l].clone();
                match self.inf.shallow(&loc.ty) {
                    Ty::Ref(inner) => {
                        let (places, deps) = self.split_deps(&loc.refs);
                        Some(LVal {
                            places,
                            ty: *inner,
                            owner: None,
                            through_ref: true,
                            uniq: loc.uniq,
                            deps,
                        })
                    }
                    t => {
                        let r = if let Some(r) = loc.root {
                            r
                        } else {
                            let r = self.root(&loc.name, RootKind::Local);
                            self.set_root(l, r);
                            r
                        };
                        Some(LVal {
                            places: vec![r],
                            ty: t,
                            owner: Some(l),
                            through_ref: false,
                            uniq: loc.uniq,
                            deps: Vec::new(),
                        })
                    }
                }
            }
            ExprKind::Field { base, name } => {
                if self.path_ref(base).is_some() {
                    return None;
                }
                if matches!(base.kind, ExprKind::Lit(_)) {
                    return None;
                }
                let lv = self.place_or_temp(base);
                Some(self.field_of(lv, name, e.span))
            }
            ExprKind::Index { base, index } => {
                let lv = self.place_or_temp(base);
                if let Some(ix) = index {
                    let v = self.expr(ix);
                    let t = self.deref_ty(&v.ty);
                    self.unify(&Ty::Int(IntTy::Usize), &t, ix.span);
                }
                let t = self.deref_ty(&lv.ty);
                let rt = self.inf.deep(&t);
                if let Some((step, elem)) = elem_step(self.prog, &rt) {
                    let places = match step {
                        Some(s) => lv.places.iter().map(|&p| self.child(p, s, "[]")).collect(),
                        None => lv.places.clone(),
                    };
                    Some(LVal {
                        places,
                        ty: elem,
                        ..lv
                    })
                } else {
                    let shown = self.show(&rt);
                    self.err("W0104", format!("`{shown}` has no elements"), e.span);
                    Some(LVal {
                        ty: Ty::Error,
                        ..lv
                    })
                }
            }
            _ => None,
        }
    }

    fn field_of(&mut self, lv: LVal, name: &ast::Ident, span: Span) -> LVal {
        let mut lv = lv;
        // Follow references, `Rc` groups and `Box`es.
        loop {
            match self.inf.shallow(&lv.ty) {
                Ty::Ref(inner) => {
                    lv.ty = *inner;
                    lv.through_ref = true;
                }
                Ty::Adt(a, args)
                    if matches!(
                        self.prog.adts[a].kind,
                        AdtKind::Extern {
                            deref: Some(Deref::Group),
                            ..
                        }
                    ) =>
                {
                    let inner = args.first().cloned().unwrap_or(Ty::Error);
                    let inner_r = self.inf.resolve(&inner);
                    let g = match inner_r {
                        Ty::Adt(ia, _) => self.group_root(ia),
                        _ => self.group_root(a),
                    };
                    let mut deps = lv.deps.clone();
                    deps.extend(self.handle_deps(&lv.places));
                    lv = LVal {
                        places: vec![g],
                        ty: inner,
                        owner: None,
                        through_ref: true,
                        uniq: false,
                        deps,
                    };
                }
                _ => break,
            }
        }
        let t = self.inf.deep(&lv.ty);
        if let Some((steps, next, _)) = field_step(self.prog, &t, &name.name) {
            let mut places = lv.places.clone();
            for (s, text) in &steps {
                let label = if text == "*" {
                    String::new()
                } else {
                    text.clone()
                };
                places = places.iter().map(|&p| self.child(p, *s, &label)).collect();
            }
            LVal {
                places,
                ty: next,
                ..lv
            }
        } else {
            if !matches!(t, Ty::Error) {
                let shown = self.show(&t);
                self.err(
                    "W0104",
                    format!("`{shown}` has no field `{}`", name.name),
                    span,
                );
            }
            LVal {
                ty: Ty::Error,
                ..lv
            }
        }
    }

    /// Reads the value at a place.
    fn place_value(&mut self, e: &Expr) -> Val {
        let Some(lv) = self.place_expr(e) else {
            return Val {
                ty: Ty::Error,
                ..Val::default()
            };
        };
        for &p in &lv.places {
            self.read(p);
        }
        let refs = if matches!(self.inf.shallow(&lv.ty), Ty::Ref(_)) {
            self.field_referents(e).unwrap_or_default()
        } else {
            Vec::new()
        };
        Val {
            ty: lv.ty.clone(),
            refs,
            place: Some(lv),
            ..Val::default()
        }
    }

    /// Returns the places that a reference field of a `!Move` struct points
    /// into: the place of the field type, in the same struct.
    pub(super) fn field_referents(&mut self, e: &Expr) -> Option<Vec<PlaceId>> {
        let ExprKind::Field { base, name } = &e.kind else {
            return None;
        };
        let blv = self.place_expr(base)?;
        let Ty::Adt(a, _) = self.deref_ty(&blv.ty) else {
            return None;
        };
        let AdtKind::Struct(fs) = &self.prog.adts[a].kind else {
            return None;
        };
        let sp = fs
            .iter()
            .find(|f| f.name == name.name)
            .and_then(|f| f.place.clone())?;
        Some(self.subst_place(&sp, std::slice::from_ref(&blv.places), 0))
    }

    fn borrow(&mut self, inner: &Expr) -> Val {
        // `&x[]` and `&x.f` name places; `&value` borrows a temporary.
        let lv = match &inner.kind {
            ExprKind::Index { base, index: None } => {
                let lv = self.place_or_temp(base);
                let t = self.deref_ty(&lv.ty);
                let rt = self.inf.deep(&t);
                match elem_step(self.prog, &rt) {
                    Some((step, elem)) => {
                        let places = match step {
                            Some(s) => lv.places.iter().map(|&p| self.child(p, s, "[]")).collect(),
                            None => lv.places.clone(),
                        };
                        LVal {
                            places,
                            ty: Ty::Slice(Box::new(elem)),
                            ..lv
                        }
                    }
                    None => lv,
                }
            }
            _ => {
                if let Some(lv) = self.place_expr(inner) {
                    lv
                } else {
                    let v = self.expr(inner);
                    self.consume(&v, inner.span);
                    let r = self.temp_root(inner.span, &v.ty);
                    LVal {
                        places: vec![r],
                        ty: v.ty,
                        ..LVal::default()
                    }
                }
            }
        };
        let mut refs = lv.places;
        refs.extend(lv.deps);
        Val {
            ty: Ty::Ref(Box::new(lv.ty)),
            refs,
            uniq: false,
            ..Val::default()
        }
    }

    fn binary(&mut self, op: BinOp, lhs: &Expr, rhs: &Expr, span: Span) -> Val {
        if matches!(op, BinOp::And | BinOp::Or) {
            let a = self.expr(lhs);
            let at = self.deref_ty(&a.ty);
            self.unify(&Ty::Bool, &at, lhs.span);
            let br = self.emit(span, "branch", String::new());
            let b = self.expr(rhs);
            let bt = self.deref_ty(&b.ty);
            self.unify(&Ty::Bool, &bt, rhs.span);
            self.flush(expr_tail(rhs));
            let join = self.emit(span, "join", String::new());
            self.facts.cfg_edge.push((br, join));
            return Val {
                ty: Ty::Bool,
                ..Val::default()
            };
        }
        let a = self.expr(lhs);
        let held = self.hold_later(&a, "operand", lhs.span);
        let b = self.expr(rhs);
        self.pend_uses.extend(held);
        match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let at = self.deref_ty(&a.ty);
                let bt = self.deref_ty(&b.ty);
                self.unify(&at, &bt, span);
                Val {
                    ty: Ty::Bool,
                    ..Val::default()
                }
            }
            _ => {
                self.arith(&a.ty, &b.ty, span);
                Val {
                    ty: self.deref_ty(&a.ty),
                    ..Val::default()
                }
            }
        }
    }

    fn struct_lit(
        &mut self,
        path: &[ast::Ident],
        fields: &[(ast::Ident, Expr)],
        span: Span,
    ) -> Val {
        let Some(adt) = self.adt_by_path(path) else {
            self.err(
                "W0101",
                format!(
                    "unknown struct `{}`",
                    path.last().map_or("", |p| p.name.as_str())
                ),
                span,
            );
            return Val {
                ty: Ty::Error,
                ..Val::default()
            };
        };
        let AdtKind::Struct(defs) = self.prog.adts[adt].kind.clone() else {
            self.err("W0102", "this type is not a struct", span);
            return Val {
                ty: Ty::Error,
                ..Val::default()
            };
        };
        let args: Vec<Ty> = self.prog.adts[adt]
            .generics
            .iter()
            .map(|_| self.inf.fresh())
            .collect();
        let mut caps = std::collections::BTreeSet::new();
        for (name, value) in fields {
            let expected = defs
                .iter()
                .find(|d| d.name == name.name)
                .map(|d| super::subst(&d.ty, &args));
            let v = self.expr_with(value, expected.as_ref());
            match defs.iter().find(|d| d.name == name.name) {
                Some(d) => {
                    let ft = super::subst(&d.ty, &args);
                    self.unify(&ft, &v.ty, value.span);
                }
                None => self.err("W0104", format!("no field `{}`", name.name), name.span),
            }
            self.escape(&v);
            caps.extend(self.val_caps(&v));
            self.consume(&v, value.span);
        }
        for d in &defs {
            if !fields.iter().any(|(n, _)| n.name == d.name) && d.place.is_none() {
                self.err("W0115", format!("missing field `{}`", d.name), span);
            }
        }
        Val {
            ty: Ty::Adt(adt, args),
            caps,
            ..Val::default()
        }
    }

    pub(super) fn adt_by_path(&self, path: &[ast::Ident]) -> Option<usize> {
        let mut m = self.module;
        for (i, seg) in path.iter().enumerate() {
            let r = if i == 0 {
                self.prog.lookup(m, &seg.name)
            } else {
                self.prog.lookup_in(m, &seg.name)
            };
            match r? {
                ItemRef::Mod(s) => m = s,
                ItemRef::Adt(a) if i + 1 == path.len() => return Some(a),
                _ => return None,
            }
        }
        None
    }

    fn if_expr(&mut self, cond: &Expr, then: &ast::Block, else_: Option<&Expr>, span: Span) -> Val {
        let c = self.expr(cond);
        let ct = self.deref_ty(&c.ty);
        self.unify(&Ty::Bool, &ct, cond.span);
        let br = self.emit(cond.span, "branch", String::new());
        let a = self.block(then);
        self.flush(block_tail(then));
        let a_end = self.cur;
        self.cur = Some(br);
        let b = else_.map_or_else(Val::default, |e| self.expr(e));
        if let Some(e) = else_ {
            self.flush(expr_tail(e));
        }
        let b_end = self.cur;
        let join = self.facts.add_node(span, "join", String::new());
        let mut any = false;
        for end in [a_end, b_end].into_iter().flatten() {
            self.facts.cfg_edge.push((end, join));
            any = true;
        }
        self.cur = if any { Some(join) } else { None };
        let mut refs = a.refs.clone();
        refs.extend(b.refs.iter().copied());
        let uniq = a.uniq && b.uniq;
        // The value of either branch: function values in it join.
        let v = if else_.is_none() {
            Val {
                ty: Ty::Unit,
                ..Val::default()
            }
        } else if matches!(self.inf.shallow(&a.ty), Ty::Never) {
            Val {
                refs: Vec::new(),
                ..b
            }
        } else if matches!(self.inf.shallow(&b.ty), Ty::Never) {
            Val {
                refs: Vec::new(),
                ..a
            }
        } else {
            self.unify(&a.ty, &b.ty, span);
            self.join_val(&a, &b)
        };
        Val {
            refs,
            uniq,
            var: None,
            local: None,
            place: None,
            task: None,
            ..v
        }
    }

    fn match_expr(&mut self, scrut: &Expr, arms: &[ast::Arm], span: Span) -> Val {
        let lv = self.place_expr(scrut);
        // A binding by reference depends on the `Rc` handles on the way.
        let deps = lv.as_ref().map(|l| l.deps.clone()).unwrap_or_default();
        let saved_deps = std::mem::replace(&mut self.match_deps, deps);
        let (sty, by_ref, places, sval) = if let Some(lv) = lv {
            let by_ref = lv.through_ref;
            // A by-value binding moves the local, or a part of it.
            let whole = lv
                .owner
                .filter(|&l| self.locals[l].root.is_some_and(|r| lv.places == [r]));
            let v = Val {
                ty: lv.ty.clone(),
                place: Some(lv.clone()),
                var: whole.map(|l| self.locals[l].var),
                ..Val::default()
            };
            (lv.ty.clone(), by_ref, lv.places, v)
        } else {
            let v = self.expr(scrut);
            let r = self.temp_root(scrut.span, &v.ty);
            (v.ty.clone(), false, vec![r], v)
        };
        for &p in &places {
            self.read(p);
        }
        let br = self.emit(scrut.span, "match", String::new());
        let join = self.facts.add_node(span, "end match", String::new());
        let result = self.inf.fresh();
        let mut refs = Vec::new();
        let mut reached = false;
        let mut joined: Option<Val> = None;
        for arm in arms {
            self.cur = Some(br);
            self.frames.push(Frame {
                names: Vec::new(),
                barrier: None,
            });
            let bn = self.emit(arm.pat.span(), "arm", String::new());
            self.match_moves = false;
            self.match_pattern(&arm.pat, &sty, &places, by_ref, &sval, bn);
            // A by-value binding moves the scrutinee once.
            if self.match_moves {
                self.consume(&sval, arm.pat.span());
            }
            let v = self.expr(&arm.body);
            self.flush(expr_tail(&arm.body));
            if !matches!(self.inf.shallow(&v.ty), Ty::Never) {
                self.unify(&result, &v.ty, arm.body.span);
                // The function values of the arms join.
                joined = Some(match joined.take() {
                    Some(j) => self.join_val(&j, &v),
                    None => Val {
                        ty: v.ty.clone(),
                        summary: v.summary,
                        item: v.item,
                        fn_param: v.fn_param,
                        parts: v.parts.clone(),
                        ..Val::default()
                    },
                });
            }
            refs.extend(v.refs.iter().copied());
            let v = self.hand_out(v, arm.span);
            let tail = expr_tail(&arm.body);
            let held = self.hold_out(&v, tail);
            self.end_frame(arm.span);
            self.frames.pop();
            let _ = self.use_held(held, tail);
            if let Some(c) = self.cur {
                self.facts.cfg_edge.push((c, join));
                reached = true;
            }
        }
        self.cur = if reached { Some(join) } else { None };
        self.match_deps = saved_deps;
        match joined {
            Some(j) if self.has_fn(&j.ty, 0) => Val { refs, ..j },
            _ => Val {
                ty: result,
                refs,
                ..Val::default()
            },
        }
    }

    fn match_pattern(
        &mut self,
        pat: &Pattern,
        ty: &Ty,
        places: &[PlaceId],
        by_ref: bool,
        sval: &Val,
        n: NodeId,
    ) {
        let t = self.deref_ty(ty);
        match pat {
            Pattern::Wild(_) => {}
            Pattern::Lit(l, s) => {
                let v = self.lit(l);
                self.unify(&t, &v.ty, *s);
            }
            Pattern::Bind(id) => {
                // A copy payload binds by value: the arm reads the place.
                let by_ref = by_ref && !self.is_scalar(&t);
                if !by_ref {
                    for &p in places {
                        self.read(p);
                    }
                }
                let v = if by_ref {
                    let mut refs = places.to_vec();
                    refs.extend(self.match_deps.iter().copied());
                    Val {
                        ty: Ty::Ref(Box::new(t)),
                        refs,
                        ..Val::default()
                    }
                } else {
                    Val {
                        ty: t.clone(),
                        ..sval.clone()
                    }
                };
                if !by_ref && !self.is_copy(&v.ty) {
                    self.match_moves = true;
                }
                let l = self.new_local(&id.name, VarKind::Local, id.span, v.ty.clone(), false);
                self.assign_local(l, &v, n);
            }
            Pattern::Tuple(ps, s) => {
                let rt = self.inf.deep(&t);
                let Ty::Tuple(ts) = rt else {
                    self.err("W0102", "this value is not a tuple", *s);
                    return;
                };
                for (i, (p, pt)) in ps.iter().zip(&ts).enumerate() {
                    let step = Step {
                        kind: StepKind::Field {
                            id: u32::try_from(i).unwrap_or(0),
                        },
                        unstable: false,
                    };
                    let sub: Vec<PlaceId> = places
                        .iter()
                        .map(|&q| self.child(q, step, &format!(".{i}")))
                        .collect();
                    self.match_pattern(
                        p,
                        pt,
                        &sub,
                        by_ref,
                        &Val {
                            ty: pt.clone(),
                            ..sval.clone()
                        },
                        n,
                    );
                }
            }
            Pattern::Variant { path, fields, span } => {
                let name = &path[path.len() - 1].name;
                let rt = self.inf.deep(&t);
                let (adt, args) = match rt {
                    Ty::Adt(a, args) => (a, args),
                    Ty::Var(_) | Ty::Error => {
                        let Some(&(a, _)) = self.prog.variants.get(name).and_then(|v| v.first())
                        else {
                            self.err("W0101", format!("unknown variant `{name}`"), *span);
                            return;
                        };
                        let args: Vec<Ty> = self.prog.adts[a]
                            .generics
                            .iter()
                            .map(|_| self.inf.fresh())
                            .collect();
                        self.unify(&t, &Ty::Adt(a, args.clone()), *span);
                        (a, args)
                    }
                    _ => {
                        self.err(
                            "W0102",
                            format!("variant `{name}` does not match this type"),
                            *span,
                        );
                        return;
                    }
                };
                let AdtKind::Enum(vs) = self.prog.adts[adt].kind.clone() else {
                    self.err("W0102", "this value is not an enum", *span);
                    return;
                };
                let Some(vi) = vs.iter().position(|v| &v.name == name) else {
                    self.err("W0101", format!("unknown variant `{name}`"), *span);
                    return;
                };
                let ftys: Vec<Ty> = vs[vi]
                    .fields
                    .iter()
                    .map(|t| super::subst(t, &args))
                    .collect();
                if ftys.len() != fields.len() {
                    self.err(
                        "W0103",
                        format!("variant `{name}` has {} fields", ftys.len()),
                        *span,
                    );
                    return;
                }
                let vstep = Step {
                    kind: StepKind::Variant {
                        id: u32::try_from(vi).unwrap_or(0),
                    },
                    unstable: true,
                };
                let vplaces: Vec<PlaceId> = places
                    .iter()
                    .map(|&q| self.child(q, vstep, &format!(".{name}")))
                    .collect();
                for (i, (p, ft)) in fields.iter().zip(&ftys).enumerate() {
                    let sub = if ftys.len() == 1 {
                        vplaces.clone()
                    } else {
                        let step = Step {
                            kind: StepKind::Field {
                                id: u32::try_from(i).unwrap_or(0),
                            },
                            unstable: false,
                        };
                        vplaces
                            .iter()
                            .map(|&q| self.child(q, step, &format!(".{i}")))
                            .collect()
                    };
                    self.match_pattern(
                        p,
                        ft,
                        &sub,
                        by_ref,
                        &Val {
                            ty: ft.clone(),
                            ..sval.clone()
                        },
                        n,
                    );
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // Closures
    // -----------------------------------------------------------------------

    /// Lowers a closure as its own CFG component and returns the closure value.
    pub(super) fn closure(
        &mut self,
        params: &[ast::Param],
        body: &Expr,
        expected: Option<&FnTy>,
        span: Span,
    ) -> Val {
        let saved = self.cur;
        let saved_pending = self.take_pending();
        let saved_stmts = std::mem::take(&mut self.stmt_temps);
        // A jump in the closure stays in it: `break` and `continue` go to its own loops.
        let saved_loops = std::mem::take(&mut self.loops);
        self.sums.push(Summary::default());
        let si = self.sums.len() - 1;
        self.frames.push(Frame {
            names: Vec::new(),
            barrier: Some(si),
        });
        let ret = match expected {
            Some(f) if !matches!(self.inf.shallow(&f.ret), Ty::Unit) => f.ret.clone(),
            _ => self.inf.fresh(),
        };
        self.jumps.push(Jump::Closure {
            exit: None,
            ret: ret.clone(),
            frame: self.frames.len() - 1,
            values: Vec::new(),
            span,
        });
        let entry = self.start(span, "closure entry");
        self.open_stmt();
        let mut ptys = Vec::new();
        let mut param_roots = std::collections::BTreeMap::new();
        for (i, p) in params.iter().enumerate() {
            let ty = match (&p.ty, expected.and_then(|f| f.params.get(i))) {
                (Some(t), _) => self.local_ty_pub(t),
                (None, Some(t)) => t.clone(),
                (None, None) => self.inf.fresh(),
            };
            ptys.push(ty.clone());
            let l = self.new_local(&p.name.name, VarKind::Param, p.span, ty.clone(), false);
            // A parameter that holds references points into what the call gives.
            let refs = if self.holds_refs(&ty) {
                let r = self.root(&p.name.name, RootKind::Arg);
                param_roots.insert(r, i);
                vec![r]
            } else {
                Vec::new()
            };
            let fn_param = matches!(self.inf.shallow(&ty), Ty::Fn(_)).then_some((si, i));
            self.assign_local(
                l,
                &Val {
                    ty,
                    refs,
                    fn_param,
                    ..Val::default()
                },
                entry,
            );
        }
        // The body returns its value: W0204 reports a value into its own locals.
        let v = match &body.kind {
            ExprKind::Block(b) => self.block_with(b, false),
            _ => self.expr(body),
        };
        // The body can end normally, or only through `return`.
        let falls = self.cur.is_some();
        let stated = expected.is_some_and(|f| !matches!(self.inf.shallow(&f.ret), Ty::Unit));
        if stated {
            self.unify(&ret, &v.ty, body.span);
        }
        let v = self.hand_out(v, body.span);
        let mut ret_refs = self.closure_ret_refs(&v, expr_tail(body));
        let Some(Jump::Closure {
            exit,
            values: returned,
            ..
        }) = self.jumps.pop()
        else {
            return Val::default();
        };
        self.loops = saved_loops;
        // With a `return`, the result type is the type of the returns.
        let ret_ty = if returned.is_empty() {
            v.ty.clone()
        } else {
            if falls && !stated {
                self.unify(&ret, &v.ty, expr_tail(body));
            }
            ret.clone()
        };
        for r in &returned {
            ret_refs.extend(r.refs.iter().copied());
        }
        self.sum().ret_refs = ret_refs;
        self.sum().param_roots = param_roots;
        self.sum().literal = true;
        self.drop_value(&v, body.span);
        self.flush(expr_tail(body));
        self.end_frame(span);
        if let Some(x) = exit {
            if let Some(c) = self.cur {
                self.facts.cfg_edge.push((c, x));
            }
            self.cur = Some(x);
        }
        let end = self.cur;
        self.frames.pop();
        let mut sum = self.sums.pop().unwrap_or_default();
        // A returned function value: a call of the closure can do what it does.
        let tail = falls.then_some(&v);
        for rv in returned.iter().chain(tail) {
            if let Ty::Fn(f) = self.inf.shallow(&rv.ty) {
                let info = self.fn_info(rv);
                let r = self.value_summary(&info, f.effects.as_deref());
                let ret = self.closures[r].clone();
                sum.union_ret(&ret);
                sum.rets.insert(r);
            }
        }
        // A captured linear value that the closure moves must be consumed inside it.
        for &var in &sum.moved_captures {
            if self.facts.var(var).linear {
                self.facts.rebound_at.push((var, entry));
                if let Some(e) = end {
                    self.facts.scope_end.push((var, e));
                }
            }
        }
        // Captures of an outer closure are captures of this one too.
        if let Some(outer) = self.sums.last_mut() {
            let _ = outer;
        }
        let id = self.closures.len();
        sum.members.insert(id);
        self.close_scope(si, super::fnval::Scope::Closure(id));
        self.closures.push(sum.clone());
        self.cur = saved;
        self.restore_pending(saved_pending);
        self.stmt_temps = saved_stmts;
        // The closure refers to the variables that it captures, as in the
        // interpreter. A captured copy value stays readable after its scope
        // ends; another value goes away with its variable, also a value that the
        // closure moves when it runs.
        let mut refs = Vec::new();
        let caps: Vec<_> = sum.captures.iter().copied().collect();
        for v in &caps {
            if let Some(l) = self.locals.iter().position(|l| l.var == *v) {
                let loc = self.locals[l].clone();
                refs.extend(loc.refs.iter().copied());
                if !loc.ty.is_ref() && self.may_free(&loc.ty) {
                    refs.extend(loc.root);
                }
                self.pend_uses.push(*v);
                self.note_capture(l);
            }
        }
        refs.sort();
        refs.dedup();
        // The moved captures are moved before the closure exists, so that the
        // move does not invalidate the new closure.
        let moved: Vec<_> = sum
            .moved_captures
            .iter()
            .copied()
            .filter(|&v| !self.is_copy_var(v))
            .collect();
        if !moved.is_empty() {
            let m = self.emit(span, "move", String::new());
            for v in moved {
                self.move_var(v, m);
            }
        }
        let n = self.emit(span, "closure", String::new());
        let fty = FnTy {
            params: ptys,
            ret: ret_ty,
            effects: None,
            summary: Some(id),
            item: None,
        };
        let ty = Ty::Fn(Rc::new(fty));
        let info = self.var_info("{closure}", VarKind::Closure, span, &ty, false);
        let var = self.facts.add_var(info);
        if self.closure_is_once(id) {
            self.facts.vars[var.index()].once = true;
        }
        self.bind(var, n);
        for &p in &refs {
            self.facts.points_into.push((var, p));
        }
        Val {
            ty,
            refs,
            var: Some(var),
            summary: Some(id),
            ..Val::default()
        }
    }

    /// Lowers `return` in a closure: the value is the result of the closure, and
    /// control goes to the exit of the closure.
    pub(super) fn closure_return(&mut self, v: &Val, span: Span) {
        let Some(Jump::Closure {
            exit, ret, frame, ..
        }) = self.jumps.last().cloned()
        else {
            return;
        };
        let before = self.diags.len();
        self.unify(&ret, &v.ty, span);
        let typed = self.diags.len() == before;
        self.consume(v, span);
        let refs = if typed {
            self.closure_ret_refs(v, span)
        } else {
            Vec::new()
        };
        let n = self.emit(span, "return", String::new());
        self.end_frames_above(frame, n);
        let exit = exit.unwrap_or_else(|| {
            let close = match self.jumps.last() {
                Some(Jump::Closure { span, .. }) => *span,
                _ => span,
            };
            self.facts.add_node(close, "closure exit", String::new())
        });
        self.facts.cfg_edge.push((n, exit));
        if let Some(Jump::Closure {
            exit: e, values, ..
        }) = self.jumps.last_mut()
        {
            *e = Some(exit);
            values.push(Val {
                refs,
                var: None,
                local: None,
                place: None,
                ..v.clone()
            });
        }
    }

    /// Returns the places of a closure result. A place inside a local of the
    /// closure is W0204: the local goes out of scope when the closure returns.
    fn closure_ret_refs(&mut self, v: &Val, span: Span) -> Vec<PlaceId> {
        let own = self.sum().own_roots.clone();
        let mut out = Vec::new();
        let mut reported = Vec::new();
        for &r in &v.refs {
            let root = self.facts.place(r).root;
            let local = self.facts.roots[root.index()].kind == RootKind::Local;
            if own.contains(&root) && local {
                if !reported.contains(&root) {
                    reported.push(root);
                    let name = self.facts.roots[root.index()].name.clone();
                    let param = self.facts.owner.iter().any(|&(rt, var)| {
                        self.facts.place(rt).root == root
                            && self.facts.var(var).kind == VarKind::Param
                    });
                    let whose = match (param, name.as_str()) {
                        (true, _) => format!("its parameter `{name}`"),
                        (false, "temporary") => "its temporary value".to_string(),
                        (false, _) => format!("its local `{name}`"),
                    };
                    let shown = &self.facts.place(r).display;
                    let head = if v.summary.is_some() {
                        format!("the closure returns a closure that captures `{shown}`")
                    } else {
                        format!("the closure returns a reference into `{shown}`")
                    };
                    self.err(
                        "W0204",
                        format!("{head}: {whose} goes out of scope at the return"),
                        span,
                    );
                }
            } else {
                out.push(r);
            }
        }
        out
    }

    /// The places of a closure call result: a place under a reference parameter of
    /// the closure stands for the places of that argument.
    pub(super) fn closure_call_refs(&mut self, s: usize, args: &[Vec<PlaceId>]) -> Vec<PlaceId> {
        let sum = self.closures[s].clone();
        let mut out = Vec::new();
        for &r in &sum.ret_refs {
            let root = self.root_place(r);
            match sum.param_roots.get(&root).copied() {
                Some(i) => {
                    for &a in args.get(i).map_or(&[][..], Vec::as_slice) {
                        out.push(self.rebase(r, root, a));
                    }
                }
                None => out.push(r),
            }
        }
        out
    }

    /// Returns the root place of `p`.
    pub(super) fn root_place(&self, p: PlaceId) -> PlaceId {
        let mut p = p;
        while let Some(q) = self.facts.place(p).parent {
            p = q;
        }
        p
    }

    /// Moves place `p` from under `from` to under `onto`, with the same steps.
    pub(super) fn rebase(&mut self, p: PlaceId, from: PlaceId, onto: PlaceId) -> PlaceId {
        let mut chain = Vec::new();
        let mut at = p;
        while at != from {
            let Some(parent) = self.facts.place(at).parent else {
                return p;
            };
            chain.push((at, parent));
            at = parent;
        }
        let mut out = onto;
        for &(child, parent) in chain.iter().rev() {
            let info = self.facts.place(child);
            let Some(&step) = info.steps.last() else {
                return p;
            };
            let text = info
                .display
                .get(self.facts.place(parent).display.len()..)
                .unwrap_or("")
                .to_string();
            out = self.child(out, step, &text);
            if self.dep_places.contains(&child) {
                self.dep_places.insert(out);
            }
        }
        out
    }

    pub(super) fn local_ty_pub(&mut self, t: &ast::TypeExpr) -> Ty {
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

    // -----------------------------------------------------------------------
    // Handlers
    // -----------------------------------------------------------------------

    fn handle(
        &mut self,
        effect: &ast::Ident,
        clauses: &[ast::HandlerClause],
        body: &Expr,
        span: Span,
    ) -> Val {
        let eid = match effects::canonical(self.prog, self.module, &effect.name) {
            Some(names) if names.len() == 1 => self.prog.effect_named(self.module, &names[0]),
            _ => None,
        };
        let Some(eid) = eid else {
            self.err(
                "W0101",
                format!("unknown effect `{}`", effect.name),
                effect.span,
            );
            return self.expr(body);
        };
        let def = self.prog.effects[eid].clone();
        let cap = self.facts.add_cap();
        let hid = weft_facts::HandlerId(u32::try_from(self.facts.handlers.len()).unwrap_or(0));
        self.facts.handlers.push(HandlerInfo {
            effect: def.name.clone(),
            is_std: def.is_std,
            forwards: false,
            span,
        });
        self.handlers.push(HandlerFrame {
            effect: def.name.clone(),
            cap,
            multi: def.has_multi(),
        });
        self.sum().own_caps.insert(cap);
        self.sums.push(Summary::default());
        self.jumps.push(Jump::Fence("handled body"));
        let start = self.handle_start();
        let v = self.expr(body);
        self.jumps.pop();
        // A function value that performs through the handler cannot leave its body.
        self.check_cap_escape(cap, &def.name, start, &v, span);
        self.flush(expr_tail(body));
        let body_sum = self.sums.pop().unwrap_or_default();
        self.merge_summary(&body_sum);
        self.handlers.pop();
        let ty = v.ty.clone();
        let saved = self.cur;
        let mut footprint = Vec::new();
        // The places that the clauses lend outside them: each node that runs a clause lends them.
        let mut lent = Vec::new();
        let mut clause_sum = Summary::default();
        let mut clauses_done = Vec::new();
        let mut clause_vals: Vec<Val> = Vec::new();
        for c in clauses {
            let Some(op) = def.ops.iter().find(|o| o.name == c.op.name).cloned() else {
                self.err(
                    "W0104",
                    format!("effect `{}` has no operation `{}`", def.name, c.op.name),
                    c.op.span,
                );
                continue;
            };
            if op.params.len() != c.params.len() {
                self.err(
                    "W0103",
                    format!(
                        "operation `{}` takes {} parameters",
                        op.name,
                        op.params.len()
                    ),
                    c.span,
                );
            }
            self.sums.push(Summary::default());
            let si = self.sums.len() - 1;
            self.frames.push(Frame {
                names: Vec::new(),
                barrier: Some(si),
            });
            let entry = self.start(c.span, "handler clause");
            let saved_stmts = std::mem::take(&mut self.stmt_temps);
            self.open_stmt();
            // A parameter that holds references points into what the operation gets.
            let mut param_roots = std::collections::BTreeMap::new();
            for (i, (p, pt)) in c.params.iter().zip(&op.params).enumerate() {
                let l = self.new_local(&p.name.name, VarKind::Param, p.span, pt.clone(), false);
                let refs = if self.holds_refs(pt) {
                    let r = self.root(&p.name.name, RootKind::Arg);
                    param_roots.insert(r, i);
                    vec![r]
                } else {
                    Vec::new()
                };
                self.assign_local(
                    l,
                    &Val {
                        ty: pt.clone(),
                        refs,
                        ..Val::default()
                    },
                    entry,
                );
            }
            let kty = Ty::Cont(Box::new(op.ret.clone()), Box::new(ty.clone()));
            let k = self.new_local("resume", VarKind::Continuation, c.span, kty, false);
            self.facts.vars[self.locals[k].var.index()].once = !op.multi;
            self.locals[k].cont = Some(ContInfo {
                arg: op.ret.clone(),
                ret: ty.clone(),
                multi: op.multi,
                muts: body_sum.muts.iter().copied().collect(),
                cap,
                depth: self.handlers.len(),
            });
            let kv = self.locals[k].var;
            self.bind(kv, entry);
            let resumes_before = self.resumes.len();
            self.jumps.push(Jump::Fence("handler clause"));
            let cv = self.block(&c.body);
            self.jumps.pop();
            self.flush(block_tail(&c.body));
            let returns = !matches!(self.inf.shallow(&cv.ty), Ty::Never);
            if returns {
                self.unify(&ty, &cv.ty, c.body.span);
            }
            self.end_frame(c.span);
            self.frames.pop();
            self.stmt_temps = saved_stmts;
            self.close_scope(si, super::fnval::Scope::Clause);
            let mut cs = self.sums.pop().unwrap_or_default();
            cs.param_roots = param_roots;
            // The value of the clause is the value of the `handle`.
            if returns {
                let mut cv = cv;
                cv.refs
                    .retain(|&p| !cs.own_roots.contains(&self.facts.place(p).root));
                clause_vals.push(cv);
            }
            // The clause runs in the environment of the `handle`: what it performs
            // goes to the handlers outside this one.
            for e in self.clause_effects(&cs) {
                self.facts.clause_performs.push((hid, e));
            }
            for &m in &cs.muts {
                if !cs.own_roots.contains(&self.facts.place(m).root) {
                    footprint.push(m);
                }
            }
            for &l in &cs.lends {
                if !cs.own_roots.contains(&self.facts.place(l).root) {
                    lent.push(l);
                }
            }
            let oi = def.ops.iter().position(|o| o.name == op.name);
            let own_resumes: Vec<NodeId> = self.resumes[resumes_before..]
                .iter()
                .filter(|(_, c)| *c == cap)
                .map(|(n, _)| *n)
                .collect();
            clauses_done.push((oi, cs.clone(), own_resumes));
            self.merge_summary(&cs);
            clause_sum.captures.extend(cs.captures.iter().copied());
            clause_sum
                .moved_captures
                .extend(cs.moved_captures.iter().copied());
            clause_sum.dropped.extend(cs.dropped.iter().copied());
            clause_sum.spawns.extend(cs.spawns.iter().copied());
            for &r in &cs.reads {
                if !cs.own_roots.contains(&self.facts.place(r).root) {
                    clause_sum.reads.insert(r);
                }
            }
        }
        footprint.sort();
        footprint.dedup();
        for &m in &footprint {
            self.facts.footprint.push((cap, m));
        }
        // The suspension points of the handler (effects rule 1): a node that runs a
        // clause, and a resume, can resume more than once if a clause or the body can.
        if clauses_done.iter().any(|(_, cs, _)| cs.multi) {
            self.facts.clause_multi.push(cap);
        }
        if body_sum.multi {
            self.facts.body_multi.push(cap);
        }
        lent.sort();
        lent.dedup();
        // Resumes run the handled computation and the clauses again.
        let resumes: Vec<NodeId> = self
            .resumes
            .iter()
            .filter(|(_, c)| *c == cap)
            .map(|(n, _)| *n)
            .collect();
        for &n in &resumes {
            self.facts.resumes_at.push((n, cap));
            for &m in &footprint {
                self.facts.mutates_at.push((n, m));
            }
            for &l in &lent {
                self.facts.lends_mut.push((n, l));
            }
        }
        let mut changes: Vec<PlaceId> = body_sum
            .muts
            .iter()
            .chain(&body_sum.lends)
            .copied()
            .collect();
        changes.extend(footprint.iter().chain(&lent).copied());
        let mut h = super::Handled {
            cap,
            clauses: clauses_done,
            footprint,
            lent,
            clause_sum,
            resumes,
            changes,
        };
        let calls: Vec<NodeId> = self
            .cap_calls
            .iter()
            .filter(|(_, c)| *c == cap)
            .map(|(n, _)| *n)
            .collect();
        let args: Vec<super::OpArg> = self
            .op_args
            .iter()
            .filter(|a| a.cap == cap)
            .copied()
            .collect();
        self.run_handler(&mut h, &calls, &args);
        self.handled.push(h);
        self.cur = saved;
        let _ = self.emit(span, "end handle", String::new());
        // The value of the handled body: also a task handle or a function value. A
        // clause value that holds references or function values joins it.
        let mut out = v;
        for cv in clause_vals {
            if cv.refs.is_empty() && !self.has_fn(&cv.ty, 0) {
                continue;
            }
            let mut refs = out.refs.clone();
            refs.extend(cv.refs.iter().copied());
            let j = self.join_val(&out, &cv);
            out = Val { refs, ..j };
        }
        out
    }

    /// The clauses of handler `h` run at the nodes `calls`, and they get the places
    /// `args`. `apply_stored` calls it again for the nodes that it adds.
    pub(super) fn run_handler(
        &mut self,
        h: &mut super::Handled,
        calls: &[NodeId],
        args: &[super::OpArg],
    ) {
        // A call that reaches this handler must not pass places that the handler mutates.
        for &n in calls {
            for &m in h.footprint.iter().chain(&h.lent) {
                self.facts.call_mut.push((n, m, 1000 + h.cap.0));
            }
            for &l in &h.lent {
                self.facts.lends_mut.push((n, l));
            }
        }
        // A clause mutates and reads through its parameters what the operation gets.
        let mut changes: Vec<PlaceId> = Vec::new();
        for (oi, cs, _) in &h.clauses {
            changes.extend(self.clause_through_params(args, *oi, cs));
        }
        // A resume runs the handled computation, also these changes. The node that
        // gives the places reports a mutation that needs a declaration, so the
        // resume only lends them.
        for &n in &h.resumes {
            for &q in &changes {
                self.facts.lends_mut.push((n, q));
            }
        }
        h.changes.extend(changes);
        // A clause that holds a reference into what its parameter gets across
        // `resume` sees each change of the argument place as a change of the parameter.
        let all: Vec<super::OpArg> = self
            .op_args
            .iter()
            .filter(|a| a.cap == h.cap)
            .copied()
            .collect();
        for (oi, cs, own_resumes) in &h.clauses {
            self.resume_through_params(&all, *oi, cs, own_resumes, &h.changes);
        }
        // A clause runs at each operation that it handles. There it uses its
        // captures, moves the moved ones, and its locals go out of scope.
        for &n in calls {
            for &v in &h.clause_sum.captures {
                self.facts.uses.push((v, n));
            }
            for &r in &h.clause_sum.reads {
                self.facts.reads_at.push((n, r));
            }
            for &v in &h.clause_sum.moved_captures {
                if !self.is_copy_var(v) {
                    self.move_var(v, n);
                }
            }
            for &v in &h.clause_sum.dropped {
                self.facts.scope_end.push((v, n));
            }
            // A task that a clause spawns into an outer scope starts there.
            for &t in &h.clause_sum.spawns {
                self.facts.spawned_at.push((t, n));
            }
        }
    }

    /// Applies what clause `cs` of operation `op` does through its reference
    /// parameters at each node of `args` that gives places to the operation.
    /// Returns the places that change: the clause mutates them or lends them.
    fn clause_through_params(
        &mut self,
        args: &[super::OpArg],
        op: Option<usize>,
        cs: &Summary,
    ) -> Vec<PlaceId> {
        let mut changed = Vec::new();
        let here = self.frames.iter().rev().find_map(|f| f.barrier);
        let args: Vec<_> = args
            .iter()
            .filter(|a| a.op.is_none() || a.op == op)
            .copied()
            .collect();
        let through = |me: &mut Self, p: PlaceId, a: &super::OpArg| -> Vec<PlaceId> {
            let r = me.root_place(p);
            let Some(&k) = cs.param_roots.get(&r) else {
                return Vec::new();
            };
            let given = super::fnval::Given {
                pos: a.pos,
                place: a.place,
                root: a.root,
            };
            me.through(p, r, k, &[given])
                .into_iter()
                .map(|g| g.place)
                .collect()
        };
        for a in &args {
            for &m in &cs.muts {
                for q in through(self, m, a) {
                    changed.push(q);
                    // The summary of the body gets the change only for its own nodes.
                    if a.body == here {
                        self.mutate(a.node, q);
                    } else {
                        self.facts.mutates_at.push((a.node, q));
                    }
                    self.facts.call_mut.push((a.node, q, a.root));
                }
            }
            for &r in &cs.reads {
                for q in through(self, r, a) {
                    self.facts.reads_at.push((a.node, q));
                    if a.body == here {
                        self.sum().reads.insert(q);
                    }
                }
            }
            for &(l, p) in &cs.binds {
                for q in through(self, p, a) {
                    self.point_local(l, q);
                }
            }
            for &l in &cs.lends {
                for q in through(self, l, a) {
                    changed.push(q);
                    if a.body == here {
                        self.lend(a.node, q, a.root);
                    } else {
                        self.facts.lends_mut.push((a.node, q));
                        self.facts.call_mut.push((a.node, q, a.root));
                    }
                }
            }
        }
        changed
    }

    /// At each resume of clause `cs` of operation `op`, a change of a place that
    /// the operation gets is a change of the parameter of the clause.
    fn resume_through_params(
        &mut self,
        args: &[super::OpArg],
        op: Option<usize>,
        cs: &Summary,
        resumes: &[NodeId],
        changes: &[PlaceId],
    ) {
        if resumes.is_empty() {
            return;
        }
        let args: Vec<_> = args
            .iter()
            .filter(|a| a.op.is_none() || a.op == op)
            .copied()
            .collect();
        let mut out = Vec::new();
        for (&x, &k) in &cs.param_roots {
            for a in args.iter().filter(|a| a.pos.is_none_or(|i| i == k)) {
                for &m in changes {
                    out.extend(self.onto_param(m, a.place, x, a.pos.is_some()));
                }
            }
        }
        out.sort();
        out.dedup();
        for &n in resumes {
            for &q in &out {
                self.facts.mutates_at.push((n, q));
            }
        }
    }

    /// Returns the place below parameter root `x` that a change of `m` changes, where
    /// `x` stands for argument place `p`. With `exact` false, `x` can be anywhere inside `p`.
    fn onto_param(&mut self, m: PlaceId, p: PlaceId, x: PlaceId, exact: bool) -> Option<PlaceId> {
        let (pm, pp) = (self.facts.place(m), self.facts.place(p));
        if pm.root != pp.root {
            return None;
        }
        let base = |me: &Self, q: PlaceId| me.facts.wild_base(q).unwrap_or(q);
        let (bm, bp) = (base(self, m), base(self, p));
        let overlap = weft_verified::places::overlaps(
            &self.facts.place(bm).steps,
            &self.facts.place(bp).steps,
        );
        if !overlap {
            return None;
        }
        // A change at or below the argument place keeps its steps below `x`.
        let mut at = Some(m);
        while let Some(q) = at {
            if q == p {
                return Some(if exact {
                    self.rebase(m, p, x)
                } else {
                    self.facts.wildcard(x)
                });
            }
            at = self.facts.place(q).parent;
        }
        // A change above the argument place, or one that can alias it, can change
        // any place below `x`.
        Some(self.facts.wildcard(x))
    }

    fn merge_summary(&mut self, s: &Summary) {
        let own = s.own_roots.clone();
        let t = self.sum();
        for &m in &s.muts {
            t.muts.insert(m);
        }
        t.reads.extend(s.reads.iter().copied());
        t.escapes.extend(s.escapes.iter().cloned());
        t.performs.extend(s.performs.iter().copied());
        t.may_abort |= s.may_abort;
        t.multi |= s.multi;
        t.passthrough.extend(s.passthrough.iter().copied());
        t.own_roots.extend(own);
        t.captures.extend(s.captures.iter().copied());
        t.moved_captures.extend(s.moved_captures.iter().copied());
        t.dropped.extend(s.dropped.iter().copied());
        t.lends.extend(s.lends.iter().copied());
        t.spawns.extend(s.spawns.iter().copied());
        t.own_caps.extend(s.own_caps.iter().copied());
        t.tasks.extend(s.tasks.iter().copied());
        for &a in &s.op_args {
            if !t.op_args.contains(&a) {
                t.op_args.push(a);
            }
        }
    }

    // -----------------------------------------------------------------------
    // Scopes
    // -----------------------------------------------------------------------

    fn scope(&mut self, binder: &ast::Ident, body: &ast::Block, span: Span) -> Val {
        self.frames.push(Frame {
            names: Vec::new(),
            barrier: None,
        });
        let n = self.emit(span, "scope", String::new());
        let l = self.new_local(&binder.name, VarKind::Local, binder.span, Ty::Scope, false);
        self.facts.vars[self.locals[l].var.index()].nonportable = true;
        self.assign_local(
            l,
            &Val {
                ty: Ty::Scope,
                ..Val::default()
            },
            n,
        );
        self.perform_effect(n, "Async");
        self.abortive(n);
        self.scopes.push((l, Vec::new()));
        // The tasks join before the locals of the body go out of scope.
        self.frames.push(Frame {
            names: Vec::new(),
            barrier: None,
        });
        self.jumps.push(Jump::Fence("scope body"));
        let v = self.block_inner(body);
        self.jumps.pop();
        let v = self.hand_out(v, body.span);
        let tail = block_tail(body);
        self.flush(tail);
        let (_, tasks) = self.scopes.pop().unwrap_or_default();
        let end = self.emit(span, "scope end", String::new());
        for t in tasks {
            self.facts.joined_at.push((t, end));
        }
        let held = self.hold_out(&v, tail);
        self.end_frame(body.span);
        self.frames.pop();
        let v = if self.use_held(held, tail) {
            Val { var: None, ..v }
        } else {
            v
        };
        self.end_frame(span);
        self.frames.pop();
        v
    }
}
