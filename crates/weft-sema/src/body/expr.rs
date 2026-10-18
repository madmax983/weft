//! Expressions, places, closures, handlers and scopes.

use super::{
    ast, block_tail, effects, elem_step, expr_tail, field_step, AdtKind, BinOp, ContInfo, Deref,
    Expr, ExprKind, FnTy, Frame, HandlerFrame, HandlerInfo, IntTy, ItemRef, LVal, Lit, Lower,
    NodeId, PathRef, Pattern, PlaceId, Rc, RootKind, Span, StrPart, Summary, Ty, UnOp, Val,
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
                // Each part is moved and held before the next one runs.
                let mut parts: Vec<Val> = Vec::new();
                let mut held = Vec::new();
                for (i, x) in es.iter().enumerate() {
                    let p = self.expr(x);
                    self.consume(&p, x.span);
                    if i + 1 < es.len() {
                        held.extend(self.hold(&p, "tuple part", x.span));
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
                for x in es {
                    let v = self.expr(x);
                    self.unify(&t, &v.ty, x.span);
                    self.consume(&v, x.span);
                }
                let ty = self.b.vec.map_or(Ty::Error, |v| Ty::Adt(v, vec![t]));
                Val {
                    ty,
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
                for x in es {
                    let v = self.expr(x);
                    self.unify(&elem, &v.ty, x.span);
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
                    let id = ast::Ident {
                        name: self.prog.fns[f].name.clone(),
                        span: name.span,
                    };
                    let _ = id;
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
                    Some(Val {
                        ty,
                        item: Some(f),
                        ..Val::default()
                    })
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
            };
        }
        if let Some(ItemRef::Fn(f)) = self.prog.lookup(self.module, &id.name) {
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
        // A reference field of a `!Move` struct points into the same struct.
        let mut refs = Vec::new();
        if let (ExprKind::Field { base, name }, Ty::Ref(_)) = (&e.kind, self.inf.shallow(&lv.ty)) {
            if let Some(blv) = self.place_expr(base) {
                if let Ty::Adt(a, _) = self.deref_ty(&blv.ty) {
                    if let AdtKind::Struct(fs) = &self.prog.adts[a].kind {
                        if let Some(sp) = fs
                            .iter()
                            .find(|f| f.name == name.name)
                            .and_then(|f| f.place.clone())
                        {
                            refs = self.subst_place(&sp, std::slice::from_ref(&blv.places), 0);
                        }
                    }
                }
            }
        }
        Val {
            ty: lv.ty.clone(),
            refs,
            place: Some(lv),
            ..Val::default()
        }
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
                    let r = self.root("temporary", RootKind::Local);
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
        let held = self.hold(&a, "operand", lhs.span);
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
            self.consume(&v, value.span);
        }
        for d in &defs {
            if !fields.iter().any(|(n, _)| n.name == d.name) && d.place.is_none() {
                self.err("W0115", format!("missing field `{}`", d.name), span);
            }
        }
        Val {
            ty: Ty::Adt(adt, args),
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
        let ty = if else_.is_none() {
            Ty::Unit
        } else if matches!(self.inf.shallow(&a.ty), Ty::Never) {
            b.ty.clone()
        } else {
            self.unify(&a.ty, &b.ty, span);
            a.ty.clone()
        };
        let mut refs = a.refs.clone();
        refs.extend(b.refs.iter().copied());
        let uniq = a.uniq && b.uniq;
        Val {
            ty,
            refs,
            uniq,
            ..Val::default()
        }
    }

    fn match_expr(&mut self, scrut: &Expr, arms: &[ast::Arm], span: Span) -> Val {
        let lv = self.place_expr(scrut);
        // A binding by reference depends on the `Rc` handles on the way.
        let deps = lv.as_ref().map(|l| l.deps.clone()).unwrap_or_default();
        let saved_deps = std::mem::replace(&mut self.match_deps, deps);
        let (sty, by_ref, places, sval) = if let Some(lv) = lv {
            let by_ref = lv.through_ref;
            let v = Val {
                ty: lv.ty.clone(),
                place: Some(lv.clone()),
                var: lv.owner.map(|l| self.locals[l].var),
                ..Val::default()
            };
            (lv.ty.clone(), by_ref, lv.places, v)
        } else {
            let v = self.expr(scrut);
            let r = self.root("temporary", RootKind::Local);
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
            }
            refs.extend(v.refs.iter().copied());
            let v = self.hand_out(v, arm.span);
            let tail = expr_tail(&arm.body);
            let held = self.hold_out(&v, tail);
            self.end_frame(arm.span);
            self.frames.pop();
            self.use_held(held, tail);
            if let Some(c) = self.cur {
                self.facts.cfg_edge.push((c, join));
                reached = true;
            }
        }
        self.cur = if reached { Some(join) } else { None };
        self.match_deps = saved_deps;
        Val {
            ty: result,
            refs,
            ..Val::default()
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
        self.sums.push(Summary::default());
        let si = self.sums.len() - 1;
        self.frames.push(Frame {
            names: Vec::new(),
            barrier: Some(si),
        });
        let entry = self.start(span, "closure entry");
        let mut ptys = Vec::new();
        let mut param_roots = Vec::new();
        for (i, p) in params.iter().enumerate() {
            let ty = match (&p.ty, expected.and_then(|f| f.params.get(i))) {
                (Some(t), _) => self.local_ty_pub(t),
                (None, Some(t)) => t.clone(),
                (None, None) => self.inf.fresh(),
            };
            ptys.push(ty.clone());
            let l = self.new_local(&p.name.name, VarKind::Param, p.span, ty.clone(), false);
            let refs = if ty.is_ref() {
                vec![self.root(&p.name.name, RootKind::Param)]
            } else {
                Vec::new()
            };
            param_roots.push(refs.first().copied());
            self.assign_local(
                l,
                &Val {
                    ty,
                    refs,
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
        if let Some(f) = expected {
            if !matches!(self.inf.shallow(&f.ret), Ty::Unit) {
                self.unify(&f.ret, &v.ty, body.span);
            }
        }
        let v = self.hand_out(v, body.span);
        let ret_refs = self.closure_ret_refs(&v, expr_tail(body));
        self.sum().ret_refs = ret_refs;
        self.sum().param_roots = param_roots;
        let ret_ty = v.ty.clone();
        self.drop_value(&v, body.span);
        self.flush(expr_tail(body));
        self.end_frame(span);
        let end = self.cur;
        self.frames.pop();
        let sum = self.sums.pop().unwrap_or_default();
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
        self.closures.push(sum.clone());
        self.cur = saved;
        self.restore_pending(saved_pending);
        // The creation node uses the captures and moves the moved ones.
        let mut refs = Vec::new();
        let caps: Vec<_> = sum.captures.iter().copied().collect();
        for v in &caps {
            if let Some(l) = self.locals.iter().position(|l| l.var == *v) {
                let loc = self.locals[l].clone();
                refs.extend(loc.refs.iter().copied());
                if !loc.ty.is_ref() {
                    if let Some(r) = loc.root {
                        if !sum.moved_captures.contains(v) {
                            refs.push(r);
                        }
                    }
                }
                self.pend_uses.push(*v);
                self.note_capture(l);
            }
        }
        refs.sort();
        refs.dedup();
        let n = self.emit(span, "closure", String::new());
        for v in &sum.moved_captures {
            if !self.is_copy_var(*v) {
                self.move_var(*v, n);
            }
        }
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
                    self.err(
                        "W0204",
                        format!(
                            "the closure returns a reference into `{}`: its local `{name}` goes out of scope at the return",
                            self.facts.place(r).display
                        ),
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
            match sum.param_roots.iter().position(|&p| p == Some(root)) {
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
    fn rebase(&mut self, p: PlaceId, from: PlaceId, onto: PlaceId) -> PlaceId {
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

    /// Applies a closure summary at a node: the closure runs there.
    pub(super) fn apply_summary(&mut self, n: NodeId, s: usize, root_index: u32) {
        let sum = self.closures[s].clone();
        let own = |me: &Self, p: PlaceId| sum.own_roots.contains(&me.facts.place(p).root);
        for &m in &sum.muts {
            if !own(self, m) {
                self.mutate(n, m);
                self.facts.call_mut.push((n, m, root_index));
            }
        }
        for &r in &sum.reads {
            if !own(self, r) {
                self.facts.reads_at.push((n, r));
                self.sum().reads.insert(r);
            }
        }
        for e in &sum.escapes {
            self.facts.escapes_at.push((n, e.clone()));
            self.sum().escapes.insert(e.clone());
        }
        for &c in &sum.performs {
            self.facts.performs_at.push((n, c));
            self.sum().performs.insert(c);
            self.cap_calls.push((n, c));
        }
        if sum.may_abort {
            self.abortive(n);
        }
        if sum.multi {
            self.multi_node(n);
        }
        let pt = sum.passthrough.clone();
        self.sum().passthrough.extend(pt);
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
        self.sums.push(Summary::default());
        let v = self.expr(body);
        self.flush(expr_tail(body));
        let body_sum = self.sums.pop().unwrap_or_default();
        self.merge_summary(&body_sum);
        self.handlers.pop();
        let ty = v.ty.clone();
        let saved = self.cur;
        let mut footprint = Vec::new();
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
            for (p, pt) in c.params.iter().zip(&op.params) {
                let l = self.new_local(&p.name.name, VarKind::Param, p.span, pt.clone(), false);
                self.assign_local(
                    l,
                    &Val {
                        ty: pt.clone(),
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
            });
            let kv = self.locals[k].var;
            self.bind(kv, entry);
            let cv = self.block(&c.body);
            self.flush(block_tail(&c.body));
            if !matches!(self.inf.shallow(&cv.ty), Ty::Never) {
                self.unify(&ty, &cv.ty, c.body.span);
            }
            self.end_frame(c.span);
            self.frames.pop();
            let cs = self.sums.pop().unwrap_or_default();
            for &m in &cs.muts {
                if !cs.own_roots.contains(&self.facts.place(m).root) {
                    footprint.push(m);
                }
            }
            self.merge_summary(&cs);
        }
        footprint.sort();
        footprint.dedup();
        for &m in &footprint {
            self.facts.footprint.push((cap, m));
        }
        // Resumes run the handled computation and the clauses again.
        let resumes: Vec<NodeId> = self
            .resumes
            .iter()
            .filter(|(_, c)| *c == cap)
            .map(|(n, _)| *n)
            .collect();
        for n in resumes {
            for &m in &footprint {
                self.facts.mutates_at.push((n, m));
            }
        }
        // A call that reaches this handler must not pass places that the handler mutates.
        let calls: Vec<NodeId> = self
            .cap_calls
            .iter()
            .filter(|(_, c)| *c == cap)
            .map(|(n, _)| *n)
            .collect();
        for n in calls {
            for &m in &footprint {
                self.facts.call_mut.push((n, m, 1000 + cap.0));
            }
        }
        self.cur = saved;
        if let Ty::Fn(f) = self.inf.resolve(&ty) {
            if let Some(s) = f.summary {
                if self.closures[s].performs.contains(&cap) {
                    self.err(
                        "W0313",
                        format!("a closure that performs `{}` escapes its handler", def.name),
                        span,
                    );
                }
            }
        }
        let _ = self.emit(span, "end handle", String::new());
        Val {
            ty,
            refs: v.refs,
            parts: v.parts,
            uniq: v.uniq,
            ..Val::default()
        }
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
        self.scopes.push(Vec::new());
        let v = self.block(body);
        let tasks = self.scopes.pop().unwrap_or_default();
        let v = self.hand_out(v, span);
        let end = self.emit(span, "scope end", String::new());
        for t in tasks {
            self.facts.joined_at.push((t, end));
        }
        self.end_frame(span);
        self.frames.pop();
        v
    }
}
