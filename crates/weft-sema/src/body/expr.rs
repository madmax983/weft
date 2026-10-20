//! Expressions, places, closures, handlers and scopes.

use super::{
    ast, block_tail, effects, elem_step, expr_tail, field_step, AdtKind, BinOp, ContInfo, Deref,
    Expr, ExprKind, FnId, FnTy, HandlerFrame, HandlerInfo, IntTy, ItemRef, Jump, LVal, Lit, Lower,
    NodeId, PathRef, Pattern, PlaceId, Rc, RootKind, Span, StrPart, Summary, Ty, UnOp, Val, VarId,
    VarKind,
};
use std::collections::{BTreeMap, BTreeSet};

use weft_facts::{Step, StepKind, TaskId};

use crate::props::Prop;

impl Lower<'_> {
    /// Lowers an expression and returns its value.
    pub(super) fn expr(&mut self, e: &Expr) -> Val {
        match &e.kind {
            ExprKind::Lit(l) => {
                self.lit_span = e.span;
                self.lit(l)
            }
            ExprKind::Unary {
                op: UnOp::Neg,
                expr,
            } if neg_literal(expr) => {
                // `-128` is one literal: its value is negative. `--128` is 128.
                let v = self.expr(expr);
                if let Some(last) = self.int_lits.last_mut() {
                    last.1 = !last.1;
                    last.3 = e.span;
                }
                let t = self.deref_ty(&v.ty);
                self.arith(&t, &t, expr.span);
                Val {
                    ty: t,
                    ..Val::default()
                }
            }
            ExprKind::Name(id) => self.name(id, e.span),
            ExprKind::Field { base, name } => {
                if let ExprKind::Lit(l) = &base.kind {
                    // `2.s` and `500.ms` are durations. A literal has no other field.
                    if matches!(l, Lit::Int(_)) && matches!(name.name.as_str(), "s" | "ms") {
                        let d = self
                            .b
                            .duration
                            .map_or(Ty::Error, |d| Ty::Adt(d, Vec::new()));
                        return Val {
                            ty: d,
                            ..Val::default()
                        };
                    }
                    self.lit_span = base.span;
                    let _ = self.lit(l);
                    self.err(
                        "W0104",
                        format!("a literal has no field `{}`", name.name),
                        name.span,
                    );
                    return Val {
                        ty: Ty::Error,
                        ..Val::default()
                    };
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
                let (mut held, mut taken) = (Vec::new(), Vec::new());
                for (i, x) in es.iter().enumerate() {
                    let p = self.expr(x);
                    let p = self.with_fn_refs(p);
                    self.consume(&p, x.span);
                    if i + 1 < es.len() {
                        self.hold_part(&p, "tuple part", x.span, &mut held, &mut taken);
                    }
                    parts.push(p);
                }
                self.pend_uses.extend(held);
                self.take_held_here(&taken, e.span);
                // A part that can hold a function value gets a type variable, as
                // the element of a `Vec` does. So a new function value in the part
                // joins the values of the type (`Lower::unify`).
                let mut tys = Vec::new();
                for p in &parts {
                    if self.has_fn(&p.ty) {
                        let tv = self.inf.fresh();
                        let _ = self.inf.unify(&tv, &p.ty);
                        tys.push(tv);
                    } else {
                        tys.push(p.ty.clone());
                    }
                }
                let ty = Ty::Tuple(tys);
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
                let (caps, refs) = self.elements(es, &t);
                let ty = self.b.vec.map_or(Ty::Error, |v| Ty::Adt(v, vec![t]));
                Val {
                    ty,
                    refs,
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
                let (caps, refs) = self.elements(es, &elem);
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
                    refs,
                    ..Val::default()
                }
            }
            (ExprKind::Closure { params, body }, Some(Ty::Fn(f))) => {
                self.closure(params, body, Some(&f), e.span)
            }
            _ => self.expr(e),
        }
    }

    /// Lowers the elements of an array literal with element type `elem`. Returns
    /// the capabilities and the places of the elements: the array points where
    /// its elements point. Each element is held while the later ones run.
    fn elements(
        &mut self,
        es: &[Expr],
        elem: &Ty,
    ) -> (std::collections::BTreeSet<weft_facts::CapId>, Vec<PlaceId>) {
        let mut caps = std::collections::BTreeSet::new();
        let mut refs = Vec::new();
        let (mut held, mut taken) = (Vec::new(), Vec::new());
        for (i, x) in es.iter().enumerate() {
            let v = self.expr(x);
            let v = self.with_fn_refs(v);
            self.unify(elem, &v.ty, x.span);
            self.keep_modes(&v, elem, x.span);
            self.escape(&v);
            caps.extend(self.val_caps(&v));
            self.consume(&v, x.span);
            if i + 1 < es.len() {
                self.hold_part(&v, "element", x.span, &mut held, &mut taken);
            }
            refs.extend(v.refs.iter().copied());
        }
        self.pend_uses.extend(held);
        if let Some(last) = es.last() {
            self.take_held_here(&taken, last.span);
        }
        refs.sort();
        refs.dedup();
        (caps, refs)
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
                                empty: true,
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
                    self.check_visible(f, name.span);
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
            Lit::Int(n) => {
                let t = self.inf.fresh_int();
                self.int_lits.push((*n, false, t.clone(), self.lit_span));
                t
            }
            Lit::Bool(_) => Ty::Bool,
            Lit::Unit => Ty::Unit,
            Lit::Str(parts) => {
                for p in parts {
                    if let StrPart::Interp(e) = p {
                        // The text reads the whole value.
                        let v = self.expr(e);
                        if let Some(lv) = &v.place {
                            self.touch_unset(&lv.places);
                        }
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
            if self.locals[l].cont.as_ref().is_some_and(|k| k.fail) {
                self.fail_resume(span);
            }
            self.use_local(l);
            let loc = self.locals[l].clone();
            // A use of the local as a value reads its variable (W0405).
            if let Some(c) = self.var_place(l) {
                self.read_var(c);
            }
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
                    uniq: self.locals.is_uniq(l),
                    deps: Vec::new(),
                    held: std::collections::BTreeSet::new(),
                })
            };
            return Val {
                ty: loc.ty.clone(),
                refs: loc.refs.clone(),
                var: Some(loc.var),
                local: Some(l),
                uniq: self.locals.is_uniq(l),
                summary: loc.summary,
                tasks: loc.tasks,
                parts: None,
                place,
                fn_param: loc.fn_param,
                item: None,
                caps: loc.caps,
                empty: false,
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
        self.check_item_value(f, &targs, span);
        let sig = &self.sigs[f];
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
            empty: true,
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
                        effects::by_identity(self.prog, &names[0]).map(PathRef::Effect)
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
                        // A place through the reference reads the reference.
                        if let Some(c) = loc.cell {
                            self.read_var(c);
                        }
                        let (places, deps) = self.split_deps(&loc.refs);
                        Some(LVal {
                            places,
                            ty: *inner,
                            owner: None,
                            through_ref: true,
                            uniq: self.locals.is_uniq(l),
                            deps,
                            held: loc.caps,
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
                            uniq: self.locals.is_uniq(l),
                            deps: Vec::new(),
                            held: std::collections::BTreeSet::new(),
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
                // An element through a reference that a part holds: the elements
                // are where the reference points.
                let lv = match self.inf.shallow(&lv.ty) {
                    Ty::Ref(inner) => LVal {
                        ty: *inner,
                        ..self.deref_lval(lv)
                    },
                    _ => lv,
                };
                // An index reads the length and the buffer of the indexed place,
                // also for a borrow of the element (W0405).
                for &p in &lv.places {
                    self.read_var(p);
                }
                if let Some(ix) = index {
                    let v = self.expr(ix);
                    let t = self.deref_ty(&v.ty);
                    self.unify(&Ty::Int(IntTy::Usize), &t, ix.span);
                }
                let t = self.deref_ty(&lv.ty);
                // The element type keeps its type variables: a new function value
                // in the element joins the values of the type (`Lower::unify`).
                let rt = self.inf.shallow(&t);
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
                    lv = self.deref_lval(lv);
                    lv.ty = *inner;
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
                        held: std::mem::take(&mut lv.held),
                    };
                }
                _ => break,
            }
        }
        let t = self.inf.deep(&lv.ty);
        if let Some((steps, next, _)) = field_step(self.prog, &t, &name.name) {
            // The field type keeps the type variables of the struct type: a new
            // function value in the field joins the values of the type
            // (`Lower::unify`).
            let next = match field_step(self.prog, &self.inf.shallow(&lv.ty), &name.name) {
                Some((s, n, _)) if s.len() == steps.len() => n,
                _ => next,
            };
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

    /// Follows the reference that the places of `lv` hold: a part of a tuple, a
    /// field or an element of type `&T`. The result has the places that the
    /// reference points into (`held_refs`), so a field of it is a place there,
    /// not a place of the value that holds the reference. If the body does not
    /// know them, the places stay.
    fn deref_lval(&mut self, lv: LVal) -> LVal {
        let held = self.held_refs(&lv.places);
        let (named, deps) = self.split_deps(&held);
        if named.is_empty() {
            return LVal {
                through_ref: true,
                ..lv
            };
        }
        let mut all_deps = lv.deps;
        all_deps.extend(deps);
        LVal {
            places: named,
            through_ref: true,
            deps: all_deps,
            ..lv
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
        // A value that holds references points where the references at the place point.
        let refs = match self.field_referents(e) {
            Some(rs) if matches!(self.inf.shallow(&lv.ty), Ty::Ref(_)) => rs,
            _ if self.holds_refs(&lv.ty) => self.held_refs(&lv.places),
            _ => Vec::new(),
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
                    // A borrowed temporary goes away at the end of the statement.
                    self.drop_value(&v, inner.span);
                    let r = self.temp_root(inner.span, &v.ty);
                    LVal {
                        places: vec![r],
                        ty: v.ty,
                        ..LVal::default()
                    }
                }
            }
        };
        self.touch_unset(&lv.places);
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
                // A comparison only reads its operands: a temporary goes away.
                self.drop_value(&a, lhs.span);
                self.drop_value(&b, rhs.span);
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
        let mut given: Vec<&str> = Vec::new();
        let mut refs = Vec::new();
        let (mut held, mut taken) = (Vec::new(), Vec::new());
        for (i, (name, value)) in fields.iter().enumerate() {
            if given.contains(&name.name.as_str()) {
                self.err(
                    "W0107",
                    format!("field `{}` is given twice", name.name),
                    name.span,
                );
            }
            given.push(&name.name);
            let expected = defs
                .iter()
                .find(|d| d.name == name.name)
                .map(|d| super::subst(&d.ty, &args));
            let v = self.expr_with(value, expected.as_ref());
            let v = self.with_fn_refs(v);
            match defs.iter().find(|d| d.name == name.name) {
                Some(d) => {
                    let ft = super::subst(&d.ty, &args);
                    self.unify(&ft, &v.ty, value.span);
                    self.keep_modes(&v, &ft, value.span);
                    // A literal is not in a place yet, so nothing can point into it.
                    if let (Some(sp), false) = (&d.place, v.refs.is_empty()) {
                        let at = self.place_text(&v.refs);
                        let msg = format!("`{}` can point only into `{}` of its own struct, but this value points into `{at}`; give the field its value after the struct has a place", name.name, sp.text);
                        self.err("W0605", msg, value.span);
                    }
                }
                None => self.err("W0104", format!("no field `{}`", name.name), name.span),
            }
            self.escape(&v);
            caps.extend(self.val_caps(&v));
            self.consume(&v, value.span);
            // The struct points where its fields point. A field is held while the
            // later fields run.
            if i + 1 < fields.len() {
                self.hold_part(&v, "field", value.span, &mut held, &mut taken);
            }
            refs.extend(v.refs.iter().copied());
        }
        self.pend_uses.extend(held);
        self.take_held_here(&taken, span);
        // A place field that the literal does not give has no value yet: see
        // `Lower::unset_paths`.
        for d in &defs {
            if d.place.is_none() && !fields.iter().any(|(n, _)| n.name == d.name) {
                self.err("W0115", format!("missing field `{}`", d.name), span);
            }
        }
        Val {
            ty: Ty::Adt(adt, args),
            caps,
            refs,
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
        let before = self.branch_state();
        let a = self.block(then);
        // The value of a branch moves into the value of the `if`, as in the
        // interpreter: a local that a branch names is moved there.
        if else_.is_some() {
            self.consume(&a, block_tail(then));
        } else {
            // With no `else`, nothing uses the value of the branch.
            self.discard_block_value(&a, block_tail(then));
        }
        self.flush(block_tail(then));
        let a_end = self.cur;
        let a_state = self.branch_state();
        self.set_branch(&before);
        self.cur = Some(br);
        let b = else_.map_or_else(Val::default, |e| self.expr(e));
        if let Some(e) = else_ {
            self.consume(&b, expr_tail(e));
            self.flush(expr_tail(e));
        }
        let b_end = self.cur;
        let b_state = self.branch_state();
        let pairs: Vec<_> = [(a_end, a_state), (b_end, b_state)]
            .into_iter()
            .filter_map(|(end, st)| end.map(|n| (n, st)))
            .collect();
        let ends: Vec<_> = pairs.iter().map(|(_, st)| st.clone()).collect();
        self.join_branches(&ends);
        let join = self.facts.add_node(span, "join", String::new());
        let mut any = false;
        for end in [a_end, b_end].into_iter().flatten() {
            self.facts.cfg_edge.push((end, join));
            any = true;
        }
        let joined = Self::joined(&ends);
        for (end, st) in &pairs {
            self.retire_stale(*end, join, st, &joined);
        }
        self.cur = if any { Some(join) } else { None };
        let mut refs = a.refs.clone();
        refs.extend(b.refs.iter().copied());
        let uniq = a.uniq && b.uniq;
        // A new task handle, for example of a scope with a spawn at its end.
        let tasks: BTreeSet<TaskId> = [&a, &b]
            .iter()
            .filter(|x| x.local.is_none() && !matches!(self.inf.shallow(&x.ty), Ty::Never))
            .flat_map(|x| x.tasks.iter().copied())
            .filter(|_| else_.is_some())
            .collect();
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
            tasks,
            ..v
        }
    }

    fn match_expr(&mut self, scrut: &Expr, arms: &[ast::Arm], span: Span) -> Val {
        let errors = self.diags.len();
        let lv = self.place_expr(scrut);
        let temp = lv.is_none();
        // A binding by reference depends on the `Rc` handles on the way.
        let deps = lv.as_ref().map(|l| l.deps.clone()).unwrap_or_default();
        let saved_deps = std::mem::replace(&mut self.match_deps, deps);
        let (sty, by_ref, places, sval) = if let Some(lv) = lv {
            let by_ref = lv.through_ref;
            // A by-value binding moves the local, or a part of it.
            let whole = lv
                .owner
                .filter(|&l| self.locals[l].root.is_some_and(|r| lv.places == [r]));
            // A by-value binding points where the references in the value point.
            let refs = if !by_ref && self.holds_refs(&lv.ty) {
                self.held_refs(&lv.places)
            } else {
                Vec::new()
            };
            let v = Val {
                ty: lv.ty.clone(),
                place: Some(lv.clone()),
                var: whole.map(|l| self.locals[l].var),
                refs,
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
        let mut tasks: BTreeSet<TaskId> = BTreeSet::new();
        let before = self.branch_state();
        let mut ends = Vec::new();
        let mut end_nodes = Vec::new();
        for arm in arms {
            self.cur = Some(br);
            self.set_branch(&before);
            self.push_frame(None);
            let bn = self.emit(arm.pat.span(), "arm", String::new());
            self.match_moves = false;
            self.check_binders(&arm.pat);
            self.match_pattern(&arm.pat, &sty, &places, by_ref, &sval, bn);
            // A by-value binding moves the scrutinee once.
            if self.match_moves {
                self.consume(&sval, arm.pat.span());
            }
            self.match_drops(&arm.pat, &sty, &sval, temp || self.match_moves);
            let v = self.expr(&arm.body);
            self.flush(expr_tail(&arm.body));
            if !matches!(self.inf.shallow(&v.ty), Ty::Never) {
                if v.local.is_none() {
                    tasks.extend(v.tasks.iter().copied());
                }
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
            // The value of the arm moves into the value of the `match`.
            self.consume(&v, tail);
            let held = self.hold_out(&v, tail);
            self.end_frame(arm.span);
            self.pop_frame();
            let _ = self.use_held(held, tail);
            if let Some(c) = self.cur {
                self.facts.cfg_edge.push((c, join));
                reached = true;
                ends.push(self.branch_state());
                end_nodes.push(c);
            }
        }
        self.join_branches(&ends);
        let at_join = Self::joined(&ends);
        for (end, st) in end_nodes.iter().zip(&ends) {
            self.retire_stale(*end, join, st, &at_join);
        }
        self.cur = if reached { Some(join) } else { None };
        self.match_deps = saved_deps;
        // A `match` with an error has no second error for its arms.
        if self.diags.len() == errors {
            let pats: Vec<&Pattern> = arms.iter().map(|a| &a.pat).collect();
            self.check_exhaustive(&pats, &sty, span);
        }
        match joined {
            Some(j) if self.has_fn(&j.ty) => Val { refs, tasks, ..j },
            _ => Val {
                ty: result,
                refs,
                tasks,
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
                self.lit_span = *s;
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
                    // A by-value binding of a reference payload is that reference.
                    Val {
                        ty: ty.clone(),
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
        self.push_frame(Some(si));
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
        let first_node = u32::try_from(entry.index()).unwrap_or(u32::MAX);
        self.open_stmt();
        let mut ptys = Vec::new();
        let mut param_roots = std::collections::BTreeMap::new();
        for (i, p) in params.iter().enumerate() {
            if params[..i].iter().any(|q| q.name.name == p.name.name) {
                self.err(
                    "W0107",
                    format!("parameter `{}` is defined twice", p.name.name),
                    p.name.span,
                );
            }
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
                let rid = self.facts.place(r).root;
                self.param_of_root.insert(rid, (si, i));
                vec![r]
            } else {
                Vec::new()
            };
            let fn_param = matches!(self.inf.shallow(&ty), Ty::Fn(_)).then_some((si, i));
            // A parameter that holds a function value in a field or an element holds
            // what each call gives: the body cannot follow it.
            let mark = !matches!(self.inf.shallow(&ty), Ty::Fn(_)) && self.has_fn(&ty);
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
            if mark {
                self.locals.get_mut(l).caps.insert(super::caps::UNKNOWN_FN);
                self.locals
                    .get_mut(l)
                    .sticky
                    .insert(super::caps::UNKNOWN_FN);
            }
            // A parameter whose type is not known yet can be a function value
            // that the body runs, for example as a task (`tasks`, ADR 0006).
            if matches!(self.inf.shallow(&self.locals[l].ty), Ty::Var(_)) {
                self.locals.get_mut(l).fn_param = Some((si, i));
            }
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
        // The jump of this closure is on top: `closure_return` keeps it there.
        let (exit, returned) = match self.jumps.pop() {
            Some(Jump::Closure { exit, values, .. }) => (exit, values),
            _ => (None, Vec::new()),
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
        // The value of the body is the result of the closure: it moves there, as
        // the value of a function body does.
        if falls {
            self.consume(&v, expr_tail(body));
        }
        self.flush(expr_tail(body));
        self.end_frame(span);
        if let Some(x) = exit {
            if let Some(c) = self.cur {
                self.facts.cfg_edge.push((c, x));
            }
            self.cur = Some(x);
        }
        let end = self.cur;
        self.pop_frame();
        let mut sum = self.sums.pop().unwrap_or_default();
        sum.repeats = self.take_repeats(si).into();
        // A returned function value: a call of the closure can do what it does.
        let tail = falls.then_some(&v);
        for rv in returned.iter().chain(tail) {
            sum.ret_caps.extend(self.val_caps(rv));
            sum.ret_tasks.extend(rv.tasks.iter().copied());
            if let Ty::Fn(f) = self.inf.shallow(&rv.ty) {
                let info = self.fn_info(rv);
                let r = self.value_summary(&info, f.effects.as_deref());
                let ret = self.closures[r].clone();
                sum.union_ret(&ret);
                sum.rets.insert(r);
            }
        }
        // A captured linear value is live where the closure starts, so a new value
        // in the closure overwrites it (W0601). A value that the closure moves must
        // be consumed inside it, before the closure ends.
        self.captures_live_at(&sum.captures.to_set(), entry);
        let close = Span::new(span.hi.saturating_sub(1), span.hi);
        let mut closure_end = None;
        for &var in &sum.moved_captures {
            if !self.var_linear(var) {
                continue;
            }
            let Some(c) = end else { break };
            let e = *closure_end.get_or_insert_with(|| {
                let e = self.facts.add_node(close, "closure end", String::new());
                self.facts.cfg_edge.push((c, e));
                e
            });
            self.facts.scope_end.push((var, e));
        }
        // Captures of an outer closure are captures of this one too.
        if let Some(outer) = self.sums.last_mut() {
            let _ = outer;
        }
        let id = self.closures.len();
        sum.members.insert(id);
        sum.nodes = (
            first_node,
            u32::try_from(self.facts.nodes.len()).unwrap_or(u32::MAX),
        );
        self.close_scope(si, super::fnval::Scope::Closure(id));
        self.closures.push(sum.clone());
        self.cur = saved;
        self.restore_pending(saved_pending);
        self.stmt_temps = saved_stmts;
        // The closure refers to the variables that it captures, as in the
        // interpreter. A captured copy value stays readable after its scope
        // ends; another value goes away with its variable. The scope
        // capability ends with its scope: a closure that spawns into the scope
        // cannot run after it. This holds for a copy value that holds the
        // capability too, such as a tuple or an `Option` (a resource part,
        // `Prop::Resource`). A capture that the closure moves goes into a
        // cell of the closure when the closure is made. The closure still
        // points into the variable, so it cannot leave the scope of the
        // variable: its type does not show that it runs only once, or that it
        // holds a linear value. This is conservative.
        // The closure can read a place field that has no value yet (W0304).
        let reads: Vec<PlaceId> = sum.reads.iter().copied().collect();
        self.touch_unset(&reads);
        let moved: Vec<_> = sum
            .moved_captures
            .iter()
            .copied()
            .filter(|&v| !self.is_copy_var(v))
            .collect();
        let mut refs = Vec::new();
        let mut used = Vec::new();
        let caps: Vec<_> = sum.captures.iter().copied().collect();
        for v in &caps {
            if let Some(l) = self.local_of(*v) {
                let loc = self.locals[l].clone();
                refs.extend(loc.refs.iter().copied());
                let scope = self.ty_has(&loc.ty, Prop::Resource);
                if !loc.ty.is_ref() && (self.may_free(&loc.ty) || scope) {
                    refs.extend(loc.root);
                }
                if !moved.contains(v) {
                    used.push(*v);
                }
                self.note_capture(l);
            }
        }
        refs.sort();
        refs.dedup();
        // A node that runs the closure joins the values that the other captures
        // have there (`Lower::late_join`).
        self.note_cap_values(id, &caps, &moved);
        // The moved captures are moved before the closure exists, so that the
        // move does not invalidate the new closure. The interpreter moves them
        // into the closure there (`FnFacts::by_value`). The other captures are
        // used after the move: a capture that points into a moved value is not
        // valid in the closure (W0301).
        if !moved.is_empty() {
            let m = self.emit(span, "move", String::new());
            for v in moved {
                self.move_var(v, m);
                self.facts.by_value.push((span, v));
            }
        }
        self.pend_uses.extend(used);
        let n = self.emit(span, "closure", String::new());
        let fty = FnTy {
            params: ptys,
            ret: ret_ty,
            effects: None,
            summary: Some(id),
            item: None,
        };
        let ty = Ty::Fn(Rc::new(fty));
        let mut info = self.var_info("{closure}", VarKind::Closure, span, &ty, false);
        info.once |= self.closure_not_many(id);
        info.uniq = self.closure_uniq(id);
        let var = self.new_var(info, &ty);
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

    /// The linear values among `captures` are live at `entry`, the start of a
    /// closure or a clause. A new value there overwrites the value from outside.
    fn captures_live_at(&mut self, captures: &std::collections::BTreeSet<VarId>, entry: NodeId) {
        for &var in captures {
            if self.var_linear(var) {
                self.facts.rebound_at.push((var, entry));
            }
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
        let caps = self.val_caps(v);
        let n = self.emit(span, "return", String::new());
        self.end_frames_above(frame, n);
        self.leave_in_flight(n, self.jumps.len(), 0);
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
                caps,
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
        // A captured variable can have a new value where the closure runs.
        out.extend(self.late_ret_refs(s));
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
            Some(names) if names.len() == 1 => effects::by_identity(self.prog, &names[0]),
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
        let ident = effects::identity(self.prog, eid);
        let cap = self.facts.add_cap();
        self.cap_effects.insert(cap, ident.clone());
        let hid = weft_facts::HandlerId(u32::try_from(self.facts.handlers.len()).unwrap_or(0));
        self.facts.handlers.push(HandlerInfo {
            effect: ident.clone(),
            is_std: def.is_std,
            sim_root: false,
            span,
        });
        self.handlers.push(HandlerFrame {
            effect: ident,
            cap,
            multi: def.has_multi(),
            frames: self.frames.len(),
            jumps: self.jumps.len(),
        });
        self.sum().own_caps.insert(cap);
        self.sums.push(Summary::default());
        self.jumps.push(Jump::Fence("handled body"));
        let start = self.handle_start();
        let moves_before = (self.facts.moved_at.len(), self.facts.moved_part.len());
        let ends_before = self.facts.scope_end.len();
        // The handled body runs in a frame of its own, as a closure does in the
        // interpreter. So the temporaries of its value go out of scope at its
        // end, and an abort path finishes them with the body.
        self.stmt_temps.push((self.frames.len() + 1, Vec::new()));
        let v = if def.has_multi() && !resumes_at_most_once(clauses) {
            self.handled_again(body, cap)
        } else {
            self.expr(body)
        };
        self.close_stmt(expr_tail(body));
        let body_frees = self.body_frees(moves_before, start.locals);
        // A clause parameter can point into a local of the body too.
        let mut arg_frees = body_frees.clone();
        arg_frees.extend(self.inner_frees(moves_before.0, ends_before));
        arg_frees.sort();
        arg_frees.dedup();
        self.jumps.pop();
        // A function value that performs through the handler cannot leave its body.
        let escaped = self.check_cap_escape(cap, &def.name, start, &v, span);
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
        let mut clause_locals: Vec<(Option<usize>, PlaceId)> = Vec::new();
        let mut aborts = false;
        let mut clause_nodes = Vec::new();
        let mut inner_caps = BTreeSet::new();
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
            self.push_frame(Some(si));
            // The locals and the kept values from here are of the clause.
            let clause_start = self.handle_start();
            let first_node = NodeId(u32::try_from(self.facts.nodes.len()).unwrap_or(u32::MAX));
            let entry = self.start(c.span, "handler clause");
            // The detail names the capability: a diagnostic finds the clause that
            // a node runs (`clause_read` in `weft-check`).
            self.facts.nodes[entry.index()].detail = format!("c{}", cap.0);
            let saved_stmts = std::mem::take(&mut self.stmt_temps);
            self.open_stmt();
            // A parameter that holds references points into what the operation gets.
            let mut param_roots = std::collections::BTreeMap::new();
            for (i, (p, pt)) in c.params.iter().zip(&op.params).enumerate() {
                let l = self.new_local(&p.name.name, VarKind::Param, p.span, pt.clone(), false);
                let refs = if self.holds_refs(pt) {
                    let r = self.root(&p.name.name, RootKind::Arg);
                    param_roots.insert(r, i);
                    let rid = self.facts.place(r).root;
                    self.param_of_root.insert(rid, (si, i));
                    vec![r]
                } else {
                    Vec::new()
                };
                // A function parameter: the operation gives the value, and the
                // perform runs it. The clause summary records what the clause does with it.
                let fn_param = matches!(self.inf.shallow(pt), Ty::Fn(_)).then_some((si, i));
                self.assign_local(
                    l,
                    &Val {
                        ty: pt.clone(),
                        refs,
                        fn_param,
                        ..Val::default()
                    },
                    entry,
                );
                // The parameter holds the function values that the nodes give to
                // the operation. The clause can keep them (W0313).
                let oi = def.ops.iter().position(|o| o.name == op.name);
                let given: std::collections::BTreeSet<weft_facts::CapId> = self
                    .op_fn_args
                    .iter()
                    .filter(|a| a.cap == cap && (a.op.is_none() || a.op == oi))
                    .filter(|a| a.pos.is_none_or(|p| p == i))
                    .flat_map(|a| a.held.iter().copied())
                    .collect();
                self.locals.get_mut(l).caps.extend(given.iter().copied());
                self.locals.get_mut(l).sticky.extend(given);
                // A function parameter is one of the function values that the
                // nodes give to the operation. A task or a fork branch of the
                // clause runs them (W0401, W0403, W0405).
                if fn_param.is_some() {
                    self.note_clause_fn(cap, oi, (si, i));
                }
                // A callee can give a value that holds a function value in a field or
                // an element: the clause cannot follow it.
                if !matches!(self.inf.shallow(pt), Ty::Fn(_)) && self.has_fn(pt) {
                    self.locals.get_mut(l).caps.insert(super::caps::UNKNOWN_FN);
                    self.locals
                        .get_mut(l)
                        .sticky
                        .insert(super::caps::UNKNOWN_FN);
                }
                self.mark_modes(l);
            }
            let kty = Ty::Cont(Box::new(op.ret.clone()), Box::new(ty.clone()));
            let k = self.new_local("resume", VarKind::Continuation, c.span, kty, false);
            self.facts.vars[self.locals[k].var.index()].once = !op.multi;
            self.locals.get_mut(k).cont = Some(ContInfo {
                arg: op.ret.clone(),
                ret: ty.clone(),
                multi: op.multi,
                muts: body_sum.muts.iter().copied().collect(),
                frees: body_frees.clone(),
                cap,
                depth: self.handlers.len(),
                fail: def.is_std && def.name == "Fail",
            });
            let kv = self.locals[k].var;
            self.bind(kv, entry);
            // The continuation is a capability of the clause: a closure that
            // resumes it holds the capability, and it cannot leave the clause.
            let kcap = self.facts.add_cap();
            self.cont_caps.insert(kcap);
            self.locals.get_mut(k).caps.insert(kcap);
            self.clause_conts.push((kcap, self.handlers.len()));
            let resumes_before = self.resumes.len();
            self.jumps.push(Jump::Fence("handler clause"));
            let cv = self.block(&c.body);
            self.jumps.pop();
            self.clause_conts.pop();
            self.check_cont_escape(
                kcap,
                &op.name,
                (clause_start, start.locals),
                &cv,
                (c.span, c.body.span),
            );
            let returns = !matches!(self.inf.shallow(&cv.ty), Ty::Never);
            if returns {
                self.unify(&ty, &cv.ty, c.body.span);
                // The value of the clause moves into the value of the `handle`.
                self.consume(&cv, block_tail(&c.body));
            }
            self.flush(block_tail(&c.body));
            self.end_frame(c.span);
            // A clause that can end with no `resume` ends the handled body at the
            // node that runs it.
            if let Some(end) = self.cur {
                let stops: Vec<NodeId> = self.resumes[resumes_before..]
                    .iter()
                    .filter(|(_, rc)| *rc == cap)
                    .map(|(n, _)| *n)
                    .collect();
                aborts |= self.reaches_without(entry, end, &stops);
            }
            self.pop_frame();
            self.stmt_temps = saved_stmts;
            self.close_scope(si, super::fnval::Scope::Clause);
            let _ = self.take_repeats(si);
            self.clause_fns.retain(|&(d, _), _| d != si);
            let mut cs = self.sums.pop().unwrap_or_default();
            let end_node = NodeId(u32::try_from(self.facts.nodes.len()).unwrap_or(u32::MAX));
            clause_nodes.push((first_node, end_node));
            inner_caps.extend(cs.own_caps.iter().copied());
            self.captures_live_at(&cs.captures.to_set(), entry);
            cs.param_roots = param_roots;
            // The places that the `resume`s give: the result of the operation
            // points into them. A local of the clause ends with the `handle`.
            let oi = def.ops.iter().position(|o| o.name == op.name);
            let own = cs.own_roots.to_set();
            let local = self.note_resumed_refs(cap, oi, &cs.param_roots, &own);
            clause_locals.extend(local.into_iter().map(|p| (oi, p)));
            // The value of the clause is the value of the `handle`. A reference into
            // a parameter points into what each node gives to the operation.
            if returns {
                let mut cv = cv;
                let oi = def.ops.iter().position(|o| o.name == op.name);
                let mut refs = self.clause_refs_onto_args(&cv.refs, &cs.param_roots, cap, oi);
                refs.extend(
                    cv.refs
                        .iter()
                        .copied()
                        .filter(|&p| !cs.own_roots.contains(&self.facts.place(p).root)),
                );
                cv.refs = refs;
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
        // A clause that runs its parameter as a task: the value that a node gives
        // to the operation must not perform through a handler of this task.
        self.check_clause_tasks(cap, &clauses_done);
        // The local handlers outside the `handle` that the clauses perform through.
        // A node that runs a clause runs their clauses too.
        let clause_caps: std::collections::BTreeSet<weft_facts::CapId> = clauses_done
            .iter()
            .flat_map(|(_, cs, _)| cs.performs.difference(&cs.own_caps))
            .copied()
            .filter(|c| self.handlers.iter().any(|h| h.cap == *c))
            .collect();
        let mut h = super::Handled {
            cap,
            clauses: clauses_done,
            footprint,
            lent,
            clause_sum,
            resumes,
            changes,
            frees: arg_frees,
            end: NodeId(0),
            aborts,
            locals: start.locals,
            clause_caps,
            clause_vars: Vec::new(),
            keeps: (!escaped).then(|| (def.name.clone(), span)),
            clause_nodes,
            inner_caps,
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
        self.run_clause_caps(&h, &calls);
        self.cur = saved;
        // A clause can give the value of the `handle` too. Then the value of the body
        // moves into it, as the value of a branch of an `if` does.
        if !clause_vals.is_empty() {
            self.consume(&v, expr_tail(body));
        }
        let end = self.emit(span, "end handle", String::new());
        // A reference that a clause resumes with into its own local is not valid
        // after the `handle`: the clause has ended. The result of an operation
        // of that clause, or of a call that reaches the handler, can be one.
        for (oi, p) in clause_locals {
            let results: Vec<PlaceId> = self
                .op_results
                .iter()
                .filter(|((c, o), _)| *c == cap && (o.is_none() || oi.is_none() || *o == oi))
                .map(|(_, &r)| r)
                .collect();
            let root = self.facts.place(p).root;
            if let Some(l) = self.root_owner(root) {
                let var = self.locals[l].var;
                self.facts.scope_end.push((var, end));
                h.clause_vars.push(var);
                if v_refs_result(&self.facts, &results, &v.refs) {
                    let name = self.locals[l].name.clone();
                    self.err(
                        "W0204",
                        format!("the `handle` returns a reference into `{name}`: the local of the clause goes out of scope when the clause ends"),
                        span,
                    );
                }
            }
        }
        // The abort paths and the check of the locals outside the body come after
        // the whole body (`finish_aborts`). A stored value can run a clause too.
        h.end = end;
        self.handled.push(h);
        // The value of the handled body: also a task handle or a function value. A
        // clause value that holds references or function values joins it. A value
        // with no linear part needs one from each clause too.
        let mut out = v;
        if !clause_vals.is_empty() {
            out.empty &= clause_vals.iter().all(|cv| cv.empty);
            out.var = None;
            out.local = None;
            out.place = None;
        }
        for cv in clause_vals {
            if cv.refs.is_empty() && !self.has_fn(&cv.ty) {
                continue;
            }
            let mut refs = out.refs.clone();
            refs.extend(cv.refs.iter().copied());
            let j = self.join_val(&out, &cv);
            out = Val { refs, ..j };
        }
        out
    }

    /// Returns the places that `refs` of a clause of operation `op` stand for: a
    /// place below the root of a reference parameter is that place below each
    /// place that a node gives to the operation of the handler behind `cap`.
    pub(super) fn clause_refs_onto_args(
        &mut self,
        refs: &[PlaceId],
        param_roots: &std::collections::BTreeMap<PlaceId, usize>,
        cap: weft_facts::CapId,
        op: Option<usize>,
    ) -> Vec<PlaceId> {
        let args: Vec<super::OpArg> = self
            .op_args
            .iter()
            .filter(|a| a.cap == cap && (a.op.is_none() || a.op == op))
            .copied()
            .collect();
        let mut out = Vec::new();
        for &p in refs {
            let r = self.root_place(p);
            let Some(&k) = param_roots.get(&r) else {
                continue;
            };
            for a in args.iter().filter(|a| a.pos.is_none_or(|i| i == k)) {
                let q = match a.pos {
                    Some(_) => self.rebase(p, r, a.place),
                    // The parameter can point anywhere inside the place.
                    None => self.facts.wildcard(a.place),
                };
                out.push(q);
            }
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
        // An operation that a callee performs can give a place in a local of
        // the callee, which ends before the `resume` returns.
        let callee = self.callee_ops.contains(&h.cap);
        for (oi, cs, own_resumes) in &h.clauses {
            self.resume_through_params(&all, *oi, cs, own_resumes, &h.changes, &h.frees);
            if callee {
                for &n in own_resumes {
                    for &x in cs.param_roots.keys() {
                        self.facts.releases_at.push((n, x));
                    }
                }
            }
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

    /// The clauses of handler `h` perform through the local handlers of
    /// `Handled::clause_caps`. So each node of `calls` that runs a clause of `h`
    /// runs their clauses too. It mutates their footprints. A clause of theirs
    /// that does not resume ends their handled body there.
    pub(super) fn run_clause_caps(&mut self, h: &super::Handled, calls: &[NodeId]) {
        for &n in calls {
            for &c in &h.clause_caps {
                self.facts.performs_at.push((n, c));
                self.cap_calls.push((n, c));
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
            // The clause puts what the operation gets behind a reference
            // parameter of the function or into an `rc` object.
            let at = self.facts.node(a.node).span;
            for &(to, p, _) in &cs.param_stores {
                let qs = through(self, p, a);
                self.note_stored_as(to, &qs, at, false);
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

    /// Lowers the handled body of a handler with a `multi` operation. A clause can
    /// resume the body more than once: the code after a node that runs a clause
    /// then runs again. The locals from outside the body keep the values of the
    /// run before; the locals of the body get a copy of their values at the node
    /// (the interpreter copies the frames of the continuation). So the body is
    /// lowered as a loop (`lower_loop`) until the values of the locals from
    /// outside it are stable. Its end gets a path back to the nodes after each
    /// node that runs a clause of the handler (`cap`), through a node that gives
    /// each local of the body its copy again (`again_node`).
    fn handled_again(&mut self, body: &Expr, cap: weft_facts::CapId) -> Val {
        let mut out = None;
        self.lower_loop(body.span, &mut |me: &mut Self| {
            let calls = me.cap_calls.len();
            let outer = me.locals.len();
            let v = me.expr(body);
            if let Some(end) = me.cur {
                let again: Vec<NodeId> = me.cap_calls[calls..]
                    .iter()
                    .filter(|&&(_, c)| c == cap)
                    .map(|&(n, _)| n)
                    .collect();
                // The run goes on after the node that runs the clause: the node
                // itself, with its arguments, does not run again.
                let next: BTreeSet<NodeId> = me
                    .facts
                    .cfg_edge
                    .iter()
                    .filter(|(a, _)| again.contains(a))
                    .map(|&(_, b)| b)
                    .collect();
                if !next.is_empty() {
                    let node = me.again_node(body.span, outer);
                    me.facts.cfg_edge.push((end, node));
                    for n in next {
                        me.facts.cfg_edge.push((node, n));
                    }
                }
            }
            // The body is not a loop of the source: no part holder retires at
            // its edges.
            me.last_loop = None;
            out = Some(v);
        });
        out.unwrap_or_default()
    }

    /// Adds the node where a handled body runs again after a `multi` resume. Each
    /// local of the body (index `outer` or more) gets a copy of its value at the
    /// operation there, so a move or a free of its own value later in the run
    /// before does not count. A local that can point into a place of another value
    /// keeps its state: the copy points there too. (W0503 rejects a linear value or
    /// another value that is not `many` across the operation.)
    fn again_node(&mut self, span: Span, outer: usize) -> NodeId {
        let node = self
            .facts
            .add_node(span, "resume again", "the handled body runs again");
        let inner = |me: &Self, p: PlaceId| {
            me.root_owner(me.facts.place(p).root)
                .is_some_and(|l| l >= outer)
        };
        for l in outer..self.locals.len() {
            let var = self.locals[l].var;
            let own = self
                .facts
                .points_into
                .iter()
                .filter(|&&(v, _)| v == var)
                .all(|&(_, p)| inner(self, p));
            // The copy has the state of the local at the node of the operation,
            // which the path from there gives: the state at the end does not
            // count. So no linear value starts here (`empty_at`).
            if own {
                self.facts.rebound_at.push((var, node));
                self.facts.empty_at.push((var, node));
            }
        }
        node
    }

    /// Returns the places that the moves since `before` (the lengths of `moved_at`
    /// and `moved_part`) free, for the locals below index `locals`: the root of a
    /// local that moves, and a part that moves. A handled body that moves a local
    /// from outside the `handle` frees it before the `resume` returns.
    fn body_frees(&self, before: (usize, usize), locals: usize) -> Vec<PlaceId> {
        let mut out: Vec<PlaceId> = self.facts.moved_at[before.0..]
            .iter()
            .filter_map(|&(v, _)| self.local_of(v))
            .filter(|&l| l < locals)
            .filter_map(|l| self.locals[l].root)
            .collect();
        out.extend(
            self.facts.moved_part[before.1..]
                .iter()
                .map(|&(m, _)| m)
                .filter(|&m| {
                    self.root_owner(self.facts.place(m).root)
                        .is_some_and(|l| l < locals)
                }),
        );
        out.sort();
        out.dedup();
        out
    }

    /// Returns the roots that the handled body frees since the lengths `moves`
    /// of `moved_at` and `ends` of `scope_end`: the owners that move, and the
    /// owners that go out of scope, such as a local or a temporary of the body.
    /// An operation can give a clause parameter a place inside them. The body
    /// frees them before the `resume` of the clause returns.
    fn inner_frees(&self, moves: usize, ends: usize) -> Vec<PlaceId> {
        let moved = self.facts.moved_at.get(moves..).unwrap_or_default();
        let ended = self.facts.scope_end.get(ends..).unwrap_or_default();
        let vars: BTreeSet<VarId> = moved.iter().chain(ended).map(|&(v, _)| v).collect();
        self.facts
            .owner
            .iter()
            .filter(|(_, v)| vars.contains(v))
            .map(|&(r, _)| r)
            .collect()
    }

    /// At each resume of clause `cs` of operation `op`, a change of a place that
    /// the operation gets is a change of the parameter of the clause. A change
    /// above the argument place can also free what the parameter points to
    /// (`releases_at`).
    fn resume_through_params(
        &mut self,
        args: &[super::OpArg],
        op: Option<usize>,
        cs: &Summary,
        resumes: &[NodeId],
        changes: &[PlaceId],
        frees: &[PlaceId],
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
        let mut freed = Vec::new();
        for (&x, &k) in &cs.param_roots {
            for a in args.iter().filter(|a| a.pos.is_none_or(|i| i == k)) {
                for &m in changes {
                    if let Some((q, frees)) = self.onto_param(m, a.place, x, a.pos.is_some()) {
                        out.push(q);
                        if frees {
                            freed.push(x);
                        }
                    }
                }
                // A move of the argument place, or of a place above it, frees it.
                if frees.iter().any(|&m| self.free_kills(m, a.place)) {
                    freed.push(x);
                }
            }
        }
        out.sort();
        out.dedup();
        freed.sort();
        freed.dedup();
        for &n in resumes {
            for &q in &out {
                self.facts.mutates_at.push((n, q));
            }
            for &x in &freed {
                self.facts.releases_at.push((n, x));
            }
        }
    }

    /// A node that runs a closure that calls `resume` runs the handled
    /// computation there: a call of the closure, or a call that gets it. So it
    /// changes, lends and frees what each `resume` in the closure does
    /// (`mutates_at`, `lends_mut`, `releases_at`). A closure that calls such a
    /// closure passes the facts on to each node where it runs.
    pub(super) fn finish_resume_runs(&mut self) {
        if self.resumes.is_empty() {
            return;
        }
        // The resumes that each node runs, the resume nodes themselves first.
        let mut runs: BTreeMap<NodeId, BTreeSet<NodeId>> = self
            .resumes
            .iter()
            .map(|&(n, _)| (n, BTreeSet::from([n])))
            .collect();
        let ranges: Vec<(NodeId, Vec<(u32, u32)>)> = self
            .applied
            .iter()
            .map(|a| {
                let mut rs: Vec<(u32, u32)> = self.closures[a.summary]
                    .members
                    .iter()
                    .filter_map(|&m| self.closures.get(m).map(|c| c.nodes))
                    .collect();
                rs.push(self.closures[a.summary].nodes);
                (a.node, rs)
            })
            .collect();
        loop {
            let mut grew = false;
            for (n, rs) in &ranges {
                let inner: BTreeSet<NodeId> = runs
                    .iter()
                    .filter(|(m, _)| rs.iter().any(|&(a, b)| (a..b).contains(&m.0)))
                    .flat_map(|(_, r)| r.iter().copied())
                    .collect();
                let set = runs.entry(*n).or_default();
                let before = set.len();
                set.extend(inner);
                grew |= set.len() > before;
            }
            if !grew {
                break;
            }
        }
        let mut muts = Vec::new();
        let mut lends = Vec::new();
        let mut frees = Vec::new();
        for (&n, rs) in &runs {
            if rs.contains(&n) {
                continue;
            }
            for &(m, q) in &self.facts.mutates_at {
                if rs.contains(&m) {
                    muts.push((n, q));
                }
            }
            for &(m, q) in &self.facts.lends_mut {
                if rs.contains(&m) {
                    lends.push((n, q));
                }
            }
            for &(m, q) in &self.facts.releases_at {
                if rs.contains(&m) {
                    frees.push((n, q));
                }
            }
        }
        self.facts.mutates_at.extend(muts);
        self.facts.lends_mut.extend(lends);
        self.facts.releases_at.extend(frees);
    }

    /// Returns what a change of `m` does to parameter root `x`, where `x` stands
    /// for argument place `p`. With `exact` false, `x` can be anywhere inside
    /// `p`. The result has the place below `x` that the change mutates, and true
    /// if the change can also free what `x` stands for: the change is above it.
    /// The wildcard place `x..` stands for places at or below `x` only, so a
    /// change above `x` needs the free (ADR 0005).
    fn onto_param(
        &mut self,
        m: PlaceId,
        p: PlaceId,
        x: PlaceId,
        exact: bool,
    ) -> Option<(PlaceId, bool)> {
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
                    (self.rebase(m, p, x), false)
                } else {
                    // `x` can be below the change.
                    (self.facts.wildcard(x), true)
                });
            }
            at = self.facts.place(q).parent;
        }
        // A change above the argument place, or one that can alias it, can change
        // any place below `x`. It frees `x` if it invalidates a reference to `p`.
        let frees = !exact || self.change_kills(m, p);
        Some((self.facts.wildcard(x), frees))
    }

    /// Returns true if a free of `m` invalidates a reference into `p`, by the free
    /// rules of the spec (`free_kills` in `weft-check`).
    fn free_kills(&self, m: PlaceId, p: PlaceId) -> bool {
        use weft_verified::places;
        let (pm, pp) = (self.facts.place(m), self.facts.place(p));
        if pm.root != pp.root {
            return false;
        }
        if places::may_prefix(&pm.steps, &pp.steps) {
            return true;
        }
        let one = self.facts.one_place_of(m);
        if one.is_some() && one == self.facts.one_place_of(p) {
            return false;
        }
        let (wm, wp) = (self.facts.wild_base(m), self.facts.wild_base(p));
        let steps = |q: PlaceId| &self.facts.place(q).steps;
        wp.is_some() && places::overlaps(steps(wm.unwrap_or(m)), steps(wp.unwrap_or(p)))
    }

    /// Returns true if a mutation of `m` invalidates a reference into `p`, by
    /// rule 3 or a wildcard rule of the spec (`mutation_kills` in `weft-check`).
    fn change_kills(&self, m: PlaceId, p: PlaceId) -> bool {
        use weft_verified::places;
        let (pm, pp) = (self.facts.place(m), self.facts.place(p));
        if pm.root != pp.root {
            return false;
        }
        if places::invalidates(&pm.steps, &pp.steps) {
            return true;
        }
        let one = self.facts.one_place_of(m);
        if one.is_some() && one == self.facts.one_place_of(p) {
            return false;
        }
        let (wm, wp) = (self.facts.wild_base(m), self.facts.wild_base(p));
        let steps = |q: PlaceId| &self.facts.place(q).steps;
        let overlaps = places::overlaps(steps(wm.unwrap_or(m)), steps(wp.unwrap_or(p)));
        (wp.is_some() && overlaps)
            || wm.is_some_and(|b| {
                steps(b).len() < pp.steps.len() && places::may_prefix(steps(b), &pp.steps)
            })
    }

    fn merge_summary(&mut self, s: &Summary) {
        let own = s.own_roots.clone();
        let spawns = self.spawns_outside(&s.spawns.to_set());
        // A capture of the clause is a capture of the body around it only if the
        // body does not declare it: a local of a closure is not a capture of it.
        let barrier = self.frames.iter().rposition(|f| f.barrier.is_some());
        let outer = |me: &Self, v: VarId| match (barrier, me.local_of(v)) {
            (Some(bi), Some(l)) => me.local_frame(l) < bi,
            _ => true,
        };
        let captures: Vec<VarId> = s
            .captures
            .iter()
            .copied()
            .filter(|&v| outer(self, v))
            .collect();
        let moved: Vec<VarId> = s
            .moved_captures
            .iter()
            .copied()
            .filter(|&v| outer(self, v))
            .collect();
        let t = self.sum();
        t.spawns.extend(spawns);
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
        t.captures.extend(captures);
        t.moved_captures.extend(moved);
        t.dropped.extend(s.dropped.iter().copied());
        t.lends.extend(s.lends.iter().copied());
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
        self.push_frame(None);
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
        // A scope with a failed child raises the failure at its end.
        self.raise_here();
        self.scopes.push((l, Vec::new()));
        // The tasks join before the locals of the body go out of scope.
        self.push_frame(None);
        self.jumps.push(Jump::Fence("scope body"));
        let v = self.block_inner(body);
        self.jumps.pop();
        let v = self.hand_out(v, body.span);
        let tail = block_tail(body);
        self.flush(tail);
        let (_, tasks) = self.scopes.pop().unwrap_or_default();
        let end = self.emit(span, "scope end", String::new());
        for &t in &tasks {
            self.facts.joined_at.push((t, end));
        }
        self.end_tasks(&tasks, span);
        let held = self.hold_out(&v, tail);
        self.end_frame(body.span);
        self.pop_frame();
        let v = if self.use_held(held, tail) {
            Val { var: None, ..v }
        } else {
            v
        };
        self.end_frame(span);
        self.pop_frame();
        v
    }
}

/// Returns true if `e` is an integer literal, or a negation of one: a chain of
/// negations of a literal has one value.
fn neg_literal(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Lit(Lit::Int(_)) => true,
        ExprKind::Unary {
            op: UnOp::Neg,
            expr,
        } => neg_literal(expr),
        _ => false,
    }
}

/// Returns true if one of the places `refs` is below one of the root places `results`.
fn v_refs_result(facts: &weft_facts::FnFacts, results: &[PlaceId], refs: &[PlaceId]) -> bool {
    refs.iter().any(|&p| {
        results
            .iter()
            .any(|&r| facts.place(r).root == facts.place(p).root)
    })
}

impl Lower<'_> {
    /// Returns true if a path of edges leads from node `from` to node `to` that does
    /// not pass through a node of `stops`.
    fn reaches_without(&self, from: NodeId, to: NodeId, stops: &[NodeId]) -> bool {
        // The nodes of the clause come after its entry.
        let mut succ: std::collections::BTreeMap<NodeId, Vec<NodeId>> =
            std::collections::BTreeMap::new();
        for &(x, y) in &self.facts.cfg_edge {
            if x.index() >= from.index() {
                succ.entry(x).or_default().push(y);
            }
        }
        let mut seen = std::collections::BTreeSet::new();
        let mut work = vec![from];
        while let Some(a) = work.pop() {
            if a == to {
                return true;
            }
            if stops.contains(&a) || !seen.insert(a) {
                continue;
            }
            work.extend(succ.get(&a).into_iter().flatten().copied());
        }
        false
    }
}

/// Returns true if each clause of `clauses` resumes at most once each time it
/// runs: it names `resume` at most once, and not in a loop, a closure or a
/// clause of another handler. Then the handled body runs at most once after
/// each operation, also for an effect with a `multi` operation.
fn resumes_at_most_once(clauses: &[ast::HandlerClause]) -> bool {
    clauses.iter().all(|c| {
        let mut seen = Resumes::default();
        for st in &c.body.stmts {
            seen.stmt(st, false);
        }
        seen.count <= 1 && !seen.again
    })
}

/// The names `resume` in a clause body (`resumes_at_most_once`).
#[derive(Default)]
struct Resumes {
    /// The number of names.
    count: usize,
    /// A name is in code that can run more than once in one run of the clause.
    again: bool,
}

impl Resumes {
    fn stmt(&mut self, st: &ast::Stmt, again: bool) {
        match &st.kind {
            ast::StmtKind::Let { init, .. } => {
                if let Some(e) = init {
                    self.expr(e, again);
                }
            }
            ast::StmtKind::Expr(e) | ast::StmtKind::Assert(e) => self.expr(e, again),
            ast::StmtKind::Assign { target, value, .. } => {
                self.expr(target, again);
                self.expr(value, again);
            }
            ast::StmtKind::Return(e) => {
                if let Some(e) = e {
                    self.expr(e, again);
                }
            }
            ast::StmtKind::Break | ast::StmtKind::Continue => {}
            ast::StmtKind::While { cond, body } => {
                self.expr(cond, true);
                self.block(body, true);
            }
            ast::StmtKind::For { iter, body, .. } => {
                self.expr(iter, again);
                self.block(body, true);
            }
            ast::StmtKind::Loop(body) => self.block(body, true),
        }
    }

    fn block(&mut self, b: &ast::Block, again: bool) {
        for st in &b.stmts {
            self.stmt(st, again);
        }
    }

    fn expr(&mut self, e: &Expr, again: bool) {
        match &e.kind {
            ExprKind::Lit(_) => {}
            ExprKind::Name(id) => {
                if id.name == "resume" {
                    self.count += 1;
                    self.again |= again;
                }
            }
            ExprKind::Field { base, .. } => self.expr(base, again),
            ExprKind::Index { base, index } => {
                self.expr(base, again);
                if let Some(i) = index {
                    self.expr(i, again);
                }
            }
            ExprKind::Call {
                callee,
                args,
                trailing,
            } => {
                self.expr(callee, again);
                for a in args {
                    self.expr(&a.value, again);
                }
                if let Some(t) = trailing {
                    self.expr(t, true);
                }
            }
            ExprKind::MethodCall {
                receiver,
                args,
                trailing,
                ..
            } => {
                self.expr(receiver, again);
                for a in args {
                    self.expr(&a.value, again);
                }
                if let Some(t) = trailing {
                    self.expr(t, true);
                }
            }
            ExprKind::Unary { expr, .. } => self.expr(expr, again),
            ExprKind::Binary { lhs, rhs, .. } => {
                self.expr(lhs, again);
                self.expr(rhs, again);
            }
            ExprKind::Range { lo, hi } => {
                self.expr(lo, again);
                self.expr(hi, again);
            }
            ExprKind::Tuple(es) | ExprKind::Array(es) => {
                for x in es {
                    self.expr(x, again);
                }
            }
            ExprKind::StructLit { fields, .. } => {
                for (_, x) in fields {
                    self.expr(x, again);
                }
            }
            ExprKind::Closure { body, .. } => self.expr(body, true),
            ExprKind::Block(b) => self.block(b, again),
            ExprKind::If { cond, then, else_ } => {
                self.expr(cond, again);
                self.block(then, again);
                if let Some(x) = else_ {
                    self.expr(x, again);
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                self.expr(scrutinee, again);
                for a in arms {
                    self.expr(&a.body, again);
                }
            }
            ExprKind::Handle { clauses, body, .. } => {
                for c in clauses {
                    self.block(&c.body, true);
                }
                self.expr(body, again);
            }
            ExprKind::Scope { body, .. } => self.block(body, again),
        }
    }
}
