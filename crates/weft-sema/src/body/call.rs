//! Calls: functions, methods, constructors, effect operations and built-ins.

use super::{
    ast, effects, AdtKind, Arg, ContInfo, Expr, ExprKind, FnId, FnTy, ItemRef, Lower, NodeId,
    PathRef, PlaceId, RootKind, SigRoot, Span, TaskKind, Ty, Val, PRELUDE,
};

/// One evaluated argument.
struct ArgVal {
    val: Val,
    span: Span,
}

impl Lower<'_> {
    pub(super) fn call(
        &mut self,
        callee: &Expr,
        args: &[Arg],
        trailing: Option<&Expr>,
        span: Span,
    ) -> Val {
        if let ExprKind::Name(id) = &callee.kind {
            if let Some(l) = self.lookup_local(&id.name) {
                if self.locals[l].cont.is_some() {
                    return self.resume(l, args, span);
                }
                return self.call_value(l, args, trailing, span);
            }
            match id.name.as_str() {
                "print" => return self.print(args, span),
                "fork" => return self.fork(args, trailing, span),
                _ => {}
            }
            match self.prog.lookup(self.module, &id.name) {
                Some(ItemRef::Fn(f)) => return self.call_fn(f, None, args, trailing, span),
                Some(ItemRef::Adt(a)) => return self.positional_struct(a, args, span),
                _ => {}
            }
            if let Some(&(adt, vi)) = self.prog.variants.get(&id.name).and_then(|v| v.first()) {
                return self.variant_ctor(adt, vi, args, span);
            }
            if let Some((e, op)) = self.find_op(&id.name) {
                return self.perform_op(e, op, args, span);
            }
            self.err("W0101", format!("unknown function `{}`", id.name), id.span);
            for a in args {
                let _ = self.expr(&a.value);
            }
            return Val {
                ty: Ty::Error,
                ..Val::default()
            };
        }
        let v = self.expr(callee);
        self.err("W0105", "this expression cannot be called", callee.span);
        let _ = v;
        Val {
            ty: Ty::Error,
            ..Val::default()
        }
    }

    /// Finds an effect operation by name: user effects first, then the prelude.
    fn find_op(&self, name: &str) -> Option<(usize, usize)> {
        let mut found = None;
        for (ei, e) in self.prog.effects.iter().enumerate() {
            if let Some(oi) = e.ops.iter().position(|o| o.name == name) {
                // Only effects that are visible from this module.
                if self.prog.effect_named(self.module, &e.name) == Some(ei) {
                    if !e.is_std {
                        return Some((ei, oi));
                    }
                    found = found.or(Some((ei, oi)));
                }
            }
        }
        found
    }

    pub(super) fn method_call(
        &mut self,
        recv: &Expr,
        method: &ast::Ident,
        args: &[Arg],
        trailing: Option<&Expr>,
        span: Span,
    ) -> Val {
        match self.path_ref(recv) {
            Some(PathRef::Mod(m)) => {
                return match self.prog.lookup_in(m, &method.name) {
                    Some(ItemRef::Fn(f)) => {
                        if self.prog.fns[f].path == "run" && self.prog.mods[m].name == "sim" {
                            return self.sim_run(f, args, trailing, span);
                        }
                        self.call_fn(f, None, args, trailing, span)
                    }
                    Some(ItemRef::Adt(a)) => self.positional_struct(a, args, span),
                    _ => {
                        self.err(
                            "W0101",
                            format!("no function `{}` in this module", method.name),
                            method.span,
                        );
                        Val {
                            ty: Ty::Error,
                            ..Val::default()
                        }
                    }
                };
            }
            Some(PathRef::Adt(a)) => {
                if let Some(&f) = self.prog.methods.get(&(a, method.name.clone())) {
                    return self.call_fn(f, None, args, trailing, span);
                }
                if let AdtKind::Enum(vs) = &self.prog.adts[a].kind {
                    if let Some(vi) = vs.iter().position(|v| v.name == method.name) {
                        return self.variant_ctor(a, vi, args, span);
                    }
                }
                let n = self.prog.adts[a].name.clone();
                self.err(
                    "W0104",
                    format!("`{n}` has no function `{}`", method.name),
                    method.span,
                );
                return Val {
                    ty: Ty::Error,
                    ..Val::default()
                };
            }
            Some(PathRef::Effect(e)) => {
                return if let Some(op) = self.prog.effects[e]
                    .ops
                    .iter()
                    .position(|o| o.name == method.name)
                {
                    self.perform_op(e, op, args, span)
                } else {
                    let n = self.prog.effects[e].name.clone();
                    self.err(
                        "W0104",
                        format!("effect `{n}` has no operation `{}`", method.name),
                        method.span,
                    );
                    Val {
                        ty: Ty::Error,
                        ..Val::default()
                    }
                };
            }
            None => {}
        }
        // A method on a value.
        let rv = match self.place_expr(recv) {
            Some(lv) => {
                let refs = Vec::new();
                let local = lv.owner;
                let var = local.map(|l| self.locals[l].var);
                let (task, summary) = local.map_or((None, None), |l| {
                    (self.locals[l].task, self.locals[l].summary)
                });
                Val {
                    ty: lv.ty.clone(),
                    refs,
                    var,
                    local,
                    place: Some(lv),
                    task,
                    summary,
                    ..Val::default()
                }
            }
            None => self.expr(recv),
        };
        let rty = self.deref_ty(&rv.ty);
        let rty = self.inf.resolve(&rty);
        match (&rty, method.name.as_str()) {
            (Ty::Scope, "spawn") => return self.spawn(args, trailing, span),
            (Ty::Adt(a, _), "join" | "detach") if Some(*a) == self.b.task => {
                return self.join(&rv, method.name == "join", span);
            }
            _ => {}
        }
        let owner = match &rty {
            Ty::Adt(a, _) => Some(*a),
            _ => None,
        };
        let Some(f) = owner.and_then(|a| self.prog.methods.get(&(a, method.name.clone())).copied())
        else {
            if !matches!(rty, Ty::Error) {
                let shown = self.show(&rty);
                self.err(
                    "W0104",
                    format!("`{shown}` has no method `{}`", method.name),
                    method.span,
                );
            }
            for a in args {
                let _ = self.expr(&a.value);
            }
            return Val {
                ty: Ty::Error,
                ..Val::default()
            };
        };
        self.call_fn(f, Some(rv), args, trailing, span)
    }

    /// Calls a function item. `recv` is the evaluated receiver of a method call.
    pub(super) fn call_fn(
        &mut self,
        f: FnId,
        recv: Option<Val>,
        args: &[Arg],
        trailing: Option<&Expr>,
        span: Span,
    ) -> Val {
        let sig = self.sigs[f].clone();
        let name = self.prog.fns[f].name.clone();
        // Only a function with `self` as its first parameter takes a receiver.
        if recv.is_some() && sig.params.first().is_none_or(|p| p.name != "self") {
            let owner = self.prog.fns[f]
                .owner
                .map_or_else(String::new, |a| format!("{}.", self.prog.adts[a].name));
            self.err(
                "W0104",
                format!("`{name}` has no `self` parameter: call it as `{owner}{name}(...)`"),
                span,
            );
            for a in args.iter().map(|a| &a.value).chain(trailing) {
                let _ = self.expr(a);
            }
            return Val {
                ty: Ty::Error,
                ..Val::default()
            };
        }
        let targs: Vec<Ty> = sig.generics.iter().map(|_| self.inf.fresh()).collect();
        let ptys: Vec<Ty> = sig
            .params
            .iter()
            .map(|p| super::subst(&p.ty, &targs))
            .collect();
        // Order the explicit arguments: named arguments go to their parameter.
        let first = usize::from(recv.is_some());
        let mut slots: Vec<Option<&Expr>> = vec![None; sig.params.len()];
        let mut pos = first;
        let mut extra = 0usize;
        for a in args {
            let idx = if let Some(n) = &a.name {
                sig.params.iter().position(|p| p.name == n.name)
            } else {
                while pos < slots.len() && slots[pos].is_some() {
                    pos += 1;
                }
                Some(pos)
            };
            match idx {
                Some(i) if i < slots.len() => slots[i] = Some(&a.value),
                _ => extra += 1,
            }
        }
        if let Some(t) = trailing {
            match slots.iter().rposition(Option::is_none) {
                Some(i) if i >= first => slots[i] = Some(t),
                _ => extra += 1,
            }
        }
        let missing = slots.iter().skip(first).filter(|s| s.is_none()).count();
        if extra > 0 || missing > 0 {
            self.err(
                "W0103",
                format!(
                    "`{name}` takes {} arguments, found {}",
                    sig.params.len() - first,
                    args.len() + usize::from(trailing.is_some())
                ),
                span,
            );
        }
        // Evaluate the arguments in order. Each argument is typed, held and moved
        // before the next one runs, so that a later argument cannot hide a
        // mutation from an earlier reference.
        let mut recv = recv;
        let mut vals: Vec<ArgVal> = Vec::new();
        let mut arg_places: Vec<Vec<PlaceId>> = Vec::new();
        let mut held_vars = Vec::new();
        for i in 0..slots.len() {
            let later = slots[i + 1..].iter().any(Option::is_some);
            let mut av = if let (0, Some(r)) = (i, recv.take()) {
                ArgVal { val: r, span }
            } else if let Some(e) = slots[i] {
                let expected = match self.inf.shallow(&ptys[i]) {
                    Ty::Fn(f) => Some((*f).clone()),
                    _ => None,
                };
                let v = match (&e.kind, expected) {
                    (ExprKind::Closure { params, body }, Some(fty)) => {
                        self.closure(params, body, Some(&fty), e.span)
                    }
                    _ => self.expr(e),
                };
                ArgVal {
                    val: v,
                    span: e.span,
                }
            } else {
                ArgVal {
                    val: Val {
                        ty: Ty::Error,
                        ..Val::default()
                    },
                    span,
                }
            };
            let pt = ptys[i].clone();
            let is_ref_param = matches!(self.inf.shallow(&pt), Ty::Ref(_));
            let arg_is_ref = matches!(self.inf.shallow(&av.val.ty), Ty::Ref(_));
            if is_ref_param && !arg_is_ref && i == 0 && first == 1 {
                // `x.m()` borrows `x` when `m` takes `self` by reference.
                let places = av.val.place.as_ref().map_or_else(
                    || vec![self.root("temporary", RootKind::Local)],
                    |lv| lv.places.clone(),
                );
                if let Ty::Ref(inner) = self.inf.shallow(&pt) {
                    self.unify(&inner, &av.val.ty, av.span);
                }
                if later {
                    let borrow = Val {
                        ty: pt.clone(),
                        refs: places.clone(),
                        ..Val::default()
                    };
                    held_vars.extend(self.hold(&borrow, "receiver", av.span));
                }
                arg_places.push(places.clone());
                av.val.refs = places;
                vals.push(av);
                continue;
            }
            if i == 0 && first == 1 && arg_is_ref && !is_ref_param {
                // A method that takes `self` by value through a reference.
                let inner = self.deref_ty(&av.val.ty);
                self.unify(&pt, &inner, av.span);
                arg_places.push(Vec::new());
                vals.push(av);
                continue;
            }
            self.unify_arg(&pt, &mut av.val, av.span);
            if is_ref_param || arg_is_ref {
                // A reference argument stays valid until the call: hold it in a variable.
                arg_places.push(av.val.refs.clone());
                match av.val.var {
                    Some(v) => held_vars.push(v),
                    None => held_vars.extend(self.hold(&av.val, "argument", av.span)),
                }
            } else {
                arg_places.push(Vec::new());
                if !matches!(self.inf.shallow(&pt), Ty::Fn(_)) || av.val.summary.is_none() {
                    let v = av.val.clone();
                    self.consume(&v, av.span);
                }
            }
            vals.push(av);
        }
        // The callee root of each parameter: a parameter with `in` shares the root of its place.
        let root_of = |mut i: usize| -> u32 {
            for _ in 0..sig.params.len() {
                match sig
                    .params
                    .get(i)
                    .and_then(|p| p.place.as_ref())
                    .map(|pl| &pl.root)
                {
                    Some(SigRoot::Param(j)) if *j != i => i = *j,
                    _ => break,
                }
            }
            u32::try_from(i).unwrap_or(0)
        };
        // The call node.
        let split = self.fresh_split();
        let mut muts: Vec<(PlaceId, u32)> = Vec::new();
        for m in &sig.effects.muts {
            let idx = match &m.root {
                SigRoot::Param(i) => root_of(*i),
                SigRoot::Group(a) => 900 + u32::try_from(*a).unwrap_or(0),
            };
            if let SigRoot::Param(i) = m.root {
                let by_ref = matches!(self.inf.shallow(&ptys[i]), Ty::Ref(_));
                let receiver = i == 0 && first == 1;
                if !by_ref && !receiver {
                    continue;
                }
            }
            for p in self.subst_place(m, &arg_places, split) {
                muts.push((p, idx));
            }
        }
        let detail = {
            let mut parts = Vec::new();
            if !muts.is_empty() {
                let ps: Vec<&str> = muts
                    .iter()
                    .map(|(p, _)| self.facts.place(*p).display.as_str())
                    .collect();
                parts.push(format!("mut({})", ps.join(", ")));
            }
            parts.extend(sig.effects.named.iter().map(|n| n.to_lowercase()));
            parts.join(", ")
        };
        let n = self.emit(span, &name, detail);
        for v in held_vars {
            self.facts.uses.push((v, n));
        }
        for (p, idx) in &muts {
            self.mutate(n, *p);
            self.facts.call_mut.push((n, *p, *idx));
        }
        for (i, ps) in arg_places.iter().enumerate() {
            for &p in ps {
                self.facts.reads_at.push((n, p));
                self.sum().reads.insert(p);
                self.facts.call_arg.push((n, p, root_of(i)));
            }
        }
        // Arguments must point where the parameters say.
        for (i, p) in sig.params.iter().enumerate() {
            if let Some(pl) = &p.place {
                let allowed = self.subst_place(pl, &arg_places, split);
                for &r in &arg_places[i] {
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
                            "W0203",
                            format!(
                                "argument `{}` points into `{rt}`, but `{name}` needs `{at}`",
                                p.name
                            ),
                            vals[i].span,
                        );
                    }
                }
            }
            if p.uniq && !vals[i].val.uniq && p.ty.is_ref() {
                self.err(
                    "W0406",
                    format!("`{name}` needs a `@ uniq` reference for `{}`", p.name),
                    vals[i].span,
                );
            }
        }
        // Effects.
        let mut abort = false;
        for e in &sig.effects.named {
            self.perform_effect(n, e);
            if self.effect_has_multi(e) {
                self.multi_node(n);
            }
            if self.handlers.iter().any(|h| &h.effect == e) {
                let cap = self
                    .handlers
                    .iter()
                    .rev()
                    .find(|h| &h.effect == e)
                    .map(|h| h.cap);
                if let Some(c) = cap {
                    self.cap_calls.push((n, c));
                }
            }
            abort = true;
        }
        for (i, av) in vals.iter().enumerate() {
            if let Some(s) = av.val.summary {
                self.apply_summary(n, s, 800 + u32::try_from(i).unwrap_or(0));
                self.check_fn_arg_effects(&ptys[i], s, av.span);
            } else if let Some(fp) = av.val.fn_param {
                self.sum().passthrough.insert(fp);
                abort = true;
            } else if let Some(item) = av.val.item {
                for e in self.sigs[item].effects.named.clone() {
                    self.perform_effect(n, &e);
                    abort = true;
                }
            }
        }
        for &j in &sig.effects.passthrough {
            if let Some(fp) = vals.get(j).and_then(|v| v.val.fn_param) {
                self.sum().passthrough.insert(fp);
            }
        }
        if abort {
            self.abortive(n);
        }
        // The result.
        let ret = super::subst(&sig.ret, &targs);
        let mut out = Val {
            ty: ret.clone(),
            ..Val::default()
        };
        if !sig.ret_places.is_empty() {
            let mut parts: Option<Vec<Val>> = match self.inf.deep(&ret) {
                Ty::Tuple(ts) => Some(
                    ts.into_iter()
                        .map(|t| Val {
                            ty: t,
                            ..Val::default()
                        })
                        .collect(),
                ),
                _ => None,
            };
            for rp in &sig.ret_places {
                let places = self.subst_place(&rp.place, &arg_places, split);
                match (rp.path.first(), parts.as_mut()) {
                    (Some(&i), Some(ps)) if i < ps.len() => {
                        ps[i].refs.extend(places.iter().copied());
                        ps[i].uniq = rp.uniq;
                    }
                    _ => {
                        out.refs.extend(places.iter().copied());
                        out.uniq = rp.uniq;
                    }
                }
                out.refs.extend(places);
            }
            out.parts = parts;
        }
        out
    }

    /// Unifies an argument with a parameter type. A reference to a copy value
    /// passes as the value: the call reads through the reference.
    fn unify_arg(&mut self, pt: &Ty, v: &mut Val, span: Span) {
        let p = self.inf.shallow(pt);
        if let (false, Ty::Ref(inner)) = (
            matches!(p, Ty::Ref(_) | Ty::Var(_)),
            self.inf.shallow(&v.ty),
        ) {
            if self.is_copy(&inner) {
                for &r in &v.refs.clone() {
                    self.read(r);
                }
                self.unify(pt, &inner, span);
                v.ty = (*inner).clone();
                v.refs = Vec::new();
                return;
            }
        }
        self.unify(pt, &v.ty, span);
    }

    /// A closure passed to a parameter with a declared effect row must stay inside it.
    fn check_fn_arg_effects(&mut self, pt: &Ty, s: usize, span: Span) {
        if let Ty::Fn(f) = self.inf.shallow(pt) {
            if let Some(allowed) = &f.effects {
                let allowed: std::collections::BTreeSet<String> =
                    effects::close(&allowed.iter().cloned().collect())
                        .into_iter()
                        .collect();
                let extra: Vec<String> = self.closures[s]
                    .escapes
                    .iter()
                    .filter(|e| !allowed.contains(*e))
                    .cloned()
                    .collect();
                if !extra.is_empty() {
                    self.err("W0705", format!("this function argument performs `{}`, which its parameter type does not allow", extra.join(", ")), span);
                }
            }
        }
    }

    /// Calls a closure value or a function parameter.
    fn call_value(&mut self, l: usize, args: &[Arg], trailing: Option<&Expr>, span: Span) -> Val {
        let loc = self.locals[l].clone();
        let Ty::Fn(fty) = self.inf.shallow(&loc.ty) else {
            let shown = self.show(&loc.ty);
            self.err(
                "W0105",
                format!("`{}` has type `{shown}` and cannot be called", loc.name),
                span,
            );
            return Val {
                ty: Ty::Error,
                ..Val::default()
            };
        };
        let exprs: Vec<&Expr> = args.iter().map(|a| &a.value).chain(trailing).collect();
        if exprs.len() != fty.params.len() {
            self.err(
                "W0103",
                format!("`{}` takes {} arguments", loc.name, fty.params.len()),
                span,
            );
        }
        // Each argument is typed, held and moved before the next one runs.
        let mut held = Vec::new();
        let mut arg_refs = Vec::new();
        for (i, a) in exprs.iter().enumerate() {
            let mut v = self.expr(a);
            if let Some(pt) = fty.params.get(i) {
                self.unify_arg(pt, &mut v, a.span);
            }
            if matches!(self.inf.shallow(&v.ty), Ty::Ref(_)) {
                arg_refs.extend(v.refs.iter().copied());
                match v.var {
                    Some(var) => held.push(var),
                    None => held.extend(self.hold(&v, "argument", a.span)),
                }
            }
            self.consume(&v, a.span);
        }
        self.use_local(l);
        let n = self.emit(span, &loc.name, String::new());
        for v in held {
            self.facts.uses.push((v, n));
        }
        for p in arg_refs {
            self.facts.reads_at.push((n, p));
            self.sum().reads.insert(p);
        }
        if self.facts.var(loc.var).once {
            self.facts.moved_at.push((loc.var, n));
        }
        if let Some(s) = loc.summary {
            self.apply_summary(n, s, 800);
        } else if let Some(fp) = loc.fn_param {
            self.sum().passthrough.insert(fp);
            if let Some(es) = &fty.effects {
                for e in es.clone() {
                    self.perform_effect(n, &e);
                }
            }
            self.abortive(n);
        } else if let Some(item) = fty.item {
            for e in self.sigs[item].effects.named.clone() {
                self.perform_effect(n, &e);
            }
        }
        Val {
            ty: fty.ret.clone(),
            ..Val::default()
        }
    }

    fn resume(&mut self, l: usize, args: &[Arg], span: Span) -> Val {
        let Some(ContInfo {
            arg,
            ret,
            multi,
            muts,
            cap,
        }) = self.locals[l].cont.clone()
        else {
            return Val {
                ty: Ty::Error,
                ..Val::default()
            };
        };
        if args.len() != 1 {
            self.err("W0103", "`resume` takes one argument", span);
        }
        for a in args {
            let v = self.expr(&a.value);
            self.unify(&arg, &v.ty, a.value.span);
            self.consume(&v, a.value.span);
        }
        let var = self.locals[l].var;
        self.pend_uses.push(var);
        let n = self.emit(span, "resume", "the handled computation runs".into());
        if !multi {
            self.facts.moved_at.push((var, n));
        }
        // The resumed computation mutates these places. They are not the handler's footprint.
        for m in muts {
            self.facts.mutates_at.push((n, m));
        }
        self.resumes.push((n, cap));
        self.abortive(n);
        Val {
            ty: ret,
            ..Val::default()
        }
    }

    fn print(&mut self, args: &[Arg], span: Span) -> Val {
        // `print` reads what its reference arguments point to.
        let mut held = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let v = self.expr(&a.value);
            for &p in &v.refs {
                self.read(p);
            }
            if i + 1 < args.len() {
                held.extend(self.hold(&v, "argument", a.value.span));
            }
        }
        self.pend_uses.extend(held);
        let _ = self.emit(span, "print", String::new());
        Val::default()
    }

    fn positional_struct(&mut self, a: usize, args: &[Arg], span: Span) -> Val {
        let AdtKind::Struct(defs) = self.prog.adts[a].kind.clone() else {
            self.err("W0105", "this type has no constructor", span);
            return Val {
                ty: Ty::Error,
                ..Val::default()
            };
        };
        let targs: Vec<Ty> = self.prog.adts[a]
            .generics
            .iter()
            .map(|_| self.inf.fresh())
            .collect();
        if defs.len() != args.len() {
            self.err(
                "W0103",
                format!("`{}` has {} fields", self.prog.adts[a].name, defs.len()),
                span,
            );
        }
        let mut held = Vec::new();
        for (i, (d, arg)) in defs.iter().zip(args).enumerate() {
            let v = self.expr(&arg.value);
            let ft = super::subst(&d.ty, &targs);
            self.unify(&ft, &v.ty, arg.value.span);
            self.consume(&v, arg.value.span);
            if i + 1 < args.len() {
                held.extend(self.hold(&v, "argument", arg.value.span));
            }
        }
        self.pend_uses.extend(held);
        Val {
            ty: Ty::Adt(a, targs),
            ..Val::default()
        }
    }

    fn variant_ctor(&mut self, adt: usize, vi: usize, args: &[Arg], span: Span) -> Val {
        let AdtKind::Enum(vs) = self.prog.adts[adt].kind.clone() else {
            return Val {
                ty: Ty::Error,
                ..Val::default()
            };
        };
        let targs: Vec<Ty> = self.prog.adts[adt]
            .generics
            .iter()
            .map(|_| self.inf.fresh())
            .collect();
        let fields = &vs[vi].fields;
        if fields.len() != args.len() {
            self.err(
                "W0103",
                format!("variant `{}` has {} fields", vs[vi].name, fields.len()),
                span,
            );
        }
        let mut refs = Vec::new();
        let mut held = Vec::new();
        for (i, (ft, a)) in fields.iter().zip(args).enumerate() {
            let v = self.expr(&a.value);
            let ft = super::subst(ft, &targs);
            self.unify(&ft, &v.ty, a.value.span);
            self.consume(&v, a.value.span);
            if i + 1 < args.len() {
                held.extend(self.hold(&v, "argument", a.value.span));
            }
            refs.extend(v.refs);
        }
        self.pend_uses.extend(held);
        Val {
            ty: Ty::Adt(adt, targs),
            refs,
            ..Val::default()
        }
    }

    /// Performs an effect operation.
    fn perform_op(&mut self, e: usize, op: usize, args: &[Arg], span: Span) -> Val {
        let eff = self.prog.effects[e].clone();
        let o = &eff.ops[op];
        if o.params.len() != args.len() {
            self.err(
                "W0103",
                format!("operation `{}` takes {} arguments", o.name, o.params.len()),
                span,
            );
        }
        let mut held = Vec::new();
        for (i, (pt, a)) in o.params.iter().zip(args).enumerate() {
            let v = self.expr(&a.value);
            self.unify(pt, &v.ty, a.value.span);
            self.consume(&v, a.value.span);
            if i + 1 < args.len() {
                held.extend(self.hold(&v, "argument", a.value.span));
            }
        }
        self.pend_uses.extend(held);
        let n = self.emit(span, &o.name, eff.name.to_lowercase());
        self.perform_effect(n, &eff.name);
        if let Some(c) = self
            .handlers
            .iter()
            .rev()
            .find(|h| h.effect == eff.name)
            .map(|h| h.cap)
        {
            self.cap_calls.push((n, c));
        }
        if o.multi {
            self.multi_node(n);
        }
        self.abortive(n);
        Val {
            ty: o.ret.clone(),
            ..Val::default()
        }
    }

    // -----------------------------------------------------------------------
    // Tasks
    // -----------------------------------------------------------------------

    fn closure_arg(&mut self, e: &Expr, ret: Option<Ty>) -> Val {
        match &e.kind {
            ExprKind::Closure { params, body } => {
                let fty = FnTy {
                    params: Vec::new(),
                    ret: ret.unwrap_or_else(|| self.inf.fresh()),
                    effects: None,
                    summary: None,
                    item: None,
                };
                self.closure(params, body, Some(&fty), e.span)
            }
            _ => self.expr(e),
        }
    }

    /// Starts a task for a closure at a new node. Returns the task.
    fn start_task(&mut self, kind: TaskKind, v: &Val, span: Span) -> (weft_facts::TaskId, NodeId) {
        let t = self.facts.add_task(kind, span);
        if let Some(var) = v.var {
            self.pend_uses.push(var);
        }
        let label = if kind == TaskKind::Fork {
            "fork branch"
        } else {
            "spawn"
        };
        let n = self.emit(span, label, String::new());
        self.facts.spawned_at.push((t, n));
        let Some(s) = v.summary else {
            if let Some(item) = v.item {
                for e in self.sigs[item].effects.named.clone() {
                    self.perform_effect(n, &e);
                }
            }
            return (t, n);
        };
        let sum = self.closures[s].clone();
        let own = |me: &Self, p: PlaceId| sum.own_roots.contains(&me.facts.place(p).root);
        for &m in &sum.muts {
            if !own(self, m) {
                self.facts.task_writes.push((t, m));
            }
        }
        for &r in &sum.reads {
            if !own(self, r) {
                self.facts.task_reads.push((t, r));
            }
        }
        for &c in &sum.captures {
            self.facts.captures.push((t, c));
            let refs = self.locals.iter().find(|l| l.var == c).map(|l| {
                let mut r = l.refs.clone();
                if !l.ty.is_ref() {
                    r.extend(l.root);
                }
                r
            });
            let refs = refs.unwrap_or_default();
            let through = sum.muts.iter().any(|&m| {
                refs.iter().any(|&r| {
                    self.facts.place(r).root == self.facts.place(m).root
                        && weft_verified::places::within(
                            &self.facts.place(m).steps,
                            &self.facts.place(r).steps,
                        )
                })
            });
            if through {
                self.facts.mut_through.push((t, c));
            }
        }
        // Effect handlers live on one task's stack: a task cannot reach them.
        let user = sum
            .escapes
            .iter()
            .filter(|e| {
                self.prog
                    .effect_named(self.module, e)
                    .is_some_and(|id| !self.prog.effects[id].is_std)
            })
            .count();
        if !sum.performs.is_empty() || user > 0 {
            self.err(
                "W0314",
                "a task cannot perform a user effect: its handler runs on another task",
                span,
            );
        }
        self.apply_summary(n, s, 700);
        (t, n)
    }

    fn spawn(&mut self, args: &[Arg], trailing: Option<&Expr>, span: Span) -> Val {
        let Some(e) = args.first().map(|a| &a.value).or(trailing) else {
            self.err("W0103", "`spawn` takes a closure", span);
            return Val {
                ty: Ty::Error,
                ..Val::default()
            };
        };
        let v = self.closure_arg(e, None);
        let ret = match self.inf.shallow(&v.ty) {
            Ty::Fn(f) => f.ret.clone(),
            _ => Ty::Error,
        };
        let (t, n) = self.start_task(TaskKind::Spawn, &v, e.span);
        self.perform_effect(n, "Async");
        self.abortive(n);
        if let Some(sc) = self.scopes.last_mut() {
            sc.push(t);
        } else {
            self.err("W0115", "`spawn` needs a `scope`", span);
        }
        let ty = self
            .b
            .task
            .map_or(Ty::Error, |task| Ty::Adt(task, vec![ret]));
        Val {
            ty,
            task: Some(t),
            ..Val::default()
        }
    }

    fn join(&mut self, rv: &Val, join: bool, span: Span) -> Val {
        let label = if join { "join" } else { "detach" };
        let n = self.emit(span, label, String::new());
        if let Some(var) = rv.var {
            self.move_var(var, n);
        }
        let task = rv
            .task
            .or_else(|| rv.local.and_then(|l| self.locals[l].task));
        let ret = match self.deref_ty(&rv.ty) {
            Ty::Adt(_, args) => args.first().cloned().unwrap_or(Ty::Error),
            _ => Ty::Error,
        };
        if join {
            if let Some(t) = task {
                self.facts.joined_at.push((t, n));
            }
            self.perform_effect(n, "Async");
            self.abortive(n);
            return Val {
                ty: ret,
                ..Val::default()
            };
        }
        Val::default()
    }

    fn fork(&mut self, args: &[Arg], trailing: Option<&Expr>, span: Span) -> Val {
        let mut tasks = Vec::new();
        let mut rets = Vec::new();
        for e in args.iter().map(|a| &a.value).chain(trailing) {
            let v = self.closure_arg(e, None);
            let ret = if let Ty::Fn(f) = self.inf.shallow(&v.ty) {
                f.ret.clone()
            } else {
                self.err("W0102", "`fork` takes closures", e.span);
                Ty::Error
            };
            rets.push(ret);
            let (t, _) = self.start_task(TaskKind::Fork, &v, e.span);
            tasks.push(t);
        }
        let n = self.emit(span, "fork join", String::new());
        for t in tasks {
            self.facts.joined_at.push((t, n));
        }
        self.perform_effect(n, "Par");
        self.abortive(n);
        let all_unit = rets.iter().all(|r| matches!(self.inf.resolve(r), Ty::Unit));
        let ty = if all_unit { Ty::Unit } else { Ty::Tuple(rets) };
        Val {
            ty,
            ..Val::default()
        }
    }

    /// `sim.run(seed: N) { body }`: the simulation handles every standard effect.
    fn sim_run(&mut self, _f: FnId, args: &[Arg], trailing: Option<&Expr>, span: Span) -> Val {
        if self.library && !self.in_test {
            self.err(
                "W0802",
                "only binaries and tests can install root handlers (`sim.run`)",
                span,
            );
        }
        for a in args {
            let v = self.expr(&a.value);
            let t = self.deref_ty(&v.ty);
            self.unify(&Ty::Int(super::IntTy::U64), &t, a.value.span);
        }
        let Some(body) = trailing else {
            self.err("W0103", "`sim.run` takes a block", span);
            return Val::default();
        };
        // Every standard effect of the body is handled here.
        let caps: Vec<String> = effects::STD_EFFECTS
            .iter()
            .map(|s| (*s).to_string())
            .collect();
        let base = self.handlers.len();
        for e in &caps {
            let cap = self.facts.add_cap();
            self.facts.handlers.push(weft_facts::HandlerInfo {
                effect: e.clone(),
                is_std: true,
                forwards: true,
                span,
            });
            self.handlers.push(super::HandlerFrame {
                effect: e.clone(),
                cap,
                multi: false,
            });
        }
        let v = self.closure_arg(body, Some(Ty::Unit));
        let n = self.emit(span, "sim.run", String::new());
        if let Some(s) = v.summary {
            self.apply_summary(n, s, 800);
        }
        self.handlers.truncate(base);
        let _ = PRELUDE;
        Val::default()
    }
}
