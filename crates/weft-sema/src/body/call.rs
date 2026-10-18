//! Calls: functions, methods, constructors, effect operations and built-ins.

use super::fnval::{Callee, Given};
use super::{
    ast, effects, AdtKind, Arg, ContInfo, Expr, ExprKind, FnId, FnSig, FnTy, ItemRef, Lower,
    NodeId, PathRef, PlaceId, Rc, SigRoot, Span, TaskKind, Ty, Val, PRELUDE,
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
                        if self.is_sim_run(f) {
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
        self.call_fn_as(f, recv, None, args, trailing, span)
    }

    /// Returns the callee root index of parameter `i`: a parameter with `in`
    /// shares the root of its place.
    fn sig_root(sig: &FnSig, i: usize) -> u32 {
        let mut i = i;
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
    }

    /// Calls a function item. `inst` is the type of the item as a value, for a call
    /// through a local: the call uses its parameter and result types.
    pub(super) fn call_fn_as(
        &mut self,
        f: FnId,
        recv: Option<Val>,
        inst: Option<&FnTy>,
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
        let ptys: Vec<Ty> = match inst {
            Some(t) if t.params.len() == sig.params.len() => t.params.clone(),
            _ => sig
                .params
                .iter()
                .map(|p| super::subst(&p.ty, &targs))
                .collect(),
        };
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
        // Evaluate the arguments in order. Type, hold and move each argument
        // before the next one runs, so that a later argument cannot hide a
        // mutation from an earlier reference.
        // A parameter of a function type gets a callback: the callee can call it. A
        // parameter of a type parameter gets a value that the callee can only keep.
        let callback = |i: usize| sig.params.get(i).is_some_and(|p| matches!(p.ty, Ty::Fn(_)));
        let mut value_refs: Vec<(usize, Vec<PlaceId>)> = Vec::new();
        let mut recv = recv;
        let mut recv_deps = Vec::new();
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
                let places = match av.val.place.as_ref() {
                    Some(lv) => lv.places.clone(),
                    None => vec![self.temp_root(av.span, &av.val.ty)],
                };
                recv_deps = av
                    .val
                    .place
                    .as_ref()
                    .map_or_else(Vec::new, |lv| lv.deps.clone());
                if let Ty::Ref(inner) = self.inf.shallow(&pt) {
                    self.unify(&inner, &av.val.ty, av.span);
                }
                if later {
                    // The borrow depends on the `Rc` handles on the way too.
                    let mut refs = places.clone();
                    refs.extend(recv_deps.iter().copied());
                    let borrow = Val {
                        ty: pt.clone(),
                        refs,
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
                held_vars.extend(self.hold_operand(&av.val, later, av.span));
            } else {
                arg_places.push(Vec::new());
                // A by-value argument that holds references, for example a closure,
                // points into them until the call.
                if !av.val.refs.is_empty() {
                    held_vars.extend(self.hold_operand(&av.val, later, av.span));
                    value_refs.push((i, av.val.refs.clone()));
                }
                if !callback(i) {
                    // The callee keeps the value, for example in a container.
                    let v = av.val.clone();
                    self.escape_all(&v);
                }
                if !matches!(self.inf.shallow(&pt), Ty::Fn(_)) || av.val.summary.is_none() {
                    let v = av.val.clone();
                    self.consume(&v, av.span);
                }
            }
            vals.push(av);
        }
        let root_of = |i: usize| Self::sig_root(&sig, i);
        let roots: Vec<u32> = (0..arg_places.len()).map(root_of).collect();
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
        for (i, ps) in &value_refs {
            // A function value inside the argument runs as a stored value (root 800).
            let root = if callback(*i) {
                800 + u32::try_from(*i).unwrap_or(0)
            } else if self.has_fn(&vals[*i].val.ty, 0) {
                800
            } else {
                root_of(*i)
            };
            for &p in ps {
                self.facts.call_arg.push((n, p, root));
            }
        }
        // Arguments must point where the parameters say. A by-value argument is
        // the base of the places inside it.
        let bases: Vec<Vec<PlaceId>> = arg_places
            .iter()
            .zip(&vals)
            .map(|(ps, av)| match (&av.val.place, ps.is_empty()) {
                (Some(lv), true) => lv.places.clone(),
                _ => ps.clone(),
            })
            .collect();
        for (i, p) in sig.params.iter().enumerate() {
            if let Some(pl) = &p.place {
                let allowed = self.subst_place(pl, &bases, split);
                let named: Vec<PlaceId> = arg_places[i]
                    .iter()
                    .copied()
                    .filter(|&r| !self.is_dep(r))
                    .collect();
                for &r in &named {
                    if allowed.iter().any(|&a| self.sig_allows(a, r)) {
                        continue;
                    }
                    let (rt, at) = (
                        self.facts.place(r).display.clone(),
                        self.place_text(&allowed),
                    );
                    let below = if allowed.iter().any(|&a| self.below_unstable(a, r)) {
                        format!(", and `{rt}` is below it through an unstable step")
                    } else {
                        String::new()
                    };
                    self.err(
                        "W0203",
                        format!(
                            "argument `{}` points into `{rt}`, but `{name}` needs `{at}`{below}",
                            p.name
                        ),
                        vals[i].span,
                    );
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
        // Effects. An operation of a local handler gets the reference arguments.
        let mut abort = false;
        let ref_args: Vec<(PlaceId, u32)> = arg_places
            .iter()
            .zip(&roots)
            .flat_map(|(ps, &r)| ps.iter().map(move |&p| (p, r)))
            .collect();
        for e in &sig.effects.named {
            self.perform_at(n, e, &ref_args);
            if self.effect_has_multi(e) {
                self.multi_node(n);
            }
            abort = true;
        }
        // The callee can call a function argument with the places that it lends to it.
        let mut fns = Vec::new();
        for (i, av) in vals.iter().enumerate() {
            let Ty::Fn(fty) = self.inf.shallow(&av.val.ty) else {
                fns.push(None);
                continue;
            };
            let info = self.fn_info(&av.val);
            let row = fty.effects.clone();
            fns.push(Some((info.clone(), row.clone())));
            if !callback(i) {
                continue;
            }
            let root = 800 + u32::try_from(i).unwrap_or(0);
            if let Some(s) = info.summary {
                self.check_fn_arg_effects(&ptys[i], s, av.span);
            }
            let given = self.lent_to(&Callee::Item(f), i, &arg_places, &roots);
            self.apply_value(n, &info, row.as_deref(), root, &given);
        }
        for &j in &sig.effects.passthrough {
            if let Some((0, fp)) = vals.get(j).and_then(|v| v.val.fn_param) {
                self.sum().passthrough.insert(fp);
            }
        }
        // The callee can store a function argument, and it can run a stored one
        // that an argument holds. A foreign function can do both.
        let def = &self.prog.fns[f];
        let foreign = def.decl.body.is_none() && !def.is_std;
        let mut holds_fn = false;
        for (i, av) in vals.iter().enumerate() {
            let ty = self.inf.shallow(&av.val.ty);
            if matches!(ty, Ty::Fn(_)) {
                if foreign || sig.effects.stores.contains(&i) {
                    self.escape(&av.val);
                }
            } else if self.has_fn(&ty, 0) {
                holds_fn = true;
            }
        }
        if holds_fn {
            if let Some(given) = self.reach_of(f, &arg_places, &roots) {
                self.reach(n, &given);
            }
        }
        if abort {
            self.abortive(n);
        }
        // The callee calls a function value that this body does not see, and it can resume more than once.
        if sig.effects.multi {
            self.multi_node(n);
            self.unknown_multi = true;
        }
        // The result.
        let ret = match inst {
            Some(t) => t.ret.clone(),
            None => super::subst(&sig.ret, &targs),
        };
        let mut out = Val {
            ty: ret.clone(),
            ..Val::default()
        };
        // A returned function value does what the callee states about it.
        if let (Some(rf), Ty::Fn(fty)) = (&sig.effects.ret, self.inf.shallow(&ret)) {
            let s = self.ret_summary(rf, &fty, &arg_places, &fns);
            out.summary = Some(s);
            out.ty = Ty::Fn(Rc::new(FnTy {
                summary: Some(s),
                item: None,
                ..(*fty).clone()
            }));
        }
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
                let mut places = self.subst_place(&rp.place, &arg_places, split);
                if matches!(rp.place.root, SigRoot::Group(_)) {
                    // A group place stays valid only while the handles on the way do.
                    places.extend(self.group_arg_deps(&arg_places, &ptys));
                }
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
            out.refs.extend(recv_deps);
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

    /// Calls a function value in a local: a closure, a function item, a function
    /// parameter, a join of these, or a value that the body does not know.
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
        let callee = self.local_fn_info(l);
        // A function item: the call is a call of the item, with its effects.
        if let (None, Some(f), None) = (callee.summary, callee.item, callee.param) {
            self.use_local(l);
            return self.call_fn_as(f, None, Some(&fty), args, trailing, span);
        }
        let exprs: Vec<&Expr> = args.iter().map(|a| &a.value).chain(trailing).collect();
        if exprs.len() != fty.params.len() {
            self.err(
                "W0103",
                format!("`{}` takes {} arguments", loc.name, fty.params.len()),
                span,
            );
        }
        // Type, hold and move each argument before the next one runs.
        let mut held = Vec::new();
        let mut arg_places: Vec<Vec<PlaceId>> = Vec::new();
        let mut arg_tys = Vec::new();
        let mut fns = Vec::new();
        let mut value_refs: Vec<(usize, Vec<PlaceId>)> = Vec::new();
        for (i, a) in exprs.iter().enumerate() {
            let later = i + 1 < exprs.len();
            let mut v = match (&a.kind, fty.params.get(i).map(|t| self.inf.shallow(t))) {
                (ExprKind::Closure { params, body }, Some(Ty::Fn(f))) => {
                    self.closure(params, body, Some(&f), a.span)
                }
                _ => self.expr(a),
            };
            if let Some(pt) = fty.params.get(i) {
                self.unify_arg(pt, &mut v, a.span);
            }
            arg_tys.push(v.ty.clone());
            if matches!(self.inf.shallow(&v.ty), Ty::Ref(_)) {
                arg_places.push(v.refs.clone());
                held.extend(self.hold_operand(&v, later, a.span));
            } else {
                arg_places.push(Vec::new());
                if !v.refs.is_empty() {
                    held.extend(self.hold_operand(&v, later, a.span));
                }
                if let Ty::Fn(f) = self.inf.shallow(&v.ty) {
                    fns.push((i, self.fn_info(&v), f.effects.clone(), v.refs.clone()));
                } else if !v.refs.is_empty() {
                    // A by-value argument that holds references points into them.
                    value_refs.push((i, v.refs.clone()));
                }
                if self.has_fn(&v.ty, 0) && !matches!(self.inf.shallow(&v.ty), Ty::Fn(_)) {
                    // The callee keeps the value: it can run a function value in it.
                    self.escape_all(&v);
                }
            }
            // A closure argument is lent to the call, as in `call_fn`.
            if v.summary.is_none() {
                self.consume(&v, a.span);
            }
        }
        let arg_refs: Vec<PlaceId> = arg_places.iter().flatten().copied().collect();
        self.use_local(l);
        let n = self.emit(span, &loc.name, String::new());
        for v in held {
            self.facts.uses.push((v, n));
        }
        let roots: Vec<u32> = (0..arg_places.len())
            .map(|i| u32::try_from(i).unwrap_or(0))
            .collect();
        let mut direct = Vec::new();
        for (i, ps) in arg_places.iter().enumerate() {
            for &p in ps {
                self.facts.reads_at.push((n, p));
                self.sum().reads.insert(p);
                self.facts.call_arg.push((n, p, roots[i]));
                direct.push(Given {
                    pos: Some(i),
                    place: p,
                    root: roots[i],
                });
            }
        }
        for (i, ps) in &value_refs {
            // A function value inside the argument runs as a stored value (root 800).
            let root = if self.has_fn(&arg_tys[*i], 0) {
                800
            } else {
                roots[*i]
            };
            for &p in ps {
                self.facts.call_arg.push((n, p, root));
                direct.push(Given {
                    pos: Some(*i),
                    place: p,
                    root,
                });
            }
        }
        if self.facts.var(loc.var).once {
            self.facts.moved_at.push((loc.var, n));
        }
        // The value runs with the arguments.
        self.apply_value(n, &callee, fty.effects.as_deref(), 800, &direct);
        // The value can call a function argument with the places that it lends to it.
        let value = Callee::Value(callee.clone());
        for (i, info, row, refs) in fns.clone() {
            let root = 810 + u32::try_from(i).unwrap_or(0);
            for p in refs {
                self.facts.call_arg.push((n, p, root));
            }
            let given = self.lent_to(&value, i, &arg_places, &roots);
            self.apply_value(n, &info, row.as_deref(), root, &given);
        }
        // The value can run a stored function value that an argument holds.
        if arg_tys
            .iter()
            .any(|t| !matches!(self.inf.shallow(t), Ty::Fn(_)) && self.has_fn(t, 0))
        {
            let given = Self::any_arg(&arg_places, &roots);
            self.reach(n, &given);
        }
        // The places of the result.
        let refs = self.value_call_refs(&callee, &fty, &arg_places, &arg_refs);
        // A function value in the result does what the callee states about it.
        let by_pos: Vec<Option<super::fnval::RowFn>> = (0..arg_places.len())
            .map(|i| {
                fns.iter()
                    .find(|(j, ..)| *j == i)
                    .map(|(_, info, row, _)| (info.clone(), row.clone()))
            })
            .collect();
        let mut ty = fty.ret.clone();
        let summary = self.result_summary(&callee, &fty, &arg_places, &by_pos);
        if let (Some(s), Ty::Fn(rty)) = (summary, self.inf.shallow(&fty.ret)) {
            ty = Ty::Fn(Rc::new(FnTy {
                summary: Some(s),
                item: None,
                ..(*rty).clone()
            }));
        }
        Val {
            ty,
            refs,
            summary,
            ..Val::default()
        }
    }

    /// Returns the places that the result of a call of a function value points into.
    fn value_call_refs(
        &mut self,
        callee: &super::FnInfo,
        fty: &FnTy,
        arg_places: &[Vec<PlaceId>],
        arg_refs: &[PlaceId],
    ) -> Vec<PlaceId> {
        let (mut refs, items, unknown) = match callee.summary {
            Some(s) => {
                let sum = &self.closures[s];
                let items: Vec<FnId> = sum.items.iter().copied().collect();
                let unknown = sum.unknown || !sum.params.is_empty();
                (self.closure_call_refs(s, arg_places), items, unknown)
            }
            None => (
                Vec::new(),
                callee.item.into_iter().collect(),
                callee.item.is_none(),
            ),
        };
        for f in items {
            let sig = self.sigs[f].clone();
            let split = self.fresh_split();
            for rp in &sig.ret_places {
                refs.extend(self.subst_place(&rp.place, arg_places, split));
                if matches!(rp.place.root, SigRoot::Group(_)) {
                    refs.extend(self.group_arg_deps(arg_places, &fty.params));
                }
            }
        }
        // An unknown function can return a reference to any place inside a
        // reference argument.
        if unknown && self.holds_refs(&fty.ret) {
            for &p in arg_refs {
                let q = if self.is_dep(p) {
                    p
                } else {
                    self.facts.wildcard(p)
                };
                refs.push(q);
            }
        }
        refs
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
                held.extend(self.hold_later(&v, "argument", a.value.span));
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
            self.escape(&v);
            self.consume(&v, arg.value.span);
            if i + 1 < args.len() {
                held.extend(self.hold_later(&v, "argument", arg.value.span));
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
            self.escape(&v);
            self.consume(&v, a.value.span);
            if i + 1 < args.len() {
                held.extend(self.hold_later(&v, "argument", a.value.span));
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
        // A perform is a call: each reference argument stays valid until it.
        let mut held = Vec::new();
        let mut arg_places = Vec::new();
        let mut value_refs: Vec<(usize, Vec<PlaceId>)> = Vec::new();
        let mut fns = Vec::new();
        for (i, (pt, a)) in o.params.iter().zip(args).enumerate() {
            let later = i + 1 < args.len();
            let v = match (&a.value.kind, self.inf.shallow(pt)) {
                (ExprKind::Closure { params, body }, Ty::Fn(f)) => {
                    self.closure(params, body, Some(&f), a.value.span)
                }
                _ => self.expr(&a.value),
            };
            self.unify(pt, &v.ty, a.value.span);
            if v.summary.is_none() {
                self.consume(&v, a.value.span);
            }
            if matches!(self.inf.shallow(&v.ty), Ty::Ref(_)) {
                arg_places.push(v.refs.clone());
                held.extend(self.hold_operand(&v, later, a.value.span));
            } else {
                arg_places.push(Vec::new());
                if later || !v.refs.is_empty() {
                    held.extend(self.hold_operand(&v, later, a.value.span));
                }
                // A by-value argument that holds references, for example a closure,
                // points into them until the perform.
                if !v.refs.is_empty() {
                    value_refs.push((i, v.refs.clone()));
                }
                if let Ty::Fn(f) = self.inf.shallow(&v.ty) {
                    fns.push((i, self.fn_info(&v), f.effects.clone()));
                } else if self.has_fn(&v.ty, 0) {
                    self.escape_all(&v);
                }
            }
        }
        self.pend_uses.extend(held);
        let n = self.emit(span, &o.name, eff.name.to_lowercase());
        self.perform_effect(n, &eff.name);
        let cap = self
            .handlers
            .iter()
            .rev()
            .find(|h| h.effect == eff.name)
            .map(|h| h.cap);
        if let Some(c) = cap {
            self.cap_calls.push((n, c));
        }
        // The clause gets the reference arguments. It pairs with the footprint of
        // the handler in `call_mut` (W0312), and it can mutate through them.
        for (i, ps) in arg_places.iter().enumerate() {
            let root = u32::try_from(i).unwrap_or(0);
            for &p in ps {
                self.facts.reads_at.push((n, p));
                self.sum().reads.insert(p);
                self.facts.call_arg.push((n, p, root));
                match cap {
                    Some(c) => self.give_op(n, c, Some(op), Some(i), p, root),
                    None => self.lend(n, p, root),
                }
            }
        }
        for (i, ps) in &value_refs {
            let root = 800 + u32::try_from(*i).unwrap_or(0);
            for &p in ps {
                self.facts.call_arg.push((n, p, root));
                // The parameter of the clause points into what the argument holds.
                if let (Some(c), false) = (cap, self.has_fn(&o.params[*i], 0)) {
                    self.give_op(n, c, Some(op), Some(*i), p, root);
                }
            }
        }
        // The clause can call a function argument with any place inside the
        // reference arguments.
        let roots: Vec<u32> = (0..arg_places.len())
            .map(|i| u32::try_from(i).unwrap_or(0))
            .collect();
        let given = Self::any_arg(&arg_places, &roots);
        for (i, info, row) in fns {
            let root = 800 + u32::try_from(i).unwrap_or(0);
            self.apply_value(n, &info, row.as_deref(), root, &given);
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
        // A place that the task lends can change as a mutation does.
        let writes: Vec<PlaceId> = sum.muts.iter().chain(&sum.lends).copied().collect();
        for &m in &writes {
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
            let through = writes.iter().any(|&m| {
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
        self.apply_summary(n, s, 700, &[]);
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
            self.apply_summary(n, s, 800, &[]);
        }
        self.handlers.truncate(base);
        let _ = PRELUDE;
        Val::default()
    }
}
