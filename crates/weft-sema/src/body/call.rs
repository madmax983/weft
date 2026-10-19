//! Calls: functions, methods, constructors, effect operations and built-ins.

use super::fnval::{Callee, Given};
use super::{
    ast, effects, AdtKind, Arg, CapId, ContInfo, Expr, ExprKind, FnId, FnSig, FnTy, ItemRef, Lower,
    NodeId, PathRef, PlaceId, Rc, SigRoot, Span, TaskKind, Ty, Val, VarId, VarKind, PRELUDE,
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
                return self.perform_op(e, op, args, trailing, span);
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
                        self.check_visible(f, method.span);
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
                    self.check_visible(f, method.span);
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
                    self.perform_op(e, op, args, trailing, span)
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
                // A receiver that holds references points where they point.
                let refs = if lv.through_ref || !self.holds_refs(&lv.ty) {
                    Vec::new()
                } else {
                    self.held_refs(&lv.places)
                };
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
            (Ty::Scope, "spawn") => return self.spawn(&rv, args, trailing, span),
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
        self.check_visible(f, method.span);
        self.call_fn(f, Some(rv), args, trailing, span)
    }

    /// Reports W0101 if function `f` is private in another unit: the project
    /// can name only the `pub` functions of a dependency, and the reverse.
    pub(super) fn check_visible(&mut self, f: FnId, span: Span) {
        let def = &self.prog.fns[f];
        let (here, there) = (
            self.prog.mods[self.module].unit,
            self.prog.mods[def.module].unit,
        );
        if !def.is_pub && !def.is_std && here != there {
            let msg = format!("`{}` is private: it is not `pub` in its package", def.path);
            self.err("W0101", msg, span);
        }
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
        // The type of the value gives the type arguments of a call through a local.
        if let Some(t) = inst {
            for (p, it) in sig.params.iter().zip(&t.params) {
                let _ = self.inf.unify(&super::subst(&p.ty, &targs), it);
            }
            let _ = self.inf.unify(&super::subst(&sig.ret, &targs), &t.ret);
        }
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
        let mut named_bad = false;
        for a in args {
            let idx = if let Some(n) = &a.name {
                let Some(i) = sig.params.iter().position(|p| p.name == n.name) else {
                    let msg = format!("`{name}` has no parameter named `{}`", n.name);
                    self.err("W0103", msg, n.span);
                    named_bad = true;
                    let _ = self.expr(&a.value);
                    continue;
                };
                if slots[i].is_some() {
                    self.err(
                        "W0103",
                        format!("argument `{}` is given twice", n.name),
                        n.span,
                    );
                    named_bad = true;
                    let _ = self.expr(&a.value);
                    continue;
                }
                Some(i)
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
        if (extra > 0 || missing > 0) && !named_bad {
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
        let mut taken = Vec::new();
        let mut kept_vals: Vec<Val> = Vec::new();
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
                let places = if let Some(lv) = av.val.place.as_ref() {
                    // The callee can read a place field: it needs a value (W0304).
                    let ps = lv.places.clone();
                    self.touch_unset(&ps);
                    ps
                } else {
                    // A temporary receiver goes away after the call.
                    let v = av.val.clone();
                    self.drop_value(&v, av.span);
                    vec![self.temp_root(av.span, &av.val.ty)]
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
                // A by-value parameter that holds references gets the places of the
                // argument: the callee can change what they point into.
                let declared = sig.params.get(i).map_or(Ty::Error, |p| p.ty.clone());
                if self.byval_refs(&declared) {
                    arg_places.push(av.val.refs.clone());
                } else {
                    arg_places.push(Vec::new());
                }
                // A by-value argument that holds references, for example a closure,
                // points into them until the call. An argument that moves before
                // the call is on its way to the callee while the later arguments run.
                let consumed =
                    (!callback(i) || av.val.summary.is_none()) && self.moves_value(&av.val.ty);
                if consumed {
                    if later {
                        taken.extend(self.hold_moved(&av.val, "argument", av.span));
                    }
                } else if !av.val.refs.is_empty() {
                    held_vars.extend(self.hold_operand(&av.val, later, av.span));
                }
                if !av.val.refs.is_empty() && !self.byval_refs(&declared) {
                    value_refs.push((i, av.val.refs.clone()));
                }
                if !callback(i) {
                    // The callee keeps the value, for example in a container.
                    let v = av.val.clone();
                    self.escape_all(&v);
                    kept_vals.push(v);
                }
                if !callback(i) || av.val.summary.is_none() {
                    let v = av.val.clone();
                    self.keep_modes(&v, &pt, av.span);
                    // A `!Move` value built here is built in place for a parameter of
                    // its own type. A type parameter lets the callee move it, as
                    // `Vec.push` does when its buffer grows.
                    let declared = sig.params.get(i).map_or(Ty::Error, |p| p.ty.clone());
                    if v.var.is_none()
                        && self.is_immovable(&v.ty)
                        && !self.is_immovable(&declared)
                        && !self.builds_in_place(f)
                    {
                        self.move_temp(&v.ty, av.span);
                    }
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
                let holds = sig.params.get(i).is_some_and(|p| self.byval_refs(&p.ty));
                if !by_ref && !receiver && !holds {
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
            parts.extend(sig.effects.named.iter().map(|n| effects::in_signature(n)));
            parts.join(", ")
        };
        let generic_held = self.hold_generic(&sig, &targs, &vals, span);
        let n = self.emit(span, &name, detail);
        self.release_generic(&generic_held, span);
        let performs_from = self.facts.performs_at.len();
        for v in held_vars {
            self.facts.uses.push((v, n));
        }
        self.take_held(&taken, n);
        self.callee_drops(&sig, &targs, &vals, span);
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
            } else if self.has_fn(&vals[*i].val.ty) {
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
        self.check_callee_tasks(f, span);
        // A task of the callee can run a function value that an argument holds, in
        // a field or a container. Foreign code and `http.serve` can too.
        for (i, av) in vals.iter().enumerate() {
            if matches!(self.inf.shallow(&av.val.ty), Ty::Fn(_)) {
                continue;
            }
            if sig.effects.tasks.contains(&i) || self.item_runs_tasks(f) {
                let held = self.arg_held(&av.val, &arg_places[i]);
                self.check_task_value(&super::FnInfo::default(), None, &held, av.span);
            }
            for (_, e) in sig.effects.op_fns.iter().filter(|(p, _)| *p == i) {
                self.give_held_to_op(&av.val, &arg_places[i], e, av.span);
            }
        }
        self.callee_op_effects(&sig.effects.op_effects, span);
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
            // The callee can give the argument to an operation.
            let to: Vec<(Option<CapId>, String)> = sig
                .effects
                .op_fns
                .iter()
                .filter(|(p, _)| *p == i)
                .map(|(_, e)| (None, e.clone()))
                .collect();
            self.give_to_ops(&av.val, &to, false, av.span);
            // A task of the callee can call the argument. Foreign code and
            // `http.serve` can call it on another thread.
            if sig.effects.tasks.contains(&i) || self.item_runs_tasks(f) {
                let held = self.val_caps(&av.val);
                self.check_task_value(&info, row.as_deref(), &held, av.span);
            }
            let given = self.lent_to(&Callee::Item(f), i, &arg_places, &roots);
            self.apply_value(n, &info, row.as_deref(), root, &given);
            self.start_ret_spawns(n, &info);
            let repeats = self.callee_repeats(&Callee::Item(f), i);
            if repeats {
                self.note_repeat(n, &info, true);
            }
            let once = self.item_runs_once(f);
            self.give_fn(n, &av.val, repeats, once);
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
        let into: Vec<PlaceId> = arg_places.iter().flatten().copied().collect();
        for (i, av) in vals.iter().enumerate() {
            let ty = self.inf.shallow(&av.val.ty);
            if matches!(ty, Ty::Fn(_)) {
                if foreign || sig.effects.stores.contains(&i) {
                    self.escape(&av.val);
                }
                // A callee with a body can store it only in what its reference
                // arguments point into. A foreign callee can store it anywhere.
                if foreign {
                    self.keep(&av.val, super::caps::KeptTo::Stored);
                } else if sig.effects.stores.contains(&i) && !into.is_empty() {
                    self.store_into(&av.val, &into);
                    self.note_fn_store(&into);
                }
            } else if self.has_fn(&ty) {
                holds_fn = true;
            }
        }
        if holds_fn {
            if let Some(given) = self.reach_of(f, &arg_places, &roots) {
                // A foreign callee can run a stored value any number of times.
                let again = foreign || self.sigs[f].effects.reach_repeats;
                self.reach(n, &given, again);
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
        // A value that the callee keeps can be in a reference argument or in the result.
        // A foreign callee can keep it anywhere.
        let mut out = Val {
            ty: ret.clone(),
            ..Val::default()
        };
        let ret_fn = self.has_fn(&ret);
        for v in &kept_vals {
            if foreign {
                self.keep(v, super::caps::KeptTo::Stored);
            } else if !into.is_empty() {
                self.store_into(v, &into);
                if self.has_fn(&v.ty) {
                    self.note_fn_store(&into);
                }
            }
            if ret_fn {
                out.caps.extend(self.val_caps(v));
            }
        }
        // The callee can copy a function value out of what a reference argument
        // points to: into what another reference argument points to, or into
        // its result.
        let mut copied = std::collections::BTreeSet::new();
        for (i, ps) in arg_places.iter().enumerate() {
            if self.points_to_fn(&ptys[i]) {
                copied.extend(self.place_caps(ps));
            }
        }
        if foreign {
            self.keep_caps(copied.clone(), super::caps::KeptTo::Stored);
        }
        for (j, ps) in arg_places.iter().enumerate() {
            let changed = foreign || sig.effects.fn_stores.contains(&j);
            if changed && self.points_to_fn(&ptys[j]) {
                self.store_caps_into(&copied, ps);
                self.note_fn_store(ps);
            }
        }
        if ret_fn {
            out.caps.extend(copied);
        }
        if ret_fn {
            // A result that is not a function value can hold a function argument,
            // for example in a tuple. The `ret` part covers a function result.
            if !matches!(self.inf.shallow(&ret), Ty::Fn(_)) {
                for av in &vals {
                    if matches!(self.inf.shallow(&av.val.ty), Ty::Fn(_)) {
                        out.caps.extend(self.val_caps(&av.val));
                    }
                }
            }
            // The callee can return what a clause of a local handler resumes with.
            out.caps.extend(self.resumed_at(n, performs_from));
            // A closure in the result can capture what an argument holds or points
            // to: a nonportable value, or a value that is not `many`.
            for av in &vals {
                let held = self.val_caps(&av.val);
                if self.is_nonportable(&av.val.ty) || held.contains(&super::caps::NONPORTABLE) {
                    out.caps.insert(super::caps::NONPORTABLE);
                }
                if av.val.uniq || held.contains(&super::caps::NOT_MANY) {
                    out.caps.insert(super::caps::NOT_MANY);
                }
            }
        }
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
        self.call_flows(&sig, &vals, &arg_places, &ptys, &muts, &ret, &mut out);
        // The callee can return what a clause of a local handler resumes with.
        if self.holds_refs(&ret) {
            let caps: Vec<CapId> = self.facts.performs_at[performs_from..]
                .iter()
                .filter(|(m, _)| *m == n)
                .map(|&(_, c)| c)
                .collect();
            for c in caps {
                let rs = self.op_result_refs(Some(c), None);
                out.refs.extend(rs);
            }
        }
        out
    }

    /// Returns true if function item `f` can put a function value into what a
    /// reference argument points to: a foreign function, or a body with `fn_stores`.
    fn item_fn_stores(&self, f: FnId) -> bool {
        let def = &self.prog.fns[f];
        (def.decl.body.is_none() && !def.is_std) || !self.sigs[f].effects.fn_stores.is_empty()
    }

    /// Returns true if function item `f` builds its argument in place on the heap:
    /// `Box.new` and `Rc.new` of the prelude.
    fn builds_in_place(&self, f: FnId) -> bool {
        let def = &self.prog.fns[f];
        let owner = def.owner.map(|a| self.prog.adts[a].name.as_str());
        def.is_std && def.name == "new" && matches!(owner, Some("Box" | "Rc"))
    }

    /// A generic callee with signature `sig` can drop a value of each type
    /// parameter in its `drops` part. If the call gives a linear type there, the
    /// value goes away at the call (W0601). `finish` decides from the inferred
    /// type argument. The diagnostic names the argument of that type.
    fn callee_drops(&mut self, sig: &FnSig, targs: &[Ty], vals: &[ArgVal], span: Span) {
        for &j in &sig.effects.drops {
            let Some(t) = targs.get(j).cloned() else {
                continue;
            };
            if !self.may_be_linear(&t) {
                continue;
            }
            let (name, at) = self.generic_arg(sig, j, vals, span);
            self.drop_linear(&name, &t, at);
        }
    }

    /// Returns the name and the span of the argument that gives a value of type
    /// parameter `j` to a call. The diagnostic names the argument if only one
    /// parameter is of the type.
    fn generic_arg(&self, sig: &FnSig, j: usize, vals: &[ArgVal], span: Span) -> (String, Span) {
        let param = u32::try_from(j).unwrap_or(u32::MAX);
        let args: Vec<usize> = (0..sig.params.len())
            .filter(|&i| super::flow::mentions(&sig.params[i].ty, param))
            .collect();
        match (args.as_slice(), args.first().and_then(|&i| vals.get(i))) {
            ([i], Some(av)) if sig.params[*i].ty == Ty::Param(param) => {
                (self.val_name(&av.val), av.span)
            }
            (_, Some(av)) => ("temporary".to_string(), av.span),
            (_, None) => ("temporary".to_string(), span),
        }
    }

    /// A generic callee with signature `sig` can hold a value of each type
    /// parameter in its `holds` part at a node that can abort or resume more than
    /// once. If the call gives a linear type there, a hidden variable holds a value
    /// of the type across the call node. The rules of W0602 and W0503 then check
    /// the call. `finish` decides from the inferred type argument. Returns the
    /// variables; `release_generic` ends them after the call node.
    fn hold_generic(
        &mut self,
        sig: &FnSig,
        targs: &[Ty],
        vals: &[ArgVal],
        span: Span,
    ) -> Vec<VarId> {
        let mut out = Vec::new();
        if self.cur.is_none() {
            return out;
        }
        for &j in &sig.effects.holds {
            let Some(t) = targs.get(j).cloned() else {
                continue;
            };
            if !self.may_be_linear(&t) {
                continue;
            }
            let (name, at) = self.generic_arg(sig, j, vals, span);
            let info = self.var_info(&name, VarKind::Temp, at, &t, false);
            let var = self.new_var(info, &t);
            out.push(var);
        }
        if !out.is_empty() {
            let n = self.emit(span, "held by the callee", String::new());
            for &v in &out {
                self.bind(v, n);
            }
        }
        out
    }

    /// Ends the variables of `hold_generic` after the call node: the callee gives
    /// the values back or consumes them.
    fn release_generic(&mut self, held: &[VarId], span: Span) {
        if held.is_empty() || self.cur.is_none() {
            return;
        }
        let n = self.emit(span, "given back by the callee", String::new());
        for &v in held {
            self.facts.uses.push((v, n));
            self.facts.moved_at.push((v, n));
        }
    }

    /// The references that a call passes on, for a callee with signature `sig`. A
    /// result that holds references, with no stated place for each of them,
    /// points where the arguments that can flow into it point. A reference
    /// argument whose pointee holds references and that the call mutates can get
    /// the references of the other arguments, as `v.push(&x)` does.
    // The parts of one call: a struct for them would be used only here.
    #[allow(clippy::too_many_arguments)]
    fn call_flows(
        &mut self,
        sig: &FnSig,
        vals: &[ArgVal],
        arg_places: &[Vec<PlaceId>],
        ptys: &[Ty],
        muts: &[(PlaceId, u32)],
        ret: &Ty,
        out: &mut Val,
    ) {
        // A reference of the result with no stated place can point anywhere
        // inside the reference arguments. A type parameter in the result passes
        // the values of the arguments on.
        let unstated = super::flow::count_refs(&sig.ret) > sig.ret_places.len();
        let derive = self.holds_refs(ret) && (unstated || super::flow::mentions_param(&sig.ret));
        let mut args: Vec<(Ty, Vec<PlaceId>, Option<Ty>)> = Vec::new();
        for (i, av) in vals.iter().enumerate() {
            let refs = match arg_places.get(i) {
                Some(ps) if !ps.is_empty() => ps.clone(),
                _ => av.val.refs.clone(),
            };
            let declared = sig.params.get(i).map_or(Ty::Error, |p| p.ty.clone());
            let pointee = match ptys.get(i).map(|t| self.inf.shallow(t)) {
                Some(Ty::Ref(inner)) => Some(*inner),
                _ => None,
            };
            args.push((declared, refs, pointee));
        }
        if derive {
            for (declared, refs, pointee) in &args {
                let f = self.flow_refs(declared, refs, pointee.as_ref(), unstated);
                out.refs.extend(f);
            }
            out.refs.sort();
            out.refs.dedup();
        }
        // A mutated reference argument can keep a reference to any place inside the
        // other arguments, and the references in them.
        let mut flows: Option<Vec<Vec<PlaceId>>> = None;
        for (j, ps) in arg_places.iter().enumerate() {
            let holds = match ptys.get(j).map(|t| self.inf.shallow(t)) {
                Some(Ty::Ref(inner)) => self.holds_refs(&inner),
                _ => false,
            };
            if !holds {
                continue;
            }
            let (named, _) = self.split_deps(ps);
            for &p in &named {
                let root = self.facts.place(p).root;
                if !muts.iter().any(|&(m, _)| self.facts.place(m).root == root) {
                    continue;
                }
                let Some(l) = self.root_owner(root) else {
                    continue;
                };
                let all = if let Some(f) = &flows {
                    f.clone()
                } else {
                    let f: Vec<Vec<PlaceId>> = args
                        .iter()
                        .map(|(d, r, t)| self.flow_refs(d, r, t.as_ref(), true))
                        .collect();
                    flows = Some(f.clone());
                    f
                };
                for (i, f) in all.iter().enumerate() {
                    if i != j {
                        for &q in f {
                            self.point_local(l, q);
                        }
                    }
                }
            }
        }
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
                    .map(|e| effects::shown(e).to_string())
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
        let mut fn_caps = std::collections::BTreeSet::new();
        let mut fn_vals: Vec<(usize, Val)> = Vec::new();
        let mut value_refs: Vec<(usize, Vec<PlaceId>)> = Vec::new();
        let mut taken = Vec::new();
        let mut holders: Vec<(usize, Val, Span)> = Vec::new();
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
            if !matches!(self.inf.shallow(&v.ty), Ty::Fn(_))
                && (self.has_fn(&v.ty) || self.points_to_fn(&v.ty))
            {
                holders.push((i, v.clone(), a.span));
            }
            if matches!(self.inf.shallow(&v.ty), Ty::Ref(_)) {
                arg_places.push(v.refs.clone());
                held.extend(self.hold_operand(&v, later, a.span));
            } else {
                arg_places.push(Vec::new());
                // An argument that moves before the call is on its way to the callee.
                if v.summary.is_none() && self.moves_value(&v.ty) {
                    if later {
                        taken.extend(self.hold_moved(&v, "argument", a.span));
                    }
                } else if !v.refs.is_empty() {
                    held.extend(self.hold_operand(&v, later, a.span));
                }
                if let Ty::Fn(f) = self.inf.shallow(&v.ty) {
                    fns.push((i, self.fn_info(&v), f.effects.clone(), v.refs.clone()));
                    fn_caps.extend(self.val_caps(&v));
                    fn_vals.push((i, v.clone()));
                } else if !v.refs.is_empty() {
                    // A by-value argument that holds references points into them.
                    value_refs.push((i, v.refs.clone()));
                }
                if self.has_fn(&v.ty) && !matches!(self.inf.shallow(&v.ty), Ty::Fn(_)) {
                    // The callee keeps the value: it can run a function value in it.
                    self.escape_all(&v);
                    self.keep(&v, super::caps::KeptTo::Given);
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
        let performs_from = self.facts.performs_at.len();
        for v in held {
            self.facts.uses.push((v, n));
        }
        self.take_held(&taken, n);
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
            let root = if self.has_fn(&arg_tys[*i]) {
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
        // A closure that moves a capture runs once: the call takes the value. A
        // closure around this call that captures the value moves it too.
        if callee.summary.is_some_and(|s| self.closure_is_once(s)) {
            self.move_var(loc.var, n);
        }
        // The value runs with the arguments.
        self.apply_value(n, &callee, fty.effects.as_deref(), 800, &direct);
        // The value can give a function argument to an operation.
        if let Some(s) = callee.summary {
            let sum = self.closures[s].clone();
            for (i, v) in &fn_vals {
                let to: Vec<(Option<CapId>, String)> = sum
                    .op_fns
                    .iter()
                    .filter(|(p, ..)| p == i)
                    .map(|(_, c, e)| (*c, e.clone()))
                    .collect();
                self.give_to_ops(v, &to, true, span);
                for &f in &sum.items {
                    let to: Vec<(Option<CapId>, String)> = self.sigs[f]
                        .effects
                        .op_fns
                        .iter()
                        .filter(|(p, _)| p == i)
                        .map(|(_, e)| (None, e.clone()))
                        .collect();
                    self.give_to_ops(v, &to, false, span);
                }
            }
        }
        // The value can call a function argument with the places that it lends to it.
        let value = Callee::Value(callee.clone());
        for (i, info, row, refs) in fns.clone() {
            // A value that the body does not know, or one that stores the argument, keeps it.
            if self.value_keeps(&callee, i) {
                let kept = Val {
                    ty: arg_tys[i].clone(),
                    summary: info.summary,
                    ..Val::default()
                };
                self.keep(&kept, super::caps::KeptTo::Given);
            }
            // A task of the value can call the argument. A value that the body
            // does not know can start such a task too.
            let spawned = callee.param.is_some()
                || callee.summary.map_or_else(
                    || callee.item.is_none(),
                    |s| {
                        let sum = &self.closures[s];
                        sum.unknown
                            || !sum.params.is_empty()
                            || sum.tasks.contains(&i)
                            || sum
                                .items
                                .iter()
                                .any(|&f| self.sigs[f].effects.tasks.contains(&i))
                    },
                );
            if spawned {
                let span = exprs.get(i).map_or(span, |e| e.span);
                let held = fn_vals
                    .iter()
                    .find(|(j, _)| *j == i)
                    .map(|(_, v)| self.val_caps(v))
                    .unwrap_or_default();
                self.check_task_value(&info, row.as_deref(), &held, span);
            }
            let root = 810 + u32::try_from(i).unwrap_or(0);
            for p in refs {
                self.facts.call_arg.push((n, p, root));
            }
            let given = self.lent_to(&value, i, &arg_places, &roots);
            self.apply_value(n, &info, row.as_deref(), root, &given);
            self.start_ret_spawns(n, &info);
            let repeats = self.callee_repeats(&value, i);
            if repeats {
                self.note_repeat(n, &info, true);
            }
            if let Some((_, v)) = fn_vals.iter().find(|(j, _)| *j == i) {
                let v = v.clone();
                self.give_fn(n, &v, repeats, false);
            }
        }
        // A value that the body does not know can start a task that runs a
        // function value that an argument holds.
        let unknown = callee.param.is_some()
            || callee.summary.map_or_else(
                || callee.item.is_none(),
                |s| self.closures[s].unknown || !self.closures[s].params.is_empty(),
            );
        if unknown {
            for (i, v, sp) in &holders {
                let held = self.arg_held(v, &arg_places[*i]);
                self.check_task_value(&super::FnInfo::default(), None, &held, *sp);
            }
        }
        // The value can run a stored function value that an argument holds.
        if arg_tys
            .iter()
            .any(|t| !matches!(self.inf.shallow(t), Ty::Fn(_)) && self.has_fn(t))
        {
            let given = Self::any_arg(&arg_places, &roots);
            // A closure passes on the nodes in its body (`apply_stored`). Another
            // value can run a stored value any number of times.
            let again = callee.summary.is_none_or(|s| {
                let sum = &self.closures[s];
                sum.unknown || !sum.params.is_empty()
            });
            self.reach(n, &given, again);
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
        // The function values and the task handle in the result.
        let (mut caps, task) = callee.summary.map_or_else(
            || (std::collections::BTreeSet::new(), None),
            |s| {
                let sum = &self.closures[s];
                (sum.ret_caps.clone(), sum.ret_tasks.first().copied())
            },
        );
        // The value can copy a function value out of what a reference argument
        // points to: into what another one points to, or into its result. A
        // value that the body does not know can do it with each argument.
        let mut copied = std::collections::BTreeSet::new();
        for (i, ps) in arg_places.iter().enumerate() {
            if self.points_to_fn(&arg_tys[i]) {
                copied.extend(self.place_caps(ps));
            }
        }
        for (j, ps) in arg_places.iter().enumerate() {
            let changed = callee.summary.is_none_or(|s| {
                let sum = &self.closures[s];
                sum.unknown
                    || !sum.params.is_empty()
                    || sum.fn_stores.contains(&j)
                    || sum.items.iter().any(|&f| self.item_fn_stores(f))
            });
            if changed && self.points_to_fn(&arg_tys[j]) {
                self.store_caps_into(&copied, ps);
                self.note_fn_store(ps);
            }
        }
        if self.has_fn(&fty.ret) {
            // A result that is not a function value can hold a function argument.
            if !matches!(self.inf.shallow(&fty.ret), Ty::Fn(_)) {
                caps.extend(fn_caps);
            }
            caps.extend(self.resumed_at(n, performs_from));
            caps.extend(copied);
        }
        Val {
            ty,
            refs,
            summary,
            task,
            caps,
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
            depth,
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
            // The handled computation gets the value: a handler inside the clause
            // ends before it runs. The value is the result of the operation there.
            self.keep_for_op(&v, depth);
            let caps = self.val_caps(&v);
            self.resumed.entry(cap).or_default().extend(caps);
            if !v.refs.is_empty() {
                self.resume_refs_pending.push((cap, v.refs.clone()));
            }
            self.consume(&v, a.value.span);
        }
        let var = self.locals[l].var;
        self.use_local(l);
        let n = self.emit(span, "resume", "the handled computation runs".into());
        // A `once` continuation resumes at most once. A closure around the
        // resume that captures it moves it too, so the closure is `once`.
        if !multi {
            self.move_var(var, n);
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
        let mut vals = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let v = self.expr(&a.value);
            // `print` reads the whole value, also a place field in it (W0304).
            if let Some(lv) = &v.place {
                self.touch_unset(&lv.places);
            }
            for &p in &v.refs {
                self.read(p);
            }
            if i + 1 < args.len() {
                held.extend(self.hold_later(&v, "argument", a.value.span));
            }
            vals.push((v, a.value.span));
        }
        self.pend_uses.extend(held);
        let _ = self.emit(span, "print", String::new());
        // `print` only reads its arguments: a temporary goes away after it.
        for (v, s) in vals {
            self.drop_value(&v, s);
        }
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
        let mut taken = Vec::new();
        let mut caps = std::collections::BTreeSet::new();
        let mut refs = Vec::new();
        for (i, (d, arg)) in defs.iter().zip(args).enumerate() {
            let v = self.expr(&arg.value);
            let ft = super::subst(&d.ty, &targs);
            self.unify(&ft, &v.ty, arg.value.span);
            self.keep_modes(&v, &ft, arg.value.span);
            self.escape(&v);
            caps.extend(self.val_caps(&v));
            self.consume(&v, arg.value.span);
            if i + 1 < args.len() {
                self.hold_part(&v, "argument", arg.value.span, &mut held, &mut taken);
            }
            refs.extend(v.refs.iter().copied());
        }
        self.pend_uses.extend(held);
        self.take_held_here(&taken, span);
        Val {
            ty: Ty::Adt(a, targs),
            caps,
            refs,
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
        let mut taken = Vec::new();
        let mut caps = std::collections::BTreeSet::new();
        for (i, (ft, a)) in fields.iter().zip(args).enumerate() {
            let v = self.expr(&a.value);
            let ft = super::subst(ft, &targs);
            self.unify(&ft, &v.ty, a.value.span);
            self.keep_modes(&v, &ft, a.value.span);
            self.escape(&v);
            caps.extend(self.val_caps(&v));
            self.consume(&v, a.value.span);
            if i + 1 < args.len() {
                self.hold_part(&v, "argument", a.value.span, &mut held, &mut taken);
            }
            refs.extend(v.refs);
        }
        self.pend_uses.extend(held);
        self.take_held_here(&taken, span);
        Val {
            ty: Ty::Adt(adt, targs),
            refs,
            caps,
            ..Val::default()
        }
    }

    /// Performs an effect operation.
    fn perform_op(
        &mut self,
        e: usize,
        op: usize,
        args: &[Arg],
        trailing: Option<&Expr>,
        span: Span,
    ) -> Val {
        let eff = self.prog.effects[e].clone();
        let ident = effects::identity(self.prog, e);
        let o = &eff.ops[op];
        let slots = self.op_slots(o, args, trailing, span);
        // A perform is a call: each reference argument stays valid until it.
        let mut held = Vec::new();
        let mut arg_places = Vec::new();
        let mut value_refs: Vec<(usize, Vec<PlaceId>)> = Vec::new();
        let mut fns = Vec::new();
        let mut fn_args: Vec<(usize, Val, Span)> = Vec::new();
        let mut taken = Vec::new();
        for (i, pt) in o.params.iter().enumerate() {
            let Some(x) = slots[i] else {
                arg_places.push(Vec::new());
                continue;
            };
            let later = slots[i + 1..].iter().any(Option::is_some);
            let v = match (&x.kind, self.inf.shallow(pt)) {
                (ExprKind::Closure { params, body }, Ty::Fn(f)) => {
                    self.closure(params, body, Some(&f), x.span)
                }
                _ => self.expr(x),
            };
            self.unify(pt, &v.ty, x.span);
            let consumed = v.summary.is_none() && self.moves_value(&v.ty);
            if v.summary.is_none() {
                self.consume(&v, x.span);
            }
            if matches!(self.inf.shallow(&v.ty), Ty::Ref(_)) {
                arg_places.push(v.refs.clone());
                held.extend(self.hold_operand(&v, later, x.span));
            } else {
                arg_places.push(Vec::new());
                // An argument that moves is on its way to the clause.
                if consumed {
                    if later {
                        taken.extend(self.hold_moved(&v, "argument", x.span));
                    }
                } else if later || !v.refs.is_empty() {
                    held.extend(self.hold_operand(&v, later, x.span));
                }
                // A by-value argument that holds references, for example a closure,
                // points into them until the perform.
                if !v.refs.is_empty() {
                    value_refs.push((i, v.refs.clone()));
                }
                if let Ty::Fn(f) = self.inf.shallow(&v.ty) {
                    fns.push((i, self.fn_info(&v), f.effects.clone()));
                    fn_args.push((i, v.clone(), x.span));
                } else if self.has_fn(&v.ty) {
                    self.escape_all(&v);
                    fn_args.push((i, v.clone(), x.span));
                }
                // The clause can keep a function value that it gets. It runs outside
                // its own handler, where only the handlers outside the `handle` live.
                self.give_to_op(&v, &ident);
            }
        }
        self.pend_uses.extend(held);
        let n = self.emit(span, &o.name, effects::in_signature(&ident));
        self.take_held(&taken, n);
        self.perform_effect(n, &ident);
        let cap = self
            .handlers
            .iter()
            .rev()
            .find(|h| h.effect == ident)
            .map(|h| h.cap);
        if let Some(c) = cap {
            self.cap_calls.push((n, c));
            for (i, v, sp) in &fn_args {
                self.note_op_fn(c, (Some(op), Some(*i)), v, *sp);
            }
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
                if let (Some(c), false) = (cap, self.has_fn(&o.params[*i])) {
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
        // A clause can call a function argument more than once.
        for (i, info, row) in fns {
            let root = 800 + u32::try_from(i).unwrap_or(0);
            self.apply_value(n, &info, row.as_deref(), root, &given);
            self.start_ret_spawns(n, &info);
            self.note_repeat(n, &info, true);
            if let Some((_, v, _)) = fn_args.iter().find(|(j, ..)| *j == i) {
                let v = v.clone();
                self.give_fn(n, &v, true, false);
            }
        }
        if o.multi {
            self.multi_node(n);
        }
        self.abortive(n);
        // The result is what a clause resumes with.
        let mut caps = std::collections::BTreeSet::new();
        if self.has_fn(&o.ret) {
            // A clause of a handler of a caller gives a value that the body cannot
            // follow.
            caps.insert(cap.map_or(super::caps::UNKNOWN_FN, super::caps::resumed_cap));
        }
        let refs = if self.holds_refs(&o.ret) {
            self.op_result_refs(cap, Some(op))
        } else {
            Vec::new()
        };
        Val {
            ty: o.ret.clone(),
            refs,
            caps,
            ..Val::default()
        }
    }

    /// Orders the arguments of operation `o`: a named argument goes to the
    /// parameter with its name, and the others fill the free parameters in order.
    /// A trailing block goes to the last free parameter, as in a call.
    fn op_slots<'e>(
        &mut self,
        o: &crate::program::OpDef,
        args: &'e [Arg],
        trailing: Option<&'e Expr>,
        span: Span,
    ) -> Vec<Option<&'e Expr>> {
        let n = o.params.len();
        let mut slots: Vec<Option<&Expr>> = vec![None; n];
        let mut pos = 0;
        let mut extra = false;
        for a in args {
            let idx = if let Some(nm) = &a.name {
                let Some(i) = o.param_names.iter().position(|p| *p == nm.name) else {
                    let msg = format!("operation `{}` has no parameter `{}`", o.name, nm.name);
                    self.err("W0103", msg, nm.span);
                    continue;
                };
                if slots[i].is_some() {
                    let msg = format!("argument `{}` is given twice", nm.name);
                    self.err("W0103", msg, nm.span);
                    continue;
                }
                i
            } else {
                while pos < n && slots[pos].is_some() {
                    pos += 1;
                }
                pos
            };
            match slots.get_mut(idx) {
                Some(s) => *s = Some(&a.value),
                None => extra = true,
            }
        }
        if let Some(t) = trailing {
            match slots.iter().rposition(Option::is_none) {
                Some(i) => slots[i] = Some(t),
                None => extra = true,
            }
        }
        if extra || slots.iter().any(Option::is_none) {
            self.err(
                "W0103",
                format!("operation `{}` takes {} arguments", o.name, n),
                span,
            );
        }
        slots
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

    /// Starts a task for a function value at a new node. Returns the task.
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
        // The task takes the closure and runs it once.
        if let (Some(var), Some(s)) = (v.var, self.fn_info(v).summary) {
            if self.closure_is_once(s) {
                self.move_var(var, n);
            }
        }
        let info = self.fn_info(v);
        let row = match self.inf.shallow(&v.ty) {
            Ty::Fn(f) => f.effects.clone(),
            _ => None,
        };
        let held = self.val_caps(v);
        self.check_task_value(&info, row.as_deref(), &held, span);
        // A function item or parameter runs as a value with no captures.
        let s = self.value_summary(&info, row.as_deref());
        let sum = self.closures[s].clone();
        let own = |me: &Self, p: PlaceId| sum.own_roots.contains(&me.facts.place(p).root);
        // A place that the task lends can change as a mutation does.
        let mut writes: Vec<PlaceId> = sum.muts.iter().chain(&sum.lends).copied().collect();
        for &f in &sum.items {
            writes.extend(self.item_group_muts(f));
        }
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
            let refs = self.local_of(c).map(|l| &self.locals[l]).map(|l| {
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
        self.apply_summary(n, s, 700, &[]);
        (t, n)
    }

    /// The `mut` places of function item `f` below `rc` groups: a call with no
    /// arguments mutates them.
    fn item_group_muts(&mut self, f: FnId) -> Vec<PlaceId> {
        let sig = self.sigs[f].clone();
        let split = self.fresh_split();
        let mut out = Vec::new();
        for m in &sig.effects.muts {
            if matches!(m.root, SigRoot::Group(_)) {
                out.extend(self.subst_place(m, &[], split));
            }
        }
        out
    }

    /// Reports W0314 if a task that runs function value `info` can perform an
    /// operation of a handler on the stack of this task: a local handler, or the
    /// handler of a user effect, which only a caller can install. The root
    /// handlers of `sim.run` are not on a stack. `held` has the capabilities of
    /// the function values that the value holds or captures, for example in a
    /// field. A task of the body can call a function parameter: then the caller
    /// checks the value that it gives. A task that performs an effect through a
    /// handler of a caller is part of the `task_effects` of the function: the
    /// caller checks its handler.
    pub(super) fn check_task_value(
        &mut self,
        info: &super::fnval::FnInfo,
        row: Option<&[String]>,
        held: &std::collections::BTreeSet<CapId>,
        span: Span,
    ) {
        // Effects that go to a handler outside the function: of a row or of a
        // closure. A user effect has a handler on the stack of a caller.
        let mut outside: Vec<String> = row.into_iter().flatten().cloned().collect();
        // Effects of function items: they resolve against the handlers here.
        let mut here: Vec<String> = Vec::new();
        let mut items: Vec<FnId> = info.item.into_iter().collect();
        let mut params: Vec<(usize, usize)> = info.param.into_iter().collect();
        let mut own = std::collections::BTreeSet::new();
        let mut bad = false;
        if let Some(s) = info.summary {
            let sum = self.closures[s].clone();
            bad |= sum
                .performs
                .iter()
                .any(|c| self.cap_on_this_stack(*c, &sum.own_caps));
            outside.extend(sum.escapes.iter().chain(&sum.row).cloned());
            items.extend(sum.items.iter().copied());
            params.extend(sum.params.iter().map(|&p| (0, p)));
            params.extend(sum.passthrough.iter().map(|&p| (0, p)));
            own = sum.own_caps;
        }
        for f in items {
            let e = &self.sigs[f].effects;
            here.extend(e.named.iter().chain(&e.task_effects).cloned());
        }
        let held = self.expand_caps(held);
        bad |= held
            .iter()
            .any(|c| Self::is_cap(*c) && self.cap_on_this_stack(*c, &own));
        // The marks of the values in a store that the task can run.
        for m in Self::task_marks(&held) {
            match m {
                super::caps::TaskMark::Escapes(id) => {
                    outside.push(effects::identity(self.prog, id));
                }
                super::caps::TaskMark::Param(p) => params.push((0, p)),
                super::caps::TaskMark::Unknown => bad = true,
            }
        }
        // A failure of a task goes to the task that joins it, not to a handler.
        for e in outside.into_iter().filter(|e| e != "Fail") {
            if self.is_user_effect(&e) {
                bad = true;
            } else {
                self.sums[0].task_effects.insert(e);
            }
        }
        for e in here.into_iter().filter(|e| e != "Fail") {
            if self.on_this_stack(&e) {
                bad = true;
            } else if !self.handlers.iter().any(|h| h.effect == e) {
                self.sums[0].task_effects.insert(e);
            }
        }
        for (d, p) in params {
            if let Some(sum) = self.sums.get_mut(d) {
                sum.tasks.insert(p);
            }
        }
        if bad {
            self.err(
                "W0314",
                "a task cannot perform through a handler of this task: the handler runs on another task",
                span,
            );
        }
    }

    /// Reports W0314 if a task of callee `f` performs an effect through a handler on
    /// the stack of this task. An effect that no local handler handles goes to a
    /// handler of a caller: it is part of the `task_effects` of this function.
    pub(super) fn check_callee_tasks(&mut self, f: FnId, span: Span) {
        let effects = self.sigs[f].effects.task_effects.clone();
        let mut bad = false;
        for e in effects {
            match self.handlers.iter().rev().find(|h| h.effect == e) {
                Some(h) => bad |= !self.root_caps.contains(&h.cap),
                None => {
                    self.sums[0].task_effects.insert(e);
                }
            }
        }
        if bad {
            let name = self.prog.fns[f].name.clone();
            self.err(
                "W0314",
                format!("a task of `{name}` performs through a handler of this task: the handler runs on another task"),
                span,
            );
        }
    }

    /// Returns true if function item `f` can run each function argument on another
    /// thread: a foreign function, or `http.serve`.
    fn item_runs_tasks(&self, f: FnId) -> bool {
        let def = &self.prog.fns[f];
        if def.decl.body.is_some() {
            return false;
        }
        !def.is_std || (def.path == "serve" && self.prog.mods[def.module].name == "http")
    }

    /// Returns true if effect `e` is a user effect: only a local handler of a caller handles it.
    fn is_user_effect(&self, e: &str) -> bool {
        effects::by_identity(self.prog, e).is_some_and(|id| !self.prog.effects[id].is_std)
    }

    /// Returns true if a task that performs through capability `c` reaches a
    /// handler on the stack of another task: not a root handler of `sim.run`, not a
    /// handler that the task installs (`own`), and not a handler of `Fail`.
    fn cap_on_this_stack(&self, c: CapId, own: &std::collections::BTreeSet<CapId>) -> bool {
        !self.root_caps.contains(&c)
            && !own.contains(&c)
            && self.cap_effects.get(&c).is_none_or(|e| e != "Fail")
    }

    /// Returns true if an operation of effect `e` that a task performs here goes to
    /// a handler on the stack of this task: a local handler that is not a root
    /// handler of `sim.run`, or the handler of a user effect.
    fn on_this_stack(&self, e: &str) -> bool {
        // A failure of a task goes to the task that joins it.
        if e == "Fail" {
            return false;
        }
        match self.handlers.iter().rev().find(|h| h.effect == e) {
            Some(h) => !self.root_caps.contains(&h.cap),
            None => self.is_user_effect(e),
        }
    }

    fn spawn(&mut self, recv: &Val, args: &[Arg], trailing: Option<&Expr>, span: Span) -> Val {
        let Some(e) = args.first().map(|a| &a.value).or(trailing) else {
            self.err("W0103", "`spawn` takes a closure", span);
            return Val {
                ty: Ty::Error,
                ..Val::default()
            };
        };
        if args.len() + usize::from(trailing.is_some()) > 1 {
            self.err("W0103", "`spawn` takes one closure", span);
        }
        let v = self.closure_arg(e, None);
        let Some(ret) = self.task_ret(&v, "spawn", e.span) else {
            return Val {
                ty: Ty::Error,
                ..Val::default()
            };
        };
        let (t, n) = self.start_task(TaskKind::Spawn, &v, e.span);
        self.perform_effect(n, "Async");
        self.abortive(n);
        // The task joins at the end of the scope of the receiver. A receiver that
        // is not a scope binder of this body joins at the end of the outermost scope.
        let at = self
            .scopes
            .iter()
            .rposition(|(b, _)| Some(*b) == recv.local)
            .or_else(|| (!self.scopes.is_empty()).then_some(0));
        if let Some(i) = at {
            let binder = self.scopes[i].0;
            self.scopes[i].1.push(t);
            self.task_scope.insert(t, binder);
            // A closure or a clause between the scope and the spawn starts the
            // task where it runs. A body around it starts the task where it
            // runs this one (`apply_summary`).
            let depth = self.local_frame(binder);
            let body = self
                .frames
                .iter()
                .enumerate()
                .rev()
                .filter(|&(fi, _)| fi > depth)
                .find_map(|(_, f)| f.barrier);
            if let Some(si) = body {
                self.sums[si].spawns.insert(t);
            }
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

    /// Returns the result type of a task that runs `v`. Reports W0102 if `v` is not
    /// a function, and W0103 if it takes arguments: a task gets none.
    fn task_ret(&mut self, v: &Val, what: &str, span: Span) -> Option<Ty> {
        // A value whose type is not known yet, for example a closure parameter,
        // is a function with no parameters.
        if matches!(self.inf.shallow(&v.ty), Ty::Var(_)) {
            let f = Ty::Fn(Rc::new(FnTy {
                params: Vec::new(),
                ret: self.inf.fresh(),
                effects: None,
                summary: None,
                item: None,
            }));
            self.unify(&f, &v.ty, span);
        }
        let Ty::Fn(f) = self.inf.shallow(&v.ty) else {
            if !matches!(self.inf.shallow(&v.ty), Ty::Error) {
                let shown = self.show(&v.ty);
                let noun = if what == "fork" {
                    "closures"
                } else {
                    "a closure"
                };
                self.err(
                    "W0102",
                    format!("`{what}` takes {noun}, found `{shown}`"),
                    span,
                );
            }
            return None;
        };
        if !f.params.is_empty() {
            self.err(
                "W0103",
                format!("a closure of `{what}` takes no arguments"),
                span,
            );
        }
        Some(f.ret.clone())
    }

    fn fork(&mut self, args: &[Arg], trailing: Option<&Expr>, span: Span) -> Val {
        let mut tasks = Vec::new();
        let mut rets = Vec::new();
        let branches: Vec<&Expr> = args.iter().map(|a| &a.value).chain(trailing).collect();
        if branches.len() < 2 {
            self.err("W0103", "`fork` needs at least two closures", span);
        }
        for e in branches {
            let v = self.closure_arg(e, None);
            let Some(ret) = self.task_ret(&v, "fork", e.span) else {
                rets.push(Ty::Error);
                continue;
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
            self.cap_effects.insert(cap, e.clone());
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
            self.root_caps.insert(cap);
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
