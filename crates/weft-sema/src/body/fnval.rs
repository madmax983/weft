//! Function values: what a call of a closure, an item or a parameter does.
//!
//! A function value is a closure of the body, a function item, a function
//! parameter, or a value that the body does not know (from a field or a type).
//! Where control flow joins two different values, the value is a summary of both.
//!
//! A function value can mutate through the references that it gets. A call
//! gives it places: a direct call gives its arguments; a higher-order call gives
//! what the callee lends to its function parameter (the `lent` part of the
//! signature), or every reference argument when the callee is not known.

use std::collections::BTreeSet;

use super::{
    CapId, FnId, FnTy, Lower, NodeId, PlaceId, Rc, RootKind, SigRoot, Summary, TaskId, Ty, Val,
    VarId, VarKind,
};
use crate::program::{EffectDef, GivenPlace, LentPlace, RetFn, SigPlace};

/// What a function value can be. The default value is a value that the body does not know.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct FnInfo {
    /// A closure summary, also a joined one.
    pub summary: Option<usize>,
    /// A function item.
    pub item: Option<FnId>,
    /// A function parameter: the summary index of its body and the parameter index.
    pub param: Option<(usize, usize)>,
}

/// A place that a call gives to a parameter of a function value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Given {
    /// The parameter, or `None` for any parameter.
    pub pos: Option<usize>,
    /// The place. With `pos: None` the parameter can point anywhere inside it.
    pub place: PlaceId,
    /// The callee root index for `call_mut`.
    pub root: u32,
}

impl Given {
    /// The places and callee root indexes of `given`, for the operations that
    /// they reach.
    pub(super) fn args(given: &[Self]) -> Vec<(PlaceId, u32)> {
        given.iter().map(|g| (g.place, g.root)).collect()
    }
}

/// The parameter and the place of a `Given`, to compare two of them.
type GivenKey = (Option<usize>, PlaceId);

/// A place that a node gives to an operation of a local handler.
#[derive(Clone, Copy, Debug)]
pub(super) struct OpArg {
    /// The node.
    pub node: NodeId,
    /// The capability of the handler.
    pub cap: CapId,
    /// The operation, or `None` for any operation: a call that reaches the handler.
    pub op: Option<usize>,
    /// The argument position, or `None` for any. With `None` the parameter of the
    /// clause can point anywhere inside the place.
    pub pos: Option<usize>,
    /// The place.
    pub place: PlaceId,
    /// The callee root index for `call_mut`.
    pub root: u32,
    /// The innermost closure or clause summary around the node, or `None` for the function body.
    pub body: Option<usize>,
}

/// The body around a node: the function, a closure or a handler clause.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Scope {
    /// The function body.
    Function,
    /// A closure or a clause that is not finished: its summary index.
    Open(usize),
    /// A finished closure: its summary.
    Closure(usize),
    /// A finished handler clause.
    Clause,
}

/// A node where a function value that the body stores can run, with the places
/// that it gives.
#[derive(Clone, Debug)]
pub(super) struct Reach {
    /// The node.
    pub node: NodeId,
    /// The places that the node gives to the value.
    pub given: Vec<Given>,
    /// The body around the node.
    pub scope: Scope,
    /// The node can run a stored value more than once: a callee that runs it in a
    /// loop, for example.
    pub again: bool,
}

/// A node where a summary runs, with the places that it gives.
#[derive(Clone, Debug)]
pub(super) struct Applied {
    /// The summary index.
    pub summary: usize,
    /// The node.
    pub node: NodeId,
    /// The places that the node gives to the value.
    pub given: Vec<Given>,
    /// The body around the node.
    pub scope: Scope,
}

/// A function value with its effect row.
pub(super) type RowFn = (FnInfo, Option<Vec<String>>);

/// A function value that the body stores where it does not follow it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Stored {
    /// The value.
    pub info: FnInfo,
    /// The effect row of its type.
    pub row: Option<Vec<String>>,
    /// The places that the value points into: what it captures.
    pub refs: Vec<PlaceId>,
    /// A variable that points into `refs` from the store on. Each node that can run
    /// the value uses it.
    pub var: Option<VarId>,
}

/// The callee of a higher-order call.
pub(super) enum Callee {
    /// A function item.
    Item(FnId),
    /// A function value.
    Value(FnInfo),
}

/// Where a place of a summary is rooted.
enum Rooted {
    /// Below the root of parameter `k` of the value.
    Param(PlaceId, usize),
    /// Below a root that the value makes: invisible outside.
    Own,
    /// Below a root of the enclosing body.
    Outer,
}

impl Lower<'_> {
    /// Returns what a value of a function type can be.
    pub(super) fn fn_info(&self, v: &Val) -> FnInfo {
        let fty = match self.inf.shallow(&v.ty) {
            Ty::Fn(f) => Some(f),
            _ => None,
        };
        FnInfo {
            summary: v.summary.or_else(|| fty.as_ref().and_then(|f| f.summary)),
            item: v.item.or_else(|| fty.as_ref().and_then(|f| f.item)),
            param: v.fn_param,
        }
    }

    /// Returns what the function value in local `l` can be.
    pub(super) fn local_fn_info(&self, l: usize) -> FnInfo {
        let loc = &self.locals[l];
        let fty = match self.inf.shallow(&loc.ty) {
            Ty::Fn(f) => Some(f),
            _ => None,
        };
        FnInfo {
            summary: loc.summary.or_else(|| fty.as_ref().and_then(|f| f.summary)),
            item: fty.as_ref().and_then(|f| f.item),
            param: loc.fn_param,
        }
    }

    /// Returns true if a call of a function value with the effect row `row` can
    /// resume a `multi` continuation more than once. With no row the value passes
    /// the effects of its maker through, and any `multi` operation can reach it.
    pub(super) fn may_be_multi(&self, row: Option<&[String]>) -> bool {
        match row {
            Some(es) => es.iter().any(|e| self.effect_has_multi(e)),
            None => self.prog.effects.iter().any(EffectDef::has_multi),
        }
    }

    /// Joins two function values, each with its effect row: a call of the result
    /// can call either.
    pub(super) fn join_fn(&mut self, a: &RowFn, b: &RowFn) -> FnInfo {
        if a.0 == b.0 {
            return a.0.clone();
        }
        let mut m = Summary::default();
        self.add_fn(&mut m, &a.0, a.1.as_deref());
        self.add_fn(&mut m, &b.0, b.1.as_deref());
        self.closures.push(m);
        FnInfo {
            summary: Some(self.closures.len() - 1),
            ..FnInfo::default()
        }
    }

    /// Adds what a call of the function value `x` does to the summary `m`.
    pub(super) fn add_fn(&self, m: &mut Summary, x: &FnInfo, row: Option<&[String]>) {
        if let Some(s) = x.summary {
            m.union(&self.closures[s]);
        } else if let Some(f) = x.item {
            m.items.insert(f);
        } else {
            match x.param {
                Some((0, p)) => {
                    m.params.insert(p);
                }
                // A parameter of a closure: it is unknown outside the closure.
                _ => m.unknown = true,
            }
            m.may_abort = true;
            m.multi |= self.may_be_multi(row);
            m.row.extend(row.into_iter().flatten().cloned());
        }
    }

    /// Returns the summary of function value `x`. A value that is not a closure gets a
    /// new summary with what a call of it does.
    pub(super) fn value_summary(&mut self, x: &FnInfo, row: Option<&[String]>) -> usize {
        if let Some(s) = x.summary {
            return s;
        }
        let mut m = Summary::default();
        self.add_fn(&mut m, x, row);
        self.closures.push(m);
        self.closures.len() - 1
    }

    /// Returns the summary of the function value that a call of `callee` returns.
    /// `fty` is the type of the callee, `args` the places of the reference
    /// arguments of the call, and `fns` its function arguments by position. A
    /// closure states what it returns. A function item states it in its signature.
    /// A value that the body does not know returns a value that can mutate through
    /// the places that the call gives, and can run the function arguments.
    pub(super) fn result_summary(
        &mut self,
        callee: &FnInfo,
        fty: &FnTy,
        args: &[Vec<PlaceId>],
        fns: &[Option<RowFn>],
    ) -> Option<usize> {
        let Ty::Fn(rty) = self.inf.shallow(&fty.ret) else {
            return None;
        };
        let mut out = Summary::default();
        let mut items: Vec<FnId> = callee.item.into_iter().collect();
        let mut unknown = callee.summary.is_none() && callee.item.is_none();
        if let Some(s) = callee.summary {
            let sum = self.closures[s].clone();
            for &r in &sum.rets {
                let ret = self.closures[r].clone();
                out.union(&ret);
            }
            items.extend(sum.items.iter().copied());
            unknown |= sum.unknown || !sum.params.is_empty();
        }
        for f in items {
            if let Some(rf) = self.sigs[f].effects.ret.clone() {
                let r = self.ret_summary(&rf, &rty, args, fns);
                let ret = self.closures[r].clone();
                out.union(&ret);
            } else {
                out.unknown = true;
                out.may_abort = true;
            }
        }
        if unknown {
            out.unknown = true;
            out.may_abort = true;
            out.multi |= self.may_be_multi(rty.effects.as_deref());
            out.row.extend(rty.effects.iter().flatten().cloned());
            out.lends.extend(args.iter().flatten().copied());
            // The result can hold a function argument and run it later.
            for (info, row) in fns.iter().flatten() {
                self.add_fn(&mut out, info, row.as_deref());
            }
        }
        self.closures.push(out);
        let r = self.closures.len() - 1;
        // A call of the result can return what the result returns.
        let rets = self.closures[r].rets.clone();
        if rets.is_empty() {
            self.closures[r].rets.insert(r);
        }
        Some(r)
    }

    /// Joins the values of two branches. Function values inside tuples and type
    /// arguments join too.
    pub(super) fn join_val(&mut self, a: &Val, b: &Val) -> Val {
        let mut caps = self.val_caps(a);
        caps.extend(self.val_caps(b));
        if let (Ty::Fn(fa), Ty::Fn(fb)) = (self.inf.shallow(&a.ty), self.inf.shallow(&b.ty)) {
            let ia = (self.fn_info(a), fa.effects.clone());
            let ib = (self.fn_info(b), fb.effects.clone());
            let info = self.join_fn(&ia, &ib);
            return Val {
                ty: Ty::Fn(Rc::new(FnTy {
                    summary: info.summary,
                    item: info.item,
                    ..(*fa).clone()
                })),
                summary: info.summary,
                item: info.item,
                fn_param: info.param,
                caps,
                ..Val::default()
            };
        }
        let parts = match (&a.parts, &b.parts) {
            (Some(pa), Some(pb)) if pa.len() == pb.len() => {
                let mut out = Vec::new();
                for (x, y) in pa.iter().zip(pb) {
                    let mut j = self.join_val(x, y);
                    j.refs = x.refs.iter().chain(&y.refs).copied().collect();
                    j.uniq = x.uniq && y.uniq;
                    out.push(j);
                }
                Some(out)
            }
            _ => None,
        };
        let ty = if self.has_fn(&a.ty) || self.has_fn(&b.ty) {
            self.join_ty(&a.ty, &b.ty)
        } else {
            a.ty.clone()
        };
        Val {
            ty,
            parts,
            caps,
            tasks: a.tasks.union(&b.tasks).copied().collect(),
            ..Val::default()
        }
    }

    /// Returns true if a type can hold a function value.
    pub(super) fn has_fn(&self, t: &Ty) -> bool {
        self.ty_has(t, crate::props::Prop::Fns)
    }

    /// Joins the function values inside two types of the same shape.
    fn join_ty(&mut self, a: &Ty, b: &Ty) -> Ty {
        match (self.inf.shallow(a), self.inf.shallow(b)) {
            (Ty::Fn(fa), Ty::Fn(fb)) => {
                let ia = FnInfo {
                    summary: fa.summary,
                    item: fa.item,
                    param: None,
                };
                let ib = FnInfo {
                    summary: fb.summary,
                    item: fb.item,
                    param: None,
                };
                let info = self.join_fn(&(ia, fa.effects.clone()), &(ib, fb.effects.clone()));
                Ty::Fn(Rc::new(FnTy {
                    summary: info.summary,
                    item: info.item,
                    ..(*fa).clone()
                }))
            }
            (Ty::Tuple(xs), Ty::Tuple(ys)) if xs.len() == ys.len() => Ty::Tuple(
                xs.iter()
                    .zip(&ys)
                    .map(|(x, y)| self.join_ty(x, y))
                    .collect(),
            ),
            (Ty::Adt(i, xs), Ty::Adt(j, ys)) if i == j && xs.len() == ys.len() => Ty::Adt(
                i,
                xs.iter()
                    .zip(&ys)
                    .map(|(x, y)| self.join_ty(x, y))
                    .collect(),
            ),
            (Ty::Ref(x), Ty::Ref(y)) => Ty::Ref(Box::new(self.join_ty(&x, &y))),
            _ => a.clone(),
        }
    }

    // -----------------------------------------------------------------------
    // Calls of function values
    // -----------------------------------------------------------------------

    /// The function value `info` runs at node `n`. `given` names the places that the
    /// call gives to its parameters. `root` is the callee root index of its captures.
    pub(super) fn apply_value(
        &mut self,
        n: NodeId,
        info: &FnInfo,
        row: Option<&[String]>,
        root: u32,
        given: &[Given],
    ) {
        if let Some(s) = info.summary {
            self.apply_summary(n, s, root, given);
        } else if let Some(f) = info.item {
            self.apply_item(n, f, given);
        } else {
            match info.param {
                Some(dp) => self.call_param(n, dp, given),
                None => self.call_unknown(n, given),
            }
            let args = Given::args(given);
            for e in row.into_iter().flatten() {
                self.perform_at(n, e, &args);
            }
            self.abortive(n);
            if self.may_be_multi(row) {
                self.multi_node(n);
                // A caller does not see this value: the call of the body is `multi`.
                self.unknown_multi |= info.param.is_none();
            }
        }
    }

    fn rooted(&self, sum: &Summary, p: PlaceId) -> Rooted {
        let r = self.root_place(p);
        if let Some(&k) = sum.param_roots.get(&r) {
            Rooted::Param(r, k)
        } else if sum.own_roots.contains(&self.facts.place(p).root) {
            Rooted::Own
        } else {
            Rooted::Outer
        }
    }

    /// The places that place `p` below parameter root `r` (parameter `k`) stands
    /// for, from the places `given`. A result with `pos: Some(k)` is `p` moved onto a
    /// given place. A result with `pos: None` is a given place that the parameter can
    /// point anywhere inside: a change of the place covers a change below it.
    pub(super) fn through(
        &mut self,
        p: PlaceId,
        r: PlaceId,
        k: usize,
        given: &[Given],
    ) -> Vec<Given> {
        let mut out = Vec::new();
        for g in given {
            match g.pos {
                Some(i) if i == k => out.push(Given {
                    pos: Some(k),
                    place: self.rebase(p, r, g.place),
                    root: g.root,
                }),
                Some(_) => {}
                None => out.push(Given { pos: None, ..*g }),
            }
        }
        out
    }

    /// The places that place `p` of summary `sum` stands for where the summary runs
    /// with the places `given`. `root` is the callee root index of the captures.
    pub(super) fn places_of(
        &mut self,
        sum: &Summary,
        p: PlaceId,
        root: u32,
        given: &[Given],
    ) -> Vec<(PlaceId, u32)> {
        match self.rooted(sum, p) {
            Rooted::Param(r, k) => self
                .through(p, r, k, given)
                .into_iter()
                .map(|g| (g.place, g.root))
                .collect(),
            Rooted::Own => Vec::new(),
            Rooted::Outer => vec![(p, root)],
        }
    }

    /// Node `n` gives place `p` to code that can mutate through it, as callee root
    /// `root`. That code sees its parameters as separate places, so the place pairs
    /// with the other arguments of the node as a mutation does (W0312).
    pub(super) fn lend(&mut self, n: NodeId, p: PlaceId, root: u32) {
        self.facts.lends_mut.push((n, p));
        self.facts.call_mut.push((n, p, root));
        self.sum().lends.insert(p);
    }

    /// Applies a summary at a node: the function value runs there.
    pub(super) fn apply_summary(&mut self, n: NodeId, s: usize, root: u32, given: &[Given]) {
        let sum = self.closures[s].clone();
        // A stored value can run here too (`apply_stored`). An abort there leaves
        // the node.
        self.note_abort_ctx(n);
        let scope = self.scope_now();
        self.applied.push(Applied {
            summary: s,
            node: n,
            given: given.to_vec(),
            scope,
        });
        // The captured variables can have new values here.
        let at_run = !self.lowered;
        self.late_join(n, s, root, given, at_run);
        for &m in &sum.muts {
            for (q, i) in self.places_of(&sum, m, root, given) {
                self.mutate(n, q);
                self.facts.call_mut.push((n, q, i));
            }
        }
        for &r in &sum.reads {
            for (q, _) in self.places_of(&sum, r, root, given) {
                self.facts.reads_at.push((n, q));
                self.sum().reads.insert(q);
            }
        }
        for &l in &sum.lends {
            for (q, i) in self.places_of(&sum, l, root, given) {
                self.lend(n, q, i);
            }
        }
        for &(l, p) in &sum.binds {
            for (q, _) in self.places_of(&sum, p, root, given) {
                self.point_local(l, q);
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
        // The places that the value gives to operations of local handlers.
        for &(cap, op, pos, p) in &sum.op_args {
            match self.rooted(&sum, p) {
                Rooted::Param(r, k) => {
                    for g in self.through(p, r, k, given) {
                        let pos = g.pos.and(pos);
                        self.give_op(n, cap, op, pos, g.place, g.root);
                    }
                }
                Rooted::Own => {}
                Rooted::Outer => self.give_op(n, cap, op, pos, p, root),
            }
        }
        if sum.may_abort {
            self.abortive(n);
        }
        if sum.multi {
            self.multi_node(n);
            self.unknown_multi |= sum.unknown;
        }
        let pt = sum.passthrough.clone();
        self.sum().passthrough.extend(pt);
        for &f in &sum.items {
            self.apply_item(n, f, given);
        }
        for &p in &sum.params {
            self.call_param(n, (0, p), given);
        }
        if sum.unknown {
            self.call_unknown(n, given);
        }
        let args = Given::args(given);
        for e in &sum.row {
            self.perform_at(n, e, &args);
        }
        // The locals of the body go out of scope when it returns.
        for &v in &sum.dropped {
            self.facts.scope_end.push((v, n));
        }
        self.sum().dropped.extend(sum.dropped.iter().copied());
        // The tasks that the body spawns into an outer scope start here. They
        // start where the body around this node runs too, if their scope is
        // outside that body.
        for &t in &sum.spawns {
            self.facts.spawned_at.push((t, n));
        }
        let outside = self.spawns_outside(&sum.spawns.to_set());
        self.sum().spawns.extend(outside);
        self.sum().own_caps.extend(sum.own_caps.iter().copied());
    }

    /// A callee gets function value `info` at node `n` and can call what a call of
    /// it returns: the tasks that the result spawns start at `n`.
    pub(super) fn start_ret_spawns(&mut self, n: NodeId, info: &FnInfo) {
        let Some(s) = info.summary else {
            return;
        };
        let tasks = self.closures[s].ret_spawns.clone();
        for &t in &tasks {
            self.facts.spawned_at.push((t, n));
        }
        let outside = self.spawns_outside(&tasks.to_set());
        self.sum().spawns.extend(outside);
    }

    /// Returns the tasks of `spawns` whose scope is outside the closure or the
    /// clause around the current node: they start where that body runs.
    pub(super) fn spawns_outside(&self, spawns: &BTreeSet<TaskId>) -> Vec<TaskId> {
        let Some(bi) = self.frames.iter().rposition(|f| f.barrier.is_some()) else {
            return Vec::new();
        };
        spawns
            .iter()
            .copied()
            .filter(|t| {
                self.task_scope
                    .get(t)
                    .is_some_and(|&binder| self.local_frame(binder) < bi)
            })
            .collect()
    }

    /// A function item runs at node `n` with the places `given`.
    pub(super) fn apply_item(&mut self, n: NodeId, f: FnId, given: &[Given]) {
        let sig = self.sigs[f].clone();
        let split = self.fresh_split();
        for m in &sig.effects.muts {
            let mut places = Vec::new();
            match m.root {
                SigRoot::Param(i) => {
                    // A by-value parameter is a copy: the callee mutates its own
                    // value. One that holds references can mutate what they point into.
                    if !sig
                        .params
                        .get(i)
                        .is_some_and(|p| p.ty.is_ref() || self.byval_refs(&p.ty))
                    {
                        continue;
                    }
                    for g in given {
                        match g.pos {
                            Some(k) if k == i => {
                                let mut args = vec![Vec::new(); sig.params.len()];
                                args[i] = vec![g.place];
                                for q in self.subst_place(m, &args, split) {
                                    places.push((q, g.root));
                                }
                            }
                            Some(_) => {}
                            None => places.push((g.place, g.root)),
                        }
                    }
                }
                SigRoot::Group(a) => {
                    for q in self.subst_place(m, &[], split) {
                        places.push((q, 900 + u32::try_from(a).unwrap_or(0)));
                    }
                }
            }
            for (q, i) in places {
                self.mutate(n, q);
                self.facts.call_mut.push((n, q, i));
            }
        }
        let args = Given::args(given);
        for e in &sig.effects.named {
            self.perform_at(n, e, &args);
            if self.effect_has_multi(e) {
                self.multi_node(n);
            }
        }
        if !sig.effects.named.is_empty() || !sig.effects.passthrough.is_empty() {
            self.abortive(n);
        }
        let span = self.facts.node(n).span;
        self.check_callee_tasks(f, span);
    }

    /// A call of function parameter `p` of the body at summary index `d`: the
    /// parameter can mutate through what the call gives it.
    pub(super) fn call_param(&mut self, n: NodeId, (d, p): (usize, usize), given: &[Given]) {
        if d == 0 {
            self.sum().passthrough.insert(p);
        }
        self.caller_runs.push(n);
        self.note_param_run((d, p));
        for g in given {
            self.note_lent((d, p), g);
            self.lend(n, g.place, g.root);
        }
    }

    /// Records that the body at summary index `d` gives `g` to its function parameter `p`.
    fn note_lent(&mut self, (d, p): (usize, usize), g: &Given) {
        if let Some(s) = self.sums.get_mut(d) {
            if !s.lent.contains(&(p, g.pos, g.place)) {
                s.lent.push((p, g.pos, g.place));
            }
        }
    }

    /// A call of a function value that the body does not know. It can be any
    /// function parameter in scope, so each of them can get the places.
    pub(super) fn call_unknown(&mut self, n: NodeId, given: &[Given]) {
        self.caller_runs.push(n);
        let mut params = Vec::new();
        for f in &self.frames {
            for &(_, l) in &f.names {
                params.extend(self.locals[l].fn_param);
            }
        }
        params.sort_unstable();
        params.dedup();
        for dp in params {
            for g in given {
                self.note_lent(dp, g);
            }
        }
        for g in given {
            self.lend(n, g.place, g.root);
        }
        // A function value that the body stores can be this value. The call runs
        // it once.
        self.reach(n, given, false);
    }

    /// Node `n` performs effect `e` and gives the places `args` to the operation.
    /// A local handler takes it if one is in scope.
    pub(super) fn perform_at(&mut self, n: NodeId, e: &str, args: &[(PlaceId, u32)]) {
        self.perform_effect(n, e);
        if let Some(cap) = self
            .handlers
            .iter()
            .rev()
            .find(|h| h.effect == e)
            .map(|h| h.cap)
        {
            self.cap_calls.push((n, cap));
            self.note_abort_ctx(n);
            for &(p, i) in args {
                self.give_op(n, cap, None, None, p, i);
            }
        } else if self.effect_lends(e) {
            // A clause outside the function can mutate through what the operation gets.
            for &(p, i) in args {
                self.lend(n, p, i);
            }
        }
    }

    /// Records that node `n` gives place `p` to an operation of the handler behind `cap`.
    pub(super) fn give_op(
        &mut self,
        n: NodeId,
        cap: CapId,
        op: Option<usize>,
        pos: Option<usize>,
        p: PlaceId,
        root: u32,
    ) {
        let body = self.frames.iter().rev().find_map(|f| f.barrier);
        self.op_args.push(OpArg {
            node: n,
            cap,
            op,
            pos,
            place: p,
            root,
            body,
        });
        let entry = (cap, op, pos, p);
        if !self.sum().op_args.contains(&entry) {
            self.sum().op_args.push(entry);
        }
    }

    /// Returns true if an operation of effect `e` takes a reference.
    pub(super) fn effect_lends(&self, e: &str) -> bool {
        crate::effects::by_identity(self.prog, e).is_some_and(|id| {
            self.prog.effects[id]
                .ops
                .iter()
                .any(|o| o.params.iter().any(|t| self.holds_refs(t)))
        })
    }

    // -----------------------------------------------------------------------
    // Stored function values
    // -----------------------------------------------------------------------

    /// Returns the body around the current node.
    pub(super) fn scope_now(&self) -> Scope {
        self.frames
            .iter()
            .rev()
            .find_map(|f| f.barrier)
            .map_or(Scope::Function, Scope::Open)
    }

    /// Marks the records of the body with summary index `si` as finished.
    pub(super) fn close_scope(&mut self, si: usize, to: Scope) {
        for r in &mut self.reaches {
            if r.scope == Scope::Open(si) {
                r.scope = to;
            }
        }
        for a in &mut self.applied {
            if a.scope == Scope::Open(si) {
                a.scope = to;
            }
        }
    }

    /// The body stores `v` where it does not follow it: in a field, a payload, a
    /// container or a callee. A later call can run it.
    pub(super) fn escape(&mut self, v: &Val) {
        let Ty::Fn(f) = self.inf.shallow(&v.ty) else {
            return;
        };
        let mut info = self.fn_info(v);
        match info.param {
            Some((0, p)) => {
                self.sums[0].stores.insert(p);
            }
            // A closure parameter is unknown outside the closure. The closure
            // stores it: a caller gives the closure a value that it keeps.
            Some((d, p)) => {
                if let Some(s) = self.sums.get_mut(d) {
                    s.stores.insert(p);
                }
                info.param = None;
            }
            None => {}
        }
        if info == FnInfo::default() {
            return;
        }
        let row = f.effects.clone();
        if self
            .escaped
            .iter()
            .any(|e| e.info == info && e.row == row && e.refs == v.refs)
        {
            return;
        }
        // The stored value points into its captures from here on.
        let var = match self.cur {
            Some(n) if !v.refs.is_empty() => {
                let span = self.facts.node(n).span;
                let vi = self.var_info("{stored closure}", VarKind::Closure, span, &v.ty, false);
                let var = self.facts.add_var(vi);
                self.bind(var, n);
                for &p in &v.refs {
                    self.facts.points_into.push((var, p));
                }
                Some(var)
            }
            _ => None,
        };
        self.escaped.push(Stored {
            info,
            row,
            refs: v.refs.clone(),
            var,
        });
    }

    /// The body stores `v` and each function value in its parts.
    pub(super) fn escape_all(&mut self, v: &Val) {
        self.escape(v);
        for p in v.parts.iter().flatten() {
            self.escape_all(p);
        }
    }

    /// Node `n` can run a function value that the body stores, with the places
    /// `given`. With `again`, it can run the value more than once. A node in a loop
    /// or in a closure can run more than once too. Then the body can run a stored
    /// value more than once (`EffectSig::reach_repeats`).
    pub(super) fn reach(&mut self, n: NodeId, given: &[Given], again: bool) {
        self.note_abort_ctx(n);
        let scope = self.scope_now();
        self.reaches.push(Reach {
            node: n,
            given: given.to_vec(),
            scope,
            again,
        });
        let nested = !self.loops.is_empty() || self.frames.iter().any(|f| f.barrier.is_some());
        self.reach_runs.0 += 1;
        self.reach_runs.1 |= again || nested;
    }

    /// Returns true if a node that can run a stored value can come after another
    /// one. Then the body can run a stored value more than once. Two nodes on the
    /// two branches of an `if` do not count.
    pub(super) fn reaches_follow(&self) -> bool {
        let nodes: BTreeSet<NodeId> = self.reaches.iter().map(|r| r.node).collect();
        let succ = self.successors();
        for &n in &nodes {
            let mut seen = vec![false; succ.len()];
            let mut work: Vec<NodeId> = succ[n.index()].clone();
            while let Some(a) = work.pop() {
                if nodes.contains(&a) {
                    return true;
                }
                if std::mem::replace(&mut seen[a.index()], true) {
                    continue;
                }
                work.extend(succ[a.index()].iter().copied());
            }
        }
        false
    }

    /// Runs each stored function value at each node that can reach it. This runs
    /// after the body, so a node before the store in a loop gets it too. A node in
    /// a closure passes the values on to each node where the closure runs.
    pub(super) fn apply_stored(&mut self) {
        if self.escaped.is_empty() {
            return;
        }
        let escaped = self.escaped.clone();
        let applied = self.applied.clone();
        // A call of a closure that the body stores uses what the closure captures,
        // also when the value comes back from the store with its type only.
        for st in &escaped {
            let (Some(v), Some(s)) = (st.var, st.info.summary) else {
                continue;
            };
            let members = self.closures[s].members.clone();
            for a in &applied {
                if !self.closures[a.summary].members.is_disjoint(&members) {
                    self.facts.uses.push((v, a.node));
                }
            }
        }
        let mut work: Vec<Reach> = self.reaches.clone();
        let mut seen: BTreeSet<(NodeId, bool, Vec<GivenKey>)> = BTreeSet::new();
        while let Some(r) = work.pop() {
            let key = (
                r.node,
                r.again,
                r.given.iter().map(|g| (g.pos, g.place)).collect(),
            );
            if !seen.insert(key) {
                continue;
            }
            for st in &escaped {
                self.apply_value(r.node, &st.info, st.row.as_deref(), 800, &r.given);
                self.note_repeat(r.node, &st.info, false);
                // A node that runs the value more than once starts its tasks again.
                if r.again {
                    self.restart_after(r.node, &st.info);
                }
                // The value uses what it captures, and it points into it as an argument does.
                if let Some(v) = st.var {
                    self.facts.uses.push((v, r.node));
                }
                for &p in &st.refs {
                    self.facts.call_arg.push((r.node, p, 800));
                }
            }
            let Scope::Closure(id) = r.scope else {
                continue;
            };
            let runs: Vec<&Applied> = applied
                .iter()
                .filter(|a| self.closures[a.summary].members.contains(&id))
                .collect();
            for a in runs {
                let sum = self.closures[a.summary].clone();
                let mut given = Vec::new();
                for g in &r.given {
                    match self.rooted(&sum, g.place) {
                        Rooted::Param(pr, k) => {
                            for ag in self.through(g.place, pr, k, &a.given) {
                                given.push(Given {
                                    pos: ag.pos.and(g.pos),
                                    ..ag
                                });
                            }
                        }
                        Rooted::Own => {}
                        Rooted::Outer => given.push(*g),
                    }
                }
                // The node runs the closure more than once, or the closure runs
                // the value more than once.
                work.push(Reach {
                    node: a.node,
                    given,
                    scope: a.scope,
                    again: r.again || self.repeated.contains(&a.node),
                });
            }
        }
    }

    /// Runs the values that the body gives at its nodes after the body is
    /// lowered: the stored values (`apply_stored`) and the new values of the
    /// variables that the tasks capture (`finish_task_values`).
    pub(super) fn finish_values(&mut self) {
        self.lowered = true;
        let (calls_before, args_before) = (self.cap_calls.len(), self.op_args.len());
        self.finish_task_values();
        self.apply_stored();
        // Such a value can perform an operation of a handler that is lowered: its
        // clauses run at the new nodes too.
        let mut handled = std::mem::take(&mut self.handled);
        for h in &mut handled {
            let calls: Vec<NodeId> = self.cap_calls[calls_before..]
                .iter()
                .filter(|(_, c)| *c == h.cap)
                .map(|(n, _)| *n)
                .collect();
            let args: Vec<OpArg> = self.op_args[args_before..]
                .iter()
                .filter(|a| a.cap == h.cap)
                .copied()
                .collect();
            if !calls.is_empty() || !args.is_empty() {
                self.run_handler(h, &calls, &args);
                self.run_clause_caps(h, &calls);
            }
        }
        self.handled = handled;
    }

    // -----------------------------------------------------------------------
    // Higher-order calls
    // -----------------------------------------------------------------------

    /// Returns the places that `callee` can give to its function argument `i`.
    /// `args` are the reference arguments of the call by position, and `roots`
    /// their callee root indexes.
    pub(super) fn lent_to(
        &mut self,
        callee: &Callee,
        i: usize,
        args: &[Vec<PlaceId>],
        roots: &[u32],
    ) -> Vec<Given> {
        match callee {
            Callee::Item(f) => self.item_lent(*f, i, args, roots),
            Callee::Value(info) => {
                if let Some(s) = info.summary {
                    self.summary_lent(s, i, args, roots)
                } else if let Some(f) = info.item {
                    self.item_lent(f, i, args, roots)
                } else {
                    Self::any_arg(args, roots)
                }
            }
        }
    }

    /// Every reference argument, as a place that can hold the given place anywhere.
    pub(super) fn any_arg(args: &[Vec<PlaceId>], roots: &[u32]) -> Vec<Given> {
        let mut out = Vec::new();
        for (j, ps) in args.iter().enumerate() {
            for &p in ps {
                out.push(Given {
                    pos: None,
                    place: p,
                    root: roots.get(j).copied().unwrap_or(0),
                });
            }
        }
        out
    }

    fn item_lent(&mut self, f: FnId, i: usize, args: &[Vec<PlaceId>], roots: &[u32]) -> Vec<Given> {
        let sig = self.sigs[f].clone();
        // Analysis infers what a user body lends. Another function can lend anything.
        let def = &self.prog.fns[f];
        if def.is_std || def.decl.body.is_none() {
            return Self::any_arg(args, roots);
        }
        let split = self.fresh_split();
        let mut out = Vec::new();
        for lp in sig.effects.lent.iter().filter(|lp| lp.param == i) {
            let Some(sp) = &lp.place else {
                out.extend(Self::any_arg(args, roots));
                continue;
            };
            let root = match sp.root {
                SigRoot::Param(j) => roots.get(j).copied().unwrap_or(0),
                SigRoot::Group(a) => 900 + u32::try_from(a).unwrap_or(0),
            };
            for q in self.subst_place(sp, args, split) {
                out.push(Given {
                    pos: lp.arg,
                    place: q,
                    root,
                });
            }
        }
        out
    }

    fn summary_lent(
        &mut self,
        s: usize,
        i: usize,
        args: &[Vec<PlaceId>],
        roots: &[u32],
    ) -> Vec<Given> {
        let sum = self.closures[s].clone();
        let mut out = Vec::new();
        for &(_, pos, place) in sum.lent.iter().filter(|e| e.0 == i) {
            match self.rooted(&sum, place) {
                Rooted::Param(r, k) => {
                    for &a in args.get(k).map_or(&[][..], Vec::as_slice) {
                        let q = self.rebase(place, r, a);
                        let root = roots.get(k).copied().unwrap_or(0);
                        out.push(Given {
                            pos,
                            place: q,
                            root,
                        });
                    }
                }
                Rooted::Own => {}
                Rooted::Outer => out.push(Given {
                    pos,
                    place,
                    root: 800,
                }),
            }
        }
        for &f in &sum.items {
            out.extend(self.item_lent(f, i, args, roots));
        }
        if sum.unknown || !sum.params.is_empty() {
            out.extend(Self::any_arg(args, roots));
        }
        out
    }

    // -----------------------------------------------------------------------
    // Returned function values
    // -----------------------------------------------------------------------

    /// Returns what a call of the returned function value does, in the places of
    /// the parameters. `bases` are the places of the parameters.
    pub(super) fn ret_sig(&self, bases: &[Vec<PlaceId>]) -> Option<Box<RetFn>> {
        if self.rets.is_empty() {
            return None;
        }
        let mut u = Summary::default();
        for (info, row) in self.rets.clone() {
            self.add_fn(&mut u, &info, row.as_deref());
        }
        let mut out = RetFn {
            named: u.escapes.iter().chain(&u.row).cloned().collect(),
            passthrough: u.params.iter().chain(&u.passthrough).copied().collect(),
            items: u.items.to_set(),
            abort: u.may_abort,
            multi: u.multi,
            unknown: u.unknown,
            // A local handler of the function has ended when the value runs.
            op_fns: u
                .op_fns
                .iter()
                .filter(|(_, cap, _)| cap.is_none())
                .map(|(p, _, e)| (*p, e.clone()))
                .collect(),
            tasks: u.tasks.to_set(),
            ..RetFn::default()
        };
        let mut muts = (Vec::new(), Vec::new());
        let mut lends = (Vec::new(), Vec::new());
        for (ps, (outer, arg)) in [(&u.muts, &mut muts), (&u.lends, &mut lends)] {
            for &m in ps {
                match self.rooted(&u, m) {
                    Rooted::Param(_, k) => {
                        let sp = SigPlace {
                            root: SigRoot::Param(k),
                            steps: self.sig_steps(m),
                            text: self.facts.place(m).display.clone(),
                        };
                        if !arg.contains(&sp) {
                            arg.push(sp);
                        }
                    }
                    Rooted::Own => {}
                    Rooted::Outer => {
                        if let Some(sp) = self.sig_place(m, bases) {
                            if !outer.contains(&sp) {
                                outer.push(sp);
                            }
                        }
                    }
                }
            }
        }
        (out.muts, out.arg_muts) = muts;
        (out.lends, out.arg_lends) = lends;
        for &r in &u.reads {
            if matches!(self.rooted(&u, r), Rooted::Outer) {
                if let Some(sp) = self.sig_place(r, bases) {
                    if !out.reads.contains(&sp) {
                        out.reads.push(sp);
                    }
                }
            }
        }
        Some(Box::new(out))
    }

    /// Returns the places that the body lends to its function parameters, in the
    /// places of the parameters.
    pub(super) fn lent_sig(&self, bases: &[Vec<PlaceId>]) -> Vec<LentPlace> {
        let mut out = Vec::new();
        for &(param, arg, p) in &self.sums[0].lent {
            let root = self.facts.place(p).root;
            let place = match self.facts.roots[root.index()].kind {
                // A place of the caller.
                RootKind::Param | RootKind::Group => match self.sig_place(p, bases) {
                    Some(sp) => Some(sp),
                    None => continue,
                },
                // A local of the function: the caller cannot see it.
                RootKind::Local => continue,
                // A place that a closure of the function gets: it can be anything.
                RootKind::Arg => None,
            };
            let lp = LentPlace { param, arg, place };
            if !out.contains(&lp) {
                out.push(lp);
            }
        }
        out
    }

    /// Returns the places that the body gives to function values that it does not
    /// know, in the places of the parameters.
    pub(super) fn reach_sig(&self, bases: &[Vec<PlaceId>]) -> Vec<GivenPlace> {
        let mut out = Vec::new();
        for g in self.reaches.iter().flat_map(|r| &r.given) {
            let root = self.facts.place(g.place).root;
            let place = match self.facts.roots[root.index()].kind {
                RootKind::Param | RootKind::Group => match self.sig_place(g.place, bases) {
                    Some(sp) => Some(sp),
                    None => continue,
                },
                RootKind::Local => continue,
                RootKind::Arg => None,
            };
            let gp = GivenPlace { arg: g.pos, place };
            if !out.contains(&gp) {
                out.push(gp);
            }
        }
        out
    }

    /// Returns the places that callee `f` gives to a stored function value that it
    /// runs, or `None` if it cannot run one. `args` are the reference arguments of the
    /// call by position, and `roots` their callee root indexes.
    pub(super) fn reach_of(
        &mut self,
        f: FnId,
        args: &[Vec<PlaceId>],
        roots: &[u32],
    ) -> Option<Vec<Given>> {
        let def = &self.prog.fns[f];
        if def.is_std {
            return None;
        }
        // A function with no body can run anything that its arguments hold.
        if def.decl.body.is_none() {
            return Some(Self::any_arg(args, roots));
        }
        let sig = self.sigs[f].clone();
        if !sig.effects.reaches {
            return None;
        }
        let split = self.fresh_split();
        let mut out = Vec::new();
        for gp in &sig.effects.reach_given {
            let Some(sp) = &gp.place else {
                out.extend(Self::any_arg(args, roots));
                continue;
            };
            let root = match sp.root {
                SigRoot::Param(j) => roots.get(j).copied().unwrap_or(0),
                SigRoot::Group(a) => 900 + u32::try_from(a).unwrap_or(0),
            };
            for q in self.subst_place(sp, args, split) {
                out.push(Given {
                    pos: gp.arg,
                    place: q,
                    root,
                });
            }
        }
        Some(out)
    }

    /// Returns place `p` as a signature place: its root is a parameter or an `rc` group.
    pub(super) fn sig_place(&self, p: PlaceId, bases: &[Vec<PlaceId>]) -> Option<SigPlace> {
        let root = self.facts.place(p).root;
        let rp = self.root_place(p);
        // What the references behind a reference parameter point into.
        if let Some(&i) = self.held_of.get(&root) {
            let mut steps = vec![crate::program::SigStep::Held];
            steps.extend(self.sig_steps(p));
            steps.truncate(crate::infer::SIG_PLACE_STEPS as usize);
            return Some(SigPlace {
                root: SigRoot::Param(i),
                steps,
                text: self.facts.place(p).display.clone(),
            });
        }
        let sig_root = if let Some(i) = bases.iter().position(|b| b.first() == Some(&rp)) {
            SigRoot::Param(i)
        } else if let Some((&a, _)) = self.groups.iter().find(|(_, &g)| g == rp) {
            SigRoot::Group(a)
        } else {
            // A place under a parameter with an `in` clause.
            let i = bases
                .iter()
                .position(|b| b.iter().any(|&bp| self.facts.place(bp).root == root))?;
            SigRoot::Param(i)
        };
        let mut steps = self.sig_steps(p);
        steps.truncate(crate::infer::SIG_PLACE_STEPS as usize);
        Some(SigPlace {
            root: sig_root,
            steps,
            text: self.facts.place(p).display.clone(),
        })
    }

    /// Makes the summary of a function value that a call returns, from what the
    /// callee states about it. `args` are the places of the arguments, and `fns`
    /// the function arguments by position.
    pub(super) fn ret_summary(
        &mut self,
        rf: &RetFn,
        fty: &FnTy,
        args: &[Vec<PlaceId>],
        fns: &[Option<RowFn>],
    ) -> usize {
        let split = self.fresh_split();
        let mut sum = Summary::default();
        for sp in &rf.muts {
            sum.muts.extend(self.subst_place(sp, args, split));
        }
        for sp in &rf.reads {
            sum.reads.extend(self.subst_place(sp, args, split));
        }
        // The value gets its own parameter roots.
        let mut roots = Vec::new();
        for (k, pt) in fty.params.iter().enumerate() {
            if matches!(self.inf.shallow(pt), Ty::Ref(_)) {
                let r = self.facts.add_root("argument", RootKind::Arg);
                sum.own_roots.insert(self.facts.place(r).root);
                sum.param_roots.insert(r, k);
                roots.push(vec![r]);
            } else {
                roots.push(Vec::new());
            }
        }
        for sp in &rf.arg_muts {
            sum.muts.extend(self.subst_place(sp, &roots, split));
        }
        for sp in &rf.lends {
            sum.lends.extend(self.subst_place(sp, args, split));
        }
        for sp in &rf.arg_lends {
            sum.lends.extend(self.subst_place(sp, &roots, split));
        }
        // The named effects resolve at this call site, as for the call itself.
        for e in &rf.named {
            if let Some(h) = self.handlers.iter().rev().find(|h| &h.effect == e) {
                sum.performs.insert(h.cap);
                sum.multi |= h.multi;
            } else {
                sum.escapes.insert(e.clone());
                sum.multi |= self.effect_has_multi(e);
            }
        }
        sum.may_abort = rf.abort || !rf.named.is_empty();
        sum.multi |= rf.multi;
        for &j in &rf.passthrough {
            if let Some(Some((info, row))) = fns.get(j) {
                self.add_fn(&mut sum, info, row.as_deref());
            } else {
                sum.unknown = true;
                sum.may_abort = true;
            }
        }
        sum.items.extend(rf.items.iter().copied());
        sum.unknown |= rf.unknown;
        // The operations of the value go to the handlers at this call site.
        for (p, e) in &rf.op_fns {
            let cap = self
                .handlers
                .iter()
                .rev()
                .find(|h| &h.effect == e)
                .map(|h| h.cap);
            sum.op_fns.insert((*p, cap, e.clone()));
        }
        sum.tasks.extend(rf.tasks.iter().copied());
        // A call of the result can do what the result does: the effects of the
        // values that it returns are part of it.
        let r = self.closures.len();
        sum.rets.insert(r);
        self.closures.push(sum);
        r
    }
}
