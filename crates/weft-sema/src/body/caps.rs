//! Capabilities: where a function value that performs through a local handler goes.
//!
//! A handler capability lives only while its handled body runs. A function value
//! that performs through the capability must not leave that body (W0313): not as
//! the result, not through a local outside the body, and not to a place or code
//! that can keep it. A value in a local of the body goes out of scope with it.

use std::collections::BTreeSet;

use super::{
    effects, CapId, FnId, FnInfo, Lower, NodeId, PlaceId, RootKind, Span, Summary, Ty, Val, VarId,
};

/// The bit that marks a capability as `resumed_cap`.
const RESUMED: u32 = 1 << 31;

/// The mark of a value that holds a closure that refers to a nonportable value.
/// The mark goes where the capabilities of the value go, also into a field of
/// type `fn()` or a `Vec<fn()>`. The local that holds it is nonportable.
pub(super) const NONPORTABLE: CapId = CapId(1 << 30);

/// The mark of a value that holds a closure that is not `many`. The local that
/// holds it is not `many` either (W0503).
pub(super) const NOT_MANY: CapId = CapId(1 << 29);

/// The bit of the mark of a value that holds a closure that performs an effect
/// through a handler outside the function. The low bits are the effect.
const ESCAPES: u32 = 1 << 28;

/// The bit of the mark of a value that can hold a function value of a parameter
/// of the function. The low bits are the parameter index.
const PARAM: u32 = 1 << 27;

/// The mark of a value that can hold a function value that the body cannot
/// follow. Such a value comes from a parameter of a closure or a clause, or from
/// an operation of a handler of a caller. A task that runs it is W0314.
pub(super) const UNKNOWN_FN: CapId = CapId(1 << 26);

/// The bits of the marks: a capability with one of them is not a handler.
const MARKS: u32 = RESUMED | NONPORTABLE.0 | NOT_MANY.0 | ESCAPES | PARAM | UNKNOWN_FN.0;

/// The low bits of a mark with an index.
const INDEX: u32 = (1 << 26) - 1;

/// Returns the mark of a closure that performs effect `e` (an index in
/// `Program::effects`) through a handler outside the function.
pub(super) fn escaped_cap(e: usize) -> CapId {
    CapId(ESCAPES | (u32::try_from(e).unwrap_or(INDEX) & INDEX))
}

/// Returns the mark of a value that can hold a function value of parameter `i`.
pub(super) fn param_cap(i: usize) -> CapId {
    CapId(PARAM | (u32::try_from(i).unwrap_or(INDEX) & INDEX))
}

/// What a mark of a task value means for W0314 (`Lower::task_marks`).
pub(super) enum TaskMark {
    /// A closure performs this effect through a handler outside the function.
    Escapes(usize),
    /// A function value of this parameter of the function.
    Param(usize),
    /// A function value that the body cannot follow.
    Unknown,
}

/// Returns the mark of the values that a `resume` of the handler behind `cap` gives
/// to the handled computation. An operation result carries the mark, and
/// `Lower::expand_caps` replaces it with the capabilities of those values when the
/// clauses are lowered.
pub(super) const fn resumed_cap(cap: CapId) -> CapId {
    CapId(cap.0 | RESUMED)
}

/// A function value that can live after the node that gives it away.
#[derive(Clone, Debug)]
pub(super) struct Kept {
    /// The capabilities that a call of the value can perform through.
    pub caps: BTreeSet<CapId>,
    /// Where the value goes.
    pub to: KeptTo,
}

/// Where a kept function value goes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum KeptTo {
    /// A place that the body does not follow: a field, an element, a container or
    /// a callee that stores it.
    Stored,
    /// Code that the body does not know: it can keep the value.
    Given,
}

/// A function value that a node gives to an operation of a local handler. A
/// clause that runs its parameter as a task makes it a task (W0314).
#[derive(Clone, Debug)]
pub(super) struct OpFn {
    /// The capability of the handler.
    pub cap: CapId,
    /// The operation, or `None` for any operation: a callee performs it.
    pub op: Option<usize>,
    /// The argument position, or `None` for any.
    pub pos: Option<usize>,
    /// The value.
    pub info: FnInfo,
    /// The effect row of its type.
    pub row: Option<Vec<String>>,
    /// The capabilities of the function values that it holds.
    pub held: BTreeSet<CapId>,
    /// The span of the argument.
    pub span: Span,
}

/// The state of a handled body at its start, to find what leaves it.
#[derive(Clone, Copy, Debug)]
pub(super) struct HandleStart {
    /// The number of locals: a local below it is declared outside the body.
    pub locals: usize,
    /// The number of kept values.
    pub kept: usize,
}

impl Lower<'_> {
    /// Returns the capabilities that a call of a function value in `v` can perform
    /// through: of its summary, of its parts, and of the closures in its type.
    pub(super) fn val_caps(&self, v: &Val) -> BTreeSet<CapId> {
        let mut out = v.caps.clone();
        let info = self.fn_info(v);
        if let Some(f) = info.item {
            self.item_marks(f, &mut out);
        }
        if let Some(s) = info.summary {
            self.summary_marks(s, &mut out);
            out.extend(self.closure_caps(s));
            // A closure can call or return what it captures.
            for &c in &self.closures[s].captures {
                if let Some(l) = self.local_of(c) {
                    out.extend(self.locals[l].caps.iter().copied());
                }
            }
        }
        for p in v.parts.iter().flatten() {
            out.extend(self.val_caps(p));
        }
        self.ty_caps(&v.ty, &mut out);
        // A part of a local, for example a field, can hold what the local holds.
        let owner = v.local.or_else(|| v.place.as_ref().and_then(|p| p.owner));
        if let (Some(l), true) = (owner, self.has_fn(&v.ty)) {
            out.extend(self.locals[l].caps.iter().copied());
        }
        // A place behind a reference holds what the local that owns it holds, or
        // what the caller gives behind a reference parameter.
        if let (Some(lv), true) = (&v.place, self.has_fn(&v.ty)) {
            out.extend(self.behind_ref_marks(&lv.places));
            if lv.through_ref {
                out.extend(self.place_caps(&lv.places));
                out.extend(lv.held.iter().copied());
            }
        }
        // A reference to a value that holds function values: a copy can come out
        // of it through the reference.
        if self.points_to_fn(&v.ty) {
            out.extend(self.place_caps(&v.refs));
            out.extend(self.behind_ref_marks(&v.refs));
        }
        out
    }

    /// Returns the marks of the function values at places `ps` behind a reference
    /// parameter. A parameter of the function gives `param_cap`, also for a place
    /// behind the references that it points to. A parameter of a closure or a
    /// clause gives `UNKNOWN_FN`.
    pub(super) fn behind_ref_marks(&self, ps: &[PlaceId]) -> BTreeSet<CapId> {
        let mut out = BTreeSet::new();
        for &p in ps {
            let root = self.facts.place(p).root;
            match self.facts.roots[root.index()].kind {
                RootKind::Param => {
                    if let Some(&(0, i)) = self.param_of_root.get(&root) {
                        out.insert(param_cap(i));
                    } else if let Some(&i) = self.held_of.get(&root) {
                        out.insert(param_cap(i));
                    }
                }
                RootKind::Arg => {
                    out.insert(UNKNOWN_FN);
                }
                RootKind::Local | RootKind::Group => {}
            }
        }
        out
    }

    /// Returns the capabilities that closure `s` performs through, except those of
    /// the handlers that it installs itself.
    fn closure_caps(&self, s: usize) -> BTreeSet<CapId> {
        let sum = &self.closures[s];
        sum.performs.difference(&sum.own_caps).copied().collect()
    }

    /// Adds the marks of closure `s`: its modes, the effects that it performs
    /// through handlers outside the function, and the function parameters that
    /// it calls.
    fn summary_marks(&self, s: usize, out: &mut BTreeSet<CapId>) {
        self.mode_marks(s, out);
        let sum = &self.closures[s];
        for e in sum.escapes.iter().chain(&sum.row) {
            if let Some(id) = effects::by_identity(self.prog, e) {
                out.insert(escaped_cap(id));
            }
        }
        for &p in sum.passthrough.iter().chain(&sum.params) {
            out.insert(param_cap(p));
        }
        for &f in &sum.items {
            self.item_marks(f, out);
        }
    }

    /// Adds the marks of function item `f` as a value: the effects of its
    /// signature and of its tasks. A task that runs the item performs them where
    /// it runs, through a handler of a caller of this function.
    fn item_marks(&self, f: FnId, out: &mut BTreeSet<CapId>) {
        let e = &self.sigs[f].effects;
        for name in e.named.iter().chain(&e.task_effects) {
            if let Some(id) = effects::by_identity(self.prog, name) {
                out.insert(escaped_cap(id));
            }
        }
    }

    /// Returns what the marks in `caps` mean for a task that runs the value.
    pub(super) fn task_marks(caps: &BTreeSet<CapId>) -> Vec<TaskMark> {
        let mut out = Vec::new();
        for &c in caps {
            if c.0 & RESUMED != 0 {
                continue;
            }
            if c.0 & ESCAPES != 0 {
                out.push(TaskMark::Escapes((c.0 & INDEX) as usize));
            } else if c.0 & PARAM != 0 {
                out.push(TaskMark::Param((c.0 & INDEX) as usize));
            } else if c == UNKNOWN_FN {
                out.push(TaskMark::Unknown);
            }
        }
        out
    }

    /// Adds the capabilities of the closures in type `t`. Only an inferred type
    /// names a closure. So the walk goes through the type arguments, not through
    /// the declared field types. It is finite for a recursive type too.
    fn ty_caps(&self, t: &Ty, out: &mut BTreeSet<CapId>) {
        match self.inf.shallow(t) {
            Ty::Fn(f) => {
                if let Some(s) = f.summary {
                    self.summary_marks(s, out);
                    out.extend(self.closure_caps(s));
                }
                if let Some(g) = f.item {
                    self.item_marks(g, out);
                }
            }
            Ty::Ref(inner) | Ty::Slice(inner) | Ty::Array(inner, _) => self.ty_caps(&inner, out),
            Ty::Tuple(ts) | Ty::Adt(_, ts) => {
                for x in &ts {
                    self.ty_caps(x, out);
                }
            }
            _ => {}
        }
    }

    /// Adds the marks of the modes of closure `s`: `NONPORTABLE` and `NOT_MANY`.
    fn mode_marks(&self, s: usize, out: &mut BTreeSet<CapId>) {
        if self.closure_has(s, super::Prop::Nonportable, &mut self.has()) {
            out.insert(NONPORTABLE);
        }
        if self.closure_not_many(s) {
            out.insert(NOT_MANY);
        }
    }

    /// Gives the variable of local `l` the modes of the marks in its capabilities.
    pub(super) fn mark_modes(&mut self, l: usize) {
        let (np, nm) = (
            self.locals[l].caps.contains(&NONPORTABLE),
            self.locals[l].caps.contains(&NOT_MANY),
        );
        let v = &mut self.facts.vars[self.locals[l].var.index()];
        v.nonportable |= np;
        v.once |= nm;
    }

    /// Returns true if `c` is the capability of a handler, not a mark such as
    /// `resumed_cap`.
    pub(super) const fn is_cap(c: CapId) -> bool {
        c.0 & MARKS == 0
    }

    /// Returns `caps` with the capabilities that each `resumed_cap` mark in it stands for.
    pub(super) fn expand_caps(&self, caps: &BTreeSet<CapId>) -> BTreeSet<CapId> {
        let mut out = caps.clone();
        let mut work: Vec<CapId> = caps.iter().copied().collect();
        while let Some(c) = work.pop() {
            if Self::is_cap(c) {
                continue;
            }
            for &d in self
                .resumed
                .get(&CapId(c.0 & !RESUMED))
                .into_iter()
                .flatten()
            {
                if out.insert(d) {
                    work.push(d);
                }
            }
        }
        out
    }

    /// Returns the marks of the `resume` values of the local handlers that node `n`
    /// performs through. `from` is the length of `performs_at` before the node.
    /// The result of the node can be such a value.
    pub(super) fn resumed_at(&self, n: NodeId, from: usize) -> BTreeSet<CapId> {
        self.facts.performs_at[from.min(self.facts.performs_at.len())..]
            .iter()
            .filter(|(m, _)| *m == n)
            .map(|&(_, c)| resumed_cap(c))
            .collect()
    }

    /// Returns the capabilities of the function values in local `l`.
    fn local_caps(&self, l: usize) -> BTreeSet<CapId> {
        let mut out = self.locals[l].caps.clone();
        if let Some(s) = self.local_fn_info(l).summary {
            self.summary_marks(s, &mut out);
            out.extend(self.closure_caps(s));
        }
        self.ty_caps(&self.locals[l].ty, &mut out);
        out
    }

    /// Records that the function values in `v` go to `to`.
    pub(super) fn keep(&mut self, v: &Val, to: KeptTo) {
        let caps = self.val_caps(v);
        if !caps.is_empty() {
            self.kept.push(Kept { caps, to });
        }
    }

    /// Records that the function values in `v` go into the places `into`. A place
    /// that a local owns keeps them in the local; another place keeps them where
    /// the body does not follow them.
    pub(super) fn store_into(&mut self, v: &Val, into: &[PlaceId]) {
        let caps = self.val_caps(v);
        self.store_caps_into(&caps, into);
    }

    /// Records that a function value goes into the places `into`. A place below a
    /// reference parameter of a body is part of the `fn_stores` of that body. A
    /// caller can lose a function value there. The body is the function, a closure
    /// or a clause. A place behind a reference that a reference parameter points
    /// to counts too.
    pub(super) fn note_fn_store(&mut self, into: &[PlaceId]) {
        for &p in into {
            let root = self.facts.place(p).root;
            let at = self
                .param_of_root
                .get(&root)
                .copied()
                .or_else(|| self.held_of.get(&root).map(|&i| (0, i)));
            if let Some((d, i)) = at {
                if let Some(s) = self.sums.get_mut(d) {
                    s.fn_stores.insert(i);
                }
            }
        }
    }

    /// Records that function values with the capabilities `caps` go to `to`.
    pub(super) fn keep_caps(&mut self, caps: BTreeSet<CapId>, to: KeptTo) {
        if !caps.is_empty() {
            self.kept.push(Kept { caps, to });
        }
    }

    /// Returns the capabilities of the function values that the values at the
    /// places `ps` can hold: the values of the locals that own them.
    pub(super) fn place_caps(&self, ps: &[PlaceId]) -> BTreeSet<CapId> {
        let mut out = BTreeSet::new();
        for &p in ps {
            if let Some(l) = self.place_local(p) {
                out.extend(self.local_caps(l));
            }
        }
        out
    }

    /// Returns the capabilities and the marks of the function values that an
    /// argument `v` with places `ps` holds. They can be in its value, and in what
    /// it points to.
    pub(super) fn arg_held(&self, v: &Val, ps: &[PlaceId]) -> BTreeSet<CapId> {
        let mut out = BTreeSet::new();
        if self.has_fn(&v.ty) {
            out.extend(self.val_caps(v));
        }
        if self.points_to_fn(&v.ty) {
            out.extend(self.place_caps(ps));
            out.extend(self.behind_ref_marks(ps));
        }
        out
    }

    /// Returns true if a reference of type `t` points to a value that can hold a
    /// function value.
    pub(super) fn points_to_fn(&self, t: &Ty) -> bool {
        match self.inf.shallow(t) {
            Ty::Ref(inner) | Ty::Slice(inner) => self.has_fn(&inner),
            _ => false,
        }
    }

    /// Returns true if a reference of type `t` points to a value that can hold a
    /// reference.
    pub(super) fn points_to_refs(&self, t: &Ty) -> bool {
        match self.inf.shallow(t) {
            Ty::Ref(inner) => self.pointee_refs(&inner),
            Ty::Slice(inner) => self.holds_refs(&inner),
            _ => false,
        }
    }

    /// Records that function values with the capabilities `caps` go into the
    /// places `into`, as `store_into` does.
    pub(super) fn store_caps_into(&mut self, caps: &BTreeSet<CapId>, into: &[PlaceId]) {
        let caps = caps.clone();
        if caps.is_empty() {
            return;
        }
        let mut stored = into.is_empty();
        for &p in into {
            match self.place_local(p) {
                Some(l) => {
                    self.locals.get_mut(l).caps.extend(caps.iter().copied());
                    self.locals.get_mut(l).sticky.extend(caps.iter().copied());
                    self.mark_modes(l);
                }
                None => stored = true,
            }
        }
        if stored {
            self.kept.push(Kept {
                caps,
                to: KeptTo::Stored,
            });
        }
    }

    /// Returns the local that owns place `p`, if `p` is not behind a reference.
    fn place_local(&self, p: PlaceId) -> Option<usize> {
        let root = self.root_place(p);
        let kind = self.facts.roots[self.facts.place(root).root.index()].kind;
        if kind != RootKind::Local {
            return None;
        }
        self.root_owner(self.facts.place(root).root)
            .filter(|&l| self.locals[l].root == Some(root))
    }

    /// Records that `v` goes to code that runs where only the first `live` handlers
    /// of `Lower::handlers` are installed: the clause of an operation (the handlers
    /// outside its `handle`), or the computation that a `resume` runs. That code can
    /// keep the value, so the value must not perform through another handler.
    pub(super) fn keep_for_op(&mut self, v: &Val, live: usize) {
        let dead: BTreeSet<CapId> = self.handlers.iter().skip(live).map(|h| h.cap).collect();
        let caps: BTreeSet<CapId> = self
            .expand_caps(&self.val_caps(v))
            .intersection(&dead)
            .copied()
            .collect();
        if !caps.is_empty() {
            self.kept.push(Kept {
                caps,
                to: KeptTo::Given,
            });
        }
    }

    /// Records that function value `v` goes to operation `op` (argument `pos`) of the
    /// local handler behind `cap`, for the check of the clauses (`check_clause_tasks`).
    pub(super) fn note_op_fn(
        &mut self,
        cap: CapId,
        (op, pos): (Option<usize>, Option<usize>),
        v: &Val,
        span: Span,
    ) {
        let row = match self.inf.shallow(&v.ty) {
            Ty::Fn(f) => f.effects.clone(),
            _ => None,
        };
        let rec = OpFn {
            cap,
            op,
            pos,
            info: self.fn_info(v),
            row,
            held: self.val_caps(v),
            span,
        };
        self.op_fn_args.push(rec);
    }

    /// Reports W0314 for each function value that a node gives to an operation of
    /// the handler behind `cap` if a clause of the operation runs it as a task. The
    /// clauses are lowered, and they run in the environment of the `handle`.
    pub(super) fn check_clause_tasks(
        &mut self,
        cap: CapId,
        clauses: &[(Option<usize>, Summary, Vec<NodeId>)],
    ) {
        let recs: Vec<OpFn> = self
            .op_fn_args
            .iter()
            .filter(|a| a.cap == cap)
            .cloned()
            .collect();
        for a in recs {
            let runs = clauses.iter().any(|(oi, cs, _)| {
                (a.op.is_none() || a.op == *oi)
                    && a.pos
                        .map_or(!cs.tasks.is_empty(), |p| cs.tasks.contains(&p))
            });
            if runs {
                // A parameter of a closure that has ended: its summary is gone.
                let mut info = a.info.clone();
                if info.param.is_some_and(|(d, _)| d > 0) {
                    info.param = None;
                }
                self.check_task_value(&info, a.row.as_deref(), &a.held, a.span);
            }
        }
    }

    /// Records that function value `v` goes to an operation of effect `e`. The
    /// clause can call or keep it, and it runs where only the handlers outside the
    /// handler of `e` live. A function parameter that goes there is part of
    /// `Summary::op_fns`, so that the code that gives the parameter checks its value.
    pub(super) fn give_to_op(&mut self, v: &Val, e: &str) {
        let at = self.handlers.iter().rposition(|h| h.effect == e);
        self.keep_for_op(v, at.unwrap_or(0));
        if at.is_none() {
            self.give_to_caller_op(v, e);
        }
        let Some((d, p)) = v.fn_param else {
            return;
        };
        let cap = at.map(|i| self.handlers[i].cap);
        // A clause of this function gets a parameter of the function: the caller
        // gives the value, and the caller's handlers live here.
        if d == 0 && cap.is_some() {
            return;
        }
        if let Some(s) = self.sums.get_mut(d) {
            s.op_fns.insert((p, cap, e.to_string()));
        }
    }

    /// Function value `v` goes to a callee that gives it to operations: `to` has
    /// the capability of the receiving handler (`None`: a handler of a caller) and
    /// the effect of each operation. The operations of a closure go to the handlers
    /// where it is made (`lexical`), the operations of a function item to the
    /// handlers at the call.
    pub(super) fn give_to_ops(
        &mut self,
        v: &Val,
        to: &[(Option<CapId>, String)],
        lexical: bool,
        span: Span,
    ) {
        for (cap, e) in to {
            let local = if lexical {
                *cap
            } else {
                self.handlers
                    .iter()
                    .rev()
                    .find(|h| h.effect == *e)
                    .map(|h| h.cap)
            };
            if let Some(c) = local {
                self.note_op_fn(c, (None, None), v, span);
            }
            if !lexical {
                self.give_to_op(v, e);
                continue;
            }
            // A handler that has ended is not on the stack: the call cannot reach it.
            let live = match cap {
                Some(c) => self.handlers.iter().position(|h| h.cap == *c),
                None => Some(0),
            };
            if let Some(i) = live {
                self.keep_for_op(v, i);
            }
            if cap.is_none() {
                self.give_to_caller_op(v, e);
            }
            if let Some((d, p)) = v.fn_param.filter(|&(d, _)| d > 0 || cap.is_none()) {
                if let Some(s) = self.sums.get_mut(d) {
                    s.op_fns.insert((p, *cap, e.clone()));
                }
            }
        }
    }

    /// Function value `v` goes to an operation of effect `e` of a handler of a
    /// caller. A clause there can run it as a task. So the effects that it performs
    /// through a handler of a caller are part of `Summary::op_effects`. A parameter
    /// of the function that it holds is part of `Summary::op_fns`. The caller
    /// checks them (`callee_op_effects`).
    fn give_to_caller_op(&mut self, v: &Val, e: &str) {
        let held = self.expand_caps(&self.val_caps(v));
        for m in Self::task_marks(&held) {
            match m {
                TaskMark::Escapes(id) => {
                    let f = effects::identity(self.prog, id);
                    self.sums[0].op_effects.insert((e.to_string(), f));
                }
                TaskMark::Param(p) => {
                    self.sums[0].op_fns.insert((p, None, e.to_string()));
                }
                TaskMark::Unknown => {}
            }
        }
    }

    /// A callee gives function values to operations of handlers here: `effects`
    /// has the effect of each operation and an effect that the value performs. A
    /// local handler of the operation can run the value as a task: its clauses
    /// check it (`check_clause_tasks`). Else the operation goes to a handler of a
    /// caller, and the value goes on with it. A value that performs through a
    /// local handler that has ended when the clause runs escapes (W0313).
    pub(super) fn callee_op_effects(&mut self, effects: &BTreeSet<(String, String)>, span: Span) {
        for (e, f) in effects {
            let op_at = self.handlers.iter().rposition(|h| &h.effect == e);
            let f_at = self.handlers.iter().rposition(|h| &h.effect == f);
            let mut held = BTreeSet::new();
            match f_at {
                Some(i) => {
                    held.insert(self.handlers[i].cap);
                }
                None => {
                    if let Some(id) = effects::by_identity(self.prog, f) {
                        held.insert(escaped_cap(id));
                    }
                }
            }
            // A local handler inside the handler of the operation, or any local
            // handler for an operation of a caller, has ended in the clause.
            if let Some(fi) = f_at {
                if op_at.is_none_or(|oi| fi > oi) {
                    self.keep_caps(BTreeSet::from([self.handlers[fi].cap]), KeptTo::Given);
                }
            }
            match op_at {
                Some(oi) => {
                    let rec = OpFn {
                        cap: self.handlers[oi].cap,
                        op: None,
                        pos: None,
                        info: FnInfo::default(),
                        row: None,
                        held,
                        span,
                    };
                    self.op_fn_args.push(rec);
                }
                None if f_at.is_none() => {
                    self.sums[0].op_effects.insert((e.clone(), f.clone()));
                }
                None => {}
            }
        }
    }

    /// A callee gives argument `v` (with places `ps`) to an operation of effect
    /// `e`. The argument holds function values in a field or an element. A local
    /// handler of the operation checks them in its clauses.
    pub(super) fn give_held_to_op(&mut self, v: &Val, ps: &[PlaceId], e: &str, span: Span) {
        let held = self.arg_held(v, ps);
        if let Some(oi) = self.handlers.iter().rposition(|h| h.effect == e) {
            let rec = OpFn {
                cap: self.handlers[oi].cap,
                op: None,
                pos: None,
                info: FnInfo::default(),
                row: None,
                held,
                span,
            };
            self.op_fn_args.push(rec);
        } else {
            let v = Val {
                caps: held,
                ..Val::default()
            };
            self.give_to_caller_op(&v, e);
        }
    }

    /// Returns true if a call of function value `callee` can keep its function
    /// argument `i`: a value that the body does not know, or one that stores it.
    pub(super) fn value_keeps(&self, callee: &FnInfo, i: usize) -> bool {
        if callee.param.is_some() {
            return true;
        }
        match callee.summary {
            Some(s) => {
                let sum = &self.closures[s];
                sum.unknown
                    || !sum.params.is_empty()
                    || sum.stores.contains(&i)
                    || sum.items.iter().any(|&f| self.item_keeps(f, i))
            }
            None => callee.item.is_none_or(|f| self.item_keeps(f, i)),
        }
    }

    /// Returns true if function item `f` can keep its function argument `i`.
    fn item_keeps(&self, f: FnId, i: usize) -> bool {
        let def = &self.prog.fns[f];
        (def.decl.body.is_none() && !def.is_std) || self.sigs[f].effects.stores.contains(&i)
    }

    /// Returns the effects that clause summary `cs` performs outside its handler:
    /// the effects that escape the function, and the effects of the handlers
    /// outside the `handle` that it uses.
    pub(super) fn clause_effects(&self, cs: &Summary) -> BTreeSet<String> {
        let mut out: BTreeSet<String> = cs.escapes.iter().cloned().collect();
        for c in cs.performs.difference(&cs.own_caps) {
            if let Some(h) = self.handlers.iter().find(|h| h.cap == *c) {
                out.insert(h.effect.clone());
            }
        }
        out
    }

    /// Notes the start of the body of a handler.
    pub(super) fn handle_start(&self) -> HandleStart {
        HandleStart {
            locals: self.locals.len(),
            kept: self.kept.len(),
        }
    }

    /// Reports W0313 if a function value that performs through `cap` leaves the
    /// handled body that started at `start`: as its value `v`, or to a place or code
    /// that can keep it. Returns true if it reports. `check_local_keeps` checks the
    /// locals outside the body after the clauses.
    pub(super) fn check_cap_escape(
        &mut self,
        cap: CapId,
        effect: &str,
        start: HandleStart,
        v: &Val,
        span: Span,
    ) -> bool {
        let head = format!("a closure that performs `{effect}` escapes its handler");
        if self.expand_caps(&self.val_caps(v)).contains(&cap) {
            self.err("W0313", head, span);
            return true;
        }
        let mut how = None;
        for k in &self.kept[start.kept..] {
            if !self.expand_caps(&k.caps).contains(&cap) {
                continue;
            }
            how = Some(match k.to {
                KeptTo::Stored => "the body stores it".to_string(),
                KeptTo::Given => "the body gives it to code that can keep it".to_string(),
            });
            break;
        }
        if let Some(how) = how {
            self.err("W0313", format!("{head}: {how}"), span);
            return true;
        }
        false
    }

    /// Reports W0313 if a local outside the body of the handled computation `h`
    /// can hold a function value after the body. The value performs through the
    /// capability of `h`. The checked nodes are the end of the `handle` and the
    /// abort nodes of `exits` that leave the body. A pair of `exits` has the abort
    /// node and the number of locals when the body of its target starts. Only a
    /// local below that number lives on there. A new value of the whole local in
    /// the same part of the graph counts only if it reaches one of these nodes
    /// (`Lower::bind_caps`). Other values count always (`Local::sticky`).
    pub(super) fn check_local_keeps(
        &mut self,
        h: &super::Handled,
        effect: &str,
        exits: &[(NodeId, usize)],
        span: Span,
    ) {
        let cap = h.cap;
        let mut keeps: Option<usize> =
            (0..h.locals).find(|&l| self.expand_caps(&self.locals[l].sticky).contains(&cap));
        if keeps.is_none() {
            let binds: Vec<(usize, VarId, NodeId)> = self
                .bind_caps
                .iter()
                .filter_map(|(v, n, cs)| {
                    let l = self.local_of(*v).filter(|&l| l < h.locals)?;
                    self.expand_caps(cs).contains(&cap).then_some((l, *v, *n))
                })
                .collect();
            if !binds.is_empty() {
                let succ = self.successors();
                for (l, var, n) in binds {
                    let kills: BTreeSet<NodeId> = self
                        .facts
                        .rebound_at
                        .iter()
                        .filter(|(v, _)| *v == var)
                        .map(|&(_, m)| m)
                        .collect();
                    let mut targets = BTreeSet::from([h.end]);
                    targets.extend(
                        exits
                            .iter()
                            .filter(|&&(_, locals)| l < locals)
                            .map(|&(u, _)| u),
                    );
                    if Self::reaches_past(&succ, n, &targets, &kills) {
                        keeps = Some(l);
                        break;
                    }
                }
            }
        }
        if let Some(l) = keeps {
            let name = self.locals[l].name.clone();
            self.err(
                "W0313",
                format!("a closure that performs `{effect}` escapes its handler: the local `{name}` keeps it"),
                span,
            );
        }
    }

    /// Returns the successors of each node, by node index.
    pub(super) fn successors(&self) -> Vec<Vec<NodeId>> {
        let mut succ = vec![Vec::new(); self.facts.nodes.len()];
        for &(a, b) in &self.facts.cfg_edge {
            succ[a.index()].push(b);
        }
        succ
    }

    /// Returns true if a path of the successors `succ` leads from a successor of
    /// node `from` to a node of `to`. The path must not pass through a node of
    /// `kills` first.
    fn reaches_past(
        succ: &[Vec<NodeId>],
        from: NodeId,
        to: &BTreeSet<NodeId>,
        kills: &BTreeSet<NodeId>,
    ) -> bool {
        let mut seen = vec![false; succ.len()];
        let mut work: Vec<NodeId> = succ[from.index()].clone();
        while let Some(a) = work.pop() {
            if to.contains(&a) {
                return true;
            }
            if kills.contains(&a) || std::mem::replace(&mut seen[a.index()], true) {
                continue;
            }
            work.extend(succ[a.index()].iter().copied());
        }
        false
    }
}
