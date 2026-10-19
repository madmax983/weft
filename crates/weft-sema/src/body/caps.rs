//! Capabilities: where a function value that performs through a local handler goes.
//!
//! A handler capability lives only while its handled body runs. A function value
//! that performs through the capability must not leave that body (W0313): not as
//! the result, not through a local outside the body, and not to a place or code
//! that can keep it. A value in a local of the body goes out of scope with it.

use std::collections::BTreeSet;

use super::{CapId, FnId, FnInfo, Lower, NodeId, PlaceId, RootKind, Span, Summary, Ty, Val};

/// The bit that marks a capability as `resumed_cap`.
const RESUMED: u32 = 1 << 31;

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
        if let Some(s) = self.fn_info(v).summary {
            out.extend(self.closures[s].performs.iter().copied());
            // A closure can call or return what it captures.
            for &c in &self.closures[s].captures {
                if let Some(l) = self.locals.iter().position(|l| l.var == c) {
                    out.extend(self.locals[l].caps.iter().copied());
                }
            }
        }
        for p in v.parts.iter().flatten() {
            out.extend(self.val_caps(p));
        }
        self.ty_caps(&v.ty, 0, &mut out);
        // A part of a local, for example a field, can hold what the local holds.
        let owner = v.local.or_else(|| v.place.as_ref().and_then(|p| p.owner));
        if let (Some(l), true) = (owner, self.has_fn(&v.ty, 0)) {
            out.extend(self.locals[l].caps.iter().copied());
        }
        out
    }

    /// Adds the capabilities of the closures in type `t`.
    fn ty_caps(&self, t: &Ty, depth: usize, out: &mut BTreeSet<CapId>) {
        if depth > 6 {
            return;
        }
        let t = self.inf.shallow(t);
        match &t {
            Ty::Fn(f) => {
                if let Some(s) = f.summary {
                    out.extend(self.closures[s].performs.iter().copied());
                }
            }
            Ty::Ref(inner) => self.ty_caps(inner, depth + 1, out),
            _ => {
                for f in self.adt_fields(&t) {
                    self.ty_caps(&f, depth + 1, out);
                }
            }
        }
    }

    /// Returns true if `c` is the capability of a handler, not a `resumed_cap` mark.
    pub(super) const fn is_cap(c: CapId) -> bool {
        c.0 & RESUMED == 0
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
            out.extend(self.closures[s].performs.iter().copied());
        }
        self.ty_caps(&self.locals[l].ty, 0, &mut out);
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
        if caps.is_empty() {
            return;
        }
        let mut stored = into.is_empty();
        for &p in into {
            match self.place_local(p) {
                Some(l) => self.locals[l].caps.extend(caps.iter().copied()),
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
        self.locals.iter().position(|l| l.root == Some(root))
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
            if let Some((d, p)) = v.fn_param.filter(|&(d, _)| d > 0 || cap.is_none()) {
                if let Some(s) = self.sums.get_mut(d) {
                    s.op_fns.insert((p, *cap, e.clone()));
                }
            }
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
    /// handled body that started at `start`: as its value `v`, through a local
    /// outside it, or to a place or code that can keep it.
    pub(super) fn check_cap_escape(
        &mut self,
        cap: CapId,
        effect: &str,
        start: HandleStart,
        v: &Val,
        span: Span,
    ) {
        let head = format!("a closure that performs `{effect}` escapes its handler");
        if self.expand_caps(&self.val_caps(v)).contains(&cap) {
            self.err("W0313", head, span);
            return;
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
        if how.is_none() {
            how = (0..start.locals)
                .find(|&l| self.expand_caps(&self.local_caps(l)).contains(&cap))
                .map(|l| format!("the local `{}` keeps it", self.locals[l].name));
        }
        if let Some(how) = how {
            self.err("W0313", format!("{head}: {how}"), span);
        }
    }
}
