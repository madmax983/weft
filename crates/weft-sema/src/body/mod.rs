//! Lowering of function bodies to facts.
//!
//! The lowering walks the AST once. It infers types, computes places, and writes a
//! control-flow graph where each node does one thing. A node uses its inputs
//! before it mutates places, so a use and a mutation can share a node.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use std::sync::Arc;

use weft_facts::{
    CapId, FnFacts, HandlerInfo, NodeId, PlaceId, RootId, RootKind, Span, Step, StepKind, TaskId,
    TaskKind, VarId, VarInfo, VarKind,
};
use weft_syntax::ast::{
    self, Arg, AssignOp, BinOp, Block, Expr, ExprKind, Lit, Pattern, Stmt, StmtKind, StrPart, UnOp,
};
use weft_syntax::diag::Diagnostic;

use crate::effects;
use crate::program::{
    elem_step, field_step, AdtKind, Builtins, Deref, EffectSig, FnId, FnSig, ItemRef, ModId,
    Program, SigPlace, SigRoot, SigStep, PRELUDE,
};
use crate::props::Prop;
use crate::types::{subst, Display, FnTy, Infer, IntTy, Ty};

mod aborts;
mod args;
mod call;
mod caps;
mod drops;
mod exhaust;
mod expr;
mod flow;
mod fnval;
mod late;
pub mod loops;
mod oprefs;
mod repeat;
pub(crate) mod roots;
mod stmt;
mod tasks;

use fnval::{Applied, FnInfo, Given, OpArg, Reach};

/// A set that only grows during a loop pass, with the order of its elements.
///
/// A loop pass takes its size at the head ([`Grow::mark`]). A rewind removes
/// the elements after it ([`Grow::cut`]). So a rewind costs as much as the
/// elements of the pass, not as much as the whole set. An empty set has no
/// allocation, and the value is one pointer, so a [`Summary`] stays small on
/// the stack.
#[derive(Clone, Debug)]
pub struct Grow<T>(Option<Box<GrowInner<T>>>);

#[derive(Clone, Debug)]
struct GrowInner<T> {
    set: BTreeSet<T>,
    order: Vec<T>,
}

/// The iterator of a [`Grow`] set.
pub type GrowIter<'a, T> =
    std::iter::Flatten<std::option::IntoIter<std::collections::btree_set::Iter<'a, T>>>;

impl<T> Default for Grow<T> {
    fn default() -> Self {
        Self(None)
    }
}

impl<T: Ord> PartialEq for Grow<T> {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Some(a), Some(b)) => a.set == b.set,
            (Some(x), None) | (None, Some(x)) => x.set.is_empty(),
            (None, None) => true,
        }
    }
}

impl<T: Ord> Eq for Grow<T> {}

impl<T: Ord + Clone> Grow<T> {
    /// Adds `x`. Returns true if it is new.
    pub fn insert(&mut self, x: T) -> bool {
        let inner = self.0.get_or_insert_with(|| {
            Box::new(GrowInner {
                set: BTreeSet::new(),
                order: Vec::new(),
            })
        });
        if inner.set.insert(x.clone()) {
            inner.order.push(x);
            true
        } else {
            false
        }
    }

    /// Returns true if the set has `x`.
    pub fn contains(&self, x: &T) -> bool {
        self.0.as_ref().is_some_and(|g| g.set.contains(x))
    }

    /// The elements, in their order.
    pub fn iter(&self) -> GrowIter<'_, T> {
        self.0.as_ref().map(|g| g.set.iter()).into_iter().flatten()
    }

    /// The number of elements.
    pub fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |g| g.set.len())
    }

    /// Returns true if the set has no element.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The least element.
    pub fn first(&self) -> Option<&T> {
        self.0.as_ref().and_then(|g| g.set.first())
    }

    /// Removes each element.
    pub fn clear(&mut self) {
        self.0 = None;
    }

    /// A copy of the set.
    pub fn to_set(&self) -> BTreeSet<T> {
        self.0
            .as_ref()
            .map_or_else(BTreeSet::new, |g| g.set.clone())
    }

    /// The elements that `other` does not have.
    pub fn difference<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = &'a T> + 'a {
        self.iter().filter(move |x| !other.contains(x))
    }

    /// Returns true if the set has no element of `other`.
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.iter().all(|x| !other.contains(x))
    }

    /// The size now, for [`Grow::cut`].
    pub fn mark(&self) -> usize {
        self.0.as_ref().map_or(0, |g| g.order.len())
    }

    /// Removes the elements that came after `mark`.
    pub fn cut(&mut self, mark: usize) {
        if let Some(g) = &mut self.0 {
            let from = mark.min(g.order.len());
            for x in g.order.drain(from..) {
                g.set.remove(&x);
            }
        }
    }
}

impl<T: Ord + Clone> Extend<T> for Grow<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for x in iter {
            self.insert(x);
        }
    }
}

impl<'a, T: Ord + Clone + 'a> Extend<&'a T> for Grow<T> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        for x in iter {
            self.insert(x.clone());
        }
    }
}

impl<T: Ord + Clone> FromIterator<T> for Grow<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut g = Self::default();
        g.extend(iter);
        g
    }
}

impl<T: Ord + Clone> From<BTreeSet<T>> for Grow<T> {
    fn from(set: BTreeSet<T>) -> Self {
        set.into_iter().collect()
    }
}

impl<T> IntoIterator for Grow<T> {
    type Item = T;
    type IntoIter =
        std::iter::Flatten<std::option::IntoIter<std::collections::btree_set::IntoIter<T>>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.map(|g| g.set.into_iter()).into_iter().flatten()
    }
}

impl<'a, T: Ord + Clone> IntoIterator for &'a Grow<T> {
    type Item = &'a T;
    type IntoIter = GrowIter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// A call in a closure that gives a captured local to a `@ uniq` parameter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct UniqNeed {
    /// The name of the callee.
    pub callee: String,
    /// The name of the parameter.
    pub param: String,
    /// The name of the local.
    pub local: String,
}

/// The sizes of a [`Summary`] at a loop head: a rewind cuts it back to them.
#[derive(Clone, Debug)]
pub(super) struct SumMark {
    muts: usize,
    reads: usize,
    escapes: usize,
    performs: usize,
    passthrough: usize,
    own_roots: usize,
    captures: usize,
    moved_captures: usize,
    dropped: usize,
    items: usize,
    params: usize,
    row: usize,
    members: usize,
    stores: usize,
    lends: usize,
    rets: usize,
    spawns: usize,
    own_caps: usize,
    tasks: usize,
    ret_caps: usize,
    ret_tasks: usize,
    op_fns: usize,
    task_effects: usize,
    repeats: usize,
    fn_stores: usize,
    op_effects: usize,
    ret_spawns: usize,
    ret_refs: usize,
    lent: usize,
    op_args: usize,
    binds: usize,
    cap_runs: usize,
    uniq_needs: usize,
    param_calls: usize,
    param_stores: usize,
    may_abort: bool,
    repeat_runs: bool,
    multi: bool,
    literal: bool,
    unknown: bool,
    param_roots: BTreeMap<PlaceId, usize>,
}

/// What a body does, in the places of the enclosing function.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Summary {
    /// Mutated places.
    pub muts: Grow<PlaceId>,
    /// Read places.
    pub reads: Grow<PlaceId>,
    /// Effects that no local handler handles.
    pub escapes: Grow<String>,
    /// Local capabilities used.
    pub performs: Grow<CapId>,
    /// Some node can abort.
    pub may_abort: bool,
    /// Some node can resume a `multi` continuation.
    pub multi: bool,
    /// Function parameters that the body calls.
    pub passthrough: Grow<usize>,
    /// Roots made inside the body. They are not visible outside.
    pub own_roots: Grow<RootId>,
    /// Variables of the enclosing function that the body uses.
    pub captures: Grow<VarId>,
    /// Captured variables that the body moves.
    pub moved_captures: Grow<VarId>,
    /// Owners that the body declares. They go out of scope when the body returns.
    pub dropped: Grow<VarId>,
    /// The places that the result of a closure points into.
    pub ret_refs: Vec<PlaceId>,
    /// The root place of each reference parameter of a function value, with the
    /// parameter index. A place below it stands for a place that the call gives.
    pub param_roots: BTreeMap<PlaceId, usize>,
    /// The value is a closure of the body, or can be one: it moves, it is not copied.
    pub literal: bool,
    /// Function items that a call of the value can call. Their effects resolve where it is called.
    pub items: Grow<FnId>,
    /// Function parameters that the value can be.
    pub params: Grow<usize>,
    /// The value can be a function value that the body does not know.
    pub unknown: bool,
    /// Effects that a call of the value performs where it is called: the effect
    /// rows of the parameters and unknown values that it can be.
    pub row: Grow<String>,
    /// Places that the body gives to its function parameters: the parameter, the
    /// argument position (`None`: any position), and the place.
    pub lent: Vec<(usize, Option<usize>, PlaceId)>,
    /// Places that the body gives to operations of local handlers: the capability,
    /// the operation and the argument position (`None`: any), and the place.
    pub op_args: Vec<(CapId, Option<usize>, Option<usize>, PlaceId)>,
    /// The closures of the body that the value can be.
    pub members: Grow<usize>,
    /// Function parameters that the body stores. For a closure: its own parameters.
    pub stores: Grow<usize>,
    /// Places that the body gives to code that can mutate through them: a function
    /// parameter, an unknown function value or an operation of an outer handler.
    pub lends: Grow<PlaceId>,
    /// The summaries of the function values that a call of the value returns.
    pub rets: Grow<usize>,
    /// Locals outside the body that the body gives a place below one of its
    /// parameters: the local and the place.
    pub binds: Vec<(usize, PlaceId)>,
    /// Tasks that the body spawns into a scope outside it. Each node where the
    /// body runs starts them.
    pub spawns: Grow<TaskId>,
    /// Capabilities of the handlers that the body installs.
    pub own_caps: Grow<CapId>,
    /// The nodes of the body of a closure: from its entry to the one after its
    /// last node. A nested closure is inside.
    pub nodes: (u32, u32),
    /// Function parameters of the value that a task of its body can call.
    pub tasks: Grow<usize>,
    /// The capabilities of the function values inside the values that a call of
    /// the value returns, also inside a tuple or a struct.
    pub ret_caps: Grow<caps::Held>,
    /// The tasks of the task handles that a call of the value returns.
    pub ret_tasks: Grow<TaskId>,
    /// Function parameters that the body gives to an operation, with the
    /// capability of a local handler outside the body (`None`: a handler of a
    /// caller) and the effect. The clause can call or keep them.
    pub op_fns: Grow<(usize, Option<CapId>, String)>,
    /// Effects that a task of the body performs through a handler outside the function.
    pub task_effects: Grow<String>,
    /// Function parameters that the body can call more than once.
    pub repeats: Grow<usize>,
    /// Reference parameters whose pointee can get a function value from the body.
    pub fn_stores: Grow<usize>,
    /// The function values that the body gives to an operation of a handler of a
    /// caller. Each pair has the effect of the operation, and an effect that the
    /// value performs through a handler of a caller.
    pub op_effects: Grow<(String, String)>,
    /// Tasks that the function values that a call of the value returns spawn into
    /// a scope outside. A callee that calls such a result starts them.
    pub ret_spawns: Grow<TaskId>,
    /// The runs of captured function variables in the body: the variable and the
    /// places that the body gives to it there. A node that runs the closure runs
    /// the value that the variable has there (`Lower::late_join`).
    cap_runs: Vec<(VarId, Vec<Given>)>,
    /// Captured variables that the body gives to a parameter that must be
    /// `@ uniq`. A node that runs the closure checks that the variable is
    /// still `@ uniq` there (W0406, `not_uniq`).
    uniq_needs: Vec<(VarId, UniqNeed)>,
    /// The function parameters of the function that the body calls. Each has
    /// true if the call can run more than once in one run of the body: in a loop
    /// or in a closure inside the body. Each has true too if the call is in the
    /// body itself, not in a closure inside it. A call in a closure counts for
    /// the function where the closure runs (`Lower::repeats_sig`).
    pub param_calls: Vec<(usize, bool, bool)>,
    /// A call of the value runs a function value that it holds more than once:
    /// the value that a function returns calls a function argument more than
    /// once (`RetFn::repeats`).
    pub repeat_runs: bool,
    /// References that the body gets in its own parameters and puts behind a
    /// reference parameter of the function or into an `rc` object. Each has the
    /// place where they go, the place below the parameter, and the span. A node
    /// that runs the body puts the places that it gives there.
    param_stores: Vec<(PlaceId, PlaceId, Span)>,
}

impl Summary {
    /// The sizes now, for [`Summary::cut`]. Each field is named, so that a new
    /// field gets a decision here.
    pub(super) fn mark(&self) -> SumMark {
        let Self {
            muts,
            reads,
            escapes,
            performs,
            may_abort,
            multi,
            passthrough,
            own_roots,
            captures,
            moved_captures,
            dropped,
            ret_refs,
            param_roots,
            literal,
            items,
            params,
            unknown,
            row,
            lent,
            op_args,
            members,
            stores,
            lends,
            rets,
            binds,
            spawns,
            own_caps,
            tasks,
            ret_caps,
            ret_tasks,
            op_fns,
            task_effects,
            repeats,
            fn_stores,
            op_effects,
            ret_spawns,
            cap_runs,
            uniq_needs,
            param_calls,
            repeat_runs,
            param_stores,
            // Set when the closure ends, after each pass of a loop in it.
            nodes: _,
        } = self;
        SumMark {
            muts: muts.mark(),
            reads: reads.mark(),
            escapes: escapes.mark(),
            performs: performs.mark(),
            passthrough: passthrough.mark(),
            own_roots: own_roots.mark(),
            captures: captures.mark(),
            moved_captures: moved_captures.mark(),
            dropped: dropped.mark(),
            items: items.mark(),
            params: params.mark(),
            row: row.mark(),
            members: members.mark(),
            stores: stores.mark(),
            lends: lends.mark(),
            rets: rets.mark(),
            spawns: spawns.mark(),
            own_caps: own_caps.mark(),
            tasks: tasks.mark(),
            ret_caps: ret_caps.mark(),
            ret_tasks: ret_tasks.mark(),
            op_fns: op_fns.mark(),
            task_effects: task_effects.mark(),
            repeats: repeats.mark(),
            fn_stores: fn_stores.mark(),
            op_effects: op_effects.mark(),
            ret_spawns: ret_spawns.mark(),
            ret_refs: ret_refs.len(),
            lent: lent.len(),
            op_args: op_args.len(),
            binds: binds.len(),
            cap_runs: cap_runs.len(),
            uniq_needs: uniq_needs.len(),
            param_calls: param_calls.len(),
            param_stores: param_stores.len(),
            may_abort: *may_abort,
            repeat_runs: *repeat_runs,
            multi: *multi,
            literal: *literal,
            unknown: *unknown,
            param_roots: param_roots.clone(),
        }
    }

    /// Goes back to the sizes of `mark`: a loop pass only adds to a summary.
    pub(super) fn cut(&mut self, mark: SumMark) {
        let Self {
            muts,
            reads,
            escapes,
            performs,
            may_abort,
            multi,
            passthrough,
            own_roots,
            captures,
            moved_captures,
            dropped,
            ret_refs,
            param_roots,
            literal,
            items,
            params,
            unknown,
            row,
            lent,
            op_args,
            members,
            stores,
            lends,
            rets,
            binds,
            spawns,
            own_caps,
            tasks,
            ret_caps,
            ret_tasks,
            op_fns,
            task_effects,
            repeats,
            fn_stores,
            op_effects,
            ret_spawns,
            cap_runs,
            uniq_needs,
            param_calls,
            repeat_runs,
            param_stores,
            // Set when the closure ends, after each pass of a loop in it.
            nodes: _,
        } = self;
        muts.cut(mark.muts);
        reads.cut(mark.reads);
        escapes.cut(mark.escapes);
        performs.cut(mark.performs);
        passthrough.cut(mark.passthrough);
        own_roots.cut(mark.own_roots);
        captures.cut(mark.captures);
        moved_captures.cut(mark.moved_captures);
        dropped.cut(mark.dropped);
        items.cut(mark.items);
        params.cut(mark.params);
        row.cut(mark.row);
        members.cut(mark.members);
        stores.cut(mark.stores);
        lends.cut(mark.lends);
        rets.cut(mark.rets);
        spawns.cut(mark.spawns);
        own_caps.cut(mark.own_caps);
        tasks.cut(mark.tasks);
        ret_caps.cut(mark.ret_caps);
        ret_tasks.cut(mark.ret_tasks);
        op_fns.cut(mark.op_fns);
        task_effects.cut(mark.task_effects);
        repeats.cut(mark.repeats);
        fn_stores.cut(mark.fn_stores);
        op_effects.cut(mark.op_effects);
        ret_spawns.cut(mark.ret_spawns);
        ret_refs.truncate(mark.ret_refs);
        lent.truncate(mark.lent);
        op_args.truncate(mark.op_args);
        binds.truncate(mark.binds);
        cap_runs.truncate(mark.cap_runs);
        uniq_needs.truncate(mark.uniq_needs);
        param_calls.truncate(mark.param_calls);
        param_stores.truncate(mark.param_stores);
        *may_abort = mark.may_abort;
        *repeat_runs = mark.repeat_runs;
        *multi = mark.multi;
        *literal = mark.literal;
        *unknown = mark.unknown;
        *param_roots = mark.param_roots;
    }
}

/// The state of a property query (`Lower::ty_has`).
#[derive(Default)]
pub(super) struct Has {
    /// The closure summaries on the way.
    seen: Vec<usize>,
    /// A value of a type parameter counts as linear.
    params: bool,
}

impl Summary {
    /// Adds what `o` does: a call of the result can do either.
    fn union(&mut self, o: &Self) {
        self.muts.extend(o.muts.iter().copied());
        self.reads.extend(o.reads.iter().copied());
        self.escapes.extend(o.escapes.iter().cloned());
        self.performs.extend(o.performs.iter().copied());
        self.may_abort |= o.may_abort;
        self.multi |= o.multi;
        self.passthrough.extend(o.passthrough.iter().copied());
        self.own_roots.extend(o.own_roots.iter().copied());
        self.captures.extend(o.captures.iter().copied());
        self.moved_captures.extend(o.moved_captures.iter().copied());
        self.dropped.extend(o.dropped.iter().copied());
        self.ret_refs.extend(o.ret_refs.iter().copied());
        self.param_roots
            .extend(o.param_roots.iter().map(|(&r, &i)| (r, i)));
        self.literal |= o.literal;
        self.items.extend(o.items.iter().copied());
        self.params.extend(o.params.iter().copied());
        self.unknown |= o.unknown;
        self.row.extend(o.row.iter().cloned());
        self.lent.extend(o.lent.iter().copied());
        self.op_args.extend(o.op_args.iter().copied());
        self.members.extend(o.members.iter().copied());
        self.stores.extend(o.stores.iter().copied());
        self.lends.extend(o.lends.iter().copied());
        self.rets.extend(o.rets.iter().copied());
        for b in &o.binds {
            if !self.binds.contains(b) {
                self.binds.push(*b);
            }
        }
        self.spawns.extend(o.spawns.iter().copied());
        self.own_caps.extend(o.own_caps.iter().copied());
        self.tasks.extend(o.tasks.iter().copied());
        self.ret_caps.extend(o.ret_caps.iter().copied());
        self.ret_tasks.extend(o.ret_tasks.iter().copied());
        self.op_fns.extend(o.op_fns.iter().cloned());
        self.task_effects.extend(o.task_effects.iter().cloned());
        self.repeats.extend(o.repeats.iter().copied());
        self.ret_spawns.extend(o.ret_spawns.iter().copied());
        self.fn_stores.extend(o.fn_stores.iter().copied());
        self.op_effects.extend(o.op_effects.iter().cloned());
        for r in &o.cap_runs {
            if !self.cap_runs.contains(r) {
                self.cap_runs.push(r.clone());
            }
        }
        for u in &o.uniq_needs {
            if !self.uniq_needs.contains(u) {
                self.uniq_needs.push(u.clone());
            }
        }
        self.param_calls.extend(o.param_calls.iter().copied());
        self.repeat_runs |= o.repeat_runs;
        for st in &o.param_stores {
            if !self.param_stores.contains(st) {
                self.param_stores.push(*st);
            }
        }
    }

    /// Adds what a call of the function value that `o` stands for can do. A call of
    /// the result runs it later, and a callee that calls the result sees it here.
    /// The tasks of `o` start where a call of the result runs, or where a callee
    /// gets this value (`ret_spawns`).
    fn union_ret(&mut self, o: &Self) {
        let mut o = o.clone();
        o.ret_spawns.extend(std::mem::take(&mut o.spawns));
        o.ret_refs.clear();
        o.dropped.clear();
        o.rets.clear();
        o.tasks.clear();
        o.ret_caps.clear();
        o.ret_tasks.clear();
        o.op_fns.clear();
        o.repeats.clear();
        o.fn_stores.clear();
        o.op_effects.clear();
        o.cap_runs.clear();
        o.uniq_needs.clear();
        o.param_stores.clear();
        o.literal = false;
        self.union(&o);
    }
}

/// The result of lowering one function.
#[derive(Clone, Debug)]
pub struct Lowered {
    /// The facts.
    pub facts: FnFacts,
    /// The effects of the body, for signature inference.
    pub effects: EffectSig,
    /// Type and signature diagnostics.
    pub diags: Vec<Diagnostic>,
    /// The work of the lowering.
    pub work: crate::Work,
}

#[derive(Clone, Debug)]
struct ContInfo {
    arg: Ty,
    ret: Ty,
    multi: bool,
    muts: Vec<PlaceId>,
    /// The places that the handled body frees: a move of a local from outside the
    /// `handle`, or of a part of it. A resume frees them (`releases_at`).
    frees: Vec<PlaceId>,
    cap: CapId,
    /// The depth of `Lower::handlers` in the clause: a handler above it is inside the clause.
    depth: usize,
    /// The clause is a clause of `Fail.fail`: it cannot resume (W0504).
    fail: bool,
}

#[derive(Clone, Debug)]
struct Local {
    name: String,
    var: VarId,
    ty: Ty,
    root: Option<PlaceId>,
    /// The root place of the variable of a reference local: the memory that
    /// holds the reference, not the memory that it points to. It has no owner.
    /// A use and a new value of the local access it (W0405). An owned local
    /// uses `root` for this.
    cell: Option<PlaceId>,
    refs: Vec<PlaceId>,
    /// The tasks of the task handles that the local can hold.
    tasks: BTreeSet<TaskId>,
    summary: Option<usize>,
    /// A function parameter: the summary index of its body and the parameter index.
    fn_param: Option<(usize, usize)>,
    cont: Option<ContInfo>,
    /// The local has a value: a new value joins the function values.
    bound: bool,
    /// The index and the number (`Frame::id`) of the frame that declares it.
    frame: (usize, usize),
    /// The capabilities of the function values that the local can hold.
    caps: BTreeSet<caps::Held>,
    /// The part of `caps` that does not come from a new value of the whole local in
    /// its own part of the graph (`Lower::bind_caps`). It has the stores into a
    /// part, the new values in a closure or a clause, and the value of a parameter.
    sticky: BTreeSet<caps::Held>,
}

/// The most places with one root in the value of one local. A value with more
/// widens (`Lower::collapse_places`). Each place of the wider value includes
/// places of the old one, so the facts stay sound.
const LOCAL_PLACES_MAX: usize = 64;

/// The locals of a body, in the order of their declarations.
///
/// A loop pass can change a local from outside the loop. Each change goes
/// through [`Locals::get_mut`], which keeps the old value for each open loop
/// pass (`Locals::begin`). A rewind (`Locals::restore`) puts the old values
/// back and drops the locals of the pass. So a rewind costs as much as the
/// changes of the pass, not as much as all the locals.
#[derive(Clone, Debug, Default)]
struct Locals {
    items: Vec<Local>,
    /// The locals that hold a `@ uniq` value now.
    uniq: BTreeSet<usize>,
    /// The locals that can hold a task handle now: their task set is not empty.
    tasked: BTreeSet<usize>,
    /// The open loop passes, the innermost last.
    undo: Vec<Undo>,
}

/// The changes of the locals in one loop pass.
#[derive(Clone, Debug, Default)]
struct Undo {
    /// The number of locals at the start of the pass.
    floor: usize,
    /// The old value of each local below `floor` that the pass changed.
    old: BTreeMap<usize, Local>,
    /// The old `@ uniq` mark of each local below `floor` that the pass changed.
    old_uniq: BTreeMap<usize, bool>,
}

impl std::ops::Index<usize> for Locals {
    type Output = Local;
    fn index(&self, l: usize) -> &Local {
        &self.items[l]
    }
}

impl Locals {
    fn len(&self) -> usize {
        self.items.len()
    }

    fn get(&self, l: usize) -> Option<&Local> {
        self.items.get(l)
    }

    fn push(&mut self, local: Local, uniq: bool) {
        if uniq {
            self.uniq.insert(self.items.len());
        }
        self.items.push(local);
    }

    /// Returns true if local `l` holds a `@ uniq` value now.
    fn is_uniq(&self, l: usize) -> bool {
        self.uniq.contains(&l)
    }

    /// The locals that hold a `@ uniq` value now.
    const fn uniq_set(&self) -> &BTreeSet<usize> {
        &self.uniq
    }

    /// Returns local `l` to change it. Each open loop pass keeps its old value.
    fn get_mut(&mut self, l: usize) -> &mut Local {
        for u in &mut self.undo {
            if l < u.floor && !u.old.contains_key(&l) {
                u.old.insert(l, self.items[l].clone());
            }
        }
        &mut self.items[l]
    }

    /// The locals that can hold a task handle now.
    const fn tasked(&self) -> &BTreeSet<usize> {
        &self.tasked
    }

    /// Sets the tasks of the handles that local `l` can hold.
    fn set_tasks(&mut self, l: usize, tasks: BTreeSet<TaskId>) {
        if self.items[l].tasks == tasks {
            return;
        }
        if tasks.is_empty() {
            self.tasked.remove(&l);
        } else {
            self.tasked.insert(l);
        }
        self.get_mut(l).tasks = tasks;
    }

    /// Sets the `@ uniq` mark of local `l`. Each open loop pass keeps the old mark.
    fn set_uniq(&mut self, l: usize, uniq: bool) {
        let was = self.uniq.contains(&l);
        if was == uniq {
            return;
        }
        for u in &mut self.undo {
            if l < u.floor {
                u.old_uniq.entry(l).or_insert(was);
            }
        }
        if uniq {
            self.uniq.insert(l);
        } else {
            self.uniq.remove(&l);
        }
    }

    /// Starts a loop pass: the changes from now on are kept.
    fn begin(&mut self) {
        let floor = self.items.len();
        self.undo.push(Undo {
            floor,
            old: BTreeMap::new(),
            old_uniq: BTreeMap::new(),
        });
    }

    /// Ends the innermost loop pass, and returns its changes.
    fn end(&mut self) -> Undo {
        self.undo.pop().unwrap_or_default()
    }

    /// Puts back the values before the pass `u`, and drops the locals of the pass.
    fn restore(&mut self, u: Undo) {
        for (l, old) in u.old {
            if let Some(slot) = self.items.get_mut(l) {
                if old.tasks.is_empty() {
                    self.tasked.remove(&l);
                } else {
                    self.tasked.insert(l);
                }
                *slot = old;
            }
        }
        for (l, was) in u.old_uniq {
            if was {
                self.uniq.insert(l);
            } else {
                self.uniq.remove(&l);
            }
        }
        self.items.truncate(u.floor);
        let _ = self.uniq.split_off(&u.floor);
        let _ = self.tasked.split_off(&u.floor);
    }
}

#[derive(Clone, Debug, Default)]
struct Val {
    ty: Ty,
    refs: Vec<PlaceId>,
    var: Option<VarId>,
    local: Option<usize>,
    uniq: bool,
    summary: Option<usize>,
    /// The tasks of the task handles that the value can be.
    tasks: BTreeSet<TaskId>,
    parts: Option<Vec<Self>>,
    place: Option<LVal>,
    fn_param: Option<(usize, usize)>,
    item: Option<FnId>,
    /// The capabilities of the function values inside the value that its type
    /// does not show, for example in a struct field.
    caps: BTreeSet<caps::Held>,
    /// The value has no linear part: a variant with no payload, such as `None`.
    empty: bool,
}

#[derive(Clone, Debug, Default)]
struct LVal {
    places: Vec<PlaceId>,
    ty: Ty,
    owner: Option<usize>,
    through_ref: bool,
    uniq: bool,
    /// The `Rc` handles on the way to the place. The place stays valid only
    /// while each handle keeps its value. A reference to the place also points
    /// into these handle places.
    deps: Vec<PlaceId>,
    /// The capabilities of the function values that the reference on the way to
    /// the place can reach: the place can hold them.
    held: BTreeSet<caps::Held>,
}

/// Where the body puts a reference that the caller keeps after the return.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Behind {
    /// Behind reference parameter `i` of the function.
    Param(usize),
    /// Into an object of the `rc` type with this definition.
    Group(usize),
}

/// References that the body puts where a caller keeps them after the return
/// (`Lower::check_stored_behind`).
#[derive(Clone, Debug)]
struct StoredRef {
    /// Where they go.
    behind: Behind,
    /// The places that they point into.
    refs: Vec<PlaceId>,
    /// The span of the store.
    span: Span,
    /// They are the captures of a closure.
    closure: bool,
}

/// A method call through a reference local that can write through the local
/// (`Lower::note_via_call`).
#[derive(Clone, Debug)]
struct ViaCall {
    /// The variable of the local.
    var: VarId,
    /// The places of the local at the call.
    refs: Vec<PlaceId>,
    /// The number of nodes before the call.
    from: usize,
    /// The span of the call node.
    span: Span,
    /// The label of the call node: the method name.
    label: String,
}

/// A hidden variable that holds the references that a part of a local gets.
#[derive(Clone, Debug)]
struct PartHolder {
    /// The local.
    local: usize,
    /// The places of the part.
    places: Vec<PlaceId>,
    /// The variable.
    var: VarId,
    /// The places that the references point into.
    refs: Vec<PlaceId>,
}

/// The lowering state that each branch of an `if` or a `match` changes on its
/// own path. The branches join it at their end.
#[derive(Clone)]
pub(super) struct BranchState {
    /// The locals that hold a `@ uniq` value.
    uniq: BTreeSet<usize>,
    /// The tasks of the handles that each local can hold, for the locals with any.
    tasks: BTreeMap<usize, BTreeSet<TaskId>>,
    /// The number of locals: a local at this index or above has no mark here.
    len: usize,
    /// The holders of the references in the parts of locals.
    holders: Vec<PartHolder>,
}

#[derive(Clone)]
struct Frame {
    names: Vec<(String, usize)>,
    barrier: Option<usize>,
    /// A number that no other frame of the body has.
    id: usize,
}

#[derive(Clone)]
struct HandlerFrame {
    effect: String,
    cap: CapId,
    multi: bool,
    /// The number of frames when the handled body starts.
    frames: usize,
    /// The depth of `Lower::jumps` when the handled body starts.
    jumps: usize,
}

/// A local handler that an abort at a node can go to: a clause that does not
/// resume ends the handled body there. The way to the end of the `handle` leaves
/// the scopes that the body opened around the node.
#[derive(Clone, Debug)]
struct AbortTo {
    /// The capability of the handler.
    cap: CapId,
    /// The values of the handled body in scope at the node: owners, linear
    /// values, temporaries and values on their way to a call. The unwinder
    /// finishes them (`unwound_at`).
    vars: Vec<VarId>,
    /// The binders of the scopes that the handled body opened around the node.
    /// The unwinder cancels their tasks and waits for them.
    scopes: Vec<usize>,
    /// The local handlers inside the handled body around the node. The way to
    /// the end leaves their bodies too.
    inner: Vec<CapId>,
}

#[derive(Clone)]
struct LoopFrame {
    header: NodeId,
    exit: NodeId,
    frames: usize,
    /// The depth of `Lower::jumps` at the loop.
    jumps: usize,
}

/// A body that a jump (`return`, `break`, `continue`) can leave or not.
#[derive(Clone)]
enum Jump {
    /// A function or a test: `return` goes to its exit.
    Function { exit: Option<NodeId> },
    /// A closure: `return` goes to its exit node, with a value of type `ret`.
    /// `frame` is the frame of its parameters, and `span` the span of the closure.
    Closure {
        exit: Option<NodeId>,
        ret: Ty,
        frame: usize,
        /// The values of the `return`s, with the places that they point into.
        values: Vec<Val>,
        span: Span,
    },
    /// A handled body, a handler clause or a scope body: no jump can leave it.
    Fence(&'static str),
}

/// Returns the effect row of a function type.
fn fn_row(t: &Ty) -> Option<Vec<String>> {
    match t {
        Ty::Fn(f) => f.effects.clone(),
        _ => None,
    }
}

/// The span of the value of a block: its last statement.
fn block_tail(b: &Block) -> Span {
    match b.stmts.last() {
        Some(Stmt {
            kind: StmtKind::Expr(e),
            ..
        }) => expr_tail(e),
        Some(s) => s.span,
        None => b.span,
    }
}

/// The span of the value of an expression: the last statement of a block.
fn expr_tail(e: &Expr) -> Span {
    match &e.kind {
        ExprKind::Block(b) => block_tail(b),
        _ => e.span,
    }
}

/// A path that names something other than a value.
#[derive(Clone, Copy)]
enum PathRef {
    Mod(ModId),
    Adt(usize),
    Effect(usize),
}

/// A handler whose clauses are lowered: what they do at each node that runs them.
#[derive(Clone)]
struct Handled {
    /// The capability of the handler.
    cap: CapId,
    /// Each clause: its operation, its summary and its resumes.
    clauses: Vec<(Option<usize>, Summary, Vec<NodeId>)>,
    /// The places outside the clauses that they mutate.
    footprint: Vec<PlaceId>,
    /// The places outside the clauses that they lend.
    lent: Vec<PlaceId>,
    /// The captures, reads and locals of the clauses.
    clause_sum: Summary,
    /// The resumes of the clauses.
    resumes: Vec<NodeId>,
    /// The places that the handled computation changes.
    changes: Vec<PlaceId>,
    /// The places that the handled computation frees (`Lower::body_frees`).
    frees: Vec<PlaceId>,
    /// The end node of the `handle`.
    end: NodeId,
    /// A clause can end with no `resume`: each node of the body that runs a
    /// clause gets a path to `end` (`Lower::finish_aborts`).
    aborts: bool,
    /// The number of locals when the handled body starts: a local below it is
    /// declared outside the body.
    locals: usize,
    /// The capabilities of the local handlers outside the `handle` that the
    /// clauses perform through. A node that runs a clause runs their clauses too.
    clause_caps: BTreeSet<CapId>,
    /// The locals of the clauses that the result of an operation can point into.
    /// They go out of scope at the end of the `handle`.
    clause_vars: Vec<VarId>,
    /// The check of the locals outside the body (W0313, `check_local_keeps`):
    /// the effect and the span of the `handle`. `None` if the `handle` already
    /// reports W0313.
    keeps: Option<(String, Span)>,
    /// The nodes of each clause, from the first to the one after the last.
    clause_nodes: Vec<(NodeId, NodeId)>,
    /// The capabilities of the handlers that the clauses install.
    inner_caps: BTreeSet<CapId>,
}

/// The lowering state of one function.
///
/// A loop body can be lowered more than once (`loops::lower_loop`). A pass
/// after the first starts from the state at the loop head. `loops::LoopHead`
/// names each field: a new field needs a decision there.
pub struct Lower<'p> {
    prog: &'p Program,
    sigs: &'p [FnSig],
    b: Builtins,
    module: ModId,
    /// The facts being written.
    pub facts: FnFacts,
    diags: Vec<Diagnostic>,
    inf: Infer,
    locals: Locals,
    frames: Vec<Frame>,
    sums: Vec<Summary>,
    closures: Vec<Summary>,
    handlers: Vec<HandlerFrame>,
    loops: Vec<LoopFrame>,
    /// The bodies around the current node that a jump can leave or not.
    jumps: Vec<Jump>,
    cur: Option<NodeId>,
    pend_uses: Vec<VarId>,
    pend_reads: Vec<PlaceId>,
    groups: BTreeMap<usize, PlaceId>,
    /// The open scopes: the local of the binder, and the tasks that join at the end.
    scopes: Vec<(usize, Vec<TaskId>)>,
    /// The local of the scope binder of each task.
    task_scope: BTreeMap<TaskId, usize>,
    /// The capabilities of the root handlers that `sim.run` installs. A task reaches them.
    root_caps: BTreeSet<CapId>,
    /// The capabilities of the continuations of the clauses. A closure that
    /// calls `resume` holds the one of its clause (`check_cont_escape`).
    cont_caps: BTreeSet<CapId>,
    /// The clauses that are being lowered: the capability of the continuation,
    /// and the number of handlers outside the `handle` of the clause.
    clause_conts: Vec<(CapId, usize)>,
    /// The function parameters of the clauses that are being lowered (summary
    /// index, parameter), each with the summary of the function values that
    /// the nodes give to the operation. A local handler lowers its clauses after
    /// the handled body, so the clause runs these values (ADR 0006).
    clause_fns: BTreeMap<(usize, usize), usize>,
    /// The nodes that can abort or resume more than once in a way that can
    /// reach each value of the function: not only through an operation of a
    /// local handler (`finish_spared`).
    out_suspends: BTreeSet<NodeId>,
    /// The operations of local handlers: the node, the capability and the
    /// variables outside the handled body (`outside_vars`).
    local_performs: Vec<(NodeId, CapId, Vec<VarId>)>,
    /// The effect of the handler behind each capability.
    cap_effects: BTreeMap<CapId, String>,
    ret_ty: Ty,
    in_test: bool,
    library: bool,
    self_fn: Option<FnId>,
    split: u32,
    /// The id of each split side of a call: the base of the call and the
    /// parameter that names the split point (`Lower::seg_split`).
    seg_splits: BTreeMap<(u32, usize), u32>,
    cap_calls: Vec<(NodeId, CapId)>,
    resumes: Vec<(NodeId, CapId)>,
    match_moves: bool,
    match_deps: Vec<PlaceId>,
    /// The handle places of `LVal::deps`.
    dep_places: BTreeSet<PlaceId>,
    /// The loop keys of places (`Lower::place_key`), by place and the number of
    /// roots before the loop. A place does not change, so a key stays valid.
    keys: std::cell::RefCell<std::collections::HashMap<(PlaceId, usize), Rc<str>>>,
    /// The method calls that can write through a reference local, for
    /// `writes_via` at the end of the body.
    via_calls: Vec<ViaCall>,
    /// The open statements: the frame depth at the start, and the owners of
    /// the temporaries that go out of scope at the end.
    stmt_temps: Vec<(usize, Vec<VarId>)>,
    /// The function values that the function returns.
    rets: Vec<fnval::RowFn>,
    /// The places that nodes give to operations of local handlers.
    op_args: Vec<OpArg>,
    /// Function values that the body stores where it does not follow them.
    escaped: Vec<fnval::Stored>,
    /// The nodes where a stored function value can run.
    reaches: Vec<Reach>,
    /// The nodes where a summary runs.
    applied: Vec<Applied>,
    /// The handlers whose clauses are lowered.
    handled: Vec<Handled>,
    /// A call of a function value that the body does not know can resume a
    /// `multi` continuation more than once.
    unknown_multi: bool,
    /// The local handlers whose operations a callee, or code that the body does
    /// not see, can perform. A reference parameter of a clause can then point
    /// into a local of that code, which ends before a `resume` returns.
    callee_ops: BTreeSet<CapId>,
    /// A node of the body can raise a failure that the runtime makes, and no
    /// `Fail` handler of the body gets it (`EffectSig::raises`).
    raises: bool,
    /// Function values that perform through local handlers, where they can live on.
    kept: Vec<caps::Kept>,
    /// The capabilities of the values that the `resume`s of each local handler give.
    resumed: BTreeMap<CapId, BTreeSet<caps::Held>>,
    /// Function values that nodes give to operations of local handlers.
    op_fn_args: Vec<caps::OpFn>,
    /// The calls of each function parameter (summary index, parameter): their
    /// number, and whether one can run more than once.
    param_runs: BTreeMap<(usize, usize), (usize, bool)>,
    /// The place fields of locals that have no value yet. Each has a hidden
    /// variable that gets a value when the body sets the field.
    unset_places: Vec<(PlaceId, VarId)>,
    /// The source of the `for` loop that is being lowered is `@ uniq`.
    iter_uniq: bool,
    /// The places that the value of each temporary root points into.
    temp_refs: BTreeMap<RootId, Vec<PlaceId>>,
    /// Hidden variables that hold the references that the parts of locals get. A
    /// use of the local uses them.
    part_holders: Vec<PartHolder>,
    /// Each holder that `part_holders` had. At the end of the body, a closure
    /// that can still run gets the values of the parts of its captures from it
    /// (`Lower::cap_refs_now`).
    holder_log: Vec<PartHolder>,
    /// The integer literals: the value, true if it is negative, the type and the span.
    int_lits: Vec<(u64, bool, Ty, Span)>,
    /// The arithmetic results: the type and the span (`FnFacts::int_ops`).
    int_ops: Vec<(Ty, Span)>,
    /// The span of the literal that is being lowered.
    lit_span: Span,
    /// The local of each variable, by variable index (`usize::MAX`: none). A
    /// lookup checks the entry, because a loop pass can drop locals.
    var_local: Vec<usize>,
    /// The local that owns each root, by root index (`usize::MAX`: none).
    root_local: Vec<usize>,
    /// The program has a struct with a place field.
    has_place_fields: bool,
    /// Hidden variables and their types. `finish` sets their flags again from
    /// the type that the whole body infers.
    late_vars: Vec<(VarId, Ty)>,
    /// The body is generic: a value of a type parameter can be linear for a
    /// caller. The lowering then treats it as linear where a linear value can go
    /// away, and `finish` finds the type parameters that the body can drop.
    generic: bool,
    /// Hidden variables that are linear only because a type parameter can be.
    maybe_linear: BTreeSet<VarId>,
    /// Moves of a value whose type the body does not know yet: the variable and
    /// the node. `finish` drops the move if the type is plain data.
    tentative: Vec<(VarId, NodeId, Ty)>,
    /// The number of frames that the body opened.
    frame_ids: usize,
    /// The locals in scope by name, the innermost last.
    scope: BTreeMap<String, Vec<usize>>,
    /// The `break` (true) and `continue` jumps of the loop that is being lowered,
    /// with the state at each jump.
    loop_jumps: Vec<(bool, BranchState, NodeId)>,
    /// The header and the exit of the loop whose body was lowered last.
    last_loop: Option<(NodeId, NodeId)>,
    /// The holders of the values on their way to the node that takes them
    /// (`hold_moved`), with the depths of `jumps` and `loops` where they start. A
    /// jump out of that code leaves the value: it goes out of scope there.
    in_flight: Vec<(VarId, usize, usize)>,
    /// The number of nodes that can run a stored function value, and whether one
    /// of them can run it more than once (`Lower::reach`).
    reach_runs: (usize, bool),
    /// The nodes where a function value can run more than once (`note_repeat`).
    repeated: BTreeSet<NodeId>,
    /// The parameter roots of the function, the closures and the clauses: the
    /// summary index of the body and the parameter index.
    param_of_root: BTreeMap<weft_facts::RootId, (usize, usize)>,
    /// The root place of the result of each operation of a local handler that
    /// holds references: the capability and the operation (`None`: any). The
    /// places that the clauses resume with replace it at the end (`op_refs`).
    op_results: BTreeMap<(CapId, Option<usize>), PlaceId>,
    /// The places that the `resume`s of the clause of each operation give.
    resumed_refs: BTreeMap<(CapId, Option<usize>), Vec<PlaceId>>,
    /// The root place of what a handler of a caller can resume with: a place of
    /// the caller that the parameters do not reach (`Lower::env_ref`).
    env_root: Option<PlaceId>,
    /// The nodes that call a function parameter or a function value that the
    /// body does not know. Code of a caller runs there.
    caller_runs: Vec<NodeId>,
    /// The values that the function returns: their places, true for a closure,
    /// and the span. `check_returns` checks them after `op_refs`.
    returned: Vec<(Vec<PlaceId>, bool, Span)>,
    /// The places of the values that the function returns, after `check_returns`
    /// gave the operation results their places. `summary_to_sig` makes the
    /// `ret_refs` part of the signature from them.
    returned_places: Vec<PlaceId>,
    /// References that the body puts behind a reference parameter: the
    /// parameter, the places that they point into, and the span. A caller
    /// keeps them after the return (`check_stored_behind`). An `rc` object
    /// keeps them too: the parameter is then the `rc` type.
    stored_behind: Vec<StoredRef>,
    /// The closures that the body puts behind a reference parameter or into an
    /// `rc` object: where they go, the summary and the span. At the end of the
    /// body, the new values of their captures go there too (`Lower::late_refs`).
    late_stores: Vec<(Behind, usize, Span)>,
    /// The places of the caller that the closures behind each reference
    /// parameter point into: the parameter and the place
    /// (`EffectSig::fn_store_refs`). `check_stored_behind` finds them.
    fn_store_places: Vec<(usize, PlaceId)>,
    /// The function values that the body puts into a container of a local, such
    /// as `v.push(f)`, with the local. A return of the local returns them too.
    held_fns: Vec<(usize, Val)>,
    /// The parameters whose references the body puts into an `rc` object, with
    /// the `rc` type (`EffectSig::group_stores`). `check_stored_behind` finds them.
    group_stores: BTreeSet<(usize, usize)>,
    /// The places that the `resume`s give, while a clause is lowered.
    resume_refs_pending: Vec<(CapId, Vec<PlaceId>)>,
    /// The root places of the parameters of the function.
    param_bases: Vec<PlaceId>,
    /// The root place of what the references behind each reference parameter of
    /// the function point into, by parameter index. The second map gives the
    /// parameter of each such root.
    held_roots: BTreeMap<usize, PlaceId>,
    held_of: BTreeMap<weft_facts::RootId, usize>,
    /// The local handlers that an abort at each node can go to (`note_abort_ctx`):
    /// for a node that can run a clause of a local handler.
    abort_ctx: BTreeMap<NodeId, Rc<Vec<AbortTo>>>,
    /// The new values of whole locals in their own part of the graph: the
    /// variable, the node and the capabilities of the value.
    bind_caps: Vec<(VarId, NodeId, BTreeSet<caps::Held>)>,
    /// The variables that each closure captures by reference, with their values
    /// where the closure is made, by closure index (`late::CapValue`).
    cap_values: BTreeMap<usize, Vec<late::CapValue>>,
    /// The closures whose late values `late_join` adds now: a value can call
    /// itself.
    late_stack: Vec<usize>,
    /// The body is lowered: the nodes that `apply_stored` gives a stored value
    /// to are not in the order of the lowering.
    lowered: bool,
    /// The tasks with their spawn nodes and summaries. At the end of the body,
    /// each task gets the values that its captured variables get while it runs
    /// (`late::finish_task_values`), and the facts for work stealing
    /// (`tasks::finish_task_marks`).
    task_runs: Vec<tasks::TaskRec>,
    /// The nodes where a function parameter of the function can run: a call of
    /// it, a node that runs a closure that calls it, or a call that gives it to
    /// a callee that calls it. `tasks::finish_task_marks` uses them for the
    /// `task_runs` part of the signature.
    param_nodes: Vec<(NodeId, usize)>,
    /// The nodes that call a function that can start a pinned task
    /// (`EffectSig::pins`), also through a closure that the node runs. A task
    /// whose code has such a node is pinned (`tasks::finish_task_marks`).
    pin_calls: Vec<NodeId>,
    /// A task of the body is pinned for a reason that a caller does not see
    /// (`EffectSig::pins`). `tasks::finish_task_marks` sets it.
    pins: bool,
    /// The `task_runs` part of the signature (`tasks::finish_task_marks`).
    task_runs_sig: BTreeMap<usize, crate::TaskRun>,
    /// The places that the body writes and reads while a task runs each
    /// function parameter (`tasks::finish_task_marks`). `summary_to_sig` puts
    /// the places of the parameters into `TaskRun::writes` and `TaskRun::reads`.
    task_run_places: tasks::RunPlaces,
    /// The nodes right after the joins of the tasks: a `join`, the end of a
    /// `fork` or a scope, or an abort. At the end of the body, each node gets
    /// the places that its task writes (`late::finish_task_ends`).
    task_ends: Vec<(TaskId, NodeId)>,
    /// The work so far. A loop rewind keeps it.
    work: crate::Work,
    /// The most passes of one loop, for a test. `None`: [`loops::loop_pass_bound`].
    loop_bound: Option<usize>,
}

impl<'p> Lower<'p> {
    /// Makes a lowering state.
    pub fn new(
        prog: &'p Program,
        sigs: &'p [FnSig],
        module: ModId,
        name: &str,
        library: bool,
    ) -> Self {
        Self {
            prog,
            sigs,
            b: prog.builtins(),
            module,
            facts: FnFacts {
                name: name.into(),
                library,
                ..FnFacts::default()
            },
            diags: Vec::new(),
            inf: Infer::default(),
            locals: Locals::default(),
            frames: vec![Frame {
                names: Vec::new(),
                barrier: None,
                id: 0,
            }],
            sums: vec![Summary::default()],
            closures: Vec::new(),
            handlers: Vec::new(),
            loops: Vec::new(),
            jumps: Vec::new(),
            cur: None,
            pend_uses: Vec::new(),
            pend_reads: Vec::new(),
            groups: BTreeMap::new(),
            scopes: Vec::new(),
            task_scope: BTreeMap::new(),
            root_caps: BTreeSet::new(),
            cont_caps: BTreeSet::new(),
            clause_conts: Vec::new(),
            clause_fns: BTreeMap::new(),
            out_suspends: BTreeSet::new(),
            local_performs: Vec::new(),
            cap_effects: BTreeMap::new(),
            ret_ty: Ty::Unit,
            in_test: false,
            library,
            self_fn: None,
            split: 0,
            seg_splits: BTreeMap::new(),
            cap_calls: Vec::new(),
            resumes: Vec::new(),
            match_moves: false,
            match_deps: Vec::new(),
            dep_places: BTreeSet::new(),
            keys: std::cell::RefCell::default(),
            via_calls: Vec::new(),
            stmt_temps: Vec::new(),
            rets: Vec::new(),
            op_args: Vec::new(),
            escaped: Vec::new(),
            reaches: Vec::new(),
            applied: Vec::new(),
            handled: Vec::new(),
            unknown_multi: false,
            raises: false,
            callee_ops: BTreeSet::new(),
            kept: Vec::new(),
            resumed: BTreeMap::new(),
            param_runs: BTreeMap::new(),
            op_fn_args: Vec::new(),
            unset_places: Vec::new(),
            iter_uniq: false,
            int_lits: Vec::new(),
            int_ops: Vec::new(),
            lit_span: Span::default(),
            temp_refs: BTreeMap::new(),
            part_holders: Vec::new(),
            holder_log: Vec::new(),
            var_local: Vec::new(),
            root_local: Vec::new(),
            late_vars: Vec::new(),
            has_place_fields: prog.adts.iter().any(
                |a| matches!(&a.kind, AdtKind::Struct(fs) if fs.iter().any(|f| f.place.is_some())),
            ),
            generic: false,
            maybe_linear: BTreeSet::new(),
            tentative: Vec::new(),
            frame_ids: 0,
            scope: BTreeMap::new(),
            loop_jumps: Vec::new(),
            last_loop: None,
            in_flight: Vec::new(),
            reach_runs: (0, false),
            repeated: BTreeSet::new(),
            param_of_root: BTreeMap::new(),
            op_results: BTreeMap::new(),
            resumed_refs: BTreeMap::new(),
            env_root: None,
            caller_runs: Vec::new(),
            returned: Vec::new(),
            stored_behind: Vec::new(),
            late_stores: Vec::new(),
            fn_store_places: Vec::new(),
            held_fns: Vec::new(),
            group_stores: BTreeSet::new(),
            resume_refs_pending: Vec::new(),
            param_bases: Vec::new(),
            held_roots: BTreeMap::new(),
            held_of: BTreeMap::new(),
            abort_ctx: BTreeMap::new(),
            bind_caps: Vec::new(),
            cap_values: BTreeMap::new(),
            late_stack: Vec::new(),
            lowered: false,
            returned_places: Vec::new(),
            task_runs: Vec::new(),
            param_nodes: Vec::new(),
            pin_calls: Vec::new(),
            pins: false,
            task_runs_sig: BTreeMap::new(),
            task_run_places: BTreeMap::new(),
            task_ends: Vec::new(),
            work: crate::Work::default(),
            loop_bound: None,
        }
    }

    /// Sets the most passes of the lowering of one loop. A loop that needs more
    /// gets W0707. Only a test lowers the bound.
    #[must_use]
    pub const fn with_loop_bound(mut self, bound: Option<usize>) -> Self {
        self.loop_bound = bound;
        self
    }

    fn err(&mut self, code: &str, msg: impl Into<String>, span: Span) {
        self.diags.push(Diagnostic::error(code, msg, span));
    }

    fn show(&self, t: &Ty) -> String {
        Display {
            ty: &self.inf.resolve(t),
            names: self.prog.adts.as_slice(),
        }
        .to_string()
    }

    fn unify(&mut self, a: &Ty, b: &Ty, span: Span) {
        let mut joins = Vec::new();
        self.fn_joins(a, b, &mut joins, 0);
        if !self.inf.unify(a, b) {
            let (x, y) = (self.show(a), self.show(b));
            self.err(
                "W0102",
                format!("type mismatch: expected `{x}`, found `{y}`"),
                span,
            );
            return;
        }
        // A type variable of a function type that gets another function value, as
        // the element of a `Vec` does: it can be each of them (RR2).
        for (v, old, new) in joins {
            let a = (
                fnval::FnInfo {
                    summary: old.summary,
                    item: old.item,
                    param: None,
                },
                old.effects.clone(),
            );
            let b = (
                fnval::FnInfo {
                    summary: new.summary,
                    item: new.item,
                    param: None,
                },
                new.effects.clone(),
            );
            let info = self.join_fn(&a, &b);
            self.inf.rebind_fn(
                v,
                Arc::new(FnTy {
                    summary: info.summary,
                    item: info.item,
                    ..(*old).clone()
                }),
            );
        }
    }

    /// Finds the type variables in `a` and `b` that are bound to a function type
    /// where the other type has a function type with another function value.
    /// Each pair has the variable, its function type and the other one.
    fn fn_joins(&self, a: &Ty, b: &Ty, out: &mut Vec<(u32, Arc<FnTy>, Arc<FnTy>)>, depth: usize) {
        if depth > 16 {
            return;
        }
        let (sa, sb) = (self.inf.shallow(a), self.inf.shallow(b));
        if let (Ty::Fn(fa), Ty::Fn(fb)) = (&sa, &sb) {
            // A written function type, such as `fn()` in `Vec<fn()>`, stays as it
            // is: a value that the body does not know. A call of it runs the
            // stored values (`apply_stored`).
            for (var_side, other) in [(a, fb), (b, fa)] {
                if let Some((v, bound)) = self.inf.bound_fn(var_side) {
                    let known = bound.summary.is_some() || bound.item.is_some();
                    if known && !self.fn_covers(&bound, other) {
                        out.push((v, bound, Arc::clone(other)));
                    }
                }
            }
            return;
        }
        match (&sa, &sb) {
            (Ty::Tuple(xs), Ty::Tuple(ys)) | (Ty::Adt(_, xs), Ty::Adt(_, ys)) => {
                for (x, y) in xs.iter().zip(ys) {
                    self.fn_joins(x, y, out, depth + 1);
                }
            }
            (Ty::Ref(x), Ty::Ref(y))
            | (Ty::Slice(x), Ty::Slice(y))
            | (Ty::Array(x, _), Ty::Array(y, _)) => self.fn_joins(x, y, out, depth + 1),
            _ => {}
        }
    }

    /// Returns true if function type `a` stands for each function value that `b`
    /// can be.
    fn fn_covers(&self, a: &FnTy, b: &FnTy) -> bool {
        if (a.summary, a.item) == (b.summary, b.item) {
            return true;
        }
        let Some(sa) = a.summary else {
            return false;
        };
        let sum = &self.closures[sa];
        match (b.summary, b.item) {
            (Some(sb), _) => {
                let m = &self.closures[sb].members;
                !m.is_empty() && m.iter().all(|x| sum.members.contains(x))
            }
            (None, Some(f)) => sum.items.contains(&f),
            (None, None) => false,
        }
    }

    // -----------------------------------------------------------------------
    // Nodes and facts
    // -----------------------------------------------------------------------

    fn emit(&mut self, span: Span, label: &str, detail: String) -> NodeId {
        let n = self.facts.add_node(span, label, detail);
        if let Some(c) = self.cur {
            self.facts.cfg_edge.push((c, n));
        }
        self.cur = Some(n);
        for v in std::mem::take(&mut self.pend_uses) {
            self.facts.uses.push((v, n));
        }
        for p in std::mem::take(&mut self.pend_reads) {
            self.facts.reads_at.push((n, p));
        }
        n
    }

    /// Adds a node right after node `n`: the edges out of `n` leave the new node
    /// instead. The current node moves too if it is `n`.
    fn insert_after(&mut self, n: NodeId, label: &str, detail: String) -> NodeId {
        let span = self.facts.node(n).span;
        let m = self.facts.add_node(span, label, detail);
        for e in &mut self.facts.cfg_edge {
            if e.0 == n {
                e.0 = m;
            }
        }
        self.facts.cfg_edge.push((n, m));
        if self.cur == Some(n) {
            self.cur = Some(m);
        }
        m
    }

    /// Starts a new component: a node with no predecessor.
    fn start(&mut self, span: Span, label: &str) -> NodeId {
        self.cur = None;
        self.emit(span, label, String::new())
    }

    /// Writes the queued uses and reads into a new node on the current path.
    /// Call it before control leaves a branch, a loop body or a component, so
    /// that the queue does not go into a node of another path.
    fn flush(&mut self, span: Span) {
        if self.pend_uses.is_empty() && self.pend_reads.is_empty() {
            return;
        }
        if self.cur.is_none() {
            // The queue belongs to code that cannot run.
            self.pend_uses.clear();
            self.pend_reads.clear();
            return;
        }
        let _ = self.emit(span, "use", String::new());
    }

    /// Takes the queue away before a new component starts.
    fn take_pending(&mut self) -> (Vec<VarId>, Vec<PlaceId>) {
        (
            std::mem::take(&mut self.pend_uses),
            std::mem::take(&mut self.pend_reads),
        )
    }

    /// Puts back a queue that `take_pending` took.
    fn restore_pending(&mut self, saved: (Vec<VarId>, Vec<PlaceId>)) {
        let (mut uses, mut reads) = saved;
        uses.append(&mut self.pend_uses);
        reads.append(&mut self.pend_reads);
        self.pend_uses = uses;
        self.pend_reads = reads;
    }

    /// Holds a reference value in a temporary from this point, so that later
    /// code that invalidates it is seen. The consumer must use the temporary.
    fn hold(&mut self, v: &Val, name: &str, span: Span) -> Option<VarId> {
        if v.var.is_some() {
            return None;
        }
        self.hold_as(v, name, VarKind::Temp, span)
    }

    /// Holds an operand while the later operands run. It holds the value of a
    /// variable too, because a later operand can give the variable a new value.
    fn hold_later(&mut self, v: &Val, name: &str, span: Span) -> Option<VarId> {
        self.hold_as(v, name, VarKind::Temp, span)
    }

    /// Returns the variable that a call uses for an argument: a held copy if
    /// later arguments follow, else the variable of the value or a temporary.
    fn hold_operand(&mut self, v: &Val, later: bool, span: Span) -> Option<VarId> {
        if later {
            self.hold_later(v, "argument", span).or(v.var)
        } else {
            v.var.or_else(|| self.hold(v, "argument", span))
        }
    }

    /// Holds a by-value operand that moves before the node that takes it, while
    /// the later operands run. The holder stands for the value on its way. It
    /// points where the value points, and it is linear if the value is. So an
    /// abort in a later operand sees the value (W0602). The node that takes the
    /// value moves the holder (`take_held`).
    fn hold_moved(&mut self, v: &Val, name: &str, span: Span) -> Option<VarId> {
        self.cur?;
        let ty = self.inf.resolve(&v.ty);
        if v.refs.is_empty() && !self.is_linear(&ty) {
            return None;
        }
        let mut info = self.var_info(name, VarKind::Temp, span, &ty, v.uniq);
        // The move of the value itself is the move that W0604 sees.
        info.immovable = false;
        let var = self.new_var(info, &ty);
        let n = self.emit(span, name, String::new());
        self.bind(var, n);
        for &p in &v.refs {
            self.facts.points_into.push((var, p));
        }
        self.in_flight
            .push((var, self.jumps.len(), self.loops.len()));
        Some(var)
    }

    /// Node `n` takes the operands that `hold_moved` held.
    fn take_held(&mut self, held: &[VarId], n: NodeId) {
        for &v in held {
            self.facts.uses.push((v, n));
            self.facts.moved_at.push((v, n));
        }
        self.in_flight.retain(|(v, ..)| !held.contains(v));
    }

    /// A jump at node `n` leaves the values on their way that started deep enough.
    /// Their depth in `Lower::jumps` is `jumps` or more, and their depth in
    /// `Lower::loops` is `loops` or more. They go out of scope at `n`. A linear
    /// value is lost there (W0601).
    pub(super) fn leave_in_flight(&mut self, n: NodeId, jumps: usize, loops: usize) {
        for &(v, j, l) in &self.in_flight {
            if j >= jumps && l >= loops {
                self.facts.scope_end.push((v, n));
            }
        }
    }

    /// Takes the operands that `hold_moved` held at a new node, after the last
    /// operand of a value that is built from parts.
    fn take_held_here(&mut self, held: &[VarId], span: Span) {
        if held.is_empty() || self.cur.is_none() {
            return;
        }
        let n = self.emit(span, "value", String::new());
        self.take_held(held, n);
    }

    /// Holds a part of a value that is built from parts, while the later parts
    /// run. A part that moves goes to `taken` (`hold_moved`). Another part that
    /// holds references goes to `held`, for the next node.
    fn hold_part(
        &mut self,
        v: &Val,
        name: &str,
        span: Span,
        held: &mut Vec<VarId>,
        taken: &mut Vec<VarId>,
    ) {
        if self.moves_value(&v.ty) {
            taken.extend(self.hold_moved(v, name, span));
        } else {
            held.extend(self.hold_later(v, name, span));
        }
    }

    /// Returns true if a by-value use of a value of type `t` moves it. The value
    /// is not plain data, or its type is not known yet (see `consume`).
    pub(super) fn moves_value(&self, t: &Ty) -> bool {
        self.may_free(t)
    }

    /// Holds a reference value in a new variable of kind `kind`.
    fn hold_as(&mut self, v: &Val, name: &str, kind: VarKind, span: Span) -> Option<VarId> {
        if v.refs.is_empty() || self.cur.is_none() {
            return None;
        }
        // The holder only follows the references: the value itself has its own
        // variable, or it is plain data.
        let mut info = self.var_info(name, kind, span, &v.ty, v.uniq);
        info.linear = false;
        info.has_on_abort = true;
        let var = self.facts.add_var(info);
        let n = self.emit(span, name, String::new());
        self.bind(var, n);
        for &p in &v.refs {
            self.facts.points_into.push((var, p));
        }
        Some(var)
    }

    fn sum(&mut self) -> &mut Summary {
        let i = self.sums.len() - 1;
        &mut self.sums[i]
    }

    fn mutate(&mut self, n: NodeId, p: PlaceId) {
        self.facts.mutates_at.push((n, p));
        self.sum().muts.insert(p);
    }

    fn read(&mut self, p: PlaceId) {
        self.read_var(p);
        self.touch_unset(&[p]);
    }

    /// The node reads place `p` for W0405 only: a use of a variable reads its
    /// place (`Lower::var_place`). It does not use the place fields below `p`.
    pub(super) fn read_var(&mut self, p: PlaceId) {
        self.pend_reads.push(p);
        self.sum().reads.insert(p);
    }

    /// The node reads or borrows the places `ps`. A place field with no value at
    /// or below one of them is used there (W0304).
    fn touch_unset(&mut self, ps: &[PlaceId]) {
        let mut used = Vec::new();
        for &(u, var) in &self.unset_places {
            let mut at = Some(u);
            while let Some(a) = at {
                if ps.contains(&a) {
                    used.push(var);
                    break;
                }
                at = self.facts.place(a).parent;
            }
        }
        self.pend_uses.extend(used);
    }

    /// Returns the place of the variable of local `l`: the root place of an
    /// owned local, or the cell of a reference local (`Local::cell`). A use of
    /// the local as a value reads it, and a new value writes it (W0405).
    pub(super) fn var_place(&self, l: usize) -> Option<PlaceId> {
        let loc = &self.locals[l];
        if matches!(self.inf.shallow(&loc.ty), Ty::Ref(_)) {
            loc.cell
        } else {
            loc.root
        }
    }

    fn use_local(&mut self, l: usize) {
        let v = self.locals[l].var;
        self.pend_uses.push(v);
        // A use of the local uses the references that its parts got.
        self.work.holder_steps += self.part_holders.len();
        let parts: Vec<VarId> = self
            .part_holders
            .iter()
            .filter(|h| h.local == l)
            .map(|h| h.var)
            .collect();
        self.pend_uses.extend(parts);
        self.note_capture(l);
    }

    fn note_capture(&mut self, l: usize) {
        // A local declared outside the current closure is a capture of it.
        let v = self.locals[l].var;
        let depth = self.local_frame(l);
        for (fi, f) in self.frames.iter().enumerate() {
            if let Some(si) = f.barrier {
                if fi > depth {
                    self.sums[si].captures.insert(v);
                }
            }
        }
    }

    /// Returns the index of the frame that declares local `l`, or 0 if the frame
    /// has ended.
    fn local_frame(&self, l: usize) -> usize {
        let (depth, id) = self.locals[l].frame;
        if self.frames.get(depth).is_some_and(|f| f.id == id) {
            depth
        } else {
            0
        }
    }

    /// Ends the innermost frame: its names go out of scope.
    pub(super) fn pop_frame(&mut self) {
        let Some(f) = self.frames.pop() else { return };
        for (name, _) in f.names.iter().rev() {
            if let Some(ls) = self.scope.get_mut(name) {
                ls.pop();
                if ls.is_empty() {
                    self.scope.remove(name);
                }
            }
        }
    }

    /// Opens a frame for the locals of a block, a closure or a clause. `barrier`
    /// is the summary of a body that the frame starts.
    pub(super) fn push_frame(&mut self, barrier: Option<usize>) {
        self.frame_ids += 1;
        self.frames.push(Frame {
            names: Vec::new(),
            barrier,
            id: self.frame_ids,
        });
    }

    fn bind(&mut self, v: VarId, n: NodeId) {
        self.facts.rebound_at.push((v, n));
    }

    fn move_var(&mut self, v: VarId, n: NodeId) {
        self.facts.uses.push((v, n));
        self.facts.moved_at.push((v, n));
        let sums_len = self.sums.len();
        for s in &mut self.sums[..sums_len] {
            if s.captures.contains(&v) {
                s.moved_captures.insert(v);
            }
        }
    }

    /// Node `n` can abort. The abort can reach each value of the function
    /// (`out_suspends`).
    fn abortive(&mut self, n: NodeId) {
        self.out_suspends.insert(n);
        self.abortive_local(n);
    }

    /// Node `n` can abort, but only to a local handler: an operation of the
    /// handler, or a `resume` of its clause. `finish_spared` decides which
    /// values the abort can reach.
    fn abortive_local(&mut self, n: NodeId) {
        self.facts.may_abort.push(n);
        self.sum().may_abort = true;
    }

    /// The current node can raise a failure that the runtime makes. It counts
    /// for the signature (`EffectSig::raises`) unless a local `Fail` handler
    /// gets it. A closure can run after its `handle`, so a handler outside the
    /// closure does not count.
    fn raise_here(&mut self) {
        let caught = self.handlers.iter().any(|h| {
            h.effect == "Fail"
                && !self
                    .jumps
                    .get(h.jumps..)
                    .is_some_and(|js| js.iter().any(|j| matches!(j, Jump::Closure { .. })))
        });
        if !caught {
            self.raises = true;
        }
    }

    /// Node `n` can resume a `multi` continuation more than once. The copy can
    /// hold each value of the function (`out_suspends`).
    fn multi_node(&mut self, n: NodeId) {
        self.out_suspends.insert(n);
        self.multi_local(n);
    }

    /// Node `n` can resume a `multi` continuation of a local handler more than
    /// once, as an operation of the handler (`finish_spared`).
    fn multi_local(&mut self, n: NodeId) {
        self.facts.multi_at.push(n);
        self.sum().multi = true;
    }

    /// Returns the variables that live outside the handled body of the local
    /// handler at index `hi` of `Lower::handlers`: the locals of the frames
    /// below the handler, the temporaries of the statements around it, and the
    /// values on their way to a node outside it. An operation of the handler
    /// does not suspend them.
    ///
    /// An operation in a closure or a clause inside the handled body gets no
    /// variables: the closure or the clause can hold a value from outside the
    /// body in a cell of its own (a capture by value, or a clause cell), and
    /// it names that value by the outer variable.
    fn outside_vars(&self, hi: usize) -> Vec<VarId> {
        let Some(h) = self.handlers.get(hi) else {
            return Vec::new();
        };
        let in_fn = self.jumps.get(h.jumps..).is_some_and(|js| {
            js.iter()
                .any(|j| matches!(j, Jump::Closure { .. } | Jump::Fence("handler clause")))
        });
        if in_fn {
            return Vec::new();
        }
        let mut out = Vec::new();
        for f in &self.frames[..h.frames.min(self.frames.len())] {
            out.extend(f.names.iter().map(|&(_, l)| self.locals[l].var));
        }
        for (depth, temps) in &self.stmt_temps {
            if *depth <= h.frames {
                out.extend(temps.iter().copied());
            }
        }
        for &(v, j, _) in &self.in_flight {
            if j <= h.jumps {
                out.push(v);
            }
        }
        out
    }

    /// Node `n` can run a clause of a local handler. A clause that does not
    /// resume ends the handled body there: control goes from `n` to the end of the
    /// `handle`. Records the handlers that the node can abort to, and what goes
    /// out of scope on the way, for `finish_aborts`. A handler outside a closure
    /// or a clause around the node does not count: the node that runs the closure
    /// does.
    pub(super) fn note_abort_ctx(&mut self, n: NodeId) {
        if self.handlers.is_empty() || self.abort_ctx.contains_key(&n) {
            return;
        }
        let barrier = self
            .frames
            .iter()
            .rposition(|f| f.barrier.is_some())
            .map_or(0, |i| i + 1);
        let mut out = Vec::new();
        for (hi, h) in self.handlers.iter().enumerate() {
            if self.root_caps.contains(&h.cap) || h.frames < barrier {
                continue;
            }
            let start = h.frames.min(self.frames.len());
            let mut vars = Vec::new();
            let mut scopes = Vec::new();
            for f in &self.frames[start..] {
                for &(_, l) in &f.names {
                    let loc = &self.locals[l];
                    if loc.root.is_some() || self.may_be_linear(&loc.ty) {
                        vars.push(loc.var);
                    }
                    if matches!(loc.ty, Ty::Scope) {
                        scopes.push(l);
                    }
                }
            }
            for (depth, temps) in &self.stmt_temps {
                if *depth > h.frames {
                    vars.extend(temps.iter().copied());
                }
            }
            for &(v, j, _) in &self.in_flight {
                if j > h.jumps {
                    vars.push(v);
                }
            }
            let inner = self.handlers[hi + 1..]
                .iter()
                .filter(|x| !self.root_caps.contains(&x.cap))
                .map(|x| x.cap)
                .collect();
            out.push(AbortTo {
                cap: h.cap,
                vars,
                scopes,
                inner,
            });
        }
        if !out.is_empty() {
            self.abort_ctx.insert(n, Rc::new(out));
        }
    }

    /// Records that node `n` performs effect `e`. A lexical handler takes it if one is in scope.
    fn perform_effect(&mut self, n: NodeId, e: &str) {
        if let Some(h) = self.handlers.iter().rev().find(|h| h.effect == e) {
            let cap = h.cap;
            let multi = h.multi;
            self.facts.performs_at.push((n, cap));
            self.sum().performs.insert(cap);
            if multi {
                self.multi_local(n);
            }
        } else {
            self.facts.escapes_at.push((n, e.to_string()));
            self.sum().escapes.insert(e.to_string());
            if self.effect_has_multi(e) {
                self.multi_node(n);
            }
        }
    }

    /// Returns true if effect `e` (an identity, see `effects::identity`) has a `multi` operation.
    fn effect_has_multi(&self, e: &str) -> bool {
        effects::by_identity(self.prog, e).is_some_and(|id| self.prog.effects[id].has_multi())
    }

    // -----------------------------------------------------------------------
    // Places
    // -----------------------------------------------------------------------

    fn root(&mut self, name: &str, kind: RootKind) -> PlaceId {
        let p = self.facts.add_root(name, kind);
        let r = self.facts.place(p).root;
        self.sum().own_roots.insert(r);
        p
    }

    /// Makes the root place of a temporary value. A temporary that is not plain
    /// data goes out of scope at the end of its statement, as in the interpreter.
    fn temp_root(&mut self, span: Span, ty: &Ty) -> PlaceId {
        let r = self.root("temporary", RootKind::Local);
        if !self.may_free(ty) {
            return r;
        }
        let shown = self.show(ty);
        let var = self
            .facts
            .add_var(VarInfo::plain("temporary", VarKind::Temp, span, shown));
        self.facts.owner.push((r, var));
        if let Some(si) = self.frames.iter().rev().find_map(|f| f.barrier) {
            self.sums[si].dropped.insert(var);
        }
        if let Some((_, temps)) = self.stmt_temps.last_mut() {
            temps.push(var);
        }
        r
    }

    /// Opens a statement. The temporaries from here go out of scope at its end.
    fn open_stmt(&mut self) {
        let depth = self.frames.len();
        self.stmt_temps.push((depth, Vec::new()));
    }

    /// Closes a statement: its temporaries go out of scope at its end.
    fn close_stmt(&mut self, span: Span) {
        let Some((_, temps)) = self.stmt_temps.pop() else {
            return;
        };
        if temps.is_empty() || self.cur.is_none() {
            return;
        }
        let end = Span::new(span.hi.saturating_sub(1), span.hi);
        let n = self.emit(end, "end of statement", String::new());
        for v in temps {
            self.facts.scope_end.push((v, n));
        }
    }

    fn group_root(&mut self, adt: usize) -> PlaceId {
        if let Some(&p) = self.groups.get(&adt) {
            return p;
        }
        let name = self.prog.adts[adt].name.clone();
        let p = self.facts.add_root(name, RootKind::Group);
        self.groups.insert(adt, p);
        p
    }

    fn child(&mut self, p: PlaceId, s: Step, text: &str) -> PlaceId {
        self.facts.child(p, s, text)
    }

    const fn fresh_split(&mut self) -> u32 {
        self.split += 1;
        self.split
    }

    /// Returns the id of the split of a call whose places use `split_base`, at
    /// the parameter with index `label`. Each pair has an id of its own: the
    /// two sides of one split are disjoint, and the sides of two splits are not.
    fn seg_split(&mut self, split_base: u32, label: usize) -> u32 {
        let next = u32::try_from(self.seg_splits.len()).unwrap_or(u32::MAX);
        *self.seg_splits.entry((split_base, label)).or_insert(next)
    }

    /// Substitutes a signature place with the places of the arguments.
    fn subst_place(
        &mut self,
        sp: &SigPlace,
        args: &[Vec<PlaceId>],
        split_base: u32,
    ) -> Vec<PlaceId> {
        let bases = match &sp.root {
            SigRoot::Param(i) => args.get(*i).cloned().unwrap_or_default(),
            SigRoot::Group(a) => vec![self.group_root(*a)],
        };
        let mut out = Vec::new();
        for base in bases {
            let mut ps = vec![base];
            for st in &sp.steps {
                let mut next = Vec::new();
                for p in ps {
                    match st {
                        SigStep::Step(s, text) => next.push(self.child(p, *s, text)),
                        SigStep::Wild => next.push(self.facts.wildcard(p)),
                        // What the references at or below the place point into.
                        SigStep::Held => next.extend(self.held_refs(&[p])),
                        SigStep::Seg {
                            label,
                            hi,
                            unstable,
                        } => {
                            let split = self.seg_split(split_base, *label);
                            let text = if *hi { "[k..]" } else { "[..k]" };
                            next.push(self.child(
                                p,
                                Step {
                                    kind: StepKind::Seg { split, hi: *hi },
                                    unstable: *unstable,
                                },
                                text,
                            ));
                        }
                    }
                }
                ps = next;
            }
            out.extend(ps);
        }
        out.sort();
        out.dedup();
        out
    }

    /// Returns the handle places of `Rc` handles at `ps`. A reference through a
    /// handle depends on the handle: a move, a scope end or a new value of the
    /// handle can free the object.
    fn handle_deps(&mut self, ps: &[PlaceId]) -> Vec<PlaceId> {
        let step = Step {
            kind: StepKind::Deref,
            unstable: true,
        };
        let mut out = Vec::new();
        for &p in ps {
            let d = self.child(p, step, ".*");
            self.dep_places.insert(d);
            out.push(d);
        }
        out
    }

    /// Returns the handle places of the `Rc` handles in a value of type `ty` at
    /// place `p`. A group place that a callee reaches through the value depends
    /// on them. Past the depth limit, it depends on any handle inside `p`.
    fn inner_handle_deps(&mut self, p: PlaceId, ty: &Ty, depth: usize) -> Vec<PlaceId> {
        // An `Rc` handle is nonportable: a type with no nonportable part has none.
        if !self.is_nonportable(ty) {
            return Vec::new();
        }
        if depth > 4 {
            let any = self.facts.wildcard(p);
            return self.handle_deps(&[any]);
        }
        let t = self.inf.deep(ty);
        let mut out = Vec::new();
        match &t {
            Ty::Ref(_) => out = self.handle_deps(&[p]),
            Ty::Tuple(ts) => {
                for (i, ft) in ts.iter().enumerate() {
                    let step = Step {
                        kind: StepKind::Field {
                            id: u32::try_from(i).unwrap_or(0),
                        },
                        unstable: false,
                    };
                    let c = self.child(p, step, &format!(".{i}"));
                    out.extend(self.inner_handle_deps(c, ft, depth + 1));
                }
            }
            Ty::Adt(a, args) => match &self.prog.adts[*a].kind {
                AdtKind::Extern {
                    deref: Some(Deref::Group),
                    ..
                } => out = self.handle_deps(&[p]),
                AdtKind::Struct(_) | AdtKind::Enum(_) => {
                    let names: Vec<String> = match &self.prog.adts[*a].kind {
                        AdtKind::Struct(fs) => fs.iter().map(|f| f.name.clone()).collect(),
                        AdtKind::Enum(vs) => vs.iter().map(|v| v.name.clone()).collect(),
                        AdtKind::Extern { .. } => Vec::new(),
                    };
                    for name in &names {
                        if let Some((steps, next, _)) = field_step(self.prog, &t, name) {
                            let mut c = p;
                            for (st, text) in &steps {
                                c = self.child(c, *st, text);
                            }
                            out.extend(self.inner_handle_deps(c, &next, depth + 1));
                        }
                    }
                }
                AdtKind::Extern { .. } => {
                    if let Some((Some(step), elem)) = elem_step(self.prog, &t) {
                        let c = self.child(p, step, "[]");
                        out.extend(self.inner_handle_deps(c, &elem, depth + 1));
                    } else if let (AdtKind::Extern { deref: Some(d), .. }, Some(inner)) =
                        (&self.prog.adts[*a].kind, args.first())
                    {
                        let step = Step {
                            kind: StepKind::Deref,
                            unstable: *d == Deref::Unstable,
                        };
                        let inner = inner.clone();
                        let c = self.child(p, step, "");
                        out.extend(self.inner_handle_deps(c, &inner, depth + 1));
                    }
                }
            },
            _ => {}
        }
        out
    }

    /// Returns the handle places that a group place in a call result depends
    /// on: the handle places of the arguments, and the `Rc` handles inside the
    /// values that the reference arguments point to.
    fn group_arg_deps(&mut self, args: &[Vec<PlaceId>], ptys: &[Ty]) -> Vec<PlaceId> {
        let mut out = Vec::new();
        for (i, ps) in args.iter().enumerate() {
            let pointee = match ptys.get(i).map(|t| self.inf.shallow(t)) {
                Some(Ty::Ref(inner)) => Some(*inner),
                _ => None,
            };
            for &p in ps {
                if self.is_dep(p) {
                    out.push(p);
                } else if let Some(t) = &pointee {
                    out.extend(self.inner_handle_deps(p, t, 0));
                }
            }
        }
        out.sort();
        out.dedup();
        out
    }

    /// Returns true if `p` is a handle place of `handle_deps` or inside one.
    fn is_dep(&self, p: PlaceId) -> bool {
        let mut at = Some(p);
        while let Some(a) = at {
            if self.dep_places.contains(&a) {
                return true;
            }
            at = self.facts.place(a).parent;
        }
        false
    }

    /// Splits the places of a reference into the places it names and its handle places.
    fn split_deps(&self, refs: &[PlaceId]) -> (Vec<PlaceId>, Vec<PlaceId>) {
        refs.iter().partition(|&&p| !self.is_dep(p))
    }

    fn place_text(&self, ps: &[PlaceId]) -> String {
        let v: Vec<&str> = ps
            .iter()
            .map(|p| self.facts.place(*p).display.as_str())
            .collect();
        v.join(" | ")
    }

    // -----------------------------------------------------------------------
    // Locals
    // -----------------------------------------------------------------------

    fn lookup_local(&self, name: &str) -> Option<usize> {
        self.scope.get(name).and_then(|ls| ls.last().copied())
    }

    fn var_info(&self, name: &str, kind: VarKind, span: Span, ty: &Ty, uniq: bool) -> VarInfo {
        let t = self.inf.resolve(ty);
        let mut v = VarInfo::plain(name, kind, span, self.show(&t));
        v.callable = matches!(t, Ty::Fn(_)) || kind == VarKind::Closure;
        v.linear = self.ty_has_strict(&t, Prop::Linear);
        v.has_on_abort = self.has_on_abort(&t);
        v.immovable = self.is_immovable(&t);
        v.nonportable = self.is_nonportable(&t);
        v.uniq = uniq;
        // A value that a `multi` resume cannot copy is not `many` either.
        v.once = v.linear
            || uniq
            || matches!(kind, VarKind::Continuation)
            || self.ty_has_strict(&t, Prop::Resource);
        v
    }

    /// Adds hidden variable `info` with a value of type `ty`. In a generic body
    /// it can be linear only because a type parameter can be (`maybe_linear`).
    pub(super) fn new_var(&mut self, info: VarInfo, ty: &Ty) -> VarId {
        let wide = !info.linear && self.generic && self.is_linear(ty);
        let var = self.facts.add_var(info);
        self.late_vars.push((var, ty.clone()));
        if wide {
            self.maybe_linear.insert(var);
        }
        var
    }

    fn new_local(&mut self, name: &str, kind: VarKind, span: Span, ty: Ty, uniq: bool) -> usize {
        let info = self.var_info(name, kind, span, &ty, uniq);
        let var = self.facts.add_var(info);
        let top = self.frames.len() - 1;
        self.locals.push(
            Local {
                name: name.into(),
                var,
                ty,
                root: None,
                cell: None,
                refs: Vec::new(),
                tasks: BTreeSet::new(),
                summary: None,
                fn_param: None,
                cont: None,
                bound: false,
                caps: BTreeSet::new(),
                sticky: BTreeSet::new(),
                frame: (top, self.frames[top].id),
            },
            uniq,
        );
        let l = self.locals.len() - 1;
        let i = var.index();
        if self.var_local.len() <= i {
            self.var_local.resize(i + 1, usize::MAX);
        }
        self.var_local[i] = l;
        self.frames[top].names.push((name.into(), l));
        self.scope.entry(name.into()).or_default().push(l);
        l
    }

    /// Returns the local of variable `v`, if `v` is the variable of a local.
    pub(super) fn local_of(&self, v: VarId) -> Option<usize> {
        let l = *self.var_local.get(v.index())?;
        self.locals.get(l).filter(|loc| loc.var == v).map(|_| l)
    }

    /// Returns the local that owns root `r`.
    pub(super) fn root_owner(&self, r: RootId) -> Option<usize> {
        let l = *self.root_local.get(r.index())?;
        let loc = self.locals.get(l)?;
        loc.root
            .is_some_and(|p| self.facts.place(p).root == r)
            .then_some(l)
    }

    /// Gives local `l` the root place `r`: the local owns the memory under `r`.
    fn set_root(&mut self, l: usize, r: PlaceId) {
        self.locals.get_mut(l).root = Some(r);
        let ri = self.facts.place(r).root.index();
        if self.root_local.len() <= ri {
            self.root_local.resize(ri + 1, usize::MAX);
        }
        self.root_local[ri] = l;
        let var = self.locals[l].var;
        self.facts.owner.push((r, var));
        let depth = self.local_frame(l);
        if let Some(si) = self.frames[..=depth].iter().rev().find_map(|f| f.barrier) {
            self.sums[si].dropped.insert(var);
        }
    }

    /// Gives a local the value `v` at node `n`.
    fn assign_local(&mut self, l: usize, v: &Val, n: NodeId) {
        let var = self.locals[l].var;
        let first = !self.locals[l].bound;
        self.bind(var, n);
        // A value with no linear part gives the variable nothing to consume.
        if v.empty && v.var.is_none() {
            self.facts.empty_at.push((var, n));
        }
        // A new value of the whole local replaces the values of its parts.
        self.work.holder_steps += self.part_holders.len();
        self.part_holders.retain(|h| h.local != l);
        let caps = self.val_caps(v);
        self.locals.get_mut(l).caps.extend(caps.iter().copied());
        // A new value in the part of the graph of the local: W0313 follows it to the
        // end of a `handle` (`check_local_keeps`). Another one counts always.
        let depth = self.local_frame(l);
        let same = !self.frames[depth + 1..].iter().any(|f| f.barrier.is_some());
        if same {
            self.bind_caps.push((var, n, caps));
        } else {
            self.locals.get_mut(l).sticky.extend(caps);
        }
        self.mark_modes(l);
        for &p in &v.refs {
            self.point_local(l, p);
        }
        if !v.tasks.is_empty() {
            self.locals.set_tasks(l, v.tasks.clone());
        }
        // A function value. A new value of the local joins the old one: a later
        // call can call either.
        if let Ty::Fn(fty) = self.inf.shallow(&self.locals[l].ty) {
            let new = (self.fn_info(v), fn_row(&self.inf.shallow(&v.ty)));
            let info = if self.locals[l].bound {
                let old = (self.local_fn_info(l), fty.effects.clone());
                self.join_fn(&old, &new)
            } else {
                new.0
            };
            self.locals.get_mut(l).summary = info.summary;
            self.locals.get_mut(l).fn_param = info.param;
        }
        self.locals.get_mut(l).bound = true;
        // The local is `@ uniq` while it holds a `@ uniq` value. The variable is
        // `@ uniq` only if each of its values is, and not `many` if one is.
        self.locals.set_uniq(l, v.uniq);
        let info = &mut self.facts.vars[var.index()];
        info.uniq = weft_facts::join_uniq(v.uniq, first || info.uniq);
        info.once |= v.uniq;
        if let Some(s) = v.summary {
            if self.closure_not_many(s) {
                self.facts.vars[var.index()].once = true;
            }
        }
        // An owned value gets a root place. A reference gets a root place for its
        // variable (`Local::cell`).
        let is_ref = matches!(self.inf.shallow(&self.locals[l].ty), Ty::Ref(_));
        if !is_ref && self.locals[l].root.is_none() {
            let name = self.locals[l].name.clone();
            let r = self.root(&name, RootKind::Local);
            self.set_root(l, r);
        } else if is_ref && self.locals[l].cell.is_none() {
            let name = self.locals[l].name.clone();
            let r = self.root(&name, RootKind::Local);
            self.locals.get_mut(l).cell = Some(r);
        }
        // A new value that no place held before is built in place: its place
        // fields have no value yet.
        if v.var.is_none() && v.place.is_none() && v.local.is_none() {
            if let Some(r) = self.locals[l].root {
                self.unset_fields(l, r, n);
            }
        }
    }

    /// Gives each place field in local `l` (root place `r`) a hidden variable with
    /// no value at node `n`. A read of the field before the body sets it is W0304.
    fn unset_fields(&mut self, l: usize, r: PlaceId, n: NodeId) {
        let ty = self.inf.deep(&self.locals[l].ty);
        let var = self.locals[l].var;
        for path in self.unset_paths(&ty) {
            let mut p = r;
            let mut at = ty.clone();
            let mut found = true;
            for name in &path {
                let Some((steps, next, _)) = field_step(self.prog, &at, name) else {
                    found = false;
                    break;
                };
                for (st, text) in &steps {
                    let text = if text == "*" { "" } else { text.as_str() };
                    p = self.child(p, *st, text);
                }
                at = self.inf.deep(&next);
            }
            if !found {
                continue;
            }
            let name = self.facts.place(p).display.clone();
            let span = self.facts.var(var).span;
            let info = self.var_info(&name, VarKind::Local, span, &at, false);
            let hidden = self.facts.add_var(info);
            self.facts.unset_at.push((hidden, n));
            self.unset_places.push((p, hidden));
        }
    }

    /// Returns the paths of the place fields that a value of type `t` holds: in
    /// the value, in its parts and behind a `Box`. A struct literal cannot give a
    /// place field a value, and a `!Move` value is built in place. So a value that
    /// no place held before has no value in these fields.
    fn unset_paths(&self, t: &Ty) -> Vec<Vec<String>> {
        let mut out = Vec::new();
        if self.has_place_fields {
            self.unset_paths_into(t, &mut Vec::new(), &mut out, &mut Vec::new());
        }
        out
    }

    fn unset_paths_into(
        &self,
        t: &Ty,
        path: &mut Vec<String>,
        out: &mut Vec<Vec<String>>,
        seen: &mut Vec<usize>,
    ) {
        match self.inf.deep(t) {
            Ty::Tuple(ts) => {
                for (i, x) in ts.iter().enumerate() {
                    path.push(i.to_string());
                    self.unset_paths_into(x, path, out, seen);
                    path.pop();
                }
            }
            Ty::Adt(a, args) => {
                if seen.contains(&a) {
                    return;
                }
                seen.push(a);
                match &self.prog.adts[a].kind {
                    AdtKind::Struct(fs) => {
                        for f in fs {
                            path.push(f.name.clone());
                            if f.place.is_some() {
                                out.push(path.clone());
                            } else {
                                self.unset_paths_into(&subst(&f.ty, &args), path, out, seen);
                            }
                            path.pop();
                        }
                    }
                    AdtKind::Enum(vs) => {
                        for v in vs {
                            let payload = match v.fields.len() {
                                0 => continue,
                                1 => subst(&v.fields[0], &args),
                                _ => Ty::Tuple(v.fields.iter().map(|f| subst(f, &args)).collect()),
                            };
                            path.push(v.name.clone());
                            self.unset_paths_into(&payload, path, out, seen);
                            path.pop();
                        }
                    }
                    // A field step goes through a `Box` by itself.
                    AdtKind::Extern { deref: Some(d), .. } if *d != Deref::Group => {
                        if let Some(inner) = args.first() {
                            self.unset_paths_into(inner, path, out, seen);
                        }
                    }
                    AdtKind::Extern { .. } => {}
                }
                seen.pop();
            }
            _ => {}
        }
    }

    /// Returns the state of this path that a branch changes.
    pub(super) fn branch_state(&self) -> BranchState {
        BranchState {
            uniq: self.locals.uniq_set().clone(),
            tasks: self
                .locals
                .tasked()
                .iter()
                .map(|&l| (l, self.locals[l].tasks.clone()))
                .collect(),
            len: self.locals.len(),
            holders: self.part_holders.clone(),
        }
    }

    /// Sets the state of `branch_state` again, at the start of another branch.
    pub(super) fn set_branch(&mut self, state: &BranchState) {
        let len = state.len.min(self.locals.len());
        let changed: Vec<usize> = self
            .locals
            .uniq_set()
            .symmetric_difference(&state.uniq)
            .copied()
            .filter(|&l| l < len)
            .collect();
        for l in changed {
            self.locals.set_uniq(l, state.uniq.contains(&l));
        }
        // The task sets of the state, also an empty set for a local with none there.
        let tasked: Vec<usize> = self
            .locals
            .tasked()
            .iter()
            .chain(state.tasks.keys())
            .copied()
            .filter(|&l| l < len)
            .collect();
        for l in tasked {
            let want = state.tasks.get(&l).cloned().unwrap_or_default();
            self.locals.set_tasks(l, want);
        }
        self.part_holders.clone_from(&state.holders);
    }

    /// Joins the states at the ends of the branches that reach a join.
    pub(super) fn join_branches(&mut self, ends: &[BranchState]) {
        if !ends.is_empty() {
            let st = Self::joined(ends);
            self.set_branch(&st);
        }
    }

    /// Returns the join of states `ends`. A local has the join of its modes at
    /// the ends of the branches (`weft_facts::join_uniq`, with the verified
    /// `modes::join`): it is `@ uniq` after the join only if it is at the end
    /// of each branch. A part can hold the references of each branch.
    pub(super) fn joined(ends: &[BranchState]) -> BranchState {
        let len = ends.iter().map(|e| e.len).min().unwrap_or(0);
        let uniq = ends.first().map_or_else(BTreeSet::new, |first| {
            first
                .uniq
                .iter()
                .copied()
                .filter(|&l| {
                    l < len
                        && ends
                            .iter()
                            .fold(true, |u, e| weft_facts::join_uniq(u, e.uniq.contains(&l)))
                })
                .collect()
        });
        let mut holders: Vec<PartHolder> = Vec::new();
        for h in ends.iter().flat_map(|e| &e.holders) {
            if !holders.iter().any(|x| x.var == h.var) {
                holders.push(h.clone());
            }
        }
        // A local can hold the tasks of each branch.
        let mut tasks: BTreeMap<usize, BTreeSet<TaskId>> = BTreeMap::new();
        for (&l, ts) in ends.iter().flat_map(|e| &e.tasks) {
            if l < len {
                tasks.entry(l).or_default().extend(ts.iter().copied());
            }
        }
        BranchState {
            uniq,
            tasks,
            len,
            holders,
        }
    }

    /// A branch reaches a join over the edge `from` to `to` with the state
    /// `state`. The state at the join can have a part holder that the branch does
    /// not have. That holder is stale on this path: a later value of the part
    /// replaced it. A new node on the edge gives it a new value. So a use after
    /// the join does not see a change that came after the replacement.
    pub(super) fn retire_stale(
        &mut self,
        from: NodeId,
        to: NodeId,
        state: &BranchState,
        joined: &BranchState,
    ) {
        let stale: Vec<VarId> = joined
            .holders
            .iter()
            .filter(|h| !state.holders.iter().any(|x| x.var == h.var))
            .map(|h| h.var)
            .collect();
        if stale.is_empty() {
            return;
        }
        // The edge into the join is new: look for it from the end.
        let Some(at) = self.facts.cfg_edge.iter().rposition(|e| *e == (from, to)) else {
            return;
        };
        let span = self.facts.node(to).span;
        let m = self.facts.add_node(span, "stale part", String::new());
        self.facts.cfg_edge[at].1 = m;
        self.facts.cfg_edge.push((m, to));
        for v in stale {
            self.bind(v, m);
        }
    }

    /// The parts of local `l` at places `ps`, and the parts below them, get new
    /// values: their holders no longer hold a reference.
    pub(super) fn retire_holders(&mut self, l: usize, ps: &[PlaceId]) {
        let mut holders = std::mem::take(&mut self.part_holders);
        self.work.holder_steps += holders.len();
        holders.retain(|h| h.local != l || !self.below_any(&h.places, ps));
        self.part_holders = holders;
    }

    /// Part `p` of local `l` gets a value that points into the places `refs`,
    /// for example a closure that a callee puts there. A hidden variable holds
    /// them from the current node on, and a use of the local uses it. The value
    /// does not replace what the part held before.
    pub(super) fn hold_in_part(&mut self, l: usize, p: PlaceId, refs: &[PlaceId], span: Span) {
        let Some(n) = self.cur else {
            return;
        };
        let name = format!("value in `{}`", self.place_text(&[p]));
        let ty = self.locals[l].ty.clone();
        let mut info = self.var_info(&name, VarKind::Temp, span, &ty, false);
        info.linear = false;
        info.has_on_abort = true;
        let h = self.facts.add_var(info);
        self.bind(h, n);
        for &q in refs {
            self.facts.points_into.push((h, q));
        }
        let holder = PartHolder {
            local: l,
            places: vec![p],
            var: h,
            refs: refs.to_vec(),
        };
        self.holder_log.push(holder.clone());
        self.part_holders.push(holder);
    }

    /// Returns true if each place of `hs` is one of `ps` or below one of them.
    pub(super) fn below_any(&self, hs: &[PlaceId], ps: &[PlaceId]) -> bool {
        hs.iter().all(|&hp| {
            let mut at = Some(hp);
            while let Some(a) = at {
                if ps.contains(&a) {
                    return true;
                }
                at = self.facts.place(a).parent;
            }
            false
        })
    }

    /// Local `l` can point into place `p`. A place below a parameter of the body
    /// around the node, given to a local outside the body, is a place of each call.
    fn point_local(&mut self, l: usize, p: PlaceId) {
        let var = self.locals[l].var;
        // A local that gets the results of two calls inside one base points into
        // the shared wildcard place of the base: else its places grow with each
        // call, as in `cur = step(cur)`. The wildcard rules then compare them.
        let p = match self.facts.one_place_of(p) {
            Some(w) if self.two_results(l, w) => self.facts.wildcard(p),
            _ => self.below_shared_wild(p).unwrap_or(p),
        };
        self.facts.points_into.push((var, p));
        if !self.locals[l].refs.contains(&p) {
            self.locals.get_mut(l).refs.push(p);
            // A value with very many places in one root, such as a walk in many
            // branches, widens to the wildcard place of their common prefix.
            let root = self.facts.place(p).root;
            let same = self.locals[l]
                .refs
                .iter()
                .filter(|&&q| self.facts.place(q).root == root)
                .count();
            if same > LOCAL_PLACES_MAX {
                let refs = self.locals[l].refs.clone();
                let wide = self.collapse_places(&refs, LOCAL_PLACES_MAX);
                for &q in &wide {
                    self.facts.points_into.push((var, q));
                }
                self.locals.get_mut(l).refs = wide;
            }
        }
        let arg = self.facts.roots[self.facts.place(p).root.index()].kind == RootKind::Arg;
        let barrier = self.frames.iter().rposition(|f| f.barrier.is_some());
        if let (true, Some(bi)) = (arg, barrier) {
            if self.local_frame(l) < bi {
                if let Some(si) = self.frames[bi].barrier {
                    if !self.sums[si].binds.contains(&(l, p)) {
                        self.sums[si].binds.push((l, p));
                    }
                }
            }
        }
    }

    /// Returns the wildcard place `b..` if `p` is strictly below it and `b..` is
    /// not a one-place instance. Each place below `b..` is one of its places, so
    /// a local can point into `b..` instead: the wildcard rules decide the same,
    /// and a walk through `b..` does not make a new place at each step.
    fn below_shared_wild(&mut self, p: PlaceId) -> Option<PlaceId> {
        let b = self.facts.wild_base(p)?;
        let depth = self.facts.place(b).steps.len();
        let info = self.facts.place(p);
        let shared = info
            .steps
            .get(depth)
            .is_some_and(|s| !weft_facts::is_one_step(s));
        (shared && info.steps.len() > depth + 1).then(|| self.facts.wildcard(p))
    }

    /// Returns true if local `l` already points into a one-place wildcard place
    /// with the base of `w` that is not `w`.
    fn two_results(&self, l: usize, w: PlaceId) -> bool {
        let base = self.facts.place(w).parent;
        self.locals[l].refs.iter().any(|&q| {
            self.facts
                .one_place_of(q)
                .is_some_and(|x| x != w && self.facts.place(x).parent == base)
        })
    }

    /// Returns true if the closure with summary `s` can run only once. It moves a
    /// captured value that is not plain data, so a call takes the value.
    fn closure_is_once(&self, s: usize) -> bool {
        let sum = &self.closures[s];
        sum.moved_captures.iter().any(|v| !self.is_copy_var(*v))
    }

    /// Returns true if the closure with summary `s` is not `many`. It runs only
    /// once, or it captures a value that is not `many`, such as a `@ uniq`
    /// reference. A copy of it would copy that value.
    fn closure_not_many(&self, s: usize) -> bool {
        self.closure_is_once(s)
            || self.closures[s]
                .captures
                .iter()
                .any(|&v| self.facts.var(v).once)
    }

    /// Returns true if the closure with summary `s` captures a variable that
    /// holds a reference, and the join of the modes of these variables is
    /// `@ uniq` (`weft_facts::join_uniq`): each one is `@ uniq`. The closure
    /// then holds only parts that no other value can reach.
    fn closure_uniq(&self, s: usize) -> bool {
        let mut joined = None;
        for &v in &self.closures[s].captures {
            let Some(l) = self.local_of(v).map(|l| &self.locals[l]) else {
                continue;
            };
            if l.refs.is_empty() {
                continue;
            }
            let uniq = self.facts.var(v).uniq;
            joined = Some(joined.map_or(uniq, |u| weft_facts::join_uniq(u, uniq)));
        }
        joined.unwrap_or(false)
    }

    fn is_copy_var(&self, v: VarId) -> bool {
        self.local_of(v)
            .is_some_and(|l| self.is_copy(&self.locals[l].ty))
    }

    // -----------------------------------------------------------------------
    // Type properties
    // -----------------------------------------------------------------------

    /// Returns true if property `p` holds for a value of type `t`: a part of it has
    /// the property. The table of `Program::props` gives the definitions. A
    /// closure has the properties of what it captures: see `closure_has`. In a
    /// generic body a value of a type parameter can be linear (`Lower::generic`).
    pub(super) fn ty_has(&self, t: &Ty, p: Prop) -> bool {
        self.ty_has_in(t, p, &mut self.has())
    }

    /// `ty_has`, with a type parameter that is not linear: the flags of a variable.
    pub(super) fn ty_has_strict(&self, t: &Ty, p: Prop) -> bool {
        self.ty_has_in(t, p, &mut Has::default())
    }

    /// The state of a property query in the mode of the body.
    pub(super) const fn has(&self) -> Has {
        Has {
            seen: Vec::new(),
            params: self.generic,
        }
    }

    /// `ty_has` with the state `h`.
    fn ty_has_in(&self, t: &Ty, p: Prop, h: &mut Has) -> bool {
        match self.inf.shallow(t) {
            // The copies of a `multi` resume share an `rc` object: a function
            // value or a reference in it points into the locals of one run.
            Ty::Adt(a, args) if p == Prop::Resource && crate::props::is_rc_handle(self.prog, a) => {
                args.first().is_some_and(|x| {
                    self.ty_has_in(x, Prop::Fns, h) || self.ty_has_in(x, Prop::Refs, h)
                })
            }
            Ty::Adt(a, args) => self.prog.props().get(a, p).is_some_and(|x| {
                x.always
                    || x.params
                        .iter()
                        .any(|&j| args.get(j).is_some_and(|y| self.ty_has_in(y, p, h)))
            }),
            Ty::Tuple(ts) => ts.iter().any(|x| self.ty_has_in(x, p, h)),
            Ty::Array(x, _) => p == Prop::NotCopy || self.ty_has_in(&x, p, h),
            // A reference to a nonportable value is nonportable: another thread
            // could use the value through it.
            Ty::Ref(x) => match p {
                Prop::Refs => true,
                Prop::Fns | Prop::Nonportable => self.ty_has_in(&x, p, h),
                _ => false,
            },
            Ty::Slice(x) => match p {
                Prop::Refs | Prop::NotCopy => true,
                Prop::Fns | Prop::Nonportable => self.ty_has_in(&x, p, h),
                _ => false,
            },
            Ty::Fn(f) => match p {
                Prop::Fns => true,
                Prop::NotCopy => f.summary.is_some_and(|s| self.closures[s].literal),
                Prop::Linear | Prop::NoOnAbort | Prop::Nonportable | Prop::Resource => {
                    f.summary.is_some_and(|s| self.closure_has(s, p, h))
                }
                Prop::Immovable | Prop::Refs => false,
            },
            Ty::Param(_) => p == Prop::NotCopy || (p == Prop::Linear && h.params),
            Ty::Cont(..) => p == Prop::NotCopy,
            Ty::Scope => matches!(p, Prop::Nonportable | Prop::Resource),
            _ => false,
        }
    }

    /// Returns true if a closure with summary `s` has property `p`. It is linear if
    /// it moves a linear capture: a call takes the value. It is nonportable if it
    /// captures a nonportable value: it refers to the variable.
    fn closure_has(&self, s: usize, p: Prop, h: &mut Has) -> bool {
        if h.seen.contains(&s) {
            return false;
        }
        let sum = &self.closures[s];
        h.seen.push(s);
        let vars = if p == Prop::Nonportable {
            &sum.captures
        } else {
            &sum.moved_captures
        };
        let found = vars.iter().any(|&v| self.var_has(v, p, h));
        h.seen.pop();
        found
    }

    /// Returns true if variable `v` has property `p`: from the type of its local,
    /// or from its flags if it is not a local. In a generic body a variable of a
    /// type parameter can be linear (`Lower::maybe_linear`).
    fn var_has(&self, v: VarId, p: Prop, h: &mut Has) -> bool {
        let info = self.facts.var(v);
        let local = self.local_of(v);
        let flag = match p {
            _ if local.is_some() => false,
            Prop::Linear => info.linear || (h.params && self.maybe_linear.contains(&v)),
            Prop::Nonportable => info.nonportable,
            Prop::NoOnAbort => info.linear && !info.has_on_abort,
            _ => false,
        };
        flag || local.map(|l| &self.locals[l]).is_some_and(|l| {
            self.ty_has_in(&l.ty, p, h)
                || l.summary.is_some_and(|s| {
                    matches!(p, Prop::Linear | Prop::NoOnAbort | Prop::Nonportable)
                        && self.closure_has(s, p, h)
                })
                || (p == Prop::Nonportable && l.caps.contains(&caps::NONPORTABLE))
        })
    }

    /// Returns true if local `l` has property `p`: from its type, and for a
    /// function value from the closures that it can be.
    pub(super) fn local_has(&self, l: usize, p: Prop) -> bool {
        let v = self.locals[l].var;
        self.var_has(v, p, &mut self.has())
    }

    /// `local_has` with a type parameter that is not linear.
    pub(super) fn local_has_strict(&self, l: usize, p: Prop) -> bool {
        let v = self.locals[l].var;
        self.var_has(v, p, &mut Has::default())
    }

    /// Returns true if closure `s` is linear, in the mode of the body.
    pub(super) fn closure_linear(&self, s: usize) -> bool {
        self.closure_has(s, Prop::Linear, &mut self.has())
    }

    /// Returns true if variable `v` is linear, in the mode of the body.
    pub(super) fn var_linear(&self, v: VarId) -> bool {
        self.var_has(v, Prop::Linear, &mut self.has())
    }

    /// Returns true if a value of type `t` can hold a reference.
    pub(super) fn holds_refs(&self, t: &Ty) -> bool {
        self.ty_has(t, Prop::Refs)
    }

    pub(super) fn is_linear(&self, t: &Ty) -> bool {
        self.ty_has(t, Prop::Linear)
    }

    /// Returns true if a value of type `t` can be linear when the body knows its
    /// whole type. It is linear, or a part of its type is not known yet. A drop
    /// of such a value gets a hidden variable, and `finish` decides from the
    /// inferred type.
    pub(super) fn may_be_linear(&self, t: &Ty) -> bool {
        self.is_linear(t) || self.has_unknown(t)
    }

    /// Returns true if a part of type `t` that a value holds inline is not known yet.
    pub(super) fn has_unknown(&self, t: &Ty) -> bool {
        match self.inf.shallow(t) {
            Ty::Var(_) => true,
            Ty::Adt(_, ts) | Ty::Tuple(ts) => ts.iter().any(|x| self.has_unknown(x)),
            Ty::Array(x, _) => self.has_unknown(&x),
            _ => false,
        }
    }

    /// Returns true if each linear part of a value of type `t` has `on abort`.
    /// A value with no linear part has it too.
    pub(super) fn has_on_abort(&self, t: &Ty) -> bool {
        !self.ty_has(t, Prop::NoOnAbort)
    }

    pub(super) fn is_immovable(&self, t: &Ty) -> bool {
        self.ty_has(t, Prop::Immovable)
    }

    pub(super) fn is_nonportable(&self, t: &Ty) -> bool {
        self.ty_has(t, Prop::Nonportable)
    }

    /// Plain data is copied, not moved: integers, `bool`, references, and
    /// structs and enums of plain data.
    pub(super) fn is_copy(&self, t: &Ty) -> bool {
        !self.ty_has(t, Prop::NotCopy)
    }

    /// Returns true if the end of a variable of type `t` can free memory: the
    /// value is not plain data, or its type is not known yet.
    pub(super) fn may_free(&self, t: &Ty) -> bool {
        let t = self.inf.shallow(t);
        matches!(t, Ty::Var(_)) || !self.is_copy(&t)
    }

    /// Scalars: integers, `bool`, unit, `String` and `Duration`. A loop or a match
    /// binds a scalar by value and other values by reference.
    fn is_scalar(&self, t: &Ty) -> bool {
        match self.inf.shallow(t) {
            Ty::Int(_) | Ty::IntVar(_) | Ty::Bool | Ty::Unit => true,
            Ty::Adt(a, _) => Some(a) == self.b.string || Some(a) == self.b.duration,
            _ => false,
        }
    }

    fn deref_ty(&self, t: &Ty) -> Ty {
        match self.inf.shallow(t) {
            Ty::Ref(inner) => self.deref_ty(&inner),
            t => t,
        }
    }
}
