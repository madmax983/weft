//! Lowering of function bodies to facts.
//!
//! The lowering walks the AST once. It infers types, computes places, and writes a
//! control-flow graph where each node does one thing. A node uses its inputs
//! before it mutates places, so a use and a mutation can share a node.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

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

mod call;
mod caps;
mod drops;
mod exhaust;
mod expr;
mod flow;
mod fnval;
mod repeat;
mod stmt;

use fnval::{Applied, FnInfo, OpArg, Reach};

/// What a body does, in the places of the enclosing function.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Summary {
    /// Mutated places.
    pub muts: BTreeSet<PlaceId>,
    /// Read places.
    pub reads: BTreeSet<PlaceId>,
    /// Effects that no local handler handles.
    pub escapes: BTreeSet<String>,
    /// Local capabilities used.
    pub performs: BTreeSet<CapId>,
    /// Some node can abort.
    pub may_abort: bool,
    /// Some node can resume a `multi` continuation.
    pub multi: bool,
    /// Function parameters that the body calls.
    pub passthrough: BTreeSet<usize>,
    /// Roots made inside the body. They are not visible outside.
    pub own_roots: BTreeSet<RootId>,
    /// Variables of the enclosing function that the body uses.
    pub captures: BTreeSet<VarId>,
    /// Captured variables that the body moves.
    pub moved_captures: BTreeSet<VarId>,
    /// Owners that the body declares. They go out of scope when the body returns.
    pub dropped: BTreeSet<VarId>,
    /// The places that the result of a closure points into.
    pub ret_refs: Vec<PlaceId>,
    /// The root place of each reference parameter of a function value, with the
    /// parameter index. A place below it stands for a place that the call gives.
    pub param_roots: BTreeMap<PlaceId, usize>,
    /// The value is a closure of the body, or can be one: it moves, it is not copied.
    pub literal: bool,
    /// Function items that a call of the value can call. Their effects resolve where it is called.
    pub items: BTreeSet<FnId>,
    /// Function parameters that the value can be.
    pub params: BTreeSet<usize>,
    /// The value can be a function value that the body does not know.
    pub unknown: bool,
    /// Effects that a call of the value performs where it is called: the effect
    /// rows of the parameters and unknown values that it can be.
    pub row: BTreeSet<String>,
    /// Places that the body gives to its function parameters: the parameter, the
    /// argument position (`None`: any position), and the place.
    pub lent: Vec<(usize, Option<usize>, PlaceId)>,
    /// Places that the body gives to operations of local handlers: the capability,
    /// the operation and the argument position (`None`: any), and the place.
    pub op_args: Vec<(CapId, Option<usize>, Option<usize>, PlaceId)>,
    /// The closures of the body that the value can be.
    pub members: BTreeSet<usize>,
    /// Function parameters that the body stores. For a closure: its own parameters.
    pub stores: BTreeSet<usize>,
    /// Places that the body gives to code that can mutate through them: a function
    /// parameter, an unknown function value or an operation of an outer handler.
    pub lends: BTreeSet<PlaceId>,
    /// The summaries of the function values that a call of the value returns.
    pub rets: BTreeSet<usize>,
    /// Locals outside the body that the body gives a place below one of its
    /// parameters: the local and the place.
    pub binds: Vec<(usize, PlaceId)>,
    /// Tasks that the body spawns into a scope outside it. Each node where the
    /// body runs starts them.
    pub spawns: BTreeSet<TaskId>,
    /// Capabilities of the handlers that the body installs.
    pub own_caps: BTreeSet<CapId>,
    /// Function parameters of the value that a task of its body can call.
    pub tasks: BTreeSet<usize>,
    /// The capabilities of the function values inside the values that a call of
    /// the value returns, also inside a tuple or a struct.
    pub ret_caps: BTreeSet<CapId>,
    /// The tasks of the task handles that a call of the value returns.
    pub ret_tasks: BTreeSet<TaskId>,
    /// Function parameters that the body gives to an operation, with the
    /// capability of a local handler outside the body (`None`: a handler of a
    /// caller) and the effect. The clause can call or keep them.
    pub op_fns: BTreeSet<(usize, Option<CapId>, String)>,
    /// Effects that a task of the body performs through a handler outside the function.
    pub task_effects: BTreeSet<String>,
    /// Function parameters that the body can call more than once.
    pub repeats: BTreeSet<usize>,
    /// Tasks that the function values that a call of the value returns spawn into
    /// a scope outside. A callee that calls such a result starts them.
    pub ret_spawns: BTreeSet<TaskId>,
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
}

#[derive(Clone, Debug)]
struct ContInfo {
    arg: Ty,
    ret: Ty,
    multi: bool,
    muts: Vec<PlaceId>,
    cap: CapId,
    /// The depth of `Lower::handlers` in the clause: a handler above it is inside the clause.
    depth: usize,
}

#[derive(Clone, Debug)]
struct Local {
    name: String,
    var: VarId,
    ty: Ty,
    root: Option<PlaceId>,
    refs: Vec<PlaceId>,
    uniq: bool,
    task: Option<TaskId>,
    summary: Option<usize>,
    /// A function parameter: the summary index of its body and the parameter index.
    fn_param: Option<(usize, usize)>,
    cont: Option<ContInfo>,
    /// The local has a value: a new value joins the function values.
    bound: bool,
    /// The index and the number (`Frame::id`) of the frame that declares it.
    frame: (usize, usize),
    /// The capabilities of the function values that the local can hold.
    caps: BTreeSet<CapId>,
}

#[derive(Clone, Debug, Default)]
struct Val {
    ty: Ty,
    refs: Vec<PlaceId>,
    var: Option<VarId>,
    local: Option<usize>,
    uniq: bool,
    summary: Option<usize>,
    task: Option<TaskId>,
    parts: Option<Vec<Self>>,
    place: Option<LVal>,
    fn_param: Option<(usize, usize)>,
    item: Option<FnId>,
    /// The capabilities of the function values inside the value that its type
    /// does not show, for example in a struct field.
    caps: BTreeSet<CapId>,
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
    /// Each local holds a `@ uniq` value.
    uniq: Vec<bool>,
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
}

/// The lowering state of one function.
///
/// A loop body can be lowered more than once (`lower_loop`). A pass after the
/// first starts from a copy of the state at the loop head. Only the interned
/// tables stay from the pass before: places, roots, variables, closure
/// summaries and the inference table. Put a new field that can refer to these
/// tables in `lower_loop` too.
#[derive(Clone)]
pub struct Lower<'p> {
    prog: &'p Program,
    sigs: &'p [FnSig],
    b: Builtins,
    module: ModId,
    /// The facts being written.
    pub facts: FnFacts,
    diags: Vec<Diagnostic>,
    inf: Infer,
    locals: Vec<Local>,
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
    /// The effect of the handler behind each capability.
    cap_effects: BTreeMap<CapId, String>,
    ret_ty: Ty,
    in_test: bool,
    library: bool,
    self_fn: Option<FnId>,
    split: u32,
    cap_calls: Vec<(NodeId, CapId)>,
    resumes: Vec<(NodeId, CapId)>,
    match_moves: bool,
    match_deps: Vec<PlaceId>,
    /// The handle places of `LVal::deps`.
    dep_places: BTreeSet<PlaceId>,
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
    /// Function values that perform through local handlers, where they can live on.
    kept: Vec<caps::Kept>,
    /// The capabilities of the values that the `resume`s of each local handler give.
    resumed: BTreeMap<CapId, BTreeSet<CapId>>,
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
    /// The integer literals: the value, true if it is negative, the type and the span.
    int_lits: Vec<(u64, bool, Ty, Span)>,
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
    loop_jumps: Vec<(bool, BranchState)>,
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
            locals: Vec::new(),
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
            cap_effects: BTreeMap::new(),
            ret_ty: Ty::Unit,
            in_test: false,
            library,
            self_fn: None,
            split: 0,
            cap_calls: Vec::new(),
            resumes: Vec::new(),
            match_moves: false,
            match_deps: Vec::new(),
            dep_places: BTreeSet::new(),
            stmt_temps: Vec::new(),
            rets: Vec::new(),
            op_args: Vec::new(),
            escaped: Vec::new(),
            reaches: Vec::new(),
            applied: Vec::new(),
            handled: Vec::new(),
            unknown_multi: false,
            kept: Vec::new(),
            resumed: BTreeMap::new(),
            param_runs: BTreeMap::new(),
            op_fn_args: Vec::new(),
            unset_places: Vec::new(),
            iter_uniq: false,
            int_lits: Vec::new(),
            lit_span: Span::default(),
            temp_refs: BTreeMap::new(),
            part_holders: Vec::new(),
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
        }
    }

    fn err(&mut self, code: &str, msg: impl Into<String>, span: Span) {
        self.diags.push(Diagnostic::error(code, msg, span));
    }

    fn show(&self, t: &Ty) -> String {
        let names = self.prog.adt_names();
        Display {
            ty: &self.inf.resolve(t),
            names: &names,
        }
        .to_string()
    }

    fn unify(&mut self, a: &Ty, b: &Ty, span: Span) {
        if !self.inf.unify(a, b) {
            let (x, y) = (self.show(a), self.show(b));
            self.err(
                "W0102",
                format!("type mismatch: expected `{x}`, found `{y}`"),
                span,
            );
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
        Some(var)
    }

    /// Node `n` takes the operands that `hold_moved` held.
    fn take_held(&mut self, held: &[VarId], n: NodeId) {
        for &v in held {
            self.facts.uses.push((v, n));
            self.facts.moved_at.push((v, n));
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
        self.pend_reads.push(p);
        self.sum().reads.insert(p);
        self.touch_unset(&[p]);
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

    fn use_local(&mut self, l: usize) {
        let v = self.locals[l].var;
        self.pend_uses.push(v);
        // A use of the local uses the references that its parts got.
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

    fn abortive(&mut self, n: NodeId) {
        self.facts.may_abort.push(n);
        self.sum().may_abort = true;
    }

    fn multi_node(&mut self, n: NodeId) {
        self.facts.multi_at.push(n);
        self.sum().multi = true;
    }

    /// Records that node `n` performs effect `e`. A lexical handler takes it if one is in scope.
    fn perform_effect(&mut self, n: NodeId, e: &str) {
        if let Some(h) = self.handlers.iter().rev().find(|h| h.effect == e) {
            let cap = h.cap;
            let multi = h.multi;
            self.facts.performs_at.push((n, cap));
            self.sum().performs.insert(cap);
            if multi {
                self.multi_node(n);
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
            let mut p = base;
            for st in &sp.steps {
                p = match st {
                    SigStep::Step(s, text) => self.child(p, *s, text),
                    SigStep::Wild => self.facts.wildcard(p),
                    SigStep::Seg {
                        label,
                        hi,
                        unstable,
                    } => {
                        let split = split_base * 64 + u32::try_from(*label).unwrap_or(0);
                        let text = if *hi { "[k..]" } else { "[..k]" };
                        self.child(
                            p,
                            Step {
                                kind: StepKind::Seg { split, hi: *hi },
                                unstable: *unstable,
                            },
                            text,
                        )
                    }
                };
            }
            out.push(p);
        }
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

    /// Returns true if the signature place `a` allows a reference into `r`.
    /// Below a plain place only stable steps can follow, because a caller sees
    /// the reference at `a`. Below a wildcard place any step can follow.
    fn sig_allows(&self, a: PlaceId, r: PlaceId) -> bool {
        let (pa, pr) = (self.facts.place(a), self.facts.place(r));
        if pa.root != pr.root {
            return false;
        }
        match (pa.is_wildcard(), pa.parent) {
            (true, Some(base)) => {
                weft_verified::places::within(&pr.steps, &self.facts.place(base).steps)
            }
            _ => {
                weft_verified::places::within(&pr.steps, &pa.steps)
                    && pr.steps[pa.steps.len()..].iter().all(|s| !s.unstable)
            }
        }
    }

    /// Returns true if `r` is inside `a` only through an unstable step below it.
    fn below_unstable(&self, a: PlaceId, r: PlaceId) -> bool {
        let (pa, pr) = (self.facts.place(a), self.facts.place(r));
        pa.root == pr.root
            && !pa.is_wildcard()
            && weft_verified::places::within(&pr.steps, &pa.steps)
            && !self.sig_allows(a, r)
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
        v.once = v.linear || uniq || matches!(kind, VarKind::Continuation);
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
        self.locals.push(Local {
            name: name.into(),
            var,
            ty,
            root: None,
            refs: Vec::new(),
            uniq,
            task: None,
            summary: None,
            fn_param: None,
            cont: None,
            bound: false,
            caps: BTreeSet::new(),
            frame: (top, self.frames[top].id),
        });
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
        self.locals[l].root = Some(r);
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
        // A new value of the whole local replaces the values of its parts.
        self.part_holders.retain(|h| h.local != l);
        let caps = self.val_caps(v);
        self.locals[l].caps.extend(caps);
        self.mark_modes(l);
        for &p in &v.refs {
            self.point_local(l, p);
        }
        if v.task.is_some() {
            self.locals[l].task = v.task;
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
            self.locals[l].summary = info.summary;
            self.locals[l].fn_param = info.param;
        }
        self.locals[l].bound = true;
        // The local is `@ uniq` while it holds a `@ uniq` value. The variable is
        // `@ uniq` only if each of its values is, and not `many` if one is.
        self.locals[l].uniq = v.uniq;
        let info = &mut self.facts.vars[var.index()];
        info.uniq = v.uniq && (first || info.uniq);
        info.once |= v.uniq;
        if let Some(s) = v.summary {
            if self.closure_not_many(s) {
                self.facts.vars[var.index()].once = true;
            }
        }
        // An owned value gets a root place.
        if !matches!(self.inf.shallow(&self.locals[l].ty), Ty::Ref(_))
            && self.locals[l].root.is_none()
        {
            let name = self.locals[l].name.clone();
            let r = self.root(&name, RootKind::Local);
            self.set_root(l, r);
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
            uniq: self.locals.iter().map(|l| l.uniq).collect(),
            holders: self.part_holders.clone(),
        }
    }

    /// Sets the state of `branch_state` again, at the start of another branch.
    pub(super) fn set_branch(&mut self, state: &BranchState) {
        for (l, &u) in self.locals.iter_mut().zip(&state.uniq) {
            l.uniq = u;
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

    /// Returns the join of states `ends`. A local is `@ uniq` after the join only
    /// if it is at the end of each branch. A part can hold the references of each
    /// branch.
    pub(super) fn joined(ends: &[BranchState]) -> BranchState {
        let len = ends.iter().map(|e| e.uniq.len()).min().unwrap_or(0);
        let uniq = (0..len).map(|i| ends.iter().all(|e| e.uniq[i])).collect();
        let mut holders: Vec<PartHolder> = Vec::new();
        for h in ends.iter().flat_map(|e| &e.holders) {
            if !holders.iter().any(|x| x.var == h.var) {
                holders.push(h.clone());
            }
        }
        BranchState { uniq, holders }
    }

    /// The parts of local `l` at places `ps`, and the parts below them, get new
    /// values: their holders no longer hold a reference.
    pub(super) fn retire_holders(&mut self, l: usize, ps: &[PlaceId]) {
        let mut holders = std::mem::take(&mut self.part_holders);
        holders.retain(|h| h.local != l || !self.below_any(&h.places, ps));
        self.part_holders = holders;
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
        self.facts.points_into.push((var, p));
        if !self.locals[l].refs.contains(&p) {
            self.locals[l].refs.push(p);
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

    /// Returns true if each captured variable of the closure with summary `s` that
    /// holds a reference is `@ uniq`, and there is one. The closure then holds
    /// only parts that no other value can reach.
    fn closure_uniq(&self, s: usize) -> bool {
        let mut any = false;
        for &v in &self.closures[s].captures {
            let Some(l) = self.local_of(v).map(|l| &self.locals[l]) else {
                continue;
            };
            if l.refs.is_empty() {
                continue;
            }
            if !self.facts.var(v).uniq {
                return false;
            }
            any = true;
        }
        any
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
                Prop::Linear | Prop::NoOnAbort | Prop::Nonportable => {
                    f.summary.is_some_and(|s| self.closure_has(s, p, h))
                }
                Prop::Immovable | Prop::Refs => false,
            },
            Ty::Param(_) => p == Prop::NotCopy || (p == Prop::Linear && h.params),
            Ty::Cont(..) => p == Prop::NotCopy,
            Ty::Scope => p == Prop::Nonportable,
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
    fn may_free(&self, t: &Ty) -> bool {
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
