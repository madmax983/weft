//! The fact tables that the rules query.
//!
//! Semantic analysis writes one [`FnFacts`] per function. The Datalog engine runs
//! `spec/weft.dl` over these facts. The production checker reads the same facts.
//! Both produce a [`Violations`] value, and the two values must be equal.
//!
//! A function body, each closure body and each handler clause is one connected
//! component of the control-flow graph. All components share the place and
//! variable tables.

use std::collections::{BTreeSet, HashMap};
use std::fmt;

pub use weft_syntax::ast::Span;
pub use weft_verified::modes::Modes;
pub use weft_verified::places::{Step, StepKind};

macro_rules! id_type {
    ($(#[$doc:meta])* $name:ident, $prefix:literal) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub u32);

        impl $name {
            /// Returns the index into the owning table.
            pub const fn index(self) -> usize {
                self.0 as usize
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, concat!($prefix, "{}"), self.0)
            }
        }
    };
}

id_type!(
    /// A node of the control-flow graph.
    NodeId,
    "n"
);
id_type!(
    /// A variable: a local, a parameter, a temporary or a hidden value.
    VarId,
    "v"
);
id_type!(
    /// An interned place.
    PlaceId,
    "p"
);
id_type!(
    /// A place root.
    RootId,
    "r"
);
id_type!(
    /// A capability that a local handler creates.
    CapId,
    "c"
);
id_type!(
    /// A spawned task or a fork branch.
    TaskId,
    "t"
);
id_type!(
    /// A `handle` expression.
    HandlerId,
    "h"
);

/// The last step of a wildcard place. A wildcard place stands for any place at or
/// below its parent. No type has a field with this id.
pub const WILD: Step = Step {
    kind: StepKind::Field { id: u32::MAX },
    unstable: true,
};

/// The first field id of the steps of one-place wildcard places ([`wild_one`]).
/// No type has a field with such an id.
const ONE_FIRST: u32 = 1 << 31;

/// The last step of the one-place wildcard place `inst`.
///
/// Such a place stands for one place at or below its parent: the place that
/// one reference points to, such as the result of one call. All places at or
/// below it are inside that one place. Two different instances can be the same
/// place, as two wildcard places can.
pub const fn wild_one(inst: u32) -> Step {
    Step {
        kind: StepKind::Field {
            id: ONE_FIRST + inst % (u32::MAX - ONE_FIRST),
        },
        unstable: true,
    }
}

/// Returns true if `s` is the last step of a wildcard place: [`WILD`] or a
/// step of [`wild_one`].
pub const fn is_wild_step(s: &Step) -> bool {
    matches!(s.kind, StepKind::Field { id } if id >= ONE_FIRST) && s.unstable
}

/// Returns true if `s` is the last step of a one-place wildcard place.
pub const fn is_one_step(s: &Step) -> bool {
    is_wild_step(s) && !matches!(s.kind, StepKind::Field { id: u32::MAX })
}

/// What a place root is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RootKind {
    /// The referent of a reference parameter. Mutations need a declaration.
    Param,
    /// An owned local or an owned parameter. Mutations are local.
    Local,
    /// The group of an `rc` type. Mutations need a declaration.
    Group,
    /// The referent of a reference parameter of a closure or a handler clause.
    /// A mutation through it changes what the caller gives, and the caller sees
    /// that mutation. So it needs no declaration here.
    Arg,
}

/// A place root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Root {
    /// The name, as shown in diagnostics.
    pub name: String,
    /// The kind.
    pub kind: RootKind,
}

/// An interned place: a root plus steps.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlaceInfo {
    /// The root.
    pub root: RootId,
    /// The place without its last step. `None` for a root place.
    pub parent: Option<PlaceId>,
    /// All steps from the root.
    pub steps: Vec<Step>,
    /// The text form, for example `world.entities[]`.
    pub display: String,
    /// The parent of the outermost wildcard step on the path
    /// ([`FnFacts::wild_base`]).
    pub wild_base: Option<PlaceId>,
    /// The outermost one-place wildcard place at or above the place
    /// ([`FnFacts::one_place_of`]).
    pub one: Option<PlaceId>,
}

impl PlaceInfo {
    /// Returns true if the last step is a wildcard step ([`is_wild_step`]).
    pub fn is_wildcard(&self) -> bool {
        self.steps.last().is_some_and(is_wild_step)
    }

    /// Returns true if the place is a one-place wildcard place ([`wild_one`]).
    pub fn is_one_place(&self) -> bool {
        self.steps.last().is_some_and(is_one_step)
    }
}

/// What a variable is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VarKind {
    /// A named local.
    Local,
    /// A parameter.
    Param,
    /// A temporary value inside an expression.
    Temp,
    /// The value of a block, held across the end of the block.
    BlockValue,
    /// The hidden iterator of a `for` loop.
    Iterator,
    /// A closure value.
    Closure,
    /// A captured continuation (`resume`).
    Continuation,
    /// A task handle.
    Task,
    /// A value that a generic function item can drop where the body uses the
    /// item as a value. The name is the item.
    Dropped,
    /// The value that a body gives back (`_0` of the IR, `docs/ir.md` 6.9).
    /// The name tells the frame: `the result` (a function), `the closure
    /// result`, `handled body value`, `scope body value` or `clause value`.
    Result,
}

/// A variable and its static properties.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VarInfo {
    /// The name, as shown in diagnostics.
    pub name: String,
    /// The kind.
    pub kind: VarKind,
    /// The declaration.
    pub span: Span,
    /// The type, as shown in diagnostics.
    pub ty: String,
    /// The value is linear.
    pub linear: bool,
    /// The type declares `on abort`.
    pub has_on_abort: bool,
    /// The value is not `many`.
    pub once: bool,
    /// The type is `!Move`.
    pub immovable: bool,
    /// The value is `@ uniq`.
    pub uniq: bool,
    /// The value cannot cross threads.
    pub nonportable: bool,
    /// The value is a function value: a closure, a function parameter or a
    /// function item. A second call of a `once` function value is W0502.
    pub callable: bool,
}

/// The mode that a value needs to cross threads.
///
/// It is `portable`, with any value on the other axes. A task can move to
/// another worker only if the join of the modes of its captures is a submode
/// of it (`pinned`, `stealable`).
pub const CROSSES_THREADS: Modes = Modes {
    aliased: true,
    nonportable: false,
    shared: true,
    once: true,
};

/// Returns the mode of a value on the axis of uniqueness: `uniq`, or `aliased`.
pub const fn uniqueness(uniq: bool) -> Modes {
    Modes {
        aliased: !uniq,
        ..weft_verified::modes::bottom()
    }
}

/// Returns true if the join of two values is `@ uniq`: a value that can be
/// either one is `@ uniq` only if both are. The verified join of the mode
/// lattice decides it.
pub const fn join_uniq(a: bool, b: bool) -> bool {
    !weft_verified::modes::join(&uniqueness(a), &uniqueness(b)).aliased
}

impl VarInfo {
    /// Returns the mode of the variable where a task captures it, on the axes
    /// of uniqueness and portability. A variable that the task writes
    /// through, with an aliased reference, is shared-mutable, so it is
    /// nonportable too (ADR 0006).
    pub const fn capture_mode(&self, writes: bool) -> Modes {
        Modes {
            aliased: !self.uniq,
            nonportable: self.nonportable || (writes && !self.uniq),
            ..weft_verified::modes::bottom()
        }
    }

    /// Makes a plain `many`, portable, aliased variable.
    ///
    /// `callable` is true for a closure. A producer that knows the type sets
    /// `callable` itself.
    pub fn plain(
        name: impl Into<String>,
        kind: VarKind,
        span: Span,
        ty: impl Into<String>,
    ) -> Self {
        Self {
            name: name.into(),
            callable: kind == VarKind::Closure,
            kind,
            span,
            ty: ty.into(),
            linear: false,
            has_on_abort: false,
            once: false,
            immovable: false,
            uniq: false,
            nonportable: false,
        }
    }
}

/// A node and what it does, for diagnostics.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NodeInfo {
    /// The source location.
    pub span: Span,
    /// A short label, such as the callee name `push`.
    pub label: String,
    /// More text, such as the effect `mut(world.entities)`.
    pub detail: String,
}

/// The label of a node right after the end of a task. Semantic analysis gives
/// it the places that the task writes (`lends_mut`): the task can change them
/// at any time while it runs.
pub const TASK_END: &str = "task end";

/// The label of a node where a callee runs a function argument as a task.
///
/// The node comes after the call. Semantic analysis gives it what the run reads
/// and writes, and what the callee writes and reads while it runs (ADR 0006).
pub const ARG_TASK: &str = "task of the callee";

/// The kind of task.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TaskKind {
    /// A branch of `fork`: it runs on another thread.
    Fork,
    /// A task from `s.spawn`.
    Spawn,
}

/// A task and its source location.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TaskInfo {
    /// The kind.
    pub kind: TaskKind,
    /// The closure that the task runs.
    pub span: Span,
}

/// A `handle` expression, for the root-handler rule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandlerInfo {
    /// The handled effect.
    pub effect: String,
    /// The handler is a root handler of `sim.run`, which W0802 checks
    /// (`sim_root(H)`). It forwards its effect whatever its clauses do. Other
    /// handlers forward through their clauses (`clause_performs`).
    pub sim_root: bool,
    /// The source location.
    pub span: Span,
}

/// The first parameter index of `uniq_param(P, I)` for a call in a closure.
///
/// The closure runs at node `P`. The index of such a call is this number plus
/// its position, so it is not the index of an argument of the call at `P`.
pub const CLOSURE_ARG: u32 = 1 << 16;

/// An argument of a call that a check of the spec looks at, for diagnostics:
/// W0203 (`arg_outside`), W0406 (`not_uniq`) and W0705 (`arg_effect_outside`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArgSite {
    /// The call node.
    pub node: NodeId,
    /// The index of the parameter.
    pub index: u32,
    /// The argument.
    pub span: Span,
    /// The name of the callee.
    pub callee: String,
    /// The name of the parameter.
    pub param: String,
    /// The places that the parameter states with `in`, as text: `world.a[]`.
    pub needs: String,
    /// For a call inside a closure that runs at the node: the local that the
    /// closure gives to the parameter.
    pub via: Option<String>,
}

/// A place that states where a reference in it can point, for the diagnostics
/// of `ref_outside` (W0204, W0605). This is not a relation of the spec.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RefSite {
    /// The node of `ref_at` and `ref_in`. It has no edges: only `ref_outside`
    /// reads it.
    pub node: NodeId,
    /// What gets the reference.
    pub kind: RefKind,
    /// The places that the place states, as text: `v[]`.
    pub needs: String,
}

/// What gets a reference at a [`RefSite`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RefKind {
    /// The function returns the reference, and its signature states the
    /// returned places (W0204). `env` is the root of the references that a
    /// handler of a caller gives, if the body has them.
    Return {
        /// The root of the references that a handler of a caller gives.
        env: Option<RootId>,
    },
    /// An assignment gives a place field of a `!Move` struct a new value
    /// (W0605).
    Field,
    /// A struct literal gives the place field `field` a value (W0605). The
    /// struct has no place yet, so the field states no place of the body.
    Literal {
        /// The name of the field.
        field: String,
    },
}

/// The sizes of the relations of [`FnFacts`] at one point of the lowering.
///
/// [`FnFacts::rewind`] cuts the relations back to these sizes. The lowering of
/// a loop body uses it to start each pass again from the loop head. The
/// tables of roots, places and variables stay, so that the values of the pass
/// before stay valid.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FactMark {
    caps: u32,
    has_signature: bool,
    library: bool,
    nodes: usize,
    tasks: usize,
    handlers: usize,
    by_value: usize,
    arg_order: usize,
    cfg_edge: usize,
    points_into: usize,
    mutates_at: usize,
    reads_at: usize,
    performs_at: usize,
    footprint: usize,
    rebound_at: usize,
    uses: usize,
    moved_at: usize,
    scope_end: usize,
    overwrites: usize,
    unset_at: usize,
    empty_at: usize,
    unwound_at: usize,
    owner: usize,
    moved_part: usize,
    rest_linear: usize,
    releases_at: usize,
    may_abort: usize,
    multi_at: usize,
    spared_at: usize,
    clause_multi: usize,
    body_multi: usize,
    resumes_at: usize,
    clause_performs: usize,
    declared_mut: usize,
    declared_effect: usize,
    escapes_at: usize,
    shared_root: usize,
    spawned_at: usize,
    joined_at: usize,
    task_reads: usize,
    task_writes: usize,
    captures: usize,
    mut_through: usize,
    kept: usize,
    spawns_in: usize,
    opaque: usize,
    call_mut: usize,
    call_arg: usize,
    lends_mut: usize,
    writes_via: usize,
    arg_sites: usize,
    ref_sites: usize,
    arg_at: usize,
    param_in: usize,
    uniq_param: usize,
    arg_aliased: usize,
    fn_arg_effect: usize,
    param_effect: usize,
    sim_run_at: usize,
    ref_at: usize,
    ref_in: usize,
    std_effects: usize,
}

/// All facts of one function.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FnFacts {
    /// The function name.
    pub name: String,
    /// The place roots.
    pub roots: Vec<Root>,
    /// The places. A parent comes before its children.
    pub places: Vec<PlaceInfo>,
    /// The variables.
    pub vars: Vec<VarInfo>,
    /// The nodes.
    pub nodes: Vec<NodeInfo>,
    /// The tasks.
    pub tasks: Vec<TaskInfo>,
    /// The `handle` expressions.
    pub handlers: Vec<HandlerInfo>,
    /// The captured variables that a closure takes by value when it is made: the
    /// span of the closure and the variable. These are the captures that the
    /// closure moves. The interpreter moves each of them into a cell of the
    /// closure. This is not a relation of the spec.
    pub by_value: Vec<(Span, VarId)>,
    /// The order of the arguments of a call with named arguments, for a method
    /// of a value receiver and for a function item in a local: the span of the
    /// call and, for each parameter after the receiver, the index of its
    /// argument. The trailing block has the index after the last written
    /// argument. `None` is a parameter with no argument. The interpreter does
    /// not know these callees when it compiles the call, so it uses this order.
    /// This is not a relation of the spec.
    pub arg_order: Vec<(Span, Vec<Option<u32>>)>,
    /// The name that the body can write for each user effect that its
    /// diagnostics can name (the effects of `escapes_at`, `declared_effect`,
    /// `clause_performs` and `handlers`): the identity (`main.a.Note`) and the
    /// written name (`a.Note`, or `util.Note` for a dependency `util`). An
    /// effect that the body cannot name has no written name. Diagnostics show
    /// these names. This is not a relation of the spec.
    pub effect_names: Vec<(String, String)>,
    /// The user effects of `effect_names` that the body can see but cannot
    /// write: a nearer name hides the first name of each path to them (a
    /// module `a` inside the module of the body hides the module `a` of the
    /// root). Diagnostics tell why they show the identity. This is not a
    /// relation of the spec.
    pub hidden_effects: Vec<String>,
    /// The integer type of each arithmetic result: the span of the expression
    /// (the value of a compound assignment) and the name of the type (`u8`).
    /// The interpreter checks that the result fits in the type. This is not a
    /// relation of the spec.
    pub int_ops: Vec<(Span, String)>,
    /// The arguments that `arg_at`, `uniq_param` and `fn_arg_effect` name, for
    /// diagnostics. This is not a relation of the spec.
    pub arg_sites: Vec<ArgSite>,
    /// The places that `ref_at` and `ref_in` name, for diagnostics. This is not
    /// a relation of the spec.
    pub ref_sites: Vec<RefSite>,
    /// The number of local capabilities.
    pub caps: u32,

    /// `cfg_edge(P, Q)`.
    pub cfg_edge: Vec<(NodeId, NodeId)>,
    /// `points_into(R, Path)`.
    pub points_into: Vec<(VarId, PlaceId)>,
    /// `mutates_at(P, M)`.
    pub mutates_at: Vec<(NodeId, PlaceId)>,
    /// `reads_at(P, A)`.
    pub reads_at: Vec<(NodeId, PlaceId)>,
    /// `performs_at(P, Cap)`.
    pub performs_at: Vec<(NodeId, CapId)>,
    /// `footprint(Cap, M)`.
    pub footprint: Vec<(CapId, PlaceId)>,
    /// `rebound_at(V, P)`.
    pub rebound_at: Vec<(VarId, NodeId)>,
    /// `uses(V, P)`.
    pub uses: Vec<(VarId, NodeId)>,
    /// `moved_at(V, P)`.
    pub moved_at: Vec<(VarId, NodeId)>,
    /// `scope_end(V, P)`.
    pub scope_end: Vec<(VarId, NodeId)>,
    /// `overwrites(V, P)`: node `P` gives a part of `V` a new value, and the old
    /// value of the part goes away.
    pub overwrites: Vec<(VarId, NodeId)>,
    /// `unset_at(V, P)`: node `P` declares `V` with no value.
    pub unset_at: Vec<(VarId, NodeId)>,
    /// `empty_at(V, P)`: node `P` gives `V` a new value with no linear part, such
    /// as `None`.
    pub empty_at: Vec<(VarId, NodeId)>,
    /// `unwound_at(V, P)`: an abort path leaves the scope of `V` at node `P`. The
    /// unwinder finishes `V`.
    pub unwound_at: Vec<(VarId, NodeId)>,
    /// `owner(Rt, V)`: the root place `Rt` holds the value of `V`.
    pub owner: Vec<(PlaceId, VarId)>,
    /// `moved_part(M, P)`: node `P` moves the value at place `M` out of its owner.
    pub moved_part: Vec<(PlaceId, NodeId)>,
    /// `rest_linear(V, P)`: node `P` moves a part of `V`, and another part of
    /// `V` can hold a linear value. The rest of `V` is still live.
    pub rest_linear: Vec<(VarId, NodeId)>,
    /// `releases_at(P, M)`: node `P` can free the memory at place `M`, as a move
    /// out of its owner does. A `resume` does this for what a clause parameter
    /// points into.
    pub releases_at: Vec<(NodeId, PlaceId)>,
    /// `may_abort(P)`.
    pub may_abort: Vec<NodeId>,
    /// `multi_at(P)`.
    pub multi_at: Vec<NodeId>,
    /// `spared_at(V, P)`: an abort or a `multi` resume at node `P` does not
    /// reach `V`. Each handler that `P` suspends to is a local handler, and `V`
    /// lives outside its handled body.
    pub spared_at: Vec<(VarId, NodeId)>,
    /// `clause_multi(Cap)`: a clause of the handler behind `Cap` can resume a
    /// `multi` continuation more than once.
    pub clause_multi: Vec<CapId>,
    /// `body_multi(Cap)`: the computation that the handler behind `Cap` handles
    /// can resume a `multi` continuation more than once.
    pub body_multi: Vec<CapId>,
    /// `resumes_at(P, Cap)`: node `P` resumes the computation that the handler
    /// behind `Cap` handles.
    pub resumes_at: Vec<(NodeId, CapId)>,
    /// `clause_performs(H, E)`: a clause of handler `H` performs effect `E`
    /// through a handler outside `H`.
    pub clause_performs: Vec<(HandlerId, String)>,

    /// `has_signature()`.
    pub has_signature: bool,
    /// `declared_mut(D)`.
    pub declared_mut: Vec<PlaceId>,
    /// `declared_effect(E)`, closed under implication.
    pub declared_effect: Vec<String>,
    /// `escapes_at(P, E)`.
    pub escapes_at: Vec<(NodeId, String)>,
    /// `shared_root(S)`.
    pub shared_root: Vec<PlaceId>,

    /// `spawned_at(T, P)`.
    pub spawned_at: Vec<(TaskId, NodeId)>,
    /// `joined_at(T, P)`.
    pub joined_at: Vec<(TaskId, NodeId)>,
    /// `task_reads(T, A)`.
    pub task_reads: Vec<(TaskId, PlaceId)>,
    /// `task_writes(T, M)`.
    pub task_writes: Vec<(TaskId, PlaceId)>,
    /// `captures(T, V)`.
    pub captures: Vec<(TaskId, VarId)>,
    /// `mut_through(T, V)`.
    pub mut_through: Vec<(TaskId, VarId)>,
    /// `kept(T, Rt)`: task `T` keeps the variable at root place `Rt`. Its
    /// closure captures the variable, and the value is a copy value. The end of
    /// the variable leaves the value readable for `T`.
    pub kept: Vec<(TaskId, PlaceId)>,
    /// `spawns_in(T, U)`: task `U` starts inside the code of task `T`.
    pub spawns_in: Vec<(TaskId, TaskId)>,
    /// `opaque(T)`: task `T` runs code that the function cannot check for work
    /// stealing: a function value that it does not follow, or a callee that can
    /// start a pinned task.
    pub opaque: Vec<TaskId>,

    /// `call_mut(P, M, I)`.
    pub call_mut: Vec<(NodeId, PlaceId, u32)>,
    /// `call_arg(P, A, I)`.
    pub call_arg: Vec<(NodeId, PlaceId, u32)>,
    /// `lends_mut(P, M)`: the call at `P` gives `M` to a function value that can
    /// mutate through it.
    pub lends_mut: Vec<(NodeId, PlaceId)>,
    /// `writes_via(P, R)`: each mutation at node `P` is at or below the place
    /// that the reference `R` points to when `P` runs. `R` holds one reference.
    pub writes_via: Vec<(NodeId, VarId)>,
    /// `arg_at(P, I, A)`: the call at `P` gives parameter `I` a reference into
    /// `A`, and the parameter states an `in` place.
    pub arg_at: Vec<(NodeId, u32, PlaceId)>,
    /// `param_in(P, I, D)`: parameter `I` of the callee of the call at `P`
    /// states `in D`, in the places of the caller.
    pub param_in: Vec<(NodeId, u32, PlaceId)>,
    /// `uniq_param(P, I)`: parameter `I` of the callee of the call at `P` is a
    /// `@ uniq` reference. [`CLOSURE_ARG`] and more is a parameter of a call
    /// inside a closure that runs at `P`.
    pub uniq_param: Vec<(NodeId, u32)>,
    /// `arg_aliased(P, I)`: the argument for parameter `I` of the call at `P`
    /// can be aliased: it is not `@ uniq` there.
    pub arg_aliased: Vec<(NodeId, u32)>,
    /// `fn_arg_effect(P, I, E)`: the function argument for parameter `I` of the
    /// call at `P` performs `E`, and the parameter type states a row.
    pub fn_arg_effect: Vec<(NodeId, u32, String)>,
    /// `param_effect(P, I, E)`: the row of the type of parameter `I` of the
    /// callee of the call at `P` allows `E` (closed under implication).
    pub param_effect: Vec<(NodeId, u32, String)>,
    /// `sim_run_at(P)`: node `P` runs `sim.run`, or makes a value that can run it.
    pub sim_run_at: Vec<NodeId>,
    /// `ref_at(P, A)`: node `P` gives a reference into `A` to a place that
    /// states where it can point: the result of a function that states its
    /// returned places, or a place field of a `!Move` struct.
    pub ref_at: Vec<(NodeId, PlaceId)>,
    /// `ref_in(P, D)`: the place that gets the reference at node `P` states
    /// `D`, in the places of the body.
    pub ref_in: Vec<(NodeId, PlaceId)>,
    /// `std_effect(E)`: `E` is a standard effect. The list holds the standard
    /// effects that the other relations name.
    pub std_effects: Vec<String>,

    /// `library()`.
    pub library: bool,
    /// `started()`: the runtime starts the body: `main` or a test of the root.
    pub started: bool,
    /// `no_runtime()`: the runtime handles no effect of the body. The program
    /// has no runtime, and the body is `main`.
    pub no_runtime: bool,

    /// The interning index of places: parent and step to child. `add_root` and
    /// `child` keep it current.
    pub place_index: HashMap<(PlaceId, Step), PlaceId>,
}

impl FnFacts {
    /// Returns the sizes of the relations now (see [`FactMark`]).
    pub fn mark(&self) -> FactMark {
        // Each field is named, so that a new field gets a decision here.
        let Self {
            name: _,
            roots: _,
            places: _,
            vars: _,
            place_index: _,
            effect_names: _,
            hidden_effects: _,
            int_ops: _,
            started: _,
            no_runtime: _,
            caps,
            has_signature,
            library,
            nodes,
            tasks,
            handlers,
            by_value,
            arg_order,
            cfg_edge,
            points_into,
            mutates_at,
            reads_at,
            performs_at,
            footprint,
            rebound_at,
            uses,
            moved_at,
            scope_end,
            overwrites,
            unset_at,
            empty_at,
            unwound_at,
            owner,
            moved_part,
            rest_linear,
            releases_at,
            may_abort,
            multi_at,
            spared_at,
            clause_multi,
            body_multi,
            resumes_at,
            clause_performs,
            declared_mut,
            declared_effect,
            escapes_at,
            shared_root,
            spawned_at,
            joined_at,
            task_reads,
            task_writes,
            captures,
            mut_through,
            kept,
            spawns_in,
            opaque,
            call_mut,
            call_arg,
            lends_mut,
            writes_via,
            arg_sites,
            ref_sites,
            arg_at,
            param_in,
            uniq_param,
            arg_aliased,
            fn_arg_effect,
            param_effect,
            sim_run_at,
            ref_at,
            ref_in,
            std_effects,
        } = self;
        FactMark {
            caps: *caps,
            has_signature: *has_signature,
            library: *library,
            nodes: nodes.len(),
            tasks: tasks.len(),
            handlers: handlers.len(),
            by_value: by_value.len(),
            arg_order: arg_order.len(),
            cfg_edge: cfg_edge.len(),
            points_into: points_into.len(),
            mutates_at: mutates_at.len(),
            reads_at: reads_at.len(),
            performs_at: performs_at.len(),
            footprint: footprint.len(),
            rebound_at: rebound_at.len(),
            uses: uses.len(),
            moved_at: moved_at.len(),
            scope_end: scope_end.len(),
            overwrites: overwrites.len(),
            unset_at: unset_at.len(),
            empty_at: empty_at.len(),
            unwound_at: unwound_at.len(),
            owner: owner.len(),
            moved_part: moved_part.len(),
            rest_linear: rest_linear.len(),
            releases_at: releases_at.len(),
            may_abort: may_abort.len(),
            multi_at: multi_at.len(),
            spared_at: spared_at.len(),
            clause_multi: clause_multi.len(),
            body_multi: body_multi.len(),
            resumes_at: resumes_at.len(),
            clause_performs: clause_performs.len(),
            declared_mut: declared_mut.len(),
            declared_effect: declared_effect.len(),
            escapes_at: escapes_at.len(),
            shared_root: shared_root.len(),
            spawned_at: spawned_at.len(),
            joined_at: joined_at.len(),
            task_reads: task_reads.len(),
            task_writes: task_writes.len(),
            captures: captures.len(),
            mut_through: mut_through.len(),
            kept: kept.len(),
            spawns_in: spawns_in.len(),
            opaque: opaque.len(),
            call_mut: call_mut.len(),
            call_arg: call_arg.len(),
            lends_mut: lends_mut.len(),
            writes_via: writes_via.len(),
            arg_sites: arg_sites.len(),
            ref_sites: ref_sites.len(),
            arg_at: arg_at.len(),
            param_in: param_in.len(),
            uniq_param: uniq_param.len(),
            arg_aliased: arg_aliased.len(),
            fn_arg_effect: fn_arg_effect.len(),
            param_effect: param_effect.len(),
            sim_run_at: sim_run_at.len(),
            ref_at: ref_at.len(),
            ref_in: ref_in.len(),
            std_effects: std_effects.len(),
        }
    }

    /// Cuts the relations back to the sizes of `mark`. The tables of roots,
    /// places and variables stay.
    pub fn rewind(&mut self, mark: &FactMark) {
        let Self {
            name: _,
            roots: _,
            places: _,
            vars: _,
            place_index: _,
            effect_names: _,
            hidden_effects: _,
            int_ops: _,
            started: _,
            no_runtime: _,
            caps,
            has_signature,
            library,
            nodes,
            tasks,
            handlers,
            by_value,
            arg_order,
            cfg_edge,
            points_into,
            mutates_at,
            reads_at,
            performs_at,
            footprint,
            rebound_at,
            uses,
            moved_at,
            scope_end,
            overwrites,
            unset_at,
            empty_at,
            unwound_at,
            owner,
            moved_part,
            rest_linear,
            releases_at,
            may_abort,
            multi_at,
            spared_at,
            clause_multi,
            body_multi,
            resumes_at,
            clause_performs,
            declared_mut,
            declared_effect,
            escapes_at,
            shared_root,
            spawned_at,
            joined_at,
            task_reads,
            task_writes,
            captures,
            mut_through,
            kept,
            spawns_in,
            opaque,
            call_mut,
            call_arg,
            lends_mut,
            writes_via,
            arg_sites,
            ref_sites,
            arg_at,
            param_in,
            uniq_param,
            arg_aliased,
            fn_arg_effect,
            param_effect,
            sim_run_at,
            ref_at,
            ref_in,
            std_effects,
        } = self;
        *caps = mark.caps;
        *has_signature = mark.has_signature;
        *library = mark.library;
        nodes.truncate(mark.nodes);
        tasks.truncate(mark.tasks);
        handlers.truncate(mark.handlers);
        by_value.truncate(mark.by_value);
        arg_order.truncate(mark.arg_order);
        cfg_edge.truncate(mark.cfg_edge);
        points_into.truncate(mark.points_into);
        mutates_at.truncate(mark.mutates_at);
        reads_at.truncate(mark.reads_at);
        performs_at.truncate(mark.performs_at);
        footprint.truncate(mark.footprint);
        rebound_at.truncate(mark.rebound_at);
        uses.truncate(mark.uses);
        moved_at.truncate(mark.moved_at);
        scope_end.truncate(mark.scope_end);
        overwrites.truncate(mark.overwrites);
        unset_at.truncate(mark.unset_at);
        empty_at.truncate(mark.empty_at);
        unwound_at.truncate(mark.unwound_at);
        owner.truncate(mark.owner);
        moved_part.truncate(mark.moved_part);
        rest_linear.truncate(mark.rest_linear);
        releases_at.truncate(mark.releases_at);
        may_abort.truncate(mark.may_abort);
        multi_at.truncate(mark.multi_at);
        spared_at.truncate(mark.spared_at);
        clause_multi.truncate(mark.clause_multi);
        body_multi.truncate(mark.body_multi);
        resumes_at.truncate(mark.resumes_at);
        clause_performs.truncate(mark.clause_performs);
        declared_mut.truncate(mark.declared_mut);
        declared_effect.truncate(mark.declared_effect);
        escapes_at.truncate(mark.escapes_at);
        shared_root.truncate(mark.shared_root);
        spawned_at.truncate(mark.spawned_at);
        joined_at.truncate(mark.joined_at);
        task_reads.truncate(mark.task_reads);
        task_writes.truncate(mark.task_writes);
        captures.truncate(mark.captures);
        mut_through.truncate(mark.mut_through);
        kept.truncate(mark.kept);
        spawns_in.truncate(mark.spawns_in);
        opaque.truncate(mark.opaque);
        call_mut.truncate(mark.call_mut);
        call_arg.truncate(mark.call_arg);
        lends_mut.truncate(mark.lends_mut);
        writes_via.truncate(mark.writes_via);
        arg_sites.truncate(mark.arg_sites);
        ref_sites.truncate(mark.ref_sites);
        arg_at.truncate(mark.arg_at);
        param_in.truncate(mark.param_in);
        uniq_param.truncate(mark.uniq_param);
        arg_aliased.truncate(mark.arg_aliased);
        fn_arg_effect.truncate(mark.fn_arg_effect);
        param_effect.truncate(mark.param_effect);
        sim_run_at.truncate(mark.sim_run_at);
        ref_at.truncate(mark.ref_at);
        ref_in.truncate(mark.ref_in);
        std_effects.truncate(mark.std_effects);
    }

    /// Returns the place record.
    pub fn place(&self, p: PlaceId) -> &PlaceInfo {
        &self.places[p.index()]
    }

    /// Returns the name that the body can write for user effect `id`
    /// (see [`FnFacts::effect_names`]), or `None` if it has none.
    pub fn effect_name(&self, id: &str) -> Option<&str> {
        self.effect_names
            .iter()
            .find(|(e, _)| e == id)
            .map(|(_, w)| w.as_str())
    }

    /// Returns true if the body can see user effect `id` but cannot write a
    /// name for it (see [`FnFacts::hidden_effects`]).
    pub fn effect_hidden(&self, id: &str) -> bool {
        self.hidden_effects.iter().any(|e| e == id)
    }

    /// Returns the variable record.
    pub fn var(&self, v: VarId) -> &VarInfo {
        &self.vars[v.index()]
    }

    /// Returns the node record.
    pub fn node(&self, n: NodeId) -> &NodeInfo {
        &self.nodes[n.index()]
    }

    /// Returns true if the root of `p` needs a declaration to mutate.
    pub fn param_rooted(&self, p: PlaceId) -> bool {
        matches!(
            self.roots[self.place(p).root.index()].kind,
            RootKind::Param | RootKind::Group
        )
    }

    /// Adds a root and its root place. Returns the root place.
    pub fn add_root(&mut self, name: impl Into<String>, kind: RootKind) -> PlaceId {
        let name = name.into();
        let root = RootId(u32::try_from(self.roots.len()).unwrap_or(u32::MAX));
        self.roots.push(Root {
            name: name.clone(),
            kind,
        });
        self.push_place(PlaceInfo {
            root,
            parent: None,
            steps: Vec::new(),
            display: name,
            wild_base: None,
            one: None,
        })
    }

    /// Returns the child place of `parent` with one more step. Interns it.
    pub fn child(&mut self, parent: PlaceId, step: Step, text: &str) -> PlaceId {
        if let Some(&p) = self.place_index.get(&(parent, step)) {
            return p;
        }
        let base = self.place(parent);
        let mut steps = base.steps.clone();
        steps.push(step);
        // A place below a wildcard place is still somewhere inside its base. A
        // place below a one-place wildcard place `b..` is a place inside that
        // one place: `(b..).x`.
        let display = match base.steps.iter().find(|s| is_wild_step(s)) {
            Some(w) if is_one_step(w) && base.is_one_place() => {
                format!("({}){}", base.display, text)
            }
            Some(w) if is_one_step(w) => format!("{}{}", base.display, text),
            Some(_) => base.display.clone(),
            None => format!("{}{}", base.display, text),
        };
        let id = PlaceId(u32::try_from(self.places.len()).unwrap_or(u32::MAX));
        let wild_base = base
            .wild_base
            .or_else(|| is_wild_step(&step).then_some(parent));
        let one = base.one.or_else(|| is_one_step(&step).then_some(id));
        let info = PlaceInfo {
            root: base.root,
            parent: Some(parent),
            steps,
            display,
            wild_base,
            one,
        };
        let id = self.push_place(info);
        self.place_index.insert((parent, step), id);
        id
    }

    /// Returns the wildcard place under `p`: any place at or below `p`.
    ///
    /// If `p` is already at or below a wildcard place `b..`, the result is the
    /// outermost one, `b..`. Each place at or below `p` is inside `b..`, so
    /// this set includes the set of `p..`. Thus no place has two wildcard
    /// steps, and a chain such as `cur = step(cur)` stops at `b..`.
    pub fn wildcard(&mut self, p: PlaceId) -> PlaceId {
        let base = self.wild_base(p).unwrap_or(p);
        self.child(base, WILD, "..")
    }

    /// Returns the one-place wildcard place `inst` under `p` ([`wild_one`]): one
    /// place at or below `p`. As with [`FnFacts::wildcard`], a place at or below
    /// a wildcard place `b..` gives a place under `b`, so no place has two
    /// wildcard steps.
    pub fn wildcard_one(&mut self, p: PlaceId, inst: u32) -> PlaceId {
        let base = self.wild_base(p).unwrap_or(p);
        self.child(base, wild_one(inst), "..")
    }

    /// Returns the outermost one-place wildcard place at or above `p`. Two places
    /// with the same one are inside one place.
    pub fn one_place_of(&self, p: PlaceId) -> Option<PlaceId> {
        self.place(p).one
    }

    /// Returns the parent of the outermost wildcard step on the path of `p`.
    /// `p` can be any place at or below it.
    pub fn wild_base(&self, p: PlaceId) -> Option<PlaceId> {
        self.place(p).wild_base
    }

    fn push_place(&mut self, info: PlaceInfo) -> PlaceId {
        let id = PlaceId(u32::try_from(self.places.len()).unwrap_or(u32::MAX));
        self.places.push(info);
        id
    }

    /// Adds a variable.
    pub fn add_var(&mut self, info: VarInfo) -> VarId {
        let id = VarId(u32::try_from(self.vars.len()).unwrap_or(u32::MAX));
        self.vars.push(info);
        id
    }

    /// Adds a node.
    pub fn add_node(
        &mut self,
        span: Span,
        label: impl Into<String>,
        detail: impl Into<String>,
    ) -> NodeId {
        let id = NodeId(u32::try_from(self.nodes.len()).unwrap_or(u32::MAX));
        self.nodes.push(NodeInfo {
            span,
            label: label.into(),
            detail: detail.into(),
        });
        id
    }

    /// Adds a task.
    pub fn add_task(&mut self, kind: TaskKind, span: Span) -> TaskId {
        let id = TaskId(u32::try_from(self.tasks.len()).unwrap_or(u32::MAX));
        self.tasks.push(TaskInfo { kind, span });
        id
    }

    /// Adds a capability.
    pub const fn add_cap(&mut self) -> CapId {
        let id = CapId(self.caps);
        self.caps += 1;
        id
    }

    /// Sorts and deduplicates every relation, so that equal facts compare equal.
    pub fn normalize(&mut self) {
        fn nd<T: Ord>(v: &mut Vec<T>) {
            v.sort();
            v.dedup();
        }
        nd(&mut self.cfg_edge);
        nd(&mut self.points_into);
        nd(&mut self.mutates_at);
        nd(&mut self.reads_at);
        nd(&mut self.performs_at);
        nd(&mut self.footprint);
        nd(&mut self.rebound_at);
        nd(&mut self.uses);
        nd(&mut self.moved_at);
        nd(&mut self.scope_end);
        nd(&mut self.overwrites);
        nd(&mut self.unset_at);
        nd(&mut self.empty_at);
        nd(&mut self.unwound_at);
        nd(&mut self.owner);
        nd(&mut self.moved_part);
        nd(&mut self.rest_linear);
        nd(&mut self.releases_at);
        nd(&mut self.may_abort);
        nd(&mut self.multi_at);
        nd(&mut self.spared_at);
        nd(&mut self.clause_multi);
        nd(&mut self.body_multi);
        nd(&mut self.resumes_at);
        nd(&mut self.clause_performs);
        nd(&mut self.declared_mut);
        nd(&mut self.declared_effect);
        nd(&mut self.escapes_at);
        nd(&mut self.shared_root);
        nd(&mut self.spawned_at);
        nd(&mut self.joined_at);
        nd(&mut self.task_reads);
        nd(&mut self.task_writes);
        nd(&mut self.captures);
        nd(&mut self.mut_through);
        nd(&mut self.kept);
        nd(&mut self.spawns_in);
        nd(&mut self.opaque);
        nd(&mut self.call_mut);
        nd(&mut self.call_arg);
        nd(&mut self.lends_mut);
        nd(&mut self.writes_via);
        nd(&mut self.arg_at);
        nd(&mut self.param_in);
        nd(&mut self.uniq_param);
        nd(&mut self.arg_aliased);
        nd(&mut self.fn_arg_effect);
        nd(&mut self.param_effect);
        nd(&mut self.sim_run_at);
        nd(&mut self.ref_at);
        nd(&mut self.ref_in);
        nd(&mut self.std_effects);
    }
}

/// The violation relations of the spec. Both checkers produce this value.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Violations {
    /// `error(R, P)`: W0301.
    pub error: BTreeSet<(VarId, NodeId)>,
    /// `use_after_move(V, P)`: W0302, W0501, W0502.
    pub use_after_move: BTreeSet<(VarId, NodeId)>,
    /// `use_before_set(V, P)`: W0304.
    pub use_before_set: BTreeSet<(VarId, NodeId)>,
    /// `moved_immovable(V, P)`: W0604.
    pub moved_immovable: BTreeSet<(VarId, NodeId)>,
    /// `unconsumed(V, P)`: W0601.
    pub unconsumed: BTreeSet<(VarId, NodeId)>,
    /// `overwritten(V, P)`: W0601.
    pub overwritten: BTreeSet<(VarId, NodeId)>,
    /// `abort_unhandled(V, P)`: W0602.
    pub abort_unhandled: BTreeSet<(VarId, NodeId)>,
    /// `live_across_multi(V, P)`: W0503.
    pub live_across_multi: BTreeSet<(VarId, NodeId)>,
    /// `unauthorized_mut(P, M)`: W0703.
    pub unauthorized_mut: BTreeSet<(NodeId, PlaceId)>,
    /// `unauthorized_effect(P, E)`: W0702.
    pub unauthorized_effect: BTreeSet<(NodeId, String)>,
    /// `shared_mutation(P, M)`: W0402.
    pub shared_mutation: BTreeSet<(NodeId, PlaceId)>,
    /// `alias_conflict(P, M, A)`: W0312.
    pub alias_conflict: BTreeSet<(NodeId, PlaceId, PlaceId)>,
    /// `task_conflict(T, P)`: W0405.
    pub task_conflict: BTreeSet<(TaskId, NodeId)>,
    /// `nonportable_capture(T, V)`: W0401.
    pub nonportable_capture: BTreeSet<(TaskId, VarId)>,
    /// `shared_mut_capture(T, V)`: W0403.
    pub shared_mut_capture: BTreeSet<(TaskId, VarId)>,
    /// `root_handler_in_lib(H)`: W0801.
    pub root_handler_in_lib: BTreeSet<HandlerId>,
    /// `arg_outside(P, I, A)`: W0203.
    pub arg_outside: BTreeSet<(NodeId, u32, PlaceId)>,
    /// `ref_outside(P, A)`: W0204, W0605.
    pub ref_outside: BTreeSet<(NodeId, PlaceId)>,
    /// `not_uniq(P, I)`: W0406.
    pub not_uniq: BTreeSet<(NodeId, u32)>,
    /// `arg_effect_outside(P, I, E)`: W0705.
    pub arg_effect_outside: BTreeSet<(NodeId, u32, String)>,
    /// `sim_in_lib(P)`: W0802.
    pub sim_in_lib: BTreeSet<NodeId>,
    /// `unhandled_effect(P, E)`: W0805.
    pub unhandled_effect: BTreeSet<(NodeId, String)>,
    /// `embedded_effect(P, E)`: W0803.
    pub embedded_effect: BTreeSet<(NodeId, String)>,
    /// `stealable(T)`: information for the scheduler.
    pub stealable: BTreeSet<TaskId>,
}

impl Violations {
    /// Returns true if no rule fired (the `stealable` relation is not a violation).
    pub fn is_clean(&self) -> bool {
        self.error.is_empty()
            && self.use_after_move.is_empty()
            && self.use_before_set.is_empty()
            && self.moved_immovable.is_empty()
            && self.unconsumed.is_empty()
            && self.overwritten.is_empty()
            && self.abort_unhandled.is_empty()
            && self.live_across_multi.is_empty()
            && self.unauthorized_mut.is_empty()
            && self.unauthorized_effect.is_empty()
            && self.shared_mutation.is_empty()
            && self.alias_conflict.is_empty()
            && self.task_conflict.is_empty()
            && self.nonportable_capture.is_empty()
            && self.shared_mut_capture.is_empty()
            && self.root_handler_in_lib.is_empty()
            && self.arg_outside.is_empty()
            && self.ref_outside.is_empty()
            && self.not_uniq.is_empty()
            && self.arg_effect_outside.is_empty()
            && self.sim_in_lib.is_empty()
            && self.unhandled_effect.is_empty()
            && self.embedded_effect.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn child_places_are_interned() {
        let mut f = FnFacts::default();
        let w = f.add_root("world", RootKind::Param);
        let s = Step {
            kind: StepKind::Field { id: 0 },
            unstable: false,
        };
        let a = f.child(w, s, ".entities");
        let b = f.child(w, s, ".entities");
        assert_eq!(a, b);
        assert_eq!(f.place(a).display, "world.entities");
        assert_eq!(f.place(a).parent, Some(w));
        assert!(f.param_rooted(a));
        let l = f.add_root("lines", RootKind::Local);
        assert!(!f.param_rooted(l));
    }

    #[test]
    fn a_rewind_cuts_the_relations_and_keeps_the_tables() {
        let mut f = FnFacts::default();
        let w = f.add_root("world", RootKind::Param);
        let n0 = f.add_node(Span::default(), "a", "");
        f.mutates_at.push((n0, w));
        let mark = f.mark();
        let before = f.clone();
        let l = f.add_root("lines", RootKind::Local);
        let n1 = f.add_node(Span::default(), "b", "");
        f.mutates_at.push((n1, l));
        f.cfg_edge.push((n0, n1));
        let _ = f.add_cap();
        let _ = f.add_task(TaskKind::Spawn, Span::default());
        f.rewind(&mark);
        assert_eq!(f.nodes, before.nodes);
        assert_eq!(f.mutates_at, before.mutates_at);
        assert!(f.cfg_edge.is_empty() && f.tasks.is_empty());
        assert_eq!(f.add_cap(), CapId(0));
        // The tables stay, so that the places of the pass before stay valid.
        assert_eq!(f.roots.len(), 2);
        assert_eq!(f.place(l).display, "lines");
    }

    #[test]
    fn modes_of_values_and_captures() {
        // A join is `@ uniq` only if both values are.
        assert!(join_uniq(true, true));
        assert!(!join_uniq(true, false));
        assert!(!join_uniq(false, true));
        let mut v = VarInfo::plain("r", VarKind::Local, Span::default(), "&T");
        // A plain value crosses threads; a write through an aliased reference
        // makes it shared-mutable, so it does not.
        let crosses = |m: Modes| weft_verified::modes::submode(&m, &CROSSES_THREADS);
        assert!(crosses(v.capture_mode(false)));
        assert!(!crosses(v.capture_mode(true)));
        v.uniq = true;
        assert!(crosses(v.capture_mode(true)));
        v.nonportable = true;
        assert!(!crosses(v.capture_mode(false)));
    }

    #[test]
    fn ids_display_with_prefix() {
        assert_eq!(NodeId(3).to_string(), "n3");
        assert_eq!(VarId(1).to_string(), "v1");
        assert_eq!(PlaceId(0).to_string(), "p0");
        assert_eq!(TaskId(2).index(), 2);
    }

    #[test]
    fn normalize_sorts_and_dedups() {
        let mut f = FnFacts {
            cfg_edge: vec![
                (NodeId(2), NodeId(3)),
                (NodeId(0), NodeId(1)),
                (NodeId(2), NodeId(3)),
            ],
            ..FnFacts::default()
        };
        f.normalize();
        assert_eq!(
            f.cfg_edge,
            vec![(NodeId(0), NodeId(1)), (NodeId(2), NodeId(3))]
        );
        assert!(Violations::default().is_clean());
    }
}
