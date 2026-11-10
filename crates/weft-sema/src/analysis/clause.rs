//! Handlers in the analysis (`docs/ir.md` 6.5, 6.7; plan stage F14).
//!
//! A `handle` runs its handled body once (V15), so the analysis runs the
//! handled body as a part of the run of its site: the state before the
//! `handle`, with the capability, is the state at the entry of the handled
//! body ([`handle_run`]).
//!
//! A perform through the capability of a local handler runs the clause of
//! its operation. The clause runs while the handled body waits at the
//! perform, so the analysis runs the code of the clause before its first
//! resume point (the `pre` part) from the state at the perform, with the
//! parameters of the clause bound to the values of the arguments
//! ([`perform_run`]). The state after the perform is the join of the states
//! at the resume points of the clause, and the result of the perform is the
//! join of the values that the clause gives to `resume`. A clause that ends
//! with no `resume` aborts to its handler: the state of such an end joins the
//! state after the `handle`, and the abort edge of the perform gets it
//! ([`AbortEdge`], plan stage F15). A clause that resumes on each path never
//! aborts to its handler ([`lands`]).
//!
//! A call that runs a clause gives each parameter of the clause the places
//! that the callee can give it ([`given`], plan stage F15): the places that
//! the arguments reach, and the callee frame if the callee can give a place
//! of its frame.
//!
//! When the handled body returns, a `resume` of each clause that ran gives
//! back the value of the handled body, and the code of the clause after its
//! resume point runs (the `post` part): the analysis runs each clause from
//! the blocks after its resume points, with the locals of the clause from
//! the state at the resume point and the other locals from the state at the
//! end of the handled body. The value of the `handle` is the value of the
//! handled body and the value of each clause.
//!
//! The facts of a clause body are a component of the facts of its function
//! (`crate::factgen`), as a closure body is. Their analysis starts from the
//! join of the states at the performs that run the clause ([`Info::seeds`]),
//! and a `resume` there gives back the value of the handled body and the
//! state at its end ([`resume`]).
//!
//! A clause of a `multi` operation that can resume more than once runs the
//! rest of the handled body again from the node that ran it (plan stage
//! F16): the run of the handled body goes on from the block after each such
//! node, with the locals of the handled body as at the node (their copies)
//! and the locals of the site as at the later `resume` ([`handle_run`]).

use std::collections::{BTreeMap, BTreeSet};

use weft_ir::{BlockId, BodyId, BodyKind, HandlerId, LocalKind, Operand, Place, Program, TermKind};

use super::domain::{AbsVal, State, Tree};

/// The result of a transfer function.
type R = Result<(), AlphaError>;
use super::transfer::{self, Cx};
use super::{run_from, Mode, States};
use crate::factgen::alpha::AlphaError;

/// The blocks where a run starts, with the state there.
type Seeds = Vec<(BlockId, State)>;

/// The number of runs of the code of the clauses after their resume points
/// that the analysis does to find what a `resume` gives back: a clause
/// value can be the result of `resume` in another run of a clause.
const POST_ROUNDS: usize = 8;

/// What the analysis keeps about the handlers of one component, and the
/// run nodes of the clauses in the facts.
#[derive(Clone, Debug, Default)]
pub struct Handlers {
    /// The handlers whose handled body runs now, the innermost last.
    open: Vec<Open>,
    /// What the runs of each handler found (a join over the runs).
    info: BTreeMap<HandlerId, Info>,
    /// The nodes where the code of a clause runs (`crate::factgen::handlers`).
    pub runs: Vec<ClauseRun>,
    /// The `Main` node of each `Resume` of a clause in the facts, with the
    /// handler and the clause body.
    pub resumes: Vec<(weft_facts::NodeId, HandlerId, BodyId)>,
    /// The handler id and the capability id of each handler in the facts.
    pub ids: BTreeMap<HandlerId, (weft_facts::HandlerId, weft_facts::CapId)>,
    /// The `Exit` and `Post` nodes of each `handle` in the facts.
    pub ends: Vec<(HandlerId, weft_facts::NodeId, weft_facts::NodeId)>,
    /// The calls whose clauses of a local handler run while a task of the
    /// call can run (follow-up F19.5): the `Main` node, the handler, the
    /// task node that reads what the code of the clause at `Main` accesses,
    /// and the task that changes what the code of the clause changes
    /// (`crate::factgen::handlers::project`).
    pub wait_copies: Vec<(
        weft_facts::NodeId,
        HandlerId,
        weft_facts::NodeId,
        weft_facts::TaskId,
    )>,
    /// The tasks of the calls that stand for the tasks that can run while a
    /// clause of a local handler runs (follow-up F19.5,
    /// `crate::factgen::templates::wait_tasks`).
    pub wait_tasks: Vec<crate::factgen::templates::WaitTask>,
    /// The `Landing` node of each `handle` in the facts.
    pub landings: Vec<(HandlerId, weft_facts::NodeId)>,
    /// The state of the abort edge of the terminator that the analysis ran
    /// last, if it ran a clause (`super::edges` takes it).
    pub abort_edge: Option<AbortEdge>,
    /// For each body: the locals that a path from the entry to the
    /// terminator of each block can assign (one bit set for each block;
    /// `crate::factgen::handlers::unassigned`).
    pub assigned: BTreeMap<BodyId, Vec<Vec<u64>>>,
    /// For each body: its locals that a closure captures and that can hold
    /// a reference, with their variables
    /// (`crate::factgen::handlers::unbound_at_aborts`).
    pub unbound_vars: BTreeMap<BodyId, Vec<(weft_ir::LocalId, weft_facts::VarId)>>,
    /// The state at the re-entry of each node of a handled body that runs a
    /// clause of a `multi` handler (plan stage F16): the state before its
    /// `Copy` node, by body and block, with the values that the later
    /// `resume`s give to a perform.
    pub reentry: BTreeMap<(BodyId, BlockId), (State, Tree)>,
    /// The re-entry seeds of the handled bodies inside other bodies: a
    /// node of such a body that a later `resume` runs again (plan stage
    /// F16). The `handle` of the body adds them to the seeds of its run
    /// ([`handle_run`]).
    pub extra: BTreeMap<BodyId, Vec<(BlockId, State)>>,
    /// The nodes that can wait at a `multi` operation of a handler of a
    /// caller (`crate::factgen::frames::row_multi`, OL-R2a) that the run of
    /// a body passed: the body, the block, the block after the node and the
    /// state on its normal edge (`super::run`).
    pub rows: Vec<(BodyId, BlockId, BlockId, State)>,
    /// The run nodes whose function values can resume more than once (the
    /// analysis finds them: an applied summary is `multi`, plan stage F16).
    /// They are nodes of `crate::factgen::frames::row_multi` too.
    pub dyn_rows: std::collections::BTreeSet<(BodyId, BlockId)>,
    /// The nodes of `dyn_rows` where a summary other than code of a caller
    /// for a value of the interface is `multi` (issue #56). At another node
    /// of `dyn_rows` only the value that the caller gives can resume more
    /// than once (`crate::analysis::widen::Cycles::add_code_rows_at`).
    pub real_rows: std::collections::BTreeSet<(BodyId, BlockId)>,
    /// The handlers that a value that a run node (a body and a block) runs
    /// can reach (issues #57 and #58): a handler whose capability a closure
    /// captures (code of a caller, or a summary that performs the effect of
    /// the handler), and the local `Fail` handler of the call (code of a
    /// caller, or a summary that can fail). [`run_handlers`] reads it.
    pub cap_active: std::collections::BTreeSet<(BodyId, BlockId, HandlerId)>,
    /// The `Main` node of each perform of a closure body through a captured
    /// capability, with the index of the capture and the identity of the
    /// effect (plan stage F16): the summary of the closure performs through
    /// `Cap(k)`.
    pub cap_performs: Vec<(weft_facts::NodeId, u32, String)>,
    /// The nodes of [`Self::cap_performs`] where an operation can pass on to
    /// a caller through the handlers on the way (stage R0d): a `multi_at`
    /// row there stays a row of the summary of the closure.
    pub cap_callers: Vec<weft_facts::NodeId>,
    /// The callee frames whose heap slots hold while the clauses that their
    /// calls run are running, with the body of the call, the innermost last
    /// (`run_clause`).
    pub frames: Vec<(weft_facts::PlaceId, BodyId)>,
    /// The handlers whose capability a closure takes out of the `handle`,
    /// with how it leaves (W0313, plan stage F17).
    pub escapes: Vec<(HandlerId, Escape)>,
    /// The value of the result of the task of each spawn site, a join over
    /// the runs of the spawn (plan stage F18, `super::tasks`): `ScopeWait`
    /// gives it to the `TaskResult` local of a spawn statement.
    pub task_values: BTreeMap<weft_ir::SpawnId, Tree>,
    /// The scopes that the scope operand of each spawn site with no scope
    /// of its own (`SpawnDecl::scope` is `None`) can be, a join over the
    /// runs of the spawn (stage R0e, `super::tasks::SiteScope`).
    pub site_scopes: BTreeMap<weft_ir::SpawnId, super::tasks::SiteScope>,
    /// The `ScopeWait` nodes of each scope in the facts, with the node after
    /// each (stage R0e): a task of a spawn site that the analysis of a
    /// closure body finds later ends there too.
    pub scope_waits: Vec<(
        weft_ir::ScopeId,
        weft_facts::NodeId,
        Option<weft_facts::NodeId>,
    )>,
    /// The nodes where the cleanup chain of a scope body joins the tasks of
    /// the scope (stage R0e, as [`Self::scope_waits`]).
    pub scope_unwinds: Vec<(weft_ir::ScopeId, weft_facts::NodeId)>,
    /// The task of each spawn site of the component in the facts (plan
    /// stage F18).
    pub task_ids: BTreeMap<weft_ir::SpawnId, weft_facts::TaskId>,
    /// The nodes where a task ends (`joined_at` at a `join` or at
    /// `ScopeWait`): the templates give them the `lends_mut` of the writes
    /// of the task when the component is done (`crate::factgen::templates::task_ends`).
    pub task_ends: Vec<(weft_facts::TaskId, weft_facts::NodeId)>,
    /// The variables of the `ByRef` and `Kept` captures of each task that can hold a
    /// reference: the task reads (and writes, with `mut_through`) what each
    /// later value of the variable points into.
    /// The places that the variable points into at the spawn are in the
    /// footprint already: only the other places count.
    pub task_cells: Vec<(
        weft_facts::TaskId,
        weft_facts::VarId,
        std::collections::BTreeSet<weft_facts::PlaceId>,
    )>,
    /// The `Main` node of each `join` that ends the handle of a task of a
    /// caller (`super::tasks::iface`), with its interface site.
    pub iface_joins: Vec<(weft_ir::SpawnId, weft_facts::NodeId)>,
    /// The program runs with no runtime (`// weft: no-runtime`): no root
    /// handler serves a standard effect on a task (plan stage F18).
    pub no_runtime: bool,
    /// The closure bodies that a task runs, for each task that W0314
    /// rejects (`crate::factgen::templates::task_start`, stage R0c). A
    /// clause that a node of such a body runs runs on another task: the
    /// continuation of its `resume` has no node of the handled body
    /// (`crate::factgen::handlers`, `Region::starts`).
    pub w0314_bodies: std::collections::BTreeSet<BodyId>,
    /// The places that the clauses of the local handlers of a call can give
    /// back to the callee in a reference result of their operation, by the
    /// run node of the call (stage R0h, D3 form R, [`back_places`]): σ of
    /// `Caller` at the call has them too (`super::apply`).
    pub back: BTreeMap<u32, Vec<weft_facts::PlaceId>>,
    /// The function values that the clauses of the local handlers of a call
    /// give back to the callee with `resume`, and the places that their
    /// values point into, by the body and the block of the call (stage R0h,
    /// D3 form F, [`call_clauses`]): a join over the runs of the call. The
    /// call node runs them as code of a caller runs a value.
    pub given_back: BTreeMap<(BodyId, BlockId), (BTreeSet<super::FnVal>, Vec<weft_facts::PlaceId>)>,
    /// The places that the values of [`Self::given_back`] point into, by the
    /// run node: the environment of a closure of a clause that has no
    /// operand at the call (`super::apply::made_sigma`).
    pub given_refs: BTreeMap<u32, Vec<weft_facts::PlaceId>>,
    /// [`back_places`] runs: the run nodes that it reads ([`given`]) do not
    /// look for their own back places again.
    pub back_busy: bool,
    /// The run nodes that apply the summary of a function with the part
    /// `caller_muts` and that have no back places (stage R0h fix): the body
    /// itself can change a place that a clause of a caller gives back, so
    /// its summary gets `caller_muts` too (`Emitted::caller_muts`).
    pub caller_muts_at: BTreeSet<weft_facts::NodeId>,
    /// The run nodes that apply the summary of a function or a closure with
    /// the part `unknown_runs` (plan stage R0i fix): the body runs a
    /// function value that it does not know through its callee, so its
    /// summary gets the part too (`Emitted::code_unknown`).
    pub unknown_runs_at: BTreeSet<weft_facts::NodeId>,
    /// A clause of a handler of the body runs a function value that it
    /// does not know (`templates::Em::code_unknown` of the clause, plan stage
    /// R0i-b): the body runs it where the clause runs.
    pub clause_unknown: bool,
    /// What the values that the clauses of the local handlers of a call give
    /// to `resume` point into, for an operation with a reference result, by
    /// the body and the block of the call (stage R0h, D3 form R): a join
    /// over the runs of the call. [`back_places`] adds them (a reference
    /// into a local of a clause, too).
    pub back_refs: BTreeMap<(BodyId, BlockId), BTreeSet<weft_facts::PlaceId>>,
}

/// How a closure that captures the capability of a handler leaves the
/// `handle` (W0313, `docs/ir.md` 6.9).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Escape {
    /// It is in the value of the `handle`.
    Value,
    /// A local of the site keeps it (the name of the local).
    Local(String),
    /// A heap slot that a local of the site or a parameter reaches keeps it.
    Stored,
    /// The handled body gives it to code that can keep it (a clause of the
    /// handler itself runs it).
    Given,
    /// A closure that resumes the continuation of a clause (the body) leaves
    /// the clause (stage R0g; the old lowering, `check_cont_escape`).
    Kont(BodyId, KontEscape),
}

/// How a closure that resumes the continuation of a clause leaves the
/// clause (W0313, [`Escape::Kont`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KontEscape {
    /// It is in the value of the clause.
    Value,
    /// A local outside the `handle` keeps it (the name of the local).
    Local(Option<String>),
    /// A heap slot keeps it.
    Stored,
    /// A `resume` gives it to the handled body.
    Resumed,
}

impl Escape {
    /// True if `self` and `o` are one report: the same handler and the same
    /// kind (a capability, or the continuation of one clause).
    pub fn same_report(a: &(HandlerId, Self), b: &(HandlerId, Self)) -> bool {
        let clause = |e: &Self| match e {
            Self::Kont(cb, _) => Some(*cb),
            _ => None,
        };
        a.0 == b.0 && clause(&a.1) == clause(&b.1)
    }
}

/// The clause whose continuation capture `k` of closure `c` holds.
///
/// The source of the capture is the continuation local of a clause (or an
/// upvar local of one), or a `Kont` capture of the maker (stage R0g).
pub fn kont_capture_clause(p: &Program, c: weft_ir::ClosureId, k: u32) -> Option<BodyId> {
    let mut decl = p.closures.get(c.index())?;
    let mut k = k;
    for _ in 0..=p.closures.len() {
        let cap = decl.captures.get(k as usize)?;
        if cap.mode != weft_ir::CaptureMode::Kont {
            return None;
        }
        if let Some((_, cb, _)) = kont_handler(p, decl.maker, &cap.source) {
            return Some(cb);
        }
        let (c2, k2, _) = crate::factgen::alpha::env_capture(p, decl.maker, &cap.source)?;
        decl = p.closures.get(c2.index())?;
        k = k2;
    }
    None
}

/// True if function value `f` can resume the continuation of clause `cb`:
/// a closure that captures it, or that holds such a value (a `ByMove`
/// capture is in the value; a `Kept` or `ByRef` capture has the value of
/// its variable in state `st`). `depth` bounds the walk.
fn resumes_kont(p: &Program, cb: BodyId, f: &super::FnVal, st: &State, depth: usize) -> bool {
    let (super::FnVal::Closure(c) | super::FnVal::Made(c)) = f else {
        return false;
    };
    let Some(d) = p.closures.get(c.index()) else {
        return false;
    };
    d.captures
        .iter()
        .enumerate()
        .any(|(k, cap)| match cap.mode {
            weft_ir::CaptureMode::Kont => {
                u32::try_from(k)
                    .ok()
                    .and_then(|k| kont_capture_clause(p, *c, k))
                    == Some(cb)
            }
            weft_ir::CaptureMode::Kept | weft_ir::CaptureMode::ByRef if depth > 0 => {
                cap.source.proj.is_empty()
                    && crate::factgen::alpha::owner_local(p, d.maker, cap.source.local)
                        .ok()
                        .and_then(|key| st.tree(key))
                        .is_some_and(|t| {
                            t.flat()
                                .fns
                                .iter()
                                .any(|g| resumes_kont(p, cb, g, st, depth - 1))
                        })
            }
            _ => false,
        })
}

/// True if value `v` holds a function value that can resume the
/// continuation of clause `cb` ([`resumes_kont`]).
fn holds_kont(p: &Program, cb: BodyId, v: &Tree, st: &State) -> bool {
    v.flat()
        .fns
        .iter()
        .any(|f| resumes_kont(p, cb, f, st, RUN_DEPTH_CAP))
}

/// Notes W0313 for a closure that resumes the continuation of clause `cb`
/// of handler `h` and leaves the clause (stage R0g; the old lowering,
/// `check_cont_escape`): in the value `value` of the clause, in a local
/// outside the `handle` or in a heap slot of state `st` at an end of the
/// clause, or in the argument `resumed` of a `resume`.
fn check_kont_escape(
    cx: &mut Cx<'_>,
    (h, cb): (HandlerId, BodyId),
    st: &State,
    value: Option<&Tree>,
    resumed: Option<&Tree>,
) {
    let p = cx.p;
    if p.body(cb).and_then(|b| b.kont).is_none() {
        return;
    }
    let Some(d) = p.handlers.get(h.index()) else {
        return;
    };
    let frame = InsideAny::new(
        p,
        d.clauses
            .iter()
            .map(|(_, c)| *c)
            .chain([d.handled])
            .collect(),
    );
    let how = if value.is_some_and(|v| holds_kont(p, cb, v, st)) {
        Some(KontEscape::Value)
    } else if resumed.is_some_and(|v| holds_kont(p, cb, v, st)) {
        Some(KontEscape::Resumed)
    } else if let Some((k, _)) = st
        .trees()
        .filter(|(k, _)| !frame.test(k.0))
        .find(|(_, t)| holds_kont(p, cb, t, st))
    {
        Some(KontEscape::Local(
            p.body(k.0)
                .and_then(|b| b.local(k.1))
                .and_then(|x| x.name.clone()),
        ))
    } else if st
        .behind_fns()
        .values()
        .any(|fs| fs.iter().any(|f| resumes_kont(p, cb, f, st, RUN_DEPTH_CAP)))
    {
        Some(KontEscape::Stored)
    } else {
        None
    };
    if let Some(how) = how {
        let e = (h, Escape::Kont(cb, how));
        if !cx.hx.escapes.iter().any(|x| Escape::same_report(x, &e)) {
            cx.hx.escapes.push(e);
        }
    }
}

/// The state of the abort edge of a terminator that runs a clause.
///
/// It is the state of the clause where it aborts (plan stage F15), to its
/// handler (it ends with no `resume`) or past it, with no local of the
/// clause.
#[derive(Clone, Debug)]
pub enum AbortEdge {
    /// A `perform` through a local capability: it aborts only where the
    /// clause aborts.
    Replace(State),
    /// A call: the callee can abort too, so the state before the call
    /// joins.
    Join(State),
}

/// A node where the code of a clause runs (plan stage F14).
///
/// A perform through the capability of a local handler runs the code of the
/// clause before its first resume point, and the `Post` node of a `handle`
/// runs the code after its resume points.
#[derive(Clone, Debug)]
pub struct ClauseRun {
    /// The node.
    pub node: weft_facts::NodeId,
    /// The handler.
    pub handler: HandlerId,
    /// The clause body.
    pub clause: BodyId,
    /// The code after the resume points (`Post`), else the code before them.
    pub post: bool,
    /// σ of each parameter of the clause: the places of the argument
    /// (empty at `Post`: the places of each perform of the clause).
    pub args: Vec<Vec<weft_facts::PlaceId>>,
    /// What the references behind each argument point into.
    pub helds: Vec<Vec<weft_facts::PlaceId>>,
    /// The handle places `h.*` of the `Rc` handles on the way to each
    /// argument: a reference through a handle depends on it (ADR 0003).
    pub deps: Vec<Vec<weft_facts::PlaceId>>,
    /// The body of the node.
    pub at: BodyId,
    /// The handled bodies of the local handlers that each abort of the node
    /// goes to, if each abort goes to one (none if one can go past the
    /// function): the variables outside them are spared (`spared_at`).
    pub spares: Option<Vec<BodyId>>,
    /// The parameter whose root each parameter of the clause has in
    /// `call_mut`: a parameter of the operation with an `in` place has the
    /// root of the parameter of its place (R3RT7). Empty: its own root.
    pub ins: Vec<usize>,
    /// The node is a call: σ of each parameter is the places that the call
    /// gives (`given`, plan stage F15), not an argument of the node. Each
    /// given place of an argument has the callee root of its parameter: a
    /// change below it has that root in `call_mut`.
    pub given: Option<Vec<(weft_facts::PlaceId, u32)>>,
}

/// A handler whose handled body runs now.
#[derive(Clone, Debug)]
struct Open {
    /// The handler.
    handler: HandlerId,
    /// The state at each resume point of a clause that a perform ran: the
    /// clause body, the block and the state after its statements.
    resumes: Vec<(BodyId, BlockId, State)>,
    /// The join of the states where a clause ended with no `resume`, with
    /// no local of the clause.
    landing: Option<State>,
    /// The join of the values of the clauses that ended with no `resume`.
    landing_value: Tree,
    /// The nodes of the handled body that run a clause of a `multi`
    /// handler that can resume more than once ([`multi_twice`]), with the
    /// state on their normal edge (plan stage F16): a later `resume` runs
    /// the code after them again.
    reentries: Vec<Reentry>,
    /// A node in a body inside the handled body runs such a clause (not
    /// in scope).
    nested: bool,
    /// The value and the state (before the `resume`) of each `resume` that
    /// the code of a clause after its first resume point runs: a second
    /// `resume` of a `multi` continuation (plan stage F16).
    again: Vec<(Tree, State)>,
    /// The state on each abort edge of a node of the run that goes to a
    /// local handler outside this handler, with that handler (stage R0g):
    /// the abort leaves the handled body.
    past: Vec<(State, HandlerId)>,
}

/// A node of the handled body that runs a clause that can resume more than
/// once (plan stage F16).
#[derive(Clone, Debug)]
struct Reentry {
    /// The body of the node.
    body: BodyId,
    /// The block of the node.
    block: BlockId,
    /// The block after the node.
    next: BlockId,
    /// The destination of a perform: it gets the values of the later
    /// `resume`s too. None for a call (the callee gives its result).
    dest: Option<Place>,
    /// The state on the normal edge of the node.
    state: State,
}

/// The number of runs of a handled body that the analysis does to find the
/// states of the re-runs of a `multi` handler (plan stage F16).
const MULTI_ROUNDS: usize = 8;

/// What the runs of one handler found.
#[derive(Clone, Debug, Default)]
pub struct Info {
    /// For each clause body: the join of the states at the performs that
    /// run it, after the moves of the arguments (the parameters of the clause
    /// do not have a value there).
    pub seeds: BTreeMap<BodyId, State>,
    /// The join of the states at the `Return` of the handled body.
    pub exit: Option<State>,
    /// What a `resume` gives back: the value of the handled body, and the
    /// value of each clause after a `resume`.
    pub resumed: Tree,
    /// For each clause body: the join of the values of its parameters at
    /// the nodes that run it (the places of the arguments). The facts of
    /// the clause give each parameter these places besides its own root,
    /// so a value of the clause in a place of the site has places of the
    /// site (plan stage F15).
    pub params: BTreeMap<BodyId, Vec<Tree>>,
}

impl Handlers {
    /// What the runs of handler `h` found, if a run found something.
    pub fn info(&self, h: HandlerId) -> Option<&Info> {
        self.info.get(&h)
    }

    /// The open handler `h`, if its handled body runs now.
    fn open_mut(&mut self, h: HandlerId) -> Option<&mut Open> {
        self.open.iter_mut().rev().find(|o| o.handler == h)
    }
}

/// True if body `b` is handled body `hb`, or a handled body whose nodes
/// splice into `hb` (through the handled bodies on the way): its frames
/// are frames of a run of `hb`.
pub fn spliced_into(p: &Program, b: BodyId, hb: BodyId) -> bool {
    let mut at = b;
    for _ in 0..=p.bodies.len() {
        if at == hb {
            return true;
        }
        let Some(x) = p.bodies.get(at.index()) else {
            return false;
        };
        match (x.kind, x.parent) {
            // A scope body splices into its site too (plan stage F19).
            (BodyKind::Handled(_) | BodyKind::Scope(_), Some(site)) => at = site,
            _ => return false,
        }
    }
    false
}

/// A test if a body is inside one of the bodies `roots` (each [`inside`]),
/// with the result of each body on the way kept: a state has the locals of
/// many bodies of one chain, and a test for each of them walked the chain
/// again (stage C1.4, `redteam/crash/d09.wf`).
struct InsideAny<'a> {
    /// The program.
    p: &'a Program,
    /// The bodies.
    roots: Vec<BodyId>,
    /// The result of each body, once known.
    memo: std::cell::RefCell<std::collections::HashMap<BodyId, bool>>,
}

impl<'a> InsideAny<'a> {
    /// The test for the bodies `roots`.
    fn new(p: &'a Program, roots: Vec<BodyId>) -> Self {
        Self {
            p,
            roots,
            memo: std::cell::RefCell::default(),
        }
    }

    /// True if `inside(p, b, r)` for a body `r` of the roots.
    fn test(&self, b: BodyId) -> bool {
        let mut memo = self.memo.borrow_mut();
        let mut path = Vec::new();
        let mut at = Some(b);
        let mut out = false;
        for _ in 0..=self.p.bodies.len() {
            let Some(x) = at else {
                break;
            };
            if let Some(&known) = memo.get(&x) {
                out = known;
                break;
            }
            path.push(x);
            if self.roots.contains(&x) {
                out = true;
                break;
            }
            at = self.p.bodies.get(x.index()).and_then(|d| d.parent);
        }
        for x in path {
            memo.insert(x, out);
        }
        out
    }
}

/// True if body `b` is body `root` or a body inside it: the parent chain of
/// `b` reaches `root`.
pub fn inside(p: &Program, b: BodyId, root: BodyId) -> bool {
    let mut at = Some(b);
    for _ in 0..=p.bodies.len() {
        let Some(x) = at else {
            return false;
        };
        if x == root {
            return true;
        }
        at = p.bodies.get(x.index()).and_then(|d| d.parent);
    }
    false
}

/// The handler of the capability in `place` of body `body`.
///
/// `place` is a whole capability local of a handled body, or an upvar local
/// of one. `None` for another place (a capability in the environment of a
/// closure).
pub fn cap_handler(p: &Program, body: BodyId, place: &Place) -> Option<HandlerId> {
    if !place.proj.is_empty() {
        return None;
    }
    let (ob, ol) = crate::factgen::alpha::owner_local(p, body, place.local).ok()?;
    let b = p.body(ob)?;
    match (b.kind, b.local_kind(ol)?) {
        (BodyKind::Handled(h), LocalKind::Cap(_)) => Some(h),
        _ => None,
    }
}

/// True if terminator `t` of body `body` never goes on to its next block.
///
/// It is a perform through the capability of a local handler whose clause
/// of the operation has no `resume` (plan stage F19), such as `fail` of a
/// local `Fail` handler.
pub fn perform_never_returns(p: &Program, body: BodyId, t: &TermKind) -> bool {
    let TermKind::Perform {
        cap: weft_ir::CapOperand::Local(cap),
        op,
        ..
    } = t
    else {
        return false;
    };
    perform_target(p, body, cap, *op)
        .flatten()
        .and_then(|h| p.handlers.get(h.index()))
        .and_then(|d| d.clauses.iter().find(|(o, _)| o == op).map(|(_, c)| *c))
        .is_some_and(|c| !has_resume(p, c))
}

/// The capture index and the effect of a captured capability.
///
/// Closure body `body` holds the capability in its environment field
/// `place` (a `Cap` capture, plan stage F16): a perform through it is a
/// perform of an operation of a handler outside the closure.
pub fn captured_cap(
    p: &Program,
    tys: &weft_ir::TyTable,
    body: BodyId,
    place: &Place,
) -> Option<(u32, weft_ir::EffectId)> {
    if place.proj.len() != 1 {
        return None;
    }
    let (c, k, mode) = crate::factgen::alpha::env_capture(p, body, place)?;
    if mode != weft_ir::CaptureMode::Cap {
        return None;
    }
    let decl = p.closures.get(c.index())?;
    let src = &decl.captures.get(k as usize)?.source;
    let e = cap_effect_of(p, tys, decl.maker, src, 0)?;
    Some((k, e))
}

/// The effect of the capability in place `src` of body `body`: a
/// capability local, an upvar local of one, or a `Cap` capture of a closure
/// environment (through the makers).
fn cap_effect_of(
    p: &Program,
    tys: &weft_ir::TyTable,
    body: BodyId,
    src: &Place,
    depth: usize,
) -> Option<weft_ir::EffectId> {
    if depth > p.bodies.len() {
        return None;
    }
    if src.proj.is_empty() {
        let ty = p.body(body)?.local(src.local)?.ty;
        return match tys.try_get(ty) {
            Some(weft_ir::Ty::Cap(e)) => Some(*e),
            _ => None,
        };
    }
    let (c, k, mode) = crate::factgen::alpha::env_capture(p, body, src)?;
    if mode != weft_ir::CaptureMode::Cap || src.proj.len() != 1 {
        return None;
    }
    let decl = p.closures.get(c.index())?;
    let inner = &decl.captures.get(k as usize)?.source;
    cap_effect_of(p, tys, decl.maker, inner, depth + 1)
}

/// The local handler whose capability capture `k` of closure `c` holds.
///
/// The source of the capture is a capability local of a handled body (or
/// an upvar local of one), or a `Cap` capture of the maker (plan stage
/// F16).
pub fn capture_handler(p: &Program, c: weft_ir::ClosureId, k: u32) -> Option<HandlerId> {
    let mut decl = p.closures.get(c.index())?;
    let mut k = k;
    for _ in 0..=p.closures.len() {
        let cap = decl.captures.get(k as usize)?;
        if cap.mode != weft_ir::CaptureMode::Cap {
            return None;
        }
        if let Some(h) = cap_handler(p, decl.maker, &cap.source) {
            return Some(h);
        }
        let (c2, k2, _) = crate::factgen::alpha::env_capture(p, decl.maker, &cap.source)?;
        decl = p.closures.get(c2.index())?;
        k = k2;
    }
    None
}

/// The handler that serves operation `op` of a perform through the
/// capability of handler `h` (stage R0d).
///
/// A handler with no clause for an operation passes it on to the handler
/// of the effect around its `handle` (stage R0b, `docs/ir.md` 5.26): the
/// handler of the first environment of that chain that adds the effect. A
/// closure environment adds a captured capability: its handler is the
/// handler of the capture (`capture_handler`). Returns `None` if no local
/// handler serves it: the operation passes on to a caller (through the
/// row).
pub fn serving(p: &Program, h: HandlerId, op: weft_ir::OpIdx) -> Option<HandlerId> {
    let mut h = h;
    for _ in 0..=p.handlers.len() {
        match serving_path(p, h, op) {
            Served::Local(x) => return Some(x),
            Served::Caller => return None,
            Served::Capture(cb, k) => {
                let (c, _) = p.closure_of(cb)?;
                h = capture_handler(p, c, k)?;
            }
        }
    }
    None
}

/// Where an operation that the capability of a handler gets goes, up to the
/// first closure environment on the way ([`serving_path`], stage R0d).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Served {
    /// A local handler with a clause for the operation.
    Local(HandlerId),
    /// The capture `k` of closure body `cb`: a handler outside the closure
    /// serves it. The summary of the closure performs through `Cap(k)`.
    Capture(BodyId, u32),
    /// No handler of the program around serves it: a handler of a caller.
    Caller,
}

/// [`serving`] up to the first closure environment on the way (stage R0d).
pub fn serving_path(p: &Program, h: HandlerId, op: weft_ir::OpIdx) -> Served {
    let mut h = h;
    for _ in 0..=p.handlers.len() {
        let Some(d) = p.handlers.get(h.index()) else {
            return Served::Caller;
        };
        if d.clauses.iter().any(|(o, _)| *o == op) {
            return Served::Local(h);
        }
        let Some(hb) = p.body(d.handled) else {
            return Served::Caller;
        };
        let mut at = p.cap_envs.get(hb.cap_env.index()).and_then(|e| e.parent);
        let mut next = None;
        for _ in 0..=p.cap_envs.len() {
            let Some(id) = at else { break };
            let Some(env) = p.cap_envs.get(id.index()) else {
                break;
            };
            if let Some((_, place)) = env.adds.iter().find(|(e, _)| *e == d.effect) {
                next = Some((id, place.clone()));
                break;
            }
            at = env.parent;
        }
        let Some((id, place)) = next else {
            return Served::Caller;
        };
        let opener = p.bodies.iter().enumerate().find_map(|(i, b)| {
            (b.cap_env == id && matches!(b.kind, BodyKind::Handled(_) | BodyKind::Closure(_)))
                .then(|| BodyId(u32::try_from(i).unwrap_or(u32::MAX)))
        });
        let Some(opener) = opener else {
            return Served::Caller;
        };
        match p.body(opener).map(|b| b.kind) {
            Some(BodyKind::Handled(h2)) => h = h2,
            Some(BodyKind::Closure(_)) => {
                return match crate::factgen::alpha::env_capture(p, opener, &place) {
                    Some((_, k, weft_ir::CaptureMode::Cap)) => Served::Capture(opener, k),
                    _ => Served::Caller,
                };
            }
            _ => return Served::Caller,
        }
    }
    Served::Caller
}

/// [`serving_path`] of each operation of the effect of handler `h` (stage R0d).
///
/// For an operation that the node does not know: a callee or a closure
/// that performs the effect.
pub fn serving_paths(p: &Program, tys: &weft_ir::TyTable, h: HandlerId) -> Vec<Served> {
    let n = p
        .handlers
        .get(h.index())
        .and_then(|d| tys.effects().get(d.effect.index()))
        .map_or(0, |e| e.ops.len());
    let mut out: Vec<Served> = (0..n)
        .map(|i| serving_path(p, h, weft_ir::OpIdx(u32::try_from(i).unwrap_or(u32::MAX))))
        .collect();
    if out.is_empty() {
        out.push(Served::Local(h));
    }
    out.dedup();
    out
}

/// The capture and the effect of a perform that passes on out of the closure
/// (stage R0d, [`Served::Capture`]).
///
/// The perform is through the capability local `cap` of body `body`, and
/// the capture is a capture of the closure body of `body`.
pub fn passes_to_capture(
    p: &Program,
    body: BodyId,
    cap: &Place,
    op: weft_ir::OpIdx,
) -> Option<(u32, weft_ir::EffectId)> {
    let h = cap_handler(p, body, cap)?;
    match serving_path(p, h, op) {
        Served::Capture(cb, k) if Some(cb) == crate::factgen::alpha::unit_closure(p, body) => {
            p.handlers.get(h.index()).map(|d| (k, d.effect))
        }
        _ => None,
    }
}

/// The handlers that a perform through the capability of handler `h` can
/// run, for an operation that the node does not know.
///
/// The node is a callee or a closure that performs the effect. They are
/// `h`, and the handler that serves each operation that `h` passes on
/// ([`serving`]). The flag is true if an operation passes on to a caller.
pub fn serving_all(p: &Program, tys: &weft_ir::TyTable, h: HandlerId) -> (Vec<HandlerId>, bool) {
    let mut out = vec![h];
    let mut caller = false;
    let n = p
        .handlers
        .get(h.index())
        .and_then(|d| tys.effects().get(d.effect.index()))
        .map_or(0, |e| e.ops.len());
    for i in 0..n {
        let op = weft_ir::OpIdx(u32::try_from(i).unwrap_or(u32::MAX));
        match serving(p, h, op) {
            Some(x) => out.push(x),
            None => caller = true,
        }
    }
    out.sort();
    out.dedup();
    (out, caller)
}

/// Where a perform of operation `op` through the whole capability local
/// `cap` of body `body` goes (stage R0d).
///
/// `Some(Some(h))` for the local handler `h` that serves it ([`serving`]),
/// `Some(None)` if it passes on to a caller, and `None` if `cap` is not the
/// capability of a local handler (a captured capability).
pub fn perform_target(
    p: &Program,
    body: BodyId,
    cap: &Place,
    op: weft_ir::OpIdx,
) -> Option<Option<HandlerId>> {
    cap_handler(p, body, cap).map(|h| match serving_path(p, h, op) {
        Served::Local(x) => Some(x),
        Served::Capture(..) | Served::Caller => None,
    })
}

/// The effect of a perform that passes on to a caller ([`perform_target`]).
///
/// The perform is of operation `op` through the capability local `cap` of
/// body `body`: the handler of the capability has no clause for it, and no
/// local handler serves it. `None` for each other perform.
pub fn passes_to_caller(
    p: &Program,
    body: BodyId,
    cap: &Place,
    op: weft_ir::OpIdx,
) -> Option<weft_ir::EffectId> {
    let h = cap_handler(p, body, cap)?;
    if serving_path(p, h, op) != Served::Caller {
        return None;
    }
    p.handlers.get(h.index()).map(|d| d.effect)
}

/// The closure body and the index of the `Cap` capture whose field of the
/// environment fact place `q` is (stage R0d).
///
/// A closure that a closure makes captures the capability again, and a
/// perform through the inner capture is a perform through this one.
pub fn env_cap_of(
    p: &Program,
    facts: &weft_facts::FnFacts,
    roots: &crate::factgen::alpha::Roots,
    q: weft_facts::PlaceId,
) -> Option<(BodyId, u32)> {
    let ((cb, l), path) = roots.path_of(facts, q)?;
    let (_, decl) = p.closure_of(cb)?;
    if p.body(cb)?.params.first() != Some(&l) {
        return None;
    }
    let [super::domain::PathStep::Field(k)] = path.as_slice() else {
        return None;
    };
    (decl.captures.get(*k as usize)?.mode == weft_ir::CaptureMode::Cap).then_some((cb, *k))
}

/// The local handlers whose capability a closure of the program captures.
///
/// A run of such a closure can perform through the capability (plan stage
/// F16), so a node of the handled body that can run a function value runs
/// the clauses of the handler.
pub fn captured_handlers(p: &Program, tys: &weft_ir::TyTable) -> Vec<HandlerId> {
    let mut out: Vec<HandlerId> = p
        .closures
        .iter()
        .enumerate()
        .flat_map(|(i, d)| {
            let c = weft_ir::ClosureId(u32::try_from(i).unwrap_or(u32::MAX));
            (0..d.captures.len())
                .filter_map(move |k| capture_handler(p, c, u32::try_from(k).unwrap_or(u32::MAX)))
        })
        .collect();
    // A handler that passes an operation on: the handler that serves it
    // runs the clause too (stage R0d).
    let more: Vec<HandlerId> = out.iter().flat_map(|&h| serving_all(p, tys, h).0).collect();
    out.extend(more);
    out.sort();
    out.dedup();
    out
}

/// The handler, the clause body and the mode (`multi`) of a continuation.
///
/// `place` of body `body` is a whole continuation local of a clause, or an
/// upvar local of one. `None` for another place (a continuation in the
/// environment of a closure).
pub fn kont_handler(p: &Program, body: BodyId, place: &Place) -> Option<(HandlerId, BodyId, bool)> {
    if !place.proj.is_empty() {
        return None;
    }
    let (ob, ol) = crate::factgen::alpha::owner_local(p, body, place.local).ok()?;
    let b = p.body(ob)?;
    match (b.kind, b.kont) {
        (BodyKind::Clause(h, _), Some((k, multi))) if k == ol => Some((h, ob, multi)),
        _ => None,
    }
}

/// The clause body of operation `op` of handler `h`.
pub fn clause_of(p: &Program, h: HandlerId, op: weft_ir::OpIdx) -> Option<BodyId> {
    p.handlers
        .get(h.index())?
        .clauses
        .iter()
        .find(|(o, _)| *o == op)
        .map(|(_, b)| *b)
}

/// True if clause body `cb` can end with no resume point: a path from its
/// entry reaches a `Return` with no `Resume` on the way (plan stage F15).
///
/// Such an end aborts to the handler of the clause: its value binds to the
/// destination of the `handle`, and the frames of the handled body unwind.
/// A clause that resumes on each path to its `Return` never aborts to its
/// handler, so a perform of its operation has no abort edge to the handler.
/// The test is on the blocks of the clause body: a `resume` in a body
/// inside the clause is not a resume point here (stage F16), so the clause
/// counts as one that can end with no resume point.
pub fn lands(p: &Program, cb: BodyId) -> bool {
    let Some(b) = p.body(cb) else {
        return true;
    };
    let mut seen = vec![false; b.blocks.len()];
    let mut work = vec![b.entry];
    while let Some(at) = work.pop() {
        match seen.get_mut(at.index()) {
            Some(s) if !*s => *s = true,
            _ => continue,
        }
        let Some(blk) = b.blocks.get(at.index()) else {
            continue;
        };
        if blk.cleanup {
            continue;
        }
        match blk.term.kind {
            TermKind::Return => return true,
            TermKind::Resume { .. } => {}
            ref t => work.extend(t.normal_successors()),
        }
    }
    false
}

/// True if a clause of handler `h` can end with no resume point
/// ([`lands`]). With `op`, only the clause of that operation.
pub fn handler_lands(p: &Program, h: HandlerId, op: Option<weft_ir::OpIdx>) -> bool {
    let Some(hd) = p.handlers.get(h.index()) else {
        return true;
    };
    hd.clauses
        .iter()
        .filter(|(o, _)| op.is_none_or(|x| x == *o))
        .any(|&(_, c)| lands(p, c))
}

/// The handler `h`, or [`AlphaError::Later`] for a handler of a later
/// stage.
fn handler(p: &Program, h: HandlerId) -> Result<&weft_ir::HandlerDecl, AlphaError> {
    p.handlers
        .get(h.index())
        .ok_or_else(|| AlphaError::BadPlace(format!("no handler h{}", h.0)))
}

/// True if clause body `cb` can resume its continuation more than once.
///
/// The continuation is `multi`, and a path from the entry passes two
/// `Resume`s (also one `Resume` in a cycle), or a body inside the clause can
/// resume it (plan stage F16).
pub fn resumes_twice(p: &Program, cb: BodyId) -> bool {
    let Some(b) = p.body(cb) else {
        return false;
    };
    if !b.kont.is_some_and(|(_, multi)| multi) {
        return false;
    }
    // A body inside the clause (a closure, a handled body) can resume the
    // continuation of the clause: count it as twice.
    let inner = p.bodies.iter().enumerate().any(|(i, x)| {
        let id = BodyId(u32::try_from(i).unwrap_or(u32::MAX));
        id != cb
            && inside_or_made(p, id, cb)
            && x.blocks
                .iter()
                .any(|blk| !blk.cleanup && matches!(blk.term.kind, TermKind::Resume { .. }))
    });
    if inner {
        return true;
    }
    // A walk over (block, resumes passed, capped at 2).
    let mut seen = vec![[false; 3]; b.blocks.len()];
    let mut work = vec![(b.entry, 0usize)];
    while let Some((at, n)) = work.pop() {
        if n >= 2 {
            return true;
        }
        match seen.get_mut(at.index()).and_then(|s| s.get_mut(n)) {
            Some(s) if !*s => *s = true,
            _ => continue,
        }
        let Some(blk) = b.blocks.get(at.index()) else {
            continue;
        };
        if blk.cleanup {
            continue;
        }
        let n = if matches!(blk.term.kind, TermKind::Resume { .. }) {
            n + 1
        } else {
            n
        };
        work.extend(
            blk.term
                .kind
                .normal_successors()
                .into_iter()
                .map(|x| (x, n)),
        );
    }
    false
}

/// True if body `b` is body `root`, a body inside it, or a closure that a
/// body inside it makes (through the parents and the makers).
pub fn inside_or_made(p: &Program, b: BodyId, root: BodyId) -> bool {
    let mut at = Some(b);
    for _ in 0..=p.bodies.len() {
        let Some(x) = at else {
            return false;
        };
        if x == root {
            return true;
        }
        at = p.bodies.get(x.index()).and_then(|d| match d.kind {
            BodyKind::Closure(c) => p.closures.get(c.index()).map(|cd| cd.maker),
            _ => d.parent,
        });
    }
    false
}

/// The clause body that body `b` is in: `b` itself, or the clause that its
/// parents (or the makers of the closures on the way) reach first.
pub fn enclosing_clause(p: &Program, b: BodyId) -> Option<BodyId> {
    let mut at = Some(b);
    for _ in 0..=p.bodies.len() {
        let x = at?;
        let d = p.body(x)?;
        if matches!(d.kind, BodyKind::Clause(..)) {
            return Some(x);
        }
        at = match d.kind {
            BodyKind::Closure(c) => p.closures.get(c.index()).map(|cd| cd.maker),
            _ => d.parent,
        };
    }
    None
}

/// True if a closure that body `maker` makes can run at a node of body
/// `body` with the states of the analysis there (plan stage F16).
///
/// `maker` is in no clause, or `body` is in the same clause (the locals of
/// the clause have their values there). A closure that a clause gives to the
/// handled body (through `resume`, or a place of the site) runs where the
/// locals of the clause have no value in the states: not in scope.
pub fn runs_with_maker(p: &Program, maker: BodyId, body: BodyId) -> bool {
    enclosing_clause(p, maker).is_none_or(|c| inside_or_made(p, body, c))
}

/// True if a clause of handler `h` can resume more than once.
///
/// The clause is of a `multi` operation ([`resumes_twice`]): a node that
/// runs the clause runs the code after it again (the re-entry edges, plan
/// stage F16).
pub fn multi_twice(p: &Program, h: HandlerId) -> bool {
    p.handlers
        .get(h.index())
        .is_some_and(|d| d.multi && d.clauses.iter().any(|&(_, c)| resumes_twice(p, c)))
}

/// The body `b`.
fn body_of(p: &Program, b: BodyId) -> Result<&weft_ir::Body, AlphaError> {
    p.body(b)
        .ok_or_else(|| AlphaError::BadPlace(format!("no body b{}", b.0)))
}

/// The state at the entry of the handled body of handler `h`: the state
/// `st` before the `handle`, and the capability. The value of the
/// capability local holds the root of the local (`docs/ir.md` 6.3).
///
/// # Errors
///
/// The errors of α.
pub fn handled_entry(cx: &mut Cx<'_>, st: &State, h: HandlerId) -> Result<State, AlphaError> {
    let p = cx.p;
    let hd = handler(p, h)?;
    let hb = hd.handled;
    let hbody = body_of(p, hb)?;
    let mut init = st.clone();
    for &(_, c) in &hbody.caps {
        let r = cx.roots.local(p, cx.tys, cx.facts, hb, c)?;
        let mut v = AbsVal::plain();
        v.caps.insert(r);
        init.write((hb, c), &[], Tree::leaf(v));
    }
    Ok(init)
}

/// What the run of a `handle` gives ([`handle_run`]).
#[derive(Clone, Debug)]
pub struct HandleOut {
    /// The states of the handled body.
    pub states: States,
    /// The join of the states at the `Return` of the handled body, after its
    /// statements: the state at the `Exit` node.
    pub exit: Option<State>,
    /// The state after the `handle`, before its destination gets the value:
    /// the end of the handled body, the code of the clauses after their
    /// resume points, and the clauses that end with no `resume`. It has no
    /// local of the handled body or of a clause.
    pub after: State,
    /// The value of the `handle`.
    pub value: Tree,
    /// The join of the states where a clause ended with no `resume` (the
    /// state at the `Landing` node), with no local of a clause.
    pub landing: Option<State>,
    /// The re-entries of a `multi` handler (plan stage F16): the body and
    /// the block of each node of the handled body (or of a handled body
    /// inside it) that runs a clause that can resume more than once, the
    /// state before its `Copy` node, and the values that the later
    /// `resume`s give to a perform.
    pub reentries: Vec<(BodyId, BlockId, State, Tree)>,
}

/// The run of a `handle` of handler `h` in body `body`, from the state `st`
/// before it (see the module text).
///
/// # Errors
///
/// The errors of the transfer functions, and [`AlphaError::Later`] for a
/// handler of a later stage.
pub fn handle_run(
    cx: &mut Cx<'_>,
    _body: BodyId,
    st: &State,
    h: HandlerId,
) -> Result<HandleOut, AlphaError> {
    let p = cx.p;
    let hd = handler(p, h)?;
    let hb = hd.handled;
    let hbody = body_of(p, hb)?;
    let init = handled_entry(cx, st, h)?;
    let clauses: Vec<BodyId> = hd.clauses.iter().map(|(_, c)| *c).collect();
    let multi = multi_twice(p, h);
    // A `multi` resume runs the code after a node that runs a clause again,
    // from the copy of the frames of the handled body at that node (plan
    // stage F16): the runs of the handled body go on until the states at
    // these re-entries do not change. A node in a handled body inside `hb`
    // gets its re-entry state through `Handlers::extra` (the `handle` of
    // that body adds it to its seeds).
    let mut again: BTreeMap<BlockId, State> = BTreeMap::new();
    let mut round = 0usize;
    loop {
        let mut seeds = vec![(hbody.entry, init.clone())];
        seeds.extend(again.iter().map(|(b, s)| (*b, s.clone())));
        seeds.extend(cx.hx.extra.get(&hb).into_iter().flatten().cloned());
        let r = run_handled(cx, (h, hb, &clauses), st, seeds)?;
        if !multi || r.again.is_empty() {
            return Ok(finish_handle(cx, h, hb, r, Vec::new()));
        }
        if r.nested {
            // No re-entry of a node in a clause or a closure inside the
            // handled body: the program is in scope only if the `ir`
            // pipeline rejects it (stage R0g).
            note_pending(crate::factgen::Unsupported {
                group: crate::irbuild::scope::Group::D,
                reason: "a `multi` resume of a node in a clause or a closure inside the handled body (stage F16)"
                    .to_string(),
            });
            return Ok(finish_handle(cx, h, hb, r, Vec::new()));
        }
        // The state where a later `resume` starts the rest of the handled
        // body: the locals of the site as at that `resume`, the locals of
        // the handled body as at the node (their copies).
        let mut back: Option<State> = None;
        let mut values = Tree::none();
        for (v, s) in &r.again {
            values.join(v);
            let mut s = s.clone();
            s.remove_bodies(&|b| clauses.iter().any(|&c| inside(p, b, c)));
            match &mut back {
                Some(x) => {
                    x.join(&s);
                }
                None => back = Some(s),
            }
        }
        let back = back.unwrap_or_default();
        let mut changed = false;
        let mut out: Vec<(BodyId, BlockId, State, Tree)> = Vec::new();
        for re in &r.reentries {
            let mut s = back.with_bodies_of(&re.state, &|b| inside(p, b, hb));
            s.join_heap(&re.state);
            if let Some(dest) = &re.dest {
                if let Some((k, path)) = transfer::move_path(p, re.body, dest)? {
                    let mut v = s.value(k, &path);
                    v.join(&values);
                    transfer::bind_result(cx, re.body, &mut s, &[], dest, v)?;
                }
            }
            out.push((re.body, re.block, s.clone(), values.clone()));
            if re.body == hb {
                changed |= join_seed(&mut again, re.next, &s);
            } else {
                let seeds = cx.hx.extra.entry(re.body).or_default();
                changed |= join_seed_list(seeds, re.next, &s);
            }
        }
        if !changed {
            return Ok(finish_handle(cx, h, hb, r, out));
        }
        round += 1;
        if round > MULTI_ROUNDS {
            return Err(AlphaError::Later(
                "a `multi` handled body whose re-runs do not end (stage F16)",
            ));
        }
    }
}

/// Joins the state `s` into the seed of block `b` in `seeds`. Returns true
/// if the seed changed.
fn join_seed(seeds: &mut BTreeMap<BlockId, State>, b: BlockId, s: &State) -> bool {
    if let Some(have) = seeds.get_mut(&b) {
        return have.join(s);
    }
    seeds.insert(b, s.clone());
    true
}

/// Joins the state `s` into the seed of block `b` in the list `seeds`.
/// Returns true if the seed changed.
pub fn join_seed_list(seeds: &mut Vec<(BlockId, State)>, b: BlockId, s: &State) -> bool {
    if let Some((_, have)) = seeds.iter_mut().find(|(x, _)| *x == b) {
        return have.join(s);
    }
    seeds.push((b, s.clone()));
    true
}

/// What one run of a handled body and of the code of its clauses after
/// their resume points gives ([`run_handled`]).
struct HandledRun {
    /// The states of the handled body.
    states: States,
    /// The state at the `Exit` node.
    exit: Option<State>,
    /// The state after the `handle` (see [`HandleOut::after`]), with the
    /// locals of the handled body and of the clauses.
    after: State,
    /// The value of the handled body.
    body_value: Tree,
    /// What a `resume` gives back.
    resumed: Tree,
    /// The values of the clauses after a `resume`.
    clause_values: Tree,
    /// The record of the run of the handled body.
    open: Open,
    /// The `resume`s of the code of the clauses after their first resume
    /// point: their values and the states before them.
    again: Vec<(Tree, State)>,
    /// The nodes of the handled body that run a clause that can resume
    /// more than once.
    reentries: Vec<Reentry>,
    /// Such a node is in a body inside the handled body.
    nested: bool,
}

/// One run of the handled body `hb` of handler `h` from the states `seeds`
/// (the entry, and the re-entries of a `multi` handler), then the code of
/// each clause after its resume points. `st` is the state before the
/// `handle`.
///
/// # Errors
///
/// The errors of the transfer functions.
fn run_handled(
    cx: &mut Cx<'_>,
    (h, hb, clauses): (HandlerId, BodyId, &[BodyId]),
    st: &State,
    seeds: Vec<(BlockId, State)>,
) -> Result<HandledRun, AlphaError> {
    let p = cx.p;
    let hbody = body_of(p, hb)?;
    cx.hx.open.push(Open::new(h));
    let run = run_from(cx, hb, seeds, Mode::default());
    let open = cx.hx.open.pop();
    let (states, ends) = run?;
    let mut open = open.ok_or_else(|| AlphaError::BadPlace("no open handler".to_string()))?;
    let mut exit: Option<State> = None;
    for s in ends.returns.values() {
        match &mut exit {
            Some(e) => {
                e.join(s);
            }
            None => exit = Some(s.clone()),
        }
    }
    let body_value = exit
        .as_ref()
        .map_or_else(Tree::none, |e| e.value((hb, hbody.ret), &[]));
    // The code of each clause after its resume points: a `resume` gives back
    // the value of the handled body, or the value of a clause that resumed
    // (a nested run of a clause). A later `resume` there (a `multi`
    // continuation) goes to the record of the handler.
    let mut resumed = body_value.clone();
    let mut post: Vec<State> = Vec::new();
    let mut clause_values = Tree::none();
    let mut again: Vec<(Tree, State)> = Vec::new();
    if let Some(ex) = &exit {
        let mut stable = false;
        for _ in 0..POST_ROUNDS {
            post.clear();
            let mut vals = Tree::none();
            cx.hx.open.push(Open::new(h));
            let mut run = || -> Result<(), AlphaError> {
                for (cb, seeds) in post_seeds(cx, &open.resumes, ex, &resumed)? {
                    let ret = body_of(p, cb)?.ret;
                    let (_, ends) = run_from(cx, cb, seeds, Mode::default())?;
                    for s in ends.returns.into_values() {
                        let v = s.value((cb, ret), &[]);
                        check_kont_escape(cx, (h, cb), &s, Some(&v), None);
                        vals.join(&v);
                        post.push(s);
                    }
                }
                Ok(())
            };
            let r = run();
            let rec = cx.hx.open.pop();
            r?;
            again = rec.map(|o| o.again).unwrap_or_default();
            let mut all = body_value.clone();
            all.join(&vals);
            clause_values = vals;
            if all == resumed {
                stable = true;
                break;
            }
            resumed = all;
        }
        // The values of the clauses did not reach a fixpoint (E-POST-ROUNDS
        // of the review of group D): the analysis does not know them.
        if !stable {
            return Err(AlphaError::Later(
                "the values of the clauses of a handler that do not reach a fixpoint (stage F17)",
            ));
        }
    }
    let mut after: Option<State> = exit.clone();
    for s in post.iter().chain(open.landing.iter()) {
        match &mut after {
            Some(a) => {
                a.join(s);
            }
            None => after = Some(s.clone()),
        }
    }
    let after = after.unwrap_or_else(|| st.clone());
    let _ = clauses;
    let reentries = std::mem::take(&mut open.reentries);
    let nested = open.nested;
    Ok(HandledRun {
        states,
        exit,
        after,
        body_value,
        resumed,
        clause_values,
        open,
        again,
        reentries,
        nested,
    })
}

/// The end of the run of a `handle` of handler `h` with handled body `hb`
/// ([`handle_run`]): the state after it, its value, and what the handler
/// keeps ([`Info`]). `reentries` are the re-entries of a `multi` handler:
/// the body and the block of each node, the state before its `Copy` node
/// and the values of the later `resume`s. A closure that takes the
/// capability of the handler out of the `handle` is an escape (W0313,
/// [`Escape`]).
fn finish_handle(
    cx: &mut Cx<'_>,
    h: HandlerId,
    hb: BodyId,
    r: HandledRun,
    reentries: Vec<(BodyId, BlockId, State, Tree)>,
) -> HandleOut {
    let p = cx.p;
    let clauses: Vec<BodyId> = p
        .handlers
        .get(h.index())
        .map(|d| d.clauses.iter().map(|(_, c)| *c).collect())
        .unwrap_or_default();
    let landing = r.open.landing.clone();
    let mut after = r.after;
    // A closure that the handled body makes keeps the values of the locals
    // that it captures (`Kept`, `ByRef`): it can run after the `handle`.
    let captured: Vec<(super::Key, Tree)> = captured_locals(p, hb)
        .into_iter()
        .filter_map(|k| after.tree(k).map(|t| (k, t.clone())))
        .collect();
    let mut roots = clauses;
    roots.push(hb);
    let frame = InsideAny::new(p, roots);
    after.remove_bodies(&|b| frame.test(b));
    for (k, t) in captured {
        after.keep_value(k, t);
    }
    let mut value = r.body_value;
    value.join(&r.clause_values);
    value.join(&r.open.landing_value);
    // A closure that captures the capability of the handler and leaves the
    // `handle` (in its value, in a local of the site or in a heap slot)
    // takes the capability out of its handler: W0313 of stage F17.
    // The states where the handled body ends: its exit and the landing of
    // a clause that ends with no `resume`. The code of a clause after its
    // `resume` (`Post`) sees the locals of the site with their values at the
    // resume point too, so its states are not used here: a closure that a
    // clause puts into a place of the site after `resume` and that runs
    // later is a run outside its handler (`transfer::check_cap_apps`).
    let ends: Vec<&State> = r.exit.iter().chain(landing.iter()).collect();
    let site = |k: &super::Key| !frame.test(k.0);
    // The closure can perform through the capture (`performs_cap`). The IR
    // gives a closure of the handled body each capability in scope, so a
    // closure that holds it for nothing does not count.
    let sums = cx.sums;
    let own = |f: &super::FnVal| performs_cap(p, sums, h, f, &ends, RUN_DEPTH_CAP);
    let local = ends
        .iter()
        .flat_map(|s| s.trees())
        .filter(|(k, _)| site(k))
        .find(|(_, t)| t.flat().fns.iter().any(own))
        .map(|(k, _)| {
            p.body(k.0)
                .and_then(|b| b.local(k.1))
                .and_then(|d| d.name.clone())
        });
    // An abort from the handled body to a local handler `g` outside the
    // handler leaves the locals outside the handled body of `g` with their
    // values at the abort: a closure there leaves the handler too (stage
    // R0g; the old lowering checks these abort paths, `check_local_keeps`).
    let local = local.or_else(|| {
        r.open.past.iter().find_map(|(s, g)| {
            let gb = p.handlers.get(g.index()).map(|d| d.handled)?;
            s.trees()
                .filter(|(k, _)| !frame.test(k.0) && !inside_or_made(p, k.0, gb))
                .find(|(_, t)| t.flat().fns.iter().any(own))
                .map(|(k, _)| {
                    p.body(k.0)
                        .and_then(|b| b.local(k.1))
                        .and_then(|d| d.name.clone())
                })
        })
    });
    let how = if value.flat().fns.iter().any(own) {
        Some(Escape::Value)
    } else if let Some(name) = local {
        Some(name.map_or(Escape::Stored, Escape::Local))
    } else if ends
        .iter()
        .any(|s| s.behind_fns().values().any(|fs| fs.iter().any(own)))
    {
        Some(Escape::Stored)
    } else {
        None
    };
    // The check gives W0313 (`crate::factgen::checks::cap_escapes`).
    if let Some(how) = how {
        let e = (h, how);
        if !cx.hx.escapes.iter().any(|x| Escape::same_report(x, &e)) {
            cx.hx.escapes.push(e);
        }
    }
    let info = cx.hx.info.entry(h).or_default();
    if let Some(ex) = &r.exit {
        match &mut info.exit {
            Some(e) => {
                e.join(ex);
            }
            None => info.exit = Some(ex.clone()),
        }
    }
    info.resumed.join(&r.resumed);
    HandleOut {
        states: r.states,
        exit: r.exit,
        after,
        value,
        landing,
        reentries,
    }
}

impl Open {
    /// The record of a run of the handled body of handler `h`.
    const fn new(h: HandlerId) -> Self {
        Self {
            handler: h,
            resumes: Vec::new(),
            landing: None,
            landing_value: Tree::none(),
            reentries: Vec::new(),
            nested: false,
            again: Vec::new(),
            past: Vec::new(),
        }
    }
}

thread_local! {
    /// The handlers whose capability a closure takes to a run node that does
    /// not run the clause of the handler, where the analysis of that node
    /// found no escape (stage R0g): `crate::factgen::emit` needs a W0313 of
    /// each handler (or a W0314 with the flag: the run can be on another
    /// task).
    static PENDING: std::cell::RefCell<Vec<(HandlerId, bool)>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// Notes a run outside handler `h` (stage R0g, [`take_pending_escapes`]).
/// With `task`, a W0314 rejects the program too.
pub fn note_pending_escape(h: HandlerId, task: bool) {
    PENDING.with(|p| {
        let mut p = p.borrow_mut();
        if !p.contains(&(h, task)) {
            p.push((h, task));
        }
    });
}

/// The handlers of [`note_pending_escape`] since the last call, which
/// clears them.
pub fn take_pending_escapes() -> Vec<(HandlerId, bool)> {
    PENDING.with(|p| std::mem::take(&mut *p.borrow_mut()))
}

thread_local! {
    /// The constructs that the facts do not model in the program of the
    /// fact generator now (stage R0g): the `ir` pipeline checks such a
    /// program only if it rejects it (`crate::factgen::Scope::pending`).
    static UNMODELED: std::cell::RefCell<Vec<crate::factgen::Unsupported>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// Notes a construct that the facts do not model (stage R0g): the program
/// is in scope only if the `ir` pipeline rejects it.
pub fn note_pending(u: crate::factgen::Unsupported) {
    UNMODELED.with(|p| {
        let mut p = p.borrow_mut();
        if !p.contains(&u) {
            p.push(u);
        }
    });
}

/// The constructs of [`note_pending`] since the last call, which clears
/// them.
pub fn take_pending() -> Vec<crate::factgen::Unsupported> {
    UNMODELED.with(|p| std::mem::take(&mut *p.borrow_mut()))
}

/// Notes the state `st` on the abort edge of terminator `t` of body `body`.
///
/// It goes to each handler whose handled body runs now and that the abort
/// leaves to a local handler outside it (stage R0g; the end of the `handle` reads it).
pub fn note_past(cx: &mut Cx<'_>, body: BodyId, t: &TermKind, st: &State) {
    if cx.hx.open.len() < 2 {
        return;
    }
    let dests = crate::factgen::frames::destinations(cx.p, cx.tys, cx.sums, body, t);
    for d in dests {
        let crate::factgen::frames::Dest::Handler { handler: g, .. } = d else {
            continue;
        };
        let Some(ig) = cx.hx.open.iter().position(|o| o.handler == g) else {
            continue;
        };
        for o in cx.hx.open.iter_mut().skip(ig + 1) {
            o.past.push((st.clone(), g));
        }
    }
}

/// Notes a node that a later `resume` can run again (plan stage F16).
///
/// Terminator `t` of block `block` of body `body` runs a clause of a
/// `multi` handler that can resume more than once, with the state `st` on
/// its normal edge: the run of the handled body of the handler gets it
/// ([`handle_run`]). A node that can wait at a `multi` operation of a
/// caller goes to `Handlers::rows` (`super::run`).
pub fn note_reentry(cx: &mut Cx<'_>, body: BodyId, block: BlockId, t: &TermKind, st: &State) {
    let p = cx.p;
    // A node that can wait at a `multi` operation of a caller (OL-R2a).
    if crate::factgen::frames::row_multi(p, cx.tys, cx.sums, body, t)
        || cx.hx.dyn_rows.contains(&(body, block))
    {
        if let Some(next) = t.normal_successors().first() {
            cx.hx.rows.push((body, block, *next, st.clone()));
        }
    }
    let (hs, dest, next): (Vec<HandlerId>, Option<Place>, Option<BlockId>) = match t {
        TermKind::Perform {
            cap: weft_ir::CapOperand::Local(cap),
            dest,
            next,
            op,
            ..
        } => (
            perform_target(p, body, cap, *op)
                .flatten()
                .into_iter()
                .collect(),
            Some(dest.clone()),
            Some(*next),
        ),
        TermKind::Call { next, .. } => (run_handlers(cx, body, block, t), None, *next),
        _ => return,
    };
    let Some(next) = next else {
        return;
    };
    for h in hs {
        if !multi_twice(p, h) {
            continue;
        }
        let Some(hb) = p.handlers.get(h.index()).map(|d| d.handled) else {
            continue;
        };
        let spliced = spliced_into(p, body, hb);
        let Some(o) = cx.hx.open_mut(h) else {
            continue;
        };
        if !spliced {
            o.nested = true;
            continue;
        }
        o.reentries.push(Reentry {
            body,
            block,
            next,
            dest: dest.clone(),
            state: st.clone(),
        });
    }
}

/// The locals of handled body `hb` (and of the bodies inside it) that a
/// closure made inside it captures `Kept` or `ByRef`.
pub(crate) fn captured_locals(p: &Program, hb: BodyId) -> Vec<super::Key> {
    let mut out = Vec::new();
    for c in &p.closures {
        if !inside(p, c.maker, hb) {
            continue;
        }
        for cap in &c.captures {
            if !matches!(
                cap.mode,
                weft_ir::CaptureMode::Kept | weft_ir::CaptureMode::ByRef
            ) {
                continue;
            }
            if let Ok(k) = crate::factgen::alpha::owner_local(p, c.maker, cap.source.local) {
                if inside(p, k.0, hb) {
                    out.push(k);
                }
            }
        }
    }
    out.sort();
    out.dedup();
    out
}

/// The seeds of the runs of the clauses after their resume points: for each
/// clause body, the block after each resume point with the state there (the
/// locals of the clause from the state at the resume point, the other
/// locals from the state `exit` at the end of the handled body, and the
/// destination of the `resume` with the value `resumed`).
///
/// # Errors
///
/// The errors of α.
fn post_seeds(
    cx: &mut Cx<'_>,
    resumes: &[(BodyId, BlockId, State)],
    exit: &State,
    resumed: &Tree,
) -> Result<Vec<(BodyId, Seeds)>, AlphaError> {
    let p = cx.p;
    let mut by: BTreeMap<BodyId, Seeds> = BTreeMap::new();
    for (cb, rb, sr) in resumes {
        let cbody = body_of(p, *cb)?;
        let Some(TermKind::Resume {
            kont,
            arg,
            dest,
            next,
            ..
        }) = cbody.blocks.get(rb.index()).map(|b| &b.term.kind)
        else {
            continue;
        };
        let mut s = sr.clone();
        resume_with(cx, *cb, &mut s, (kont, arg, dest), Some(exit), resumed)?;
        by.entry(*cb).or_default().push((*next, s));
    }
    Ok(by.into_iter().collect())
}

/// The transfer of a `Resume` of body `body` in state `st`: the argument
/// moves, a `once` continuation moves, the locals that are not of the clause
/// get their values from the state `exit` at the end of the handled body
/// (if the handled body can end), joined with their values in `st` (in the
/// terms of the clause), and the destination gets the value `resumed`.
///
/// # Errors
///
/// The errors of α.
fn resume_with(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    (kont, arg, dest): (&Place, &Operand, &Place),
    exit: Option<&State>,
    resumed: &Tree,
) -> Result<(), AlphaError> {
    let p = cx.p;
    let (_, cb, multi) = kont_handler(p, body, kont)
        .ok_or(AlphaError::Later("a continuation in a closure (stage F16)"))?;
    transfer::moves(p, body, st, [arg])?;
    if !multi {
        if let Some((k, path)) = transfer::move_path(p, body, kont)? {
            st.clear(k, &path);
        }
    }
    if let Some(ex) = exit {
        let mut after = ex.with_bodies_of(st, &|b| inside(p, b, cb));
        after.join_values_but(st, &|b| inside(p, b, cb));
        *st = after;
    }
    transfer::bind_result(cx, body, st, &[], dest, resumed.clone())
}

/// The transfer of a `handle` of handler `h` in body `body`: the run of the
/// handled body and of the clauses ([`handle_run`]), then the destination
/// gets the value of the `handle`.
///
/// # Errors
///
/// The errors of [`handle_run`].
pub fn handle(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    h: HandlerId,
    dest: &Place,
) -> Result<(), AlphaError> {
    let out = handle_run(cx, body, st, h)?;
    *st = out.after;
    transfer::bind_result(cx, body, st, &[], dest, out.value)
}

/// What a perform through the capability of a local handler gives
/// ([`perform_run`]).
#[derive(Clone, Debug)]
pub struct PerformOut {
    /// The handler.
    pub handler: HandlerId,
    /// The clause body.
    pub clause: BodyId,
    /// The value of each argument.
    pub args: Vec<Tree>,
    /// The state after the perform, before its destination gets the value.
    pub after: State,
    /// The result of the perform: the join of the values that the clause
    /// gives to `resume`.
    pub value: Tree,
    /// The value of the clause where it ends with no `resume`: the value of
    /// the `handle` after the abort to the handler.
    pub landing: Tree,
    /// The state of the clause where it aborts (`AbortEdge`).
    pub abort: Option<State>,
}

/// The run of a clause at a perform of body `body` (see the module text).
///
/// The perform is of operation `op` through the capability `cap` of a local
/// handler, with the arguments `args`, from the state `st` before it.
///
/// # Errors
///
/// The errors of the transfer functions, and [`AlphaError::Later`] for a
/// capability that the analysis does not know (a capability in the
/// environment of a closure) and for a handler of a later stage.
pub fn perform_run(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    cap: &Place,
    op: weft_ir::OpIdx,
    args: &[Operand],
) -> Result<PerformOut, AlphaError> {
    let p = cx.p;
    let h = cap_handler(p, body, cap).ok_or(AlphaError::Later(
        "a perform through a captured capability (stage F16)",
    ))?;
    // A handler with no clause for the operation passes it on (stage R0d,
    // [`serving`]). An operation that passes on to a caller is a perform
    // through the row (`transfer`).
    let Served::Local(h) = serving_path(p, h, op) else {
        return Err(AlphaError::BadPlace(format!(
            "handler h{} passes an operation out of the body",
            h.0
        )));
    };
    handler(p, h)?;
    let cb = clause_of(p, h, op).ok_or_else(|| {
        AlphaError::BadPlace(format!("handler h{} has no clause of an operation", h.0))
    })?;
    let mut vals = Vec::with_capacity(args.len());
    for a in args {
        vals.push(transfer::operand(cx, body, st, a)?);
    }
    let mut s0 = st.clone();
    transfer::moves(p, body, &mut s0, args)?;
    let run = run_clause(cx, h, cb, (&s0, None), &vals)?;
    // A clause with no resume point: the code after the perform does not
    // run, and any state is right there.
    let after = run.after.unwrap_or(s0);
    Ok(PerformOut {
        handler: h,
        clause: cb,
        args: vals,
        after,
        value: run.value,
        landing: run.landing,
        abort: run.abort,
    })
}

/// The run of clause body `cb` of handler `h` from the state `s0`, with the
/// values `vals` of its parameters, up to its resume points.
///
/// What the run of a clause up to its resume points gives ([`run_clause`]).
#[derive(Clone, Debug)]
struct ClauseOut {
    /// The join of the states at the resume points with no local of the
    /// clause (none if the clause has no resume point).
    after: Option<State>,
    /// The join of the values that the clause gives to `resume`.
    value: Tree,
    /// The join of the values of the clause where it ends with no `resume`.
    landing: Tree,
    /// The join of the states where the clause aborts: where it ends with no
    /// `resume`, and where an abort leaves it (its `UnwindExit`), with no
    /// local of the clause (plan stage F15).
    abort: Option<State>,
}

/// The run of clause body `cb` of handler `h` from the state `s0`, with the
/// values `vals` of its parameters, up to its resume points
/// ([`ClauseOut`]). The state `s0` joins the seed of the facts of the
/// clause; the open run of the handler gets the states at the resume
/// points and at each end with no `resume`.
///
/// # Errors
///
/// The errors of the transfer functions.
fn run_clause(
    cx: &mut Cx<'_>,
    h: HandlerId,
    cb: BodyId,
    (s0, frame): (&State, Option<(weft_facts::PlaceId, BodyId)>),
    vals: &[Tree],
) -> Result<ClauseOut, AlphaError> {
    let p = cx.p;
    let cbody = body_of(p, cb)?;
    let hb = p.handlers.get(h.index()).map(|d| d.handled);
    // The heap slot of the callee frame (`Given::state`) holds only while
    // the clause runs: the states that leave the run do not have it. The
    // records that outlive the runs of the enclosing clauses (the seeds of
    // the facts of the clause, the states at its resume points for the code
    // after them, and its ends with no `resume`) do not have the slots of
    // their callee frames either (plan stage F16).
    let strip = |st: &State, frames: &[weft_facts::PlaceId]| -> State {
        let mut st = st.clone();
        if !frames.is_empty() {
            st.map_behind(&mut |q, refs| {
                let hit = frames.contains(&q) && !refs.is_empty();
                if hit {
                    refs.clear();
                }
                hit
            });
        }
        st
    };
    let own: Vec<weft_facts::PlaceId> = frame.iter().map(|f| f.0).collect();
    // The frames of the calls in the handled body of `h`: the records of
    // the clause outlive them.
    let all: Vec<weft_facts::PlaceId> = cx
        .hx
        .frames
        .iter()
        .chain(frame.iter())
        .filter(|(_, b)| hb.is_some_and(|hb| spliced_into(p, *b, hb)))
        .map(|(f, _)| *f)
        .collect();
    let clean = |st: &State| strip(st, &own);
    let clean_all = |st: &State| strip(st, &all);
    {
        let s0 = clean_all(s0);
        let info = cx.hx.info.entry(h).or_default();
        match info.seeds.get_mut(&cb) {
            Some(s) => {
                s.join(&s0);
            }
            None => {
                info.seeds.insert(cb, s0);
            }
        }
        let ps = info.params.entry(cb).or_default();
        for (i, v) in vals.iter().enumerate() {
            match ps.get_mut(i) {
                Some(have) => {
                    have.join(v);
                }
                None => ps.push(v.clone()),
            }
        }
    }
    let mut init = s0.clone();
    for (i, &l) in cbody.params.iter().enumerate() {
        let v = vals.get(i).cloned().unwrap_or_else(Tree::none);
        init.write(transfer::key(p, cb, l)?, &[], v);
    }
    if let Some((k, _)) = cbody.kont {
        init.write((cb, k), &[], Tree::leaf(AbsVal::plain()));
    }
    let mode = Mode {
        all: false,
        stop_at_resume: true,
    };
    cx.hx.frames.extend(frame.iter().copied());
    let run = run_from(cx, cb, vec![(cbody.entry, init)], mode);
    let n = cx.hx.frames.len().saturating_sub(own.len());
    cx.hx.frames.truncate(n);
    let (_, ends) = run?;
    let mine = |b: BodyId| inside(p, b, cb);
    let mut after: Option<State> = None;
    let mut value = Tree::none();
    for (rb, sr) in &ends.resumes {
        if let Some(TermKind::Resume { arg, .. }) =
            cbody.blocks.get(rb.index()).map(|b| &b.term.kind)
        {
            let v = transfer::operand(cx, cb, sr, arg)?;
            check_kont_escape(cx, (h, cb), sr, None, Some(&v));
            value.join(&v);
        }
        let sr = clean(sr);
        let mut s = sr.clone();
        s.remove_bodies(&mine);
        match &mut after {
            Some(a) => {
                a.join(&s);
            }
            None => after = Some(s),
        }
        let rec = clean_all(&sr);
        if let Some(o) = cx.hx.open_mut(h) {
            o.resumes.push((cb, *rb, rec));
        }
    }
    // A clause that ends with no `resume` aborts to its handler.
    let mut landing = Tree::none();
    let mut abort: Option<State> = None;
    let mut add = |s: &State| match &mut abort {
        Some(a) => {
            a.join(s);
        }
        None => abort = Some(s.clone()),
    };
    for sret in ends.returns.values() {
        let v = sret.value((cb, cbody.ret), &[]);
        check_kont_escape(cx, (h, cb), sret, Some(&v), None);
        landing.join(&v);
        let mut s = clean(sret);
        s.remove_bodies(&mine);
        add(&s);
        let mut rec = clean_all(sret);
        rec.remove_bodies(&mine);
        if let Some(o) = cx.hx.open_mut(h) {
            o.landing_value.join(&v);
            match &mut o.landing {
                Some(l) => {
                    l.join(&rec);
                }
                None => o.landing = Some(rec),
            }
        }
    }
    // An abort that leaves the clause (past its handler).
    for su in ends.unwinds.values() {
        let mut s = clean(su);
        s.remove_bodies(&mine);
        add(&s);
    }
    Ok(ClauseOut {
        after,
        value,
        landing,
        abort,
    })
}

/// The local handlers whose clauses a call can run.
///
/// They are the handlers that call `t` of body `body` performs through or
/// fails to (an effect of the row of the callee, or a failure, that
/// resolves to a handler of the component,
/// `crate::factgen::frames::clause_handlers`), also if their clauses resume
/// on each path.
pub fn call_handlers(cx: &Cx<'_>, body: BodyId, t: &TermKind) -> Vec<HandlerId> {
    crate::factgen::frames::clause_handlers(cx.p, cx.tys, cx.sums, body, t)
}

/// The handlers of [`call_handlers`] whose clauses call `t` of block `block`
/// of body `body` can run (issue #57).
///
/// A handler that the call reaches only through the values that the callee
/// runs (a closure of the program captures its capability, or a failure of
/// such a value; `crate::factgen::frames::own_clause_handlers` does not
/// give it) counts only if the analysis found a value at the node that can
/// reach it (`Handlers::cap_active`): a closure that runs a known closure
/// that performs nothing and cannot fail does not run the clause.
pub fn run_handlers(cx: &Cx<'_>, body: BodyId, block: BlockId, t: &TermKind) -> Vec<HandlerId> {
    let own = crate::factgen::frames::own_clause_handlers(cx.p, cx.tys, cx.sums, body, t);
    let mut hs = call_handlers(cx, body, t);
    hs.retain(|h| own.contains(h) || cx.hx.cap_active.contains(&(body, block, *h)));
    hs
}

/// Notes the handlers that the values of a run node can reach.
///
/// The run node is at block `block` of body `body` (`Handlers::cap_active`,
/// issues #57 and #58). `apps` are the summaries that the node applies:
/// code of a caller can perform each effect and fail, and a summary can
/// perform its effects (through the row or through a captured capability)
/// and fail.
pub fn note_cap_apps(
    cx: &mut Cx<'_>,
    (body, block): (BodyId, BlockId),
    apps: &[super::transfer::Applied],
) {
    let p = cx.p;
    for h in captured_handlers(p, cx.tys) {
        let effect = p
            .handlers
            .get(h.index())
            .and_then(|d| cx.tys.effects().get(d.effect.index()))
            .map(|e| e.identity.clone());
        let active = apps.iter().any(|a| {
            a.code
                || a.summary
                    .performs
                    .iter()
                    .any(|pf| effect.as_ref().is_none_or(|e| *e == pf.effect))
        });
        if active {
            cx.hx.cap_active.insert((body, block, h));
        }
    }
    // A value that the callee runs and that can fail: the failure goes to
    // the local `Fail` handler of the call (issue #58).
    let fail = crate::factgen::frames::FAIL;
    let fails = apps.iter().any(|a| {
        a.code
            || a.summary.aborts.contains(&super::summary::Abort::Raises)
            || a.summary.performs.iter().any(|pf| pf.effect == fail)
    });
    let env = p
        .body(body)
        .and_then(|b| b.blocks.get(block.index()))
        .and_then(|b| match &b.term.kind {
            TermKind::Call {
                caps: weft_ir::CapArgs::Lexical(e),
                ..
            } => Some(*e),
            _ => None,
        });
    if let (true, Some(e)) = (fails, env) {
        if let crate::factgen::frames::Dest::Handler { handler, .. } =
            crate::factgen::frames::resolve(p, cx.tys, e, fail, true)
        {
            cx.hx.cap_active.insert((body, block, handler));
        }
    }
}

/// True if clause body `cb` has a resume point (a `Resume` of its own
/// blocks).
pub fn has_resume(p: &Program, cb: BodyId) -> bool {
    p.body(cb).is_some_and(|b| {
        b.blocks
            .iter()
            .any(|blk| !blk.cleanup && matches!(blk.term.kind, TermKind::Resume { .. }))
    })
}

/// True if a call can run the clauses of handler `h` (plan stage F15).
///
/// No parameter and no result of an operation of a clause of the handler
/// holds a function value, and a result
/// holds no reference if the clause can resume: the values that a clause
/// gives back to the callee hold no place of the site. A parameter can
/// hold a reference: it points into the places that the callee gives
/// ([`given`]).
pub fn given_ops(p: &Program, tys: &weft_ir::TyTable, h: HandlerId) -> bool {
    let Some(hd) = p.handlers.get(h.index()) else {
        return false;
    };
    let Some(e) = tys.effects().get(hd.effect.index()) else {
        return false;
    };
    // An effect has no type parameter, so no type of an operation names one
    // (the part of follow-up F16.3 for type parameters, plan stage F20).
    let no_fns = |t: weft_ir::TyId| {
        let pr = crate::props::ir_props(tys, t);
        !pr.callable && !crate::props::ir_has_fns(tys, t)
    };
    hd.clauses.iter().all(|&(op, c)| {
        e.ops.get(op.index()).is_some_and(|o| {
            o.params.iter().all(|&t| no_fns(t))
                && no_fns(o.ret)
                && (!crate::props::ir_props(tys, o.ret).holds_refs || !has_resume(p, c))
        })
    })
}

/// True if a parameter of an operation of a clause of handler `h` can hold
/// a reference: a call that runs the clause gives it places ([`given`]).
pub fn gives_refs(p: &Program, tys: &weft_ir::TyTable, h: HandlerId) -> bool {
    let Some(hd) = p.handlers.get(h.index()) else {
        return false;
    };
    let Some(e) = tys.effects().get(hd.effect.index()) else {
        return false;
    };
    hd.clauses.iter().any(|(op, _)| {
        e.ops.get(op.index()).is_some_and(|o| {
            o.params
                .iter()
                .any(|&t| crate::props::ir_props(tys, t).holds_refs)
        })
    })
}

/// The places that a call gives to the parameters of the clauses that it
/// runs (plan stage F15).
///
/// The callee performs through the capability of a caller, so the arguments
/// of the operation are places that it can name: a local of its frame (the
/// callee frame root of the call, `docs/ir.md` 6.3, which ends at the
/// `FrameEnd` of the call and on each abort path; only if the summary of
/// the callee says that it can give one, `Summary::gives_frame`), and the
/// places that the
/// arguments of the call reach (the places of each argument, the places
/// that its references point into, the places that the references behind
/// them point into, and the `rc` groups that they reach). Each one is a
/// wildcard place: the callee can
/// give a place below it. `st` is the state before call `t` of block
/// `block` of body `body`. Empty for a call of a function value (it runs
/// no local clause).
///
/// # Errors
///
/// The errors of σ.
pub fn given(
    cx: &mut Cx<'_>,
    body: BodyId,
    block: BlockId,
    st: &State,
    t: &TermKind,
) -> Result<Given, AlphaError> {
    if let TermKind::Call {
        callee: weft_ir::Callee::Value(f),
        args,
        ..
    } = t
    {
        return given_value(cx, (body, block), st, f, args);
    }
    let TermKind::Call {
        callee: weft_ir::Callee::Fn(f, targs),
        args,
        ..
    } = t
    else {
        return Ok(Given::default());
    };
    let p = cx.p;
    let decl = p
        .fns
        .get(f.index())
        .ok_or_else(|| AlphaError::BadPlace(format!("no function f{}", f.0)))?;
    let inst = transfer::run_inst(body, block);
    let s = super::apply::sigma(cx, body, st, decl, targs, args, inst)?;
    // The callee frame root, if the callee can give a place of its frame
    // to an operation (`Summary::gives_frame`).
    // A function value that the callee runs and that performs through a
    // captured capability gives the places that it reads, and a place of
    // its frame (plan stage F16).
    let (app_gives, app_places) = cap_given(cx, (body, block), st)?;
    let gives = app_gives || cx.sums.get(*f).map_or(true, |x| x.gives_frame);
    let frame = gives.then(|| cx.roots.frame(cx.facts, inst, &decl.name));
    // The `rc` objects that the arguments reach: a place in one is a place
    // of the group root of its type, not a place below the argument.
    let mut groups = Vec::new();
    for &t in &s.tys {
        for inner in transfer::rc_inners(cx.tys, t) {
            groups.push(cx.roots.group(cx.tys, cx.facts, inner));
        }
    }
    // The places of each argument, with the callee root of its parameter
    // (`call_arg`): a change through a place that the callee gives is a
    // change through that parameter (W0312, as for a call).
    let sum_roots: Vec<u32> = cx
        .sums
        .get(*f)
        .map(|x| x.params.iter().map(|q| q.root).collect())
        .unwrap_or_default();
    let mut roots: Vec<(weft_facts::PlaceId, u32)> = Vec::new();
    for i in 0..args.len() {
        let root = sum_roots
            .get(i)
            .copied()
            .unwrap_or_else(|| crate::roots::param(i));
        let of = |v: &Vec<Vec<weft_facts::PlaceId>>| v.get(i).cloned().unwrap_or_default();
        for q in of(&s.args)
            .into_iter()
            .chain(of(&s.values))
            .chain(of(&s.helds))
        {
            roots.push((cx.facts.wildcard(q), root));
        }
    }
    for &q in &app_places {
        roots.push((q, crate::roots::STORED));
    }
    roots.sort();
    roots.dedup();
    let mut places: Vec<weft_facts::PlaceId> = roots
        .iter()
        .map(|&(q, _)| q)
        .chain(
            groups
                .into_iter()
                .chain(frame)
                .map(|q| cx.facts.wildcard(q)),
        )
        .collect();
    places.sort();
    places.dedup();
    let mut deps: Vec<weft_facts::PlaceId> = s.deps.into_iter().flatten().collect();
    deps.sort();
    deps.dedup();
    let frame = frame.map(|q| cx.facts.wildcard(q));
    Ok(Given {
        places,
        deps,
        roots,
        frame,
    })
}

/// [`given`] for a call of a function value `f` with the arguments `args`
/// (plan stage F16): a closure that performs through a captured capability
/// gives the clause a local of its frame (the frame root of the run node),
/// or a place that its arguments or its environment reach (each as a
/// wildcard place).
///
/// # Errors
///
/// The errors of α.
fn given_value(
    cx: &mut Cx<'_>,
    (body, block): (BodyId, BlockId),
    st: &State,
    f: &Operand,
    args: &[Operand],
) -> Result<Given, AlphaError> {
    let inst = transfer::run_inst(body, block);
    let mut roots: Vec<(weft_facts::PlaceId, u32)> = Vec::new();
    for (i, a) in args.iter().enumerate() {
        let root = crate::roots::param(i);
        for q in transfer::reach_refs(cx, body, st, a)? {
            roots.push((cx.facts.wildcard(q), root));
        }
    }
    for q in transfer::reach_refs(cx, body, st, f)? {
        roots.push((cx.facts.wildcard(q), crate::roots::STORED));
    }
    // The places of a perform of the closure are exact places: the perform
    // lends them (plan stage F16).
    for q in cap_given(cx, (body, block), st)?.1 {
        roots.push((q, crate::roots::STORED));
    }
    roots.sort();
    roots.dedup();
    let frame = cx.roots.frame(cx.facts, inst, "the closure");
    let frame = cx.facts.wildcard(frame);
    let mut places: Vec<weft_facts::PlaceId> = roots.iter().map(|&(q, _)| q).collect();
    places.push(frame);
    places.sort();
    places.dedup();
    Ok(Given {
        places,
        deps: Vec::new(),
        roots,
        frame: Some(frame),
    })
}

/// What the function values that the run node of block `block` applies
/// give to the clauses of the handlers of their captured capabilities (plan
/// stage F16): true if one can give a place of its frame, and the places
/// that they read or change (a perform gives a place that it reads).
fn cap_given(
    cx: &mut Cx<'_>,
    (body, block): (BodyId, BlockId),
    st: &State,
) -> Result<(bool, Vec<weft_facts::PlaceId>), AlphaError> {
    let Some(t) =
        cx.p.body(body)
            .and_then(|b| b.blocks.get(block.index()))
            .map(|b| b.term.kind.clone())
    else {
        return Ok((false, Vec::new()));
    };
    let apps = match &t {
        TermKind::Call {
            callee: weft_ir::Callee::Value(f),
            args,
            dest,
            ..
        } => transfer::value_out(cx, body, block, st, f, args, dest)?.apps,
        TermKind::Call {
            callee: weft_ir::Callee::Fn(f, targs),
            args,
            dest,
            ..
        } => transfer::call_out(cx, body, block, st, *f, targs, args, dest)?.apps,
        _ => return Ok((false, Vec::new())),
    };
    let mut gives = false;
    let mut out = Vec::new();
    for a in &apps {
        let cap = a
            .summary
            .performs
            .iter()
            .any(|pf| matches!(pf.cap, super::summary::CapIface::Cap(_)));
        if !cap {
            continue;
        }
        gives |= a.summary.gives_frame;
        // A place of a parameter is a place of an argument: the call gives
        // it with the root of its parameter.
        let env = |r: &&super::summary::IPlace| {
            matches!(
                r.root,
                super::summary::IRoot::CaptureCell(_)
                    | super::summary::IRoot::Capture(_)
                    | super::summary::IRoot::CaptureHeld(_)
                    | super::summary::IRoot::CaptureDeep(_)
            )
        };
        let places: Vec<&super::summary::IPlace> = a
            .summary
            .reads
            .iter()
            .chain(&a.summary.lends)
            .chain(a.summary.muts.iter().map(|m| &m.0))
            .filter(env)
            .collect();
        for r in places {
            out.extend(super::apply::iplaces(cx, &a.sigma, r)?);
        }
    }
    out.sort();
    out.dedup();
    Ok((gives, out))
}

/// The places that a call gives to the clauses that it runs ([`given`]).
#[derive(Clone, Debug, Default)]
pub struct Given {
    /// The wildcard places that a parameter of a clause can point into.
    pub places: Vec<weft_facts::PlaceId>,
    /// The handle places `h.*` of the `Rc` handles on the way to the
    /// arguments of the call.
    pub deps: Vec<weft_facts::PlaceId>,
    /// The given places of the arguments, each with the callee root of its
    /// parameter.
    pub roots: Vec<(weft_facts::PlaceId, u32)>,
    /// The wildcard place of the callee frame root, if the callee can give
    /// a place of its frame.
    pub frame: Option<weft_facts::PlaceId>,
}

impl Given {
    /// The state `st` where the clauses run: a reference that the callee
    /// keeps in its frame can point into each given place (a parameter of
    /// a clause can point into a local of the callee that holds one).
    pub fn state(&self, st: &State) -> State {
        let mut out = st.clone();
        if let Some(f) = self.frame {
            out.store_behind(f, self.places.iter().copied());
        }
        out
    }

    /// The value of each parameter of clause body `cb`: a parameter whose
    /// type can hold a reference points into the given places.
    ///
    /// # Errors
    ///
    /// Returns [`AlphaError::BadPlace`] for a clause body that does not
    /// exist.
    pub fn values(&self, cx: &Cx<'_>, cb: BodyId) -> Result<Vec<Tree>, AlphaError> {
        let b = body_of(cx.p, cb)?;
        Ok(b.params
            .iter()
            .map(|&l| {
                let refs = b
                    .local(l)
                    .is_some_and(|d| crate::props::ir_props(cx.tys, d.ty).holds_refs);
                // A function value of the callee (stage R0h, D3 form P): in the
                // clause it is code of a caller whose environment is the
                // places that the call gives, so a run of it lends them.
                let fns = b.local(l).is_some_and(|d| {
                    crate::props::ir_props(cx.tys, d.ty).callable
                        || crate::props::ir_has_fns(cx.tys, d.ty)
                });
                if fns {
                    let mut v = AbsVal::refs(self.places.iter().copied());
                    v.fns.insert(super::FnVal::Unknown);
                    Tree::leaf(v)
                } else if refs {
                    Tree::leaf(AbsVal::refs(self.places.iter().copied()))
                } else {
                    Tree::leaf(AbsVal::plain())
                }
            })
            .collect())
    }

    /// σ of each parameter of clause body `cb` in the facts: the given
    /// places for a parameter whose type can hold a reference (its places
    /// and what the references behind it point into), else none.
    pub fn sigma(
        &self,
        p: &Program,
        tys: &weft_ir::TyTable,
        cb: BodyId,
    ) -> (Vec<Vec<weft_facts::PlaceId>>, Vec<Vec<weft_facts::PlaceId>>) {
        let Some(b) = p.body(cb) else {
            return (Vec::new(), Vec::new());
        };
        let mut args = Vec::new();
        let mut deps = Vec::new();
        for &l in &b.params {
            let refs = b
                .local(l)
                .is_some_and(|d| crate::props::ir_props(tys, d.ty).holds_refs);
            args.push(if refs {
                self.places.clone()
            } else {
                Vec::new()
            });
            deps.push(if refs { self.deps.clone() } else { Vec::new() });
        }
        (args, deps)
    }
}

/// The values of the clauses of the local handlers that a call aborts to.
///
/// For each local handler that call `t` of body `body` can abort to: the
/// values of its clauses where they end with no `resume`, from the state
/// `st` before the call (the value of the `handle` after the abort).
///
/// # Errors
///
/// The errors of the transfer functions.
pub fn call_landings(
    cx: &mut Cx<'_>,
    (body, block): (BodyId, BlockId),
    st: &State,
    t: &TermKind,
) -> Result<Vec<(HandlerId, Tree)>, AlphaError> {
    let p = cx.p;
    let mut out = Vec::new();
    let hs = call_handlers(cx, body, t);
    if hs.is_empty() {
        return Ok(out);
    }
    let gv = given(cx, body, block, st, t)?;
    for h in hs {
        handler(p, h)?;
        let clauses: Vec<BodyId> = p
            .handlers
            .get(h.index())
            .map(|d| d.clauses.iter().map(|(_, c)| *c).collect())
            .unwrap_or_default();
        let mut v = Tree::none();
        let s0 = gv.state(st);
        for cb in clauses {
            let vals = gv.values(cx, cb)?;
            v.join(&run_clause(cx, h, cb, (&s0, gv.frame.map(|f| (f, body))), &vals)?.landing);
        }
        out.push((h, v));
    }
    Ok(out)
}

/// The clauses that a call runs (plan stages F14, F15).
///
/// After the transfer of call `t` of block `block` of body `body`, each
/// clause of each local handler that the callee can perform through (or
/// fail to) runs up to its resume points from the state `st` after the
/// call. A parameter that can hold a reference points into the places that
/// the call gives ([`given`], from the state `before` the call). The state
/// after the call is the join of `st` and the states at the resume points.
///
/// # Errors
///
/// The errors of the transfer functions, and [`AlphaError::Later`] for a
/// clause whose operation gives a function value or a reference back to
/// the callee ([`given_ops`]).
pub fn call_clauses(
    cx: &mut Cx<'_>,
    (body, block): (BodyId, BlockId),
    before: Option<&State>,
    st: &mut State,
    t: &TermKind,
) -> R {
    let p = cx.p;
    let hs = call_handlers(cx, body, t);
    if hs.is_empty() {
        return Ok(());
    }
    let mut start = st.clone();
    let gv = given(cx, body, block, before.unwrap_or(&start), t)?;
    // A clause runs while the callee waits, and a clause with no `resume`
    // ends the callee: a task handle that the call takes is lost there,
    // unless the callee joins it on each path of an abort (part
    // `abort_joins`; R2-2, follow-up F19.4).
    if let Some(b) = before {
        let ts = transfer::given_tasks(cx, body, b, t, true);
        if !ts.is_empty() {
            start.lose_tasks(ts);
        }
    }
    let mut abort: Option<State> = None;
    // The function values that the clauses give back to the callee with
    // `resume` (stage R0h, D3 form F), and what their values point into.
    let mut back_fns: BTreeSet<super::FnVal> = BTreeSet::new();
    let mut back_refs: BTreeSet<weft_facts::PlaceId> = BTreeSet::new();
    for h in hs {
        handler(p, h)?;
        let clauses: Vec<(weft_ir::OpIdx, BodyId)> = p
            .handlers
            .get(h.index())
            .map(|d| d.clauses.clone())
            .unwrap_or_default();
        let s0 = gv.state(&start);
        for (op, cb) in clauses {
            let vals = gv.values(cx, cb)?;
            let run = run_clause(cx, h, cb, (&s0, gv.frame.map(|f| (f, body))), &vals)?;
            if op_gives_refs(p, cx.tys, h, op) {
                let refs = run.value.flat().refs;
                if !refs.is_empty() {
                    cx.hx
                        .back_refs
                        .entry((body, block))
                        .or_default()
                        .extend(refs);
                }
            }
            if op_gives_fns(p, cx.tys, h, op)
                && call_performs(cx, body, before.unwrap_or(&start), t, h)?
            {
                let v = run.value.flat();
                back_fns.extend(v.fns.iter().cloned());
                back_refs.extend(v.refs.iter().copied());
            }
            if let Some(a) = run.after {
                st.join(&a);
            }
            if let Some(x) = run.abort {
                match &mut abort {
                    Some(a) => {
                        a.join(&x);
                    }
                    None => abort = Some(x),
                }
            }
        }
    }
    // The callee runs each value that a clause gives back as code of a
    // caller runs a value: more than once, at `Main` and at `Ret`, on some
    // paths only. A value that can race needs the task nodes of the worst
    // way, which the call does not have: the old pipeline checks the program
    // (stage R0h).
    back_fns.remove(&super::FnVal::Unknown);
    if !back_fns.is_empty() {
        let key = (body, block);
        let rec = cx.hx.given_back.entry(key).or_default();
        rec.0.extend(back_fns.iter().cloned());
        rec.1.extend(back_refs.iter().copied());
        rec.1.sort();
        rec.1.dedup();
        let (fns, refs) = rec.clone();
        // The callee can also keep a value in a place that it gets, and the
        // facts have no part for that (`transfer::kept_value_risk`); and a
        // `once` value has no operand at the call that a second run uses.
        // A value of the interface of the site (a parameter, its result, a
        // capture) is code of a caller of the site: the callee can keep it
        // in a place that the call gives, and the summary of the callee says
        // that the place holds code of a caller (`put_values`), not this
        // value (stage R0h fix, the review of R0h: `f32_param_back_keep`).
        let known = |g: &super::FnVal| {
            matches!(
                g,
                super::FnVal::Closure(_) | super::FnVal::Made(_) | super::FnVal::Item(..)
            )
        };
        for g in &fns {
            if !known(g)
                || transfer::can_race(cx, g)
                || transfer::kept_value_risk(cx, g)
                || transfer::once_value(p, g)
            {
                return Err(AlphaError::Later(GIVES_BACK));
            }
        }
        let inst = transfer::run_inst(body, block);
        cx.hx.given_refs.insert(inst, refs.clone());
        let from = before.cloned().unwrap_or_else(|| st.clone());
        let multi = transfer::callee_multi(cx, t);
        let apps = transfer::given_back_apps(cx, (body, block), &from, &fns, &gv.places, multi)?;
        transfer::apply_given_back(cx, (body, block), st, &apps, t, (&fns, &refs))?;
    }
    // The abort edge of the call: the state before it, and the states of
    // the clauses where they abort.
    cx.hx.abort_edge = abort.map(AbortEdge::Join);
    Ok(())
}

/// True if call `t` of body `body` can perform an operation of the effect of
/// handler `h` in state `st` (stage R0h): a callee or a closure whose
/// summary performs it or runs a function value, a callee with no summary,
/// and a function value that the analysis does not know. Else the clauses of
/// `h` do not run at the call, and they give the callee nothing.
///
/// # Errors
///
/// The errors of α.
fn call_performs(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    t: &TermKind,
    h: HandlerId,
) -> Result<bool, AlphaError> {
    let Some(effect) =
        cx.p.handlers
            .get(h.index())
            .and_then(|d| cx.tys.effects().get(d.effect.index()))
            .map(|e| e.identity.clone())
    else {
        return Ok(true);
    };
    let does = |s: &super::summary::Summary| {
        !s.runs.is_empty() || s.performs.iter().any(|pf| pf.effect == effect)
    };
    match t {
        TermKind::Call {
            callee: weft_ir::Callee::Fn(f, _),
            ..
        } => Ok(cx.sums.get(*f).map_or(true, does)),
        TermKind::Call {
            callee: weft_ir::Callee::Value(v),
            ..
        } => {
            let fns = transfer::reach_fns(cx, body, st, v)?;
            if fns.is_empty() {
                return Ok(true);
            }
            for g in &fns {
                let sum = match g {
                    super::FnVal::Closure(c) | super::FnVal::Made(c) => cx.sums.closure(*c).ok(),
                    super::FnVal::Item(f, _) => cx.sums.get(*f).ok(),
                    _ => None,
                };
                if sum.is_none_or(does) {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        _ => Ok(true),
    }
}

/// True if operation `op` of the effect of handler `h` gives a function
/// value back to the callee in its result (stage R0h, D3 form F).
pub fn op_gives_fns(p: &Program, tys: &weft_ir::TyTable, h: HandlerId, op: weft_ir::OpIdx) -> bool {
    let Some(e) = p
        .handlers
        .get(h.index())
        .and_then(|hd| tys.effects().get(hd.effect.index()))
    else {
        return false;
    };
    e.ops.get(op.index()).is_some_and(|o| {
        let pr = crate::props::ir_props(tys, o.ret);
        pr.callable || crate::props::ir_has_fns(tys, o.ret)
    })
}

/// True if operation `op` of the effect of handler `h` gives a reference
/// back to the callee in its result (stage R0h, D3 form R).
fn op_gives_refs(p: &Program, tys: &weft_ir::TyTable, h: HandlerId, op: weft_ir::OpIdx) -> bool {
    p.handlers
        .get(h.index())
        .and_then(|hd| tys.effects().get(hd.effect.index()))
        .and_then(|e| e.ops.get(op.index()))
        .is_some_and(|o| crate::props::ir_props(tys, o.ret).holds_refs)
}

/// True if a clause of handler `h` can give a reference back to the callee:
/// the result of its operation holds a reference and the clause resumes
/// (stage R0h, D3 form R).
pub fn gives_refs_back(p: &Program, tys: &weft_ir::TyTable, h: HandlerId) -> bool {
    let Some(hd) = p.handlers.get(h.index()) else {
        return false;
    };
    let Some(e) = tys.effects().get(hd.effect.index()) else {
        return false;
    };
    hd.clauses.iter().any(|&(op, c)| {
        e.ops.get(op.index()).is_some_and(|o| {
            let pr = crate::props::ir_props(tys, o.ret);
            pr.holds_refs && has_resume(p, c)
        })
    })
}

/// The places that the clauses of the local handlers of call `t` of block
/// `block` of body `body` can give back to the callee in a reference result
/// of their operation (stage R0h, D3 form R).
///
/// From the state `st` before the call: each wildcard place that a clause
/// can name. These are the places
/// that the call gives ([`given`]), and for each local of a site that a
/// clause or a body inside it names (an upvar local): its place, what its
/// references point into (also behind them), and the `rc` groups of its
/// type. A reference into a local of the clause lives while the handled body
/// runs. `None` if a clause names a local whose frame the call does not run
/// in (a call in a closure body inside the handled body).
///
/// # Errors
///
/// The errors of α.
pub fn back_places(
    cx: &mut Cx<'_>,
    (body, block): (BodyId, BlockId),
    st: &State,
    t: &TermKind,
) -> Result<Option<BackPlaces>, AlphaError> {
    let p = cx.p;
    let hs: Vec<HandlerId> = call_handlers(cx, body, t)
        .into_iter()
        .filter(|&h| gives_refs_back(p, cx.tys, h))
        .collect();
    if hs.is_empty() {
        return Ok(Some(BackPlaces::default()));
    }
    cx.hx.back_busy = true;
    let gv = given(cx, body, block, st, t);
    cx.hx.back_busy = false;
    let mut out: Vec<weft_facts::PlaceId> = gv?.places;
    // The places after this index are the places that the clauses name
    // themselves (not the places that the call gives).
    let given_len = out.len();
    let unit = crate::factgen::alpha::unit_root(p, body);
    let mut keys: BTreeSet<super::Key> = BTreeSet::new();
    for h in hs {
        let clauses: Vec<BodyId> = p
            .handlers
            .get(h.index())
            .map(|d| d.clauses.iter().map(|(_, c)| *c).collect())
            .unwrap_or_default();
        for cb in clauses {
            for (bi, b) in p.bodies.iter().enumerate() {
                let bid = BodyId(u32::try_from(bi).unwrap_or(u32::MAX));
                if !inside(p, bid, cb) {
                    continue;
                }
                for (li, d) in b.locals.iter().enumerate() {
                    if !matches!(d.kind, weft_ir::LocalKind::Upvar(_)) {
                        continue;
                    }
                    let l = weft_ir::LocalId(u32::try_from(li).unwrap_or(u32::MAX));
                    let k = transfer::key(p, bid, l)?;
                    if inside(p, k.0, cb) {
                        continue;
                    }
                    if crate::factgen::alpha::unit_root(p, k.0) != unit {
                        return Ok(None);
                    }
                    keys.insert(k);
                }
            }
        }
    }
    for (ob, ol) in keys {
        let place = Place {
            local: ol,
            proj: Vec::new(),
        };
        for q in transfer::alpha(cx, ob, st, &place)?.places {
            out.push(cx.facts.wildcard(q));
        }
        let refs: Vec<weft_facts::PlaceId> = transfer::place_value(cx, ob, st, &place)?
            .flat()
            .refs
            .into_iter()
            .collect();
        for &q in &refs {
            out.push(cx.facts.wildcard(q));
            for d in transfer::held_at(cx.p, st, cx.facts, cx.roots, q, None)? {
                out.push(cx.facts.wildcard(d));
            }
        }
        if let Some(ty) = p
            .bodies
            .get(ob.index())
            .and_then(|b| b.locals.get(ol.index()))
            .map(|d| d.ty)
        {
            for inner in transfer::rc_inners(cx.tys, ty) {
                let g = cx.roots.group(cx.tys, cx.facts, inner);
                out.push(cx.facts.wildcard(g));
            }
        }
    }
    // What the values of the clauses at `resume` point into (the runs of
    // the call so far): a local of a clause too.
    let recorded: Vec<weft_facts::PlaceId> = cx
        .hx
        .back_refs
        .get(&(body, block))
        .into_iter()
        .flatten()
        .copied()
        .collect();
    for q in recorded {
        out.push(cx.facts.wildcard(q));
    }
    let named: BTreeSet<weft_facts::RootId> = out
        .get(given_len..)
        .unwrap_or_default()
        .iter()
        .filter_map(|q| cx.facts.places.get(q.index()).map(|i| i.root))
        .collect();
    out.sort();
    out.dedup();
    Ok(Some(BackPlaces { places: out, named }))
}

/// What [`back_places`] gives: the places that the clauses can give back,
/// and the roots of the places that the clauses name themselves (not the
/// places that the call gives).
#[derive(Clone, Debug, Default)]
pub struct BackPlaces {
    /// The wildcard places.
    pub places: Vec<weft_facts::PlaceId>,
    /// The roots of the places that a clause names itself.
    pub named: BTreeSet<weft_facts::RootId>,
}

/// Why the facts do not model a `resume` in a closure or in a body inside
/// the clause (stage R0g: such a program is in scope only if the `ir`
/// pipeline rejects it).
pub const KONT_CAPTURED: &str = "a `resume` of a captured continuation (stage F16)";

/// Why a call that runs a clause is not in scope ([`given_ops`]).
pub const GIVES_BACK: &str = "a call that runs a clause of a local handler whose operation gives a function value or a reference back to the callee (stage F16)";

/// True if call `t` of body `body` runs a clause of a local handler: a
/// call, or a `join` or a `ScopeWait` whose child failure goes to a local
/// `Fail` handler (plan stage F18).
pub fn runs_clauses(cx: &Cx<'_>, body: BodyId, t: &TermKind) -> bool {
    matches!(
        t,
        TermKind::Call { .. }
            | TermKind::Join { .. }
            | TermKind::ScopeWait { .. }
            | TermKind::Fork { .. }
    ) && !call_handlers(cx, body, t).is_empty()
}

/// The transfer of a perform through the capability `cap` of a local
/// handler: the run of the clause ([`perform_run`]), then the destination
/// gets the result.
///
/// # Errors
///
/// The errors of [`perform_run`].
pub fn perform_local(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    (cap, op, args): (&Place, weft_ir::OpIdx, &[Operand]),
    dest: &Place,
) -> Result<(), AlphaError> {
    let out = perform_run(cx, body, st, cap, op, args)?;
    let abort = out.abort.map(AbortEdge::Replace);
    *st = out.after;
    transfer::bind_result(cx, body, st, &[], dest, out.value)?;
    // The abort edge of the perform: the states of the clause where it
    // aborts (`super::edges` takes it).
    cx.hx.abort_edge = abort;
    Ok(())
}

/// The transfer of a `Resume` in the facts of a clause body (its component).
///
/// The destination gets what a `resume` of the handler gives back, and the
/// locals that are not of the clause get the state at the end of the
/// handled body ([`Info`]).
///
/// # Errors
///
/// The errors of α, and [`AlphaError::Later`] for a continuation that the
/// analysis does not know (a continuation in the environment of a closure).
pub fn resume(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    (kont, arg, dest): (&Place, &Operand, &Place),
) -> Result<(), AlphaError> {
    let p = cx.p;
    let Some((h, _, _)) = kont_handler(p, body, kont) else {
        // A continuation in a closure (stage R0g): no resume point. The
        // argument moves, and the result is a plain value. The program is
        // in scope only if the `ir` pipeline rejects it.
        note_pending(crate::factgen::Unsupported {
            group: crate::irbuild::scope::Group::D,
            reason: KONT_CAPTURED.to_string(),
        });
        transfer::moves(p, body, st, [arg])?;
        return transfer::bind_result(cx, body, st, &[], dest, Tree::leaf(AbsVal::plain()));
    };
    handler(p, h)?;
    // A `resume` in the code of a clause after its first resume point,
    // while the handled body runs: a `multi` continuation runs the rest of
    // the handled body again (plan stage F16).
    if cx.hx.open.iter().any(|o| o.handler == h) {
        let v = transfer::operand(cx, body, st, arg)?;
        if let Some(o) = cx.hx.open_mut(h) {
            o.again.push((v, st.clone()));
        }
    }
    let info = cx.hx.info(h).cloned().unwrap_or_default();
    resume_with(
        cx,
        body,
        st,
        (kont, arg, dest),
        info.exit.as_ref(),
        &info.resumed,
    )
}

/// The most levels of function values that [`performs_cap`] follows.
const RUN_DEPTH_CAP: usize = 8;

/// True if the function value `f` can perform through the capability of
/// handler `h` (W0313, plan stage F17): a closure that captures the
/// capability and whose summary performs through it, runs a value of one of
/// its captures that can (with the values of the locals in the states
/// `ends`), runs a parameter, or gives a function value back or away. With
/// no summary, a capture of the capability counts. Class FP-W0313-RUN of the
/// second review of group D: a closure that runs a known closure with no
/// perform does not count.
fn performs_cap(
    p: &Program,
    sums: &super::Summaries,
    h: HandlerId,
    f: &super::FnVal,
    ends: &[&State],
    depth: usize,
) -> bool {
    let (super::FnVal::Closure(c) | super::FnVal::Made(c)) = f else {
        return false;
    };
    let Some(d) = p.closures.get(c.index()) else {
        return false;
    };
    let caps: Vec<u32> = (0..d.captures.len())
        .map(|k| u32::try_from(k).unwrap_or(u32::MAX))
        .filter(|&k| capture_handler(p, *c, k) == Some(h))
        .collect();
    if caps.is_empty() {
        return false;
    }
    let Ok(s) = sums.closure(*c) else {
        return true;
    };
    if depth == 0
        || s.performs.iter().any(|pf| {
            caps.iter()
                .any(|&k| pf.cap == super::summary::CapIface::Cap(k))
        })
        || !s.put_fns.is_empty()
        || !s.ret.fns.is_empty()
    {
        return true;
    }
    s.runs.iter().any(|r| {
        if !r.capture {
            return true;
        }
        let Some(src) = d.captures.get(r.param as usize).map(|x| &x.source) else {
            return true;
        };
        let Ok(k) = crate::factgen::alpha::owner_local(p, d.maker, src.local) else {
            return true;
        };
        ends.iter().any(|st| {
            st.tree(k).is_none_or(|t| {
                t.flat().fns.iter().any(|g| {
                    performs_cap(p, sums, h, g, ends, depth - 1)
                        || matches!(
                            g,
                            super::FnVal::Unknown
                                | super::FnVal::Param(_)
                                | super::FnVal::ParamResult(_)
                                | super::FnVal::Capture(_)
                        )
                })
            })
        })
    })
}
