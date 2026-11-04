//! The fact oracle and trace conformance (`docs/ir.md` 8.5): the hypotheses
//! of the proof link (B6) checked on runs of the IR engine.
//!
//! The oracle runs with [`RunOptions::fact_oracle`](crate::RunOptions). It
//! reads the facts of each component of a program in scope
//! (`weft_sema::factgen::components`) and the tables that map the IR to them:
//! the node of each IR location, the roots, the variables and the versions
//! of the parts. Each frame of the entry body of a component has a state,
//! and so has each frame of a closure body of the component (stage F11: the
//! closure body is a component of the facts of its function, from its node
//! `closure entry`). A captured cell of a closure frame is the cell of
//! `env.k` (capture `k`), and the targets of the references in it are
//! `(*env.k)` and below: α of the instantiated closure body names them with
//! the places of the maker (F12-fix). A move of a whole `ByMove` capture is
//! a move of its `E` variable.
//!
//! - **Trace conformance (A1).** Each op of the IR engine has its IR
//!   location. When the location of the next op of a frame changes, the
//!   oracle finds the nodes of the new location that a path of `cfg_edge`
//!   reaches from the nodes of the old one. The path can go through the
//!   other phases of the old terminator and through nodes whose location has
//!   no op (a `Goto` that falls through, an `Uninit`, the entry node). No
//!   such node is a failure: the run left the graph of the facts. An abort
//!   path goes from the aborting terminator to its cleanup copy in the same
//!   way.
//! - **The cell-to-root map.** A concrete place gets the fact places of an
//!   IR place that reaches it: a slot of the frame is its local; a cell that
//!   a value of the frame owns (a `Box`, the buffer of a `Vec`, an `Rc`
//!   object) is the place of the owner with the step of the handle; the
//!   target of a reference parameter at the entry of the frame is the
//!   `Param` root of the parameter, and a target behind it the `Held` root.
//!   α (`weft_sema::factgen::alpha`) gives the fact places of the IR place,
//!   with the roots of the component. A place that no IR place reaches
//!   (for example the result of a call that points into memory of a caller
//!   that no parameter names) has no name: the oracle counts it and does not
//!   check it.
//! - **C1 (points-into cover).** At the entry of each node, each reference
//!   that a used variable holds at run time is inside a `points_into` place
//!   of the variable. `S(l)` holds the references of the value of `l`,
//!   except the parts with variables of their own; the versions of a part
//!   hold the references of the part.
//! - **C2 (holder cover).** When the run follows a reference that a local of
//!   the frame holds, the node uses a variable of that local.
//! - **C4 (free cover).** The end of the cell of a local (`Dead`, also in a
//!   cleanup chain) has a `frees_at` at the node for a place at or above the
//!   root of the local.
//! - **C5 (change cover).** A write of a place that had a value has a
//!   `mutates_at` or a `lends_mut` at the node for a place at or above it.
//!   A read has a `reads_at` for a place that overlaps it.
//! - **D1 (move cover).** A move of a value that is not a copy value at run
//!   time has `moved_at` of the variable of its local at the node, and a
//!   move of a part also `moved_part` of the part.
//! - **D4 (suspension cover).** An abort that unwinds a frame with a live
//!   linear value has `may_abort` at the aborting node.
//!
//! - **A3 (summary cover, the summary oracle, stage F13).** An access of a
//!   callee (a function, a closure, or a callee of these) is also an access
//!   of each frame below it on the stack that waits at a run node. Each
//!   change of a place that such a frame can name has a `mutates_at` or a
//!   `lends_mut` at its run node for a place at or above it, and each read a
//!   `reads_at` that overlaps it: the facts of the summary that the run node
//!   applies (σ maps the interface of the callee to the places of the
//!   frame). A reference that a callee writes into a place of such a frame
//!   (parts `puts` and `put_fns`) is inside a `points_into` place of a
//!   variable that holds the place. A place that the frame cannot name (a
//!   local of the callee) is not checked, and the report counts it. At most
//!   [`SUMMARY_DEPTH`] frames below the callee are checked.
//!
//! - **A5 (clause cover, stage F17.2).** A clause of a local handler runs
//!   from a node of its handled body: the frames above the `handle` that
//!   are of the component of the handled body wait at their nodes. A node
//!   there with `escapes_at` of the effect of the handler and no
//!   `performs_at` with the capability of the handler is a failure: the
//!   facts send the effect past the function, and the clause does not run
//!   at the node.
//!
//! Rules of the oracle (`docs/ir.md` 8.5, "As built (F9)"): the read of `_0`
//! at `Return`, a whole write of a temporary or of `_0`, the read of the
//! buffer handle of an array and an access of a cell that the op frees need
//! no fact; a take inside a native function or a `Drop` is a write; a side
//! of a split counts as the element step. The old cell of a temporary that
//! gets a new cell (a promoted temporary in a loop, stage F10a) keeps the
//! name of the local.
//!
//! The checks on a frame in unwind mode are trace conformance and C4: the
//! cleanup chain ends the frame, and `unwound_at` invalidates what points
//! into it. A failure stops the run with a fault whose message starts with
//! `fact oracle` or `trace conformance`: a defect of the fact generator (or
//! of the oracle) with a concrete program and step.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use weft_facts::{FnFacts, NodeId, PlaceId, TaskId, VarId};
use weft_ir::{BodyId, DerefKind, FieldIdx, LocalId, Proj, VariantIdx};
use weft_sema::factgen::alpha::{self, Roots};
use weft_sema::factgen::holders::PartVersions;
use weft_sema::factgen::nodes::{Phase, NORMAL, TERM};
use weft_sema::factgen::vars::VarKey;
use weft_sema::factgen::Component;
use weft_sema::irbuild::Built;

use crate::code::Code;
use crate::heap::Heap;
use crate::value::{CellId, Place, Value};

/// One step of the IR trace (`--ir-trace`): a frame starts the ops of an IR
/// location.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IrStep {
    /// The frame: a number that the run gives each code frame.
    pub frame: u64,
    /// The body.
    pub body: u32,
    /// The block.
    pub block: u32,
    /// The statement, or the number of statements for the terminator.
    pub stmt: u32,
}

/// What the fact oracle saw in a run.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FactReport {
    /// Why the oracle checked nothing (a program that is not in scope, or a
    /// run of the AST compiler), or `None`.
    pub skipped: Option<String>,
    /// The frames that the oracle followed.
    pub frames: u64,
    /// The node changes that trace conformance checked.
    pub steps: u64,
    /// The checks of C1, C4, C5, D1 and D4.
    pub checks: u64,
    /// The concrete places that the cell-to-root map cannot name.
    pub unnamed: u64,
    /// The checks of the summary oracle (A3): an access of a callee that a
    /// frame that waits at a run node can name, and a reference that a
    /// callee puts into a place of such a frame.
    pub summary: u64,
    /// The accesses and references of a callee that the summary oracle did
    /// not check: a place that the frame below cannot name, a captured cell
    /// of a closure that a callee puts there, a place of another body.
    pub summary_unnamed: u64,
    /// The frames that the summary oracle did not check: a frame below the
    /// callee that unwinds, or that the oracle does not follow (`uid` 0: a
    /// copied frame of a continuation), at each op of a callee; and each op
    /// of a frame that the oracle does not follow.
    pub summary_skipped: u64,
    /// The checks of D4 that the oracle did not make: a frame that waits at
    /// a `handle` or at a `resume` unwinds, and no frame of its component
    /// unwound above it (plan stage F14).
    pub abort_skipped: u64,
    /// The checks of A4 (plan stage F17): a clause frame continues after its
    /// `resume`, and the rest of the handled body changed or freed the
    /// target of a reference that a local of the frame holds.
    pub resume: u64,
    /// Such references whose local has no `points_into` place: A4 does not
    /// check them.
    pub resume_unnamed: u64,
    /// The checks of A5 (plan stage F17.2): a clause of a local handler
    /// runs, and a node of its handled body has `performs_at` with the
    /// capability of the handler.
    pub clause: u64,
}

/// What the IR of a run gives the fact oracle: the IR and the components.
#[derive(Clone, Debug)]
pub struct FactInput {
    /// The IR.
    pub built: Built,
    /// The components of the program, or why the oracle checks nothing.
    pub comps: Result<Vec<Component>, String>,
}

/// An access of a place that the heap records for the oracle.
#[derive(Clone, Debug)]
pub enum HeapEvent {
    /// A read of the value at a place.
    Read(Place),
    /// A write of the value at a place: true if the place had no value (a
    /// first value).
    Write(Place, bool),
    /// A move out of a place.
    Take(Place),
    /// The run follows the reference at a place.
    Deref(Place),
    /// A cell ends: a buffer, a box or an `Rc` object is freed, or the cell
    /// of a local ends.
    Free(CellId),
}

/// What a variable is at run time.
#[derive(Clone, Copy, Debug)]
enum VarRole {
    /// `S(l)`: the value of local `l`.
    Local(LocalId),
    /// A version of the part with this index in [`Comp::parts`].
    Part(usize),
}

/// A component with the indexes of the checks.
#[derive(Clone, Debug)]
struct Comp {
    /// The index of the component of the facts (`FactInput::comps`): a
    /// function body, its closure bodies, its handled bodies and its
    /// clauses share it.
    unit: usize,
    /// The body is a clause: its nodes are in the terms of the clause (its
    /// parameters), not of the site.
    clause: bool,
    /// For a clause: the `Post` nodes of its `handle`. The code of the
    /// clause after its `resume` runs there, in the terms of the site.
    post: Vec<NodeId>,
    body: BodyId,
    facts: FnFacts,
    roots: Roots,
    tys: weft_ir::TyTable,
    entry: NodeId,
    succ: Vec<Vec<NodeId>>,
    /// The location of each node: the block and the statement (or [`TERM`]).
    loc: Vec<Option<(u32, u32)>>,
    /// The nodes of each location.
    at_loc: HashMap<(u32, u32), Vec<NodeId>>,
    /// True for a node whose location has no op.
    silent: Vec<bool>,
    uses: Vec<Vec<VarId>>,
    points: HashMap<VarId, Vec<PlaceId>>,
    frees: Vec<Vec<PlaceId>>,
    changes: Vec<Vec<PlaceId>>,
    reads: Vec<Vec<PlaceId>>,
    moved: Vec<Vec<VarId>>,
    moved_part: Vec<Vec<PlaceId>>,
    may_abort: Vec<bool>,
    roles: HashMap<VarId, VarRole>,
    s_of: HashMap<LocalId, VarId>,
    /// The `S` variable of each local of each body of the component (the
    /// maker of a closure body names a captured reference with it).
    s_any: HashMap<(u32, LocalId), VarId>,
    /// The `E` variable of each `ByMove` capture of a closure body, by the
    /// index of the capture.
    e_of: HashMap<u32, VarId>,
    /// The variables of each local: `S`, the versions of its parts, and the
    /// `U`, `C`, `W` and `N` variables of its places.
    of_local: HashMap<LocalId, Vec<VarId>>,
    parts: Vec<PartVersions>,
    /// The variables of each heap slot of the entry body, by the fact place
    /// of the slot.
    slots: Vec<(PlaceId, Vec<VarId>)>,
    /// The roots of the locals that the facts name.
    local_roots: HashMap<LocalId, PlaceId>,
    /// The blocks that end with `Return`, and the local `_0`.
    returns: HashSet<u32>,
    ret: LocalId,
    /// A scope body (follow-up F19.3): the oracle follows its frames only
    /// for trace conformance and the task check ([`FactOracle::light_step`]).
    light: bool,
    /// The tasks that each node starts (`spawned_at`), but the tasks of
    /// `waits`: no task of the run is one of them.
    spawns: Vec<Vec<TaskId>>,
    /// The tasks that end after each node (`joined_at`).
    joins: Vec<Vec<TaskId>>,
    /// The tasks of the calls that stand for the tasks that can run while a
    /// clause of a local handler runs at the call (follow-up F19.5,
    /// `weft_sema::factgen::templates::WaitTask`).
    waits: Vec<weft_sema::factgen::templates::WaitTask>,
}

/// A target of a reference: a place, or the elements of a buffer (a slice).
#[derive(Clone, Debug)]
enum Target {
    Place(Place),
    Elems(CellId),
}

impl Target {
    /// The cell of the target.
    const fn cell(&self) -> CellId {
        match self {
            Self::Place(p) => p.cell,
            Self::Elems(c) => *c,
        }
    }

    /// True if an access of the place at `path` of the cell of the target
    /// (`None`: the whole cell ends) reaches the target: the place is at,
    /// above or below the target.
    fn reached_by(&self, path: Option<&[u32]>) -> bool {
        match (self, path) {
            (_, None) | (Self::Elems(_), _) => true,
            (Self::Place(t), Some(p)) => t.path.starts_with(p) || p.starts_with(&t.path),
        }
    }
}

/// A clause frame that waits at a `resume` (A4, plan stage F17): the rest
/// of the handled body runs above it. The `Resume` node lends and frees what
/// that code changes and frees (`lends_mut`, `releases_at`).
#[derive(Clone, Debug)]
struct Wait {
    /// The component of the clause frame.
    comp: usize,
    /// The nodes of the `resume`.
    nodes: Vec<NodeId>,
    /// The task of the frame.
    task: usize,
    /// The frame (0 for a copy of a frame).
    uid: u64,
    /// Each reference that a local of the frame holds, with the local.
    refs: Vec<(Target, LocalId)>,
    /// The references whose target an access of the code above reached,
    /// with the kind of the access.
    hits: Vec<(usize, &'static str)>,
    /// For a frame in a `multi` continuation that a caller frame of the
    /// continuation runs (A4 of copies, plan stage F17.1): the fact places
    /// of each reference in the terms of that caller frame, and `nodes` are
    /// the `Copy` nodes of its run node. `None` for a clause frame that
    /// waits at its `resume`.
    names: Option<Vec<Vec<PlaceId>>>,
}

/// The target of a reference parameter at the entry of a frame, or a
/// captured cell of a frame of a closure body.
#[derive(Clone, Debug)]
struct Anchor {
    /// The concrete place.
    place: Place,
    /// The parameter local (the environment for a captured cell).
    local: LocalId,
    /// The index of the parameter. A captured cell has none: α names the
    /// places of the environment itself.
    param: Option<u32>,
    /// The projections from the parameter local to the place.
    proj: Vec<Proj>,
}

/// The state of one frame.
#[derive(Clone, Debug)]
struct FrameFacts {
    comp: usize,
    /// The nodes of the current location.
    cur: Vec<NodeId>,
    /// The current location.
    at: Option<(u32, u32)>,
    anchors: Vec<Anchor>,
    /// The old cells of the temporaries that got a new cell (`LiveTemp`
    /// again, a promoted temporary in a loop): a reference of an earlier
    /// iteration points into such a cell, and its name is the local.
    retired: HashMap<CellId, LocalId>,
    /// For the frame of a clause: the component and the nodes of the node
    /// that runs the clause (a `perform` of the handled body, in the terms
    /// of the site), if the frame that ran the op is of the same component.
    site: Option<(usize, Vec<NodeId>)>,
}

/// The base of a cell in the heap index: a local or an anchor.
#[derive(Clone, Debug)]
enum Base {
    Local(LocalId),
    Anchor(usize),
}

/// The scope bodies of component `c`, each with the `Main` node of its
/// `scope` terminator (follow-up F19.3).
fn scope_entries(built: &Built, c: &Component) -> Vec<(BodyId, NodeId)> {
    let p = &built.program;
    let mut out = Vec::new();
    for (k, &n) in c.emitted.table.iter() {
        if k.at != TERM || k.phase != Phase::Main || k.dest != NORMAL {
            continue;
        }
        let term = p
            .bodies
            .get(k.body.index())
            .and_then(|b| b.blocks.get(k.block.index()))
            .map(|blk| &blk.term.kind);
        let Some(weft_ir::TermKind::Scope { scope, .. }) = term else {
            continue;
        };
        if let Some(d) = p.scopes.get(scope.index()) {
            out.push((d.body, n));
        }
    }
    out
}

/// The most projections of the walk of [`owner_of`].
const OWNER_DEPTH: usize = 128;

/// The limit of values that one index of the cells of a frame visits.
const INDEX_LIMIT: usize = 200_000;

/// The fact oracle of one run.
#[derive(Debug)]
pub struct FactOracle {
    input: Rc<FactInput>,
    comps: Vec<Comp>,
    by_body: HashMap<u32, usize>,
    frames: HashMap<u64, FrameFacts>,
    /// For the summary oracle (A3) of one op: the component and the nodes of
    /// the frame above the frame that it checks now. A frame that waits at a
    /// `handle` checks with the nodes of the frame above it, if that frame
    /// is of the same component: the handled body and the clauses splice
    /// into the facts of the site there (plan stage F14).
    above: Option<(usize, Vec<NodeId>)>,
    /// For D4: the component and the nodes of the last frame that an abort
    /// unwound. A frame that waits at a `handle` or at a `resume` checks
    /// with them (the frame above it is its handled body or a clause).
    unwound: Option<(usize, Vec<NodeId>)>,
    /// The frame of the last op that the oracle followed: the frame that
    /// runs a clause, when a clause frame starts.
    last: Option<u64>,
    /// The fact places and the type of each IR place that the map named:
    /// the component, the place and the parameter of its anchor.
    names: NameCache,
    /// The clause frames that wait at a `resume` (A4), by frame, or by the
    /// key of a copy of a frame in a `multi` continuation.
    waits: HashMap<u64, Wait>,
    /// The waits and the references that point into each cell.
    wait_cells: HashMap<CellId, Vec<(u64, usize)>>,
    /// The last key of a copy of a waiting frame.
    copy_keys: u64,
    /// The frames of scope bodies ([`LIGHT`]): the oracle follows them only
    /// for the task check (follow-up F19.3).
    light: HashMap<u64, FrameFacts>,
    /// The frame of the last op, if it is a frame of a scope body.
    light_last: Option<u64>,
    /// The run of a function or closure body that each frame is part of
    /// (the frame of that body): a handled body and a scope body run in the
    /// run of their site.
    activation: HashMap<u64, u64>,
    /// For each task of the run: the tasks that it knows are done (a
    /// join, the end of a scope, or what its parent knew at the spawn).
    knows: HashMap<usize, HashSet<usize>>,
    /// The tasks of the run that each run of a body started at a node with
    /// `spawned_at(T, _)`: by component, run and `T`. A frame below the
    /// frame of the spawn whose nodes start `T` (a call that runs a closure
    /// that spawns) gets the task too (follow-up F19.4).
    instances: HashMap<(usize, u64, TaskId), Vec<usize>>,
    /// The nodes where task `T` of component `ci` is active (the rules
    /// `active` of the spec), by `(ci, T)`.
    active: HashMap<(usize, TaskId), Vec<bool>>,
    /// What the run saw.
    pub report: FactReport,
}

/// The bit of the number of a frame of a scope body.
///
/// The oracle follows such a frame only for the task check of `joined_at`
/// (follow-up F19.3). The machine treats it as a frame that the oracle does
/// not follow.
pub const LIGHT: u64 = 1 << 61;

/// True if the fact oracle follows frame `uid` with each check: not 0 and
/// not a frame of a scope body ([`LIGHT`]).
pub const fn tracked(uid: u64) -> bool {
    uid != 0 && uid & LIGHT == 0
}

/// The cache of [`FactOracle::name`].
type NameCache =
    HashMap<(usize, weft_ir::Place, Option<u32>), (Vec<PlaceId>, Option<weft_ir::TyId>)>;

/// The most frames below a callee that the summary oracle checks.
pub const SUMMARY_DEPTH: usize = 16;

/// The first key of a copy of a waiting frame: above the numbers of the
/// frames.
const COPY_KEYS: u64 = 1 << 62;

/// A dummy index local for an element step: α does not read it.
const ELEM: LocalId = LocalId(u32::MAX);

fn u32_of(n: usize) -> u32 {
    u32::try_from(n).unwrap_or(u32::MAX)
}

impl Comp {
    /// True if the nodes `group` of a frame are a `handle` or a `resume`:
    /// the frame waits for its handled body or for the rest of the handled
    /// body (plan stage F14).
    fn waits(&self, group: &[NodeId]) -> bool {
        group.iter().any(|n| {
            self.facts
                .nodes
                .get(n.index())
                .is_some_and(|x| x.kind == "handle" || x.kind == "resume")
        })
    }

    /// The component of body `body` (the entry body of `c`, or a closure
    /// body of it) with the entry node `entry` and the code `code`.
    fn new(
        built: &Built,
        (unit, c): (usize, &Component),
        code: Option<&Code>,
        body_id: BodyId,
        entry: NodeId,
    ) -> Self {
        let f = &c.facts;
        let n = f.nodes.len();
        let mut succ = vec![Vec::new(); n];
        for &(a, b) in &f.cfg_edge {
            if let Some(s) = succ.get_mut(a.index()) {
                s.push(b);
            }
        }
        let post = clause_post(built, c, body_id);
        let mut loc = vec![None; n];
        let mut at_loc: HashMap<(u32, u32), Vec<NodeId>> = HashMap::new();
        for (k, &id) in c.emitted.table.iter() {
            if k.body != body_id {
                continue;
            }
            if let Some(x) = loc.get_mut(id.index()) {
                *x = Some((k.block.0, k.at));
            }
            at_loc.entry((k.block.0, k.at)).or_default().push(id);
        }
        // The locations with an op.
        let body = built.program.bodies.get(body_id.index());
        let mut ops: HashSet<(u32, u32)> = HashSet::new();
        if let (Some(code), Some(b)) = (code, body) {
            for l in &code.locs {
                let n_stmts = b
                    .blocks
                    .get(l.block as usize)
                    .map_or(0, |x| u32_of(x.stmts.len()));
                let at = if l.stmt >= n_stmts { TERM } else { l.stmt };
                ops.insert((l.block, at));
            }
        }
        let silent = loc
            .iter()
            .map(|l| l.is_none_or(|l| !ops.contains(&l)))
            .collect();
        let per_node = |rel: &[(NodeId, PlaceId)]| {
            let mut out = vec![Vec::new(); n];
            for &(m, p) in rel {
                if let Some(x) = out.get_mut(m.index()) {
                    x.push(p);
                }
            }
            out
        };
        let mut uses = vec![Vec::new(); n];
        for &(v, m) in &f.uses {
            if let Some(x) = uses.get_mut(m.index()) {
                x.push(v);
            }
        }
        let mut points: HashMap<VarId, Vec<PlaceId>> = HashMap::new();
        for &(v, p) in &f.points_into {
            points.entry(v).or_default().push(p);
        }
        let mut owned: HashMap<VarId, Vec<PlaceId>> = HashMap::new();
        for &(p, v) in &f.owner {
            owned.entry(v).or_default().push(p);
        }
        let mut frees = per_node(&f.releases_at);
        let mut moved_part = vec![Vec::new(); n];
        for &(p, m) in &f.moved_part {
            if let Some(x) = frees.get_mut(m.index()) {
                x.push(p);
            }
            if let Some(x) = moved_part.get_mut(m.index()) {
                x.push(p);
            }
        }
        let mut moved = vec![Vec::new(); n];
        for &(v, m) in &f.moved_at {
            if let Some(x) = moved.get_mut(m.index()) {
                x.push(v);
            }
        }
        for &(v, m) in f.moved_at.iter().chain(&f.scope_end).chain(&f.unwound_at) {
            if let (Some(x), Some(rs)) = (frees.get_mut(m.index()), owned.get(&v)) {
                x.extend(rs.iter().copied());
            }
        }
        let mut changes = per_node(&f.mutates_at);
        for &(m, p) in &f.lends_mut {
            if let Some(x) = changes.get_mut(m.index()) {
                x.push(p);
            }
        }
        let mut footprint: HashMap<weft_facts::CapId, Vec<PlaceId>> = HashMap::new();
        for &(cap, p) in &f.footprint {
            footprint.entry(cap).or_default().push(p);
        }
        for &(m, cap) in &f.performs_at {
            if let (Some(x), Some(ps)) = (changes.get_mut(m.index()), footprint.get(&cap)) {
                x.extend(ps.iter().copied());
            }
        }
        let reads = per_node(&f.reads_at);
        let mut may_abort = vec![false; n];
        for &m in &f.may_abort {
            if let Some(x) = may_abort.get_mut(m.index()) {
                *x = true;
            }
        }
        let mut roles = HashMap::new();
        let mut s_of = HashMap::new();
        let mut s_any = HashMap::new();
        for key in c.emitted.vars.keys() {
            if let VarKey::S(b, l) = key {
                if let Some(v) = c.emitted.vars.get(key) {
                    s_any.insert((b.0, *l), v);
                }
                if *b == body_id {
                    if let Some(v) = c.emitted.vars.get(key) {
                        roles.insert(v, VarRole::Local(*l));
                        s_of.insert(*l, v);
                    }
                }
            }
        }
        let mut e_of = HashMap::new();
        for key in c.emitted.vars.keys() {
            if let VarKey::E(b, k) = key {
                if let (true, Some(v)) = (*b == body_id, c.emitted.vars.get(key)) {
                    e_of.insert(*k, v);
                }
            }
        }
        let mut of_local: HashMap<LocalId, Vec<VarId>> = HashMap::new();
        for key in c.emitted.vars.keys() {
            let local = match key {
                VarKey::S(b, l) | VarKey::C(b, l) if *b == body_id => Some(*l),
                VarKey::H(b, pl) | VarKey::U(b, pl) | VarKey::W(b, pl, _) if *b == body_id => {
                    Some(pl.local)
                }
                VarKey::N(b, _, pl, _) if *b == body_id => Some(pl.local),
                _ => None,
            };
            if let (Some(l), Some(v)) = (local, c.emitted.vars.get(key)) {
                of_local.entry(l).or_default().push(v);
            }
        }
        for (i, p) in c.emitted.parts.iter().enumerate() {
            if p.key.0 != body_id {
                continue;
            }
            for &v in &p.vars {
                roles.insert(v, VarRole::Part(i));
                of_local.entry(p.key.1).or_default().push(v);
            }
        }
        let returns = body.map_or_else(HashSet::new, |b| {
            b.blocks
                .iter()
                .enumerate()
                .filter(|(_, x)| x.term.kind == weft_ir::TermKind::Return)
                .map(|(i, _)| u32_of(i))
                .collect()
        });
        let ret = body.map_or(LocalId(0), |b| b.ret);
        let per_task = |rel: &[(TaskId, NodeId)]| {
            let mut out: Vec<Vec<TaskId>> = vec![Vec::new(); n];
            for &(t, m) in rel {
                if let Some(x) = out.get_mut(m.index()) {
                    if !x.contains(&t) {
                        x.push(t);
                    }
                }
            }
            out
        };
        let local_roots = c
            .emitted
            .roots
            .local_roots()
            .filter(|(k, _)| k.0 == body_id)
            .map(|(k, p)| (k.1, p))
            .collect();
        Self {
            unit,
            clause: built
                .program
                .bodies
                .get(body_id.index())
                .is_some_and(|b| matches!(b.kind, weft_ir::BodyKind::Clause(..))),
            post,
            body: body_id,
            facts: c.facts.clone(),
            roots: c.emitted.roots.clone(),
            tys: c.emitted.tys.clone(),
            entry,
            succ,
            loc,
            at_loc,
            silent,
            uses,
            points,
            frees,
            changes,
            reads,
            moved,
            moved_part,
            may_abort,
            roles,
            s_of,
            s_any,
            e_of,
            of_local,
            parts: c.emitted.parts.clone(),
            slots: c
                .emitted
                .slots
                .iter()
                .map(|x| (x.key, x.vars.clone()))
                .collect(),
            local_roots,
            returns,
            ret,
            light: body.is_some_and(|b| matches!(b.kind, weft_ir::BodyKind::Scope(_))),
            spawns: per_task(
                &f.spawned_at
                    .iter()
                    .copied()
                    .filter(|(t, _)| {
                        !c.emitted
                            .wait_tasks
                            .iter()
                            .any(|w| w.task == *t || w.back == *t)
                    })
                    .collect::<Vec<_>>(),
            ),
            joins: per_task(&f.joined_at),
            waits: c.emitted.wait_tasks.clone(),
        }
    }

    /// True if the facts start task `t` at some node (`spawned_at`).
    fn starts_task(&self, t: TaskId) -> bool {
        self.facts.spawned_at.iter().any(|&(u, _)| u == t)
    }

    /// The kind of node `n` (`""` for a node of no kind).
    fn kind_of(&self, n: NodeId) -> &str {
        self.facts
            .nodes
            .get(n.index())
            .map_or("", |x| x.kind.as_str())
    }

    /// The label of node `n`.
    fn label_of(&self, n: NodeId) -> &str {
        self.facts
            .nodes
            .get(n.index())
            .map_or("", |x| x.label.as_str())
    }

    /// The text of node `n` for a message.
    fn node_text(&self, n: NodeId) -> String {
        self.facts.nodes.get(n.index()).map_or_else(
            || format!("{n}"),
            |i| {
                if i.kind.is_empty() {
                    format!("{n} `{}` ({})", i.label, i.detail)
                } else {
                    format!("{n} `{}` ({}, {})", i.label, i.kind, i.at)
                }
            },
        )
    }

    /// True if place `q` is below a parameter of the body of the component
    /// (a clause: the terms of its interface).
    fn in_params(&self, q: PlaceId) -> bool {
        let root = self.facts.place(q).root;
        matches!(
            self.roots.role(root),
            Some(alpha::Role::Param(b, _) | alpha::Role::Held(b, _)) if b == self.body
        )
    }

    /// The nodes of the location of the nodes `cur`: the nodes `cur` and
    /// the nodes that their edges reach at the same location (the later
    /// phases of a terminator).
    fn group(&self, cur: &[NodeId]) -> Vec<NodeId> {
        let mut out: Vec<NodeId> = cur.to_vec();
        let mut i = 0;
        while let Some(&x) = out.get(i) {
            i += 1;
            let at = self.loc.get(x.index()).copied().flatten();
            for &y in self.succ.get(x.index()).map_or(&[][..], Vec::as_slice) {
                let same = at.is_some() && self.loc.get(y.index()).copied().flatten() == at;
                if same && !out.contains(&y) {
                    out.push(y);
                }
            }
        }
        out
    }

    /// The nodes of location `to` that a path reaches from the nodes `from`
    /// (at location `at`) through the later phases of `at` and through
    /// silent nodes.
    fn reach(&self, from: &[NodeId], at: Option<(u32, u32)>, to: (u32, u32)) -> Vec<NodeId> {
        // The sets are small: the nodes of a few locations.
        let mut seen: Vec<NodeId> = from.to_vec();
        let mut work: Vec<NodeId> = from.to_vec();
        let mut out = Vec::new();
        while let Some(x) = work.pop() {
            for &y in self.succ.get(x.index()).map_or(&[][..], Vec::as_slice) {
                if seen.contains(&y) {
                    continue;
                }
                seen.push(y);
                let yl = self.loc.get(y.index()).copied().flatten();
                if yl == Some(to) {
                    out.push(y);
                } else if (at.is_some() && yl == at)
                    || self.silent.get(y.index()).copied().unwrap_or(false)
                {
                    work.push(y);
                }
            }
        }
        out.sort();
        out
    }

    /// The nodes that a path from the nodes `from` (at location `at`) to the
    /// nodes `next` of location `to` leaves (the paths of [`Self::reach`]):
    /// the nodes `from` and the nodes between them and `next`, with no node
    /// of `next` and no node of another body.
    fn left(
        &self,
        from: &[NodeId],
        at: Option<(u32, u32)>,
        to: (u32, u32),
        next: &[NodeId],
    ) -> Vec<NodeId> {
        let mut seen: Vec<NodeId> = from.to_vec();
        let mut work: Vec<NodeId> = from.to_vec();
        let mut edges: Vec<(NodeId, NodeId)> = Vec::new();
        while let Some(x) = work.pop() {
            for &y in self.succ.get(x.index()).map_or(&[][..], Vec::as_slice) {
                let yl = self.loc.get(y.index()).copied().flatten();
                let inner = yl != Some(to)
                    && ((at.is_some() && yl == at)
                        || self.silent.get(y.index()).copied().unwrap_or(false));
                if yl == Some(to) || inner {
                    edges.push((x, y));
                }
                if inner && !seen.contains(&y) {
                    seen.push(y);
                    work.push(y);
                }
            }
        }
        // Back from `next` over the edges of the paths.
        let mut on: Vec<NodeId> = next.to_vec();
        let mut i = 0;
        while let Some(&y) = on.get(i) {
            i += 1;
            for &(a, b) in &edges {
                if b == y && !on.contains(&a) {
                    on.push(a);
                }
            }
        }
        // A node of another body (a handled body, a scope body, a clause
        // that the frame of another body runs) is that frame's to check.
        on.retain(|x| !next.contains(x) && self.loc.get(x.index()).copied().flatten().is_some());
        on
    }

    /// True if fact place `q` is inside the place `d` that a reference
    /// points into: `d` is a wildcard place or a place below one, and `q`
    /// is at or below the base of its outermost wildcard step; or `q` is at
    /// or below `d` by stable steps only.
    fn ref_inside(&self, q: PlaceId, d: PlaceId) -> bool {
        let (pq, pd) = (self.facts.place(q), self.facts.place(d));
        if pq.root != pd.root {
            return false;
        }
        // A wildcard place, and a place below one, is anywhere inside the
        // base of its outermost wildcard step (`wild_at` of the spec).
        if let Some(b) = self.facts.wild_base(d) {
            return weft_verified::places::within(&pq.steps, &coarse(&self.facts.place(b).steps));
        }
        weft_verified::places::within(&pq.steps, &coarse(&pd.steps))
            && pq.steps.iter().skip(pd.steps.len()).all(|s| !s.unstable)
    }

    /// True if fact place `q` is at or below place `m`, or below the base of
    /// the outermost wildcard step of `m` (a wildcard place, or a place below
    /// one).
    fn below(&self, q: PlaceId, m: PlaceId) -> bool {
        let (pq, pm) = (self.facts.place(q), self.facts.place(m));
        if pq.root != pm.root {
            return false;
        }
        let base = if pm.is_wildcard() || self.facts.wild_base(m).is_some() {
            self.facts.wild_base(m).or(pm.parent)
        } else {
            Some(m)
        };
        base.is_some_and(|b| {
            weft_verified::places::within(&pq.steps, &coarse(&self.facts.place(b).steps))
        })
    }
}

impl FactOracle {
    /// The oracle of a run with the IR `input` and the code `codes` (code
    /// unit `i` is IR body `i`).
    pub fn new(input: Rc<FactInput>, codes: &[Rc<Code>]) -> Self {
        let mut comps = Vec::new();
        let mut by_body = HashMap::new();
        let mut report = FactReport::default();
        match &input.comps {
            Ok(cs) => {
                for (unit, c) in cs.iter().enumerate() {
                    by_body.insert(c.entry.0, comps.len());
                    let code = codes.get(c.entry.index()).map(Rc::as_ref);
                    comps.push(Comp::new(
                        &input.built,
                        (unit, c),
                        code,
                        c.entry,
                        c.emitted.entry_node,
                    ));
                    // Each closure body and each clause body of the
                    // component, from its entry node, and each handled body,
                    // from the `Main` node of its `handle` (plan stage F14).
                    for &(cb, n) in c
                        .emitted
                        .closure_entries
                        .iter()
                        .chain(&c.emitted.clause_entries)
                        .chain(&c.emitted.handled_entries)
                    {
                        by_body.insert(cb.0, comps.len());
                        let code = codes.get(cb.index()).map(Rc::as_ref);
                        comps.push(Comp::new(&input.built, (unit, c), code, cb, n));
                    }
                    // Each scope body, from the `Main` node of its `scope`:
                    // the oracle follows it only for the task check
                    // (follow-up F19.3).
                    for (sb, n) in scope_entries(&input.built, c) {
                        if by_body.contains_key(&sb.0) {
                            continue;
                        }
                        by_body.insert(sb.0, comps.len());
                        let code = codes.get(sb.index()).map(Rc::as_ref);
                        comps.push(Comp::new(&input.built, (unit, c), code, sb, n));
                    }
                }
            }
            Err(why) => report.skipped = Some(why.clone()),
        }
        Self {
            input,
            comps,
            by_body,
            frames: HashMap::new(),
            above: None,
            unwound: None,
            last: None,
            names: HashMap::new(),
            waits: HashMap::new(),
            wait_cells: HashMap::new(),
            copy_keys: COPY_KEYS,
            light: HashMap::new(),
            light_last: None,
            activation: HashMap::new(),
            knows: HashMap::new(),
            instances: HashMap::new(),
            active: HashMap::new(),
            report,
        }
    }

    /// True if the frames of code `code` are frames of a scope body: the
    /// oracle follows them only for the task check ([`LIGHT`]).
    pub fn light_code(&self, code: &Code) -> bool {
        code.locs
            .first()
            .and_then(|l| self.by_body.get(&l.body))
            .and_then(|&ci| self.comps.get(ci))
            .is_some_and(|c| c.light)
    }

    /// Task `parent` starts task `child`; `frames` are the frames of the
    /// parent, from the top (the frame of the spawn) down. The child knows
    /// what its parent knows. For each frame whose nodes start one task `T`
    /// of the facts (`spawned_at`), the child is a task of `T` of the run of
    /// the frame: the frame of the spawn, and a frame below it that waits
    /// at a node that starts `T` (a call that runs a closure that spawns,
    /// follow-up F19.4).
    pub fn task_spawned(&mut self, parent: usize, child: usize, frames: &[u64]) {
        let known = self.knows.get(&parent).cloned().unwrap_or_default();
        self.knows.insert(child, known);
        for &uid in frames {
            let Some(fr) = self.frames.get(&uid).or_else(|| self.light.get(&uid)) else {
                continue;
            };
            let Some(comp) = self.comps.get(fr.comp) else {
                continue;
            };
            let mut ts: Vec<TaskId> = comp
                .group(&fr.cur)
                .iter()
                .flat_map(|n| comp.spawns.get(n.index()).into_iter().flatten().copied())
                .collect();
            ts.sort_unstable();
            ts.dedup();
            let [t] = ts.as_slice() else {
                continue;
            };
            let run = self.activation.get(&uid).copied().unwrap_or(uid);
            let e = self.instances.entry((comp.unit, run, *t)).or_default();
            if !e.contains(&child) {
                e.push(child);
            }
        }
    }

    /// The nodes of component `ci` where task `t` is active: the rules
    /// `active(T, Q) :- spawned_at(T, P), cfg_edge(P, Q)` and
    /// `active(T, Q) :- active(T, P), cfg_edge(P, Q), !joined_at(T, P)`.
    fn active_nodes(&mut self, ci: usize, t: TaskId) -> Option<&Vec<bool>> {
        if !self.active.contains_key(&(ci, t)) {
            let comp = self.comps.get(ci)?;
            let n = comp.succ.len();
            let mut on = vec![false; n];
            let mut work: Vec<NodeId> = Vec::new();
            for &(u, p) in &comp.facts.spawned_at {
                if u != t {
                    continue;
                }
                for &q in comp.succ.get(p.index()).into_iter().flatten() {
                    if let Some(x) = on.get_mut(q.index()) {
                        if !*x {
                            *x = true;
                            work.push(q);
                        }
                    }
                }
            }
            while let Some(p) = work.pop() {
                if comp.joins.get(p.index()).is_some_and(|ts| ts.contains(&t)) {
                    continue;
                }
                for &q in comp.succ.get(p.index()).into_iter().flatten() {
                    if let Some(x) = on.get_mut(q.index()) {
                        if !*x {
                            *x = true;
                            work.push(q);
                        }
                    }
                }
            }
            self.active.insert((ci, t), on);
        }
        self.active.get(&(ci, t))
    }

    /// The task start check (follow-up F19.4): a clause of a local handler
    /// runs on task `task` while each frame of `starts` (frame, component,
    /// nodes; from the handled body up) waits at its nodes: the nodes that
    /// run the clause, or the current nodes of a frame that does not. Each task of `T`
    /// that the run of such a frame started and that can still run (no join
    /// ordered its end before) runs at the same time as the clause. The
    /// innermost such frame names the code of the clause in its facts, so
    /// `T` must be active at a node of its `at`.
    fn check_started(
        &mut self,
        starts: &[(u64, usize, Vec<NodeId>)],
        task: usize,
        handler: weft_ir::HandlerId,
    ) -> Result<(), String> {
        let known = self.knows.get(&task).cloned().unwrap_or_default();
        // The innermost frame of each live task, with the task of the facts.
        let mut at_of: std::collections::BTreeMap<usize, (usize, TaskId)> =
            std::collections::BTreeMap::new();
        for (i, (uid, ci, _)) in starts.iter().enumerate() {
            let Some(unit) = self.comps.get(*ci).map(|c| c.unit) else {
                continue;
            };
            let run = self.activation.get(uid).copied().unwrap_or(*uid);
            for ((u, r, t), rs) in &self.instances {
                if *u != unit || *r != run {
                    continue;
                }
                for &x in rs {
                    if x != task && !known.contains(&x) {
                        at_of.insert(x, (i, *t));
                    }
                }
            }
        }
        for (r, (i, t)) in at_of {
            let Some((_, ci, at)) = starts.get(i) else {
                continue;
            };
            let ci = *ci;
            // A task of the call that stands for `T` while the clause runs
            // (follow-up F19.5) names the code of the clause too.
            let stands = self.comps.get(ci).is_some_and(|c| {
                c.waits.iter().any(|w| {
                    w.handler == handler
                        && at.contains(&w.main)
                        && w.stands.contains(&t)
                        && c.starts_task(w.task)
                })
            });
            let ok = stands
                || self.active_nodes(ci, t).is_some_and(|on| {
                    at.iter()
                        .any(|n| on.get(n.index()).copied().unwrap_or(false))
                });
            if !ok {
                let (text, name) = self
                    .comps
                    .get(ci)
                    .map(|c| {
                        let t: Vec<String> = at.iter().map(|&n| c.node_text(n)).collect();
                        (t.join(", "), c.facts.name.clone())
                    })
                    .unwrap_or_default();
                return Err(format!(
                    "fact oracle (task start): in `{name}`, a clause of a local handler runs at {text}, and task {r} of `{t}` can run at the same time, but `{t}` is not active there"
                ));
            }
        }
        Ok(())
    }

    /// The task start check for the tasks of a callee (follow-up F19.5,
    /// issue #50): a clause of a local handler runs on task `task`, and the
    /// last frame of `starts` (frame, component, nodes) is the frame of the
    /// component of the handler that waits at a call. The frames of
    /// `outer` (frame, component) are the frames of other components above
    /// it: the callees. If a task that the run of such a frame started can
    /// still run (no join ordered its end before), the call must have a task
    /// for the handler that stands for it (a `WaitTask` at a node of the
    /// nodes of the frame, whose task the facts start): else the facts of
    /// the component of the handler do not see that the task runs while the
    /// clause runs.
    fn check_waits(
        &self,
        starts: &[(u64, usize, Vec<NodeId>)],
        outer: &[(u64, usize)],
        task: usize,
        handler: weft_ir::HandlerId,
    ) -> Result<(), String> {
        let Some((_, ci, at)) = starts.last() else {
            return Ok(());
        };
        let known = self.knows.get(&task);
        let mut live: Option<(usize, usize, TaskId)> = None;
        for (uid, oci) in outer {
            let Some(unit) = self.comps.get(*oci).map(|c| c.unit) else {
                continue;
            };
            let run = self.activation.get(uid).copied().unwrap_or(*uid);
            for ((u, r, t), rs) in &self.instances {
                if *u != unit || *r != run {
                    continue;
                }
                if let Some(&x) = rs
                    .iter()
                    .find(|&&x| x != task && !known.is_some_and(|k| k.contains(&x)))
                {
                    live = Some((x, *oci, *t));
                    break;
                }
            }
            if live.is_some() {
                break;
            }
        }
        let Some((r, oci, t)) = live else {
            return Ok(());
        };
        let Some(comp) = self.comps.get(*ci) else {
            return Ok(());
        };
        if comp
            .waits
            .iter()
            .any(|w| w.handler == handler && at.contains(&w.main) && comp.starts_task(w.task))
        {
            return Ok(());
        }
        let text: Vec<String> = at.iter().map(|&n| comp.node_text(n)).collect();
        let callee = self
            .comps
            .get(oci)
            .map(|c| c.facts.name.clone())
            .unwrap_or_default();
        Err(format!(
            "fact oracle (task start): in `{}`, a clause of a local handler runs at {}, and task {r} of `{t}` of `{callee}` can run at the same time, but the call has no task that stands for it",
            comp.facts.name,
            text.join(", "),
        ))
    }

    /// Task `cur` knows that task `u` is done (a join, the end of a scope or
    /// of a `fork`, an unwinding that waits for it), and what `u` knew.
    pub fn task_joined(&mut self, cur: usize, u: usize) {
        if cur == u {
            return;
        }
        let theirs = self.knows.get(&u).cloned().unwrap_or_default();
        let mine = self.knows.entry(cur).or_default();
        mine.insert(u);
        mine.extend(theirs);
    }

    /// The task check (follow-up F19.3): the run of frame `uid`, on task
    /// `task`, leaves the nodes `left` of component `ci`. For each
    /// `joined_at(T, n)` of a node `n` of them, each task of `T` that the
    /// run of the frame started must be done, and task `task` must know it
    /// (a join orders the end of the task before the code after `n`).
    fn check_joined(
        &self,
        uid: u64,
        ci: usize,
        left: &[NodeId],
        task: usize,
    ) -> Result<(), String> {
        let Some(comp) = self.comps.get(ci) else {
            return Ok(());
        };
        let run = self.activation.get(&uid).copied().unwrap_or(uid);
        let known = self.knows.get(&task);
        for &n in left {
            for &t in comp.joins.get(n.index()).into_iter().flatten() {
                let Some(rs) = self.instances.get(&(comp.unit, run, t)) else {
                    continue;
                };
                if let Some(&r) = rs.iter().find(|&&r| !known.is_some_and(|k| k.contains(&r))) {
                    return Err(format!(
                        "fact oracle (task end): in `{}`, the run leaves {} with `joined_at({t}, {n})`, and task {r} of `{t}` is not joined: it can still run",
                        comp.facts.name,
                        comp.node_text(n),
                    ));
                }
            }
        }
        Ok(())
    }

    /// One op of the frame `uid` of a scope body ([`LIGHT`]) on task `task`
    /// runs at the location `block`, `stmt`: the task check of the nodes
    /// that the run leaves. A location that no path of the facts reaches
    /// ends the following of the frame (trace conformance is for the
    /// frames of [`Self::step`]).
    ///
    /// # Errors
    ///
    /// The message of a failure of the task check.
    pub fn light_step(
        &mut self,
        uid: u64,
        block: u32,
        stmt: u32,
        task: usize,
    ) -> Result<(), String> {
        self.light_last = Some(uid);
        let Some(fr) = self.light.get(&uid) else {
            return Ok(());
        };
        let ci = fr.comp;
        let Some(comp) = self.comps.get(ci) else {
            return Ok(());
        };
        let n_stmts = self
            .input
            .built
            .program
            .bodies
            .get(comp.body.index())
            .and_then(|b| b.blocks.get(block as usize))
            .map_or(0, |b| u32_of(b.stmts.len()));
        let at = if stmt >= n_stmts { TERM } else { stmt };
        let to = (block, at);
        if fr.at == Some(to) {
            return Ok(());
        }
        let next = comp.reach(&fr.cur, fr.at, to);
        if next.is_empty() {
            self.light.remove(&uid);
            return Ok(());
        }
        let left = comp.left(&fr.cur, fr.at, to, &next);
        self.check_joined(uid, ci, &left, task)?;
        if let Some(fr) = self.light.get_mut(&uid) {
            fr.cur = next;
            fr.at = Some(to);
        }
        Ok(())
    }

    /// True if the oracle checks the frames of code `code` (IR body `code`).
    pub fn follows(&self, code: &Code) -> bool {
        code.locs
            .first()
            .is_some_and(|l| self.by_body.contains_key(&l.body))
    }

    /// A frame `uid` of `code` starts with the cells `slots` and the
    /// captured cells `caps`: its state, the targets of the references in
    /// its parameters, and the captured cells of a closure body. Capture `k`
    /// is the cell of `env.k` (`docs/ir.md` 5.1.7: a `Kept` capture shares
    /// the cell of the variable, a `ByMove` capture has a cell of its own,
    /// a `ByRef` capture holds a reference to the cell of the variable), and
    /// the targets of the references in it are `(*env.k)` and below.
    pub fn enter(
        &mut self,
        uid: u64,
        code: &Code,
        slots: &[Option<CellId>],
        caps: &[CellId],
        heap: &Heap,
    ) {
        let Some(&ci) = code.locs.first().and_then(|l| self.by_body.get(&l.body)) else {
            return;
        };
        self.report.frames += 1;
        let Some(comp) = self.comps.get(ci) else {
            return;
        };
        // A handled body and a scope body run in the run of their site: the
        // frame of the last op (follow-up F19.3).
        let site_run = matches!(
            self.input
                .built
                .program
                .bodies
                .get(comp.body.index())
                .map(|b| b.kind),
            Some(weft_ir::BodyKind::Handled(_) | weft_ir::BodyKind::Scope(_))
        );
        let prev = self.last.or(self.light_last).filter(|p| {
            self.frames
                .get(p)
                .or_else(|| self.light.get(p))
                .and_then(|f| self.comps.get(f.comp))
                .is_some_and(|c| c.unit == comp.unit)
        });
        let run = match prev {
            Some(p) if site_run => self.activation.get(&p).copied().unwrap_or(p),
            _ => uid,
        };
        self.activation.insert(uid, run);
        if comp.light {
            self.light.insert(
                uid,
                FrameFacts {
                    comp: ci,
                    cur: vec![comp.entry],
                    at: None,
                    anchors: Vec::new(),
                    retired: HashMap::new(),
                    site: None,
                },
            );
            return;
        }
        let body = self.input.built.program.bodies.get(comp.body.index());
        let mut anchors = Vec::new();
        if let Some(b) = body {
            for (i, &l) in b.params.iter().enumerate() {
                // The slot of the parameter: the environment of a closure
                // body has no slot.
                let Some(s) = code.slot_locals.iter().position(|&x| x == l.0) else {
                    continue;
                };
                let Some(Some(cell)) = slots.get(s) else {
                    continue;
                };
                let Ok(s) = heap.slot(*cell) else {
                    continue;
                };
                let mut found = Vec::new();
                param_targets(heap, &s.val, &mut Vec::new(), 0, &mut found);
                for (proj, place) in found {
                    anchors.push(Anchor {
                        place,
                        local: l,
                        param: Some(u32_of(i)),
                        proj,
                    });
                }
            }
            let env = b.params.first().copied().filter(|&l| {
                matches!(b.kind, weft_ir::BodyKind::Closure(_))
                    && b.local(l)
                        .is_some_and(|d| matches!(d.kind, weft_ir::LocalKind::Env))
            });
            if let Some(env) = env {
                for (k, &cell) in caps.iter().enumerate() {
                    let field = vec![Proj::Field(FieldIdx(u32_of(k)))];
                    anchors.push(Anchor {
                        place: Place::root(cell),
                        local: env,
                        param: None,
                        proj: field.clone(),
                    });
                    let Ok(s) = heap.slot(cell) else {
                        continue;
                    };
                    let mut found = Vec::new();
                    param_targets(heap, &s.val, &mut field.clone(), 0, &mut found);
                    for (proj, place) in found {
                        anchors.push(Anchor {
                            place,
                            local: env,
                            param: None,
                            proj,
                        });
                    }
                }
            }
        }
        // A clause frame: the frame of the last op runs the clause (plan
        // stage F14).
        let site = if comp.clause {
            let unit = comp.unit;
            self.last
                .and_then(|l| self.site_of(l))
                .filter(|(u, _)| *u == unit)
        } else {
            None
        };
        self.frames.insert(
            uid,
            FrameFacts {
                comp: ci,
                cur: vec![comp.entry],
                at: None,
                anchors,
                retired: HashMap::new(),
                site,
            },
        );
    }

    /// The state of frame `uid` with no anchors: the component and the
    /// nodes.
    fn cursor(&self, uid: u64) -> Option<FrameFacts> {
        self.frames.get(&uid).map(|f| FrameFacts {
            comp: f.comp,
            cur: f.cur.clone(),
            at: f.at,
            anchors: Vec::new(),
            retired: HashMap::new(),
            site: f.site.clone(),
        })
    }

    /// The component and the nodes of frame `uid` in the terms of the site
    /// of its handlers: the nodes of the frame, or for a clause frame the
    /// nodes that run the clause (`None` if the oracle does not know them).
    fn site_of(&self, uid: u64) -> Option<(usize, Vec<NodeId>)> {
        let f = self.frames.get(&uid)?;
        let c = self.comps.get(f.comp)?;
        if c.clause {
            f.site.clone()
        } else {
            Some((c.unit, c.group(&f.cur)))
        }
    }

    /// What a frame below frame `uid` that waits at a `handle` or at a
    /// `resume` checks with: the nodes `group` of frame `uid` (which may
    /// wait itself, and then has the nodes of the frame above it), or the
    /// nodes that run the clause of a clause frame.
    fn passed_down(&self, uid: u64, waits: bool, group: &[NodeId]) -> Option<(usize, Vec<NodeId>)> {
        let f = self.frames.get(&uid)?;
        let c = self.comps.get(f.comp)?;
        if waits || !c.clause {
            Some((c.unit, group.to_vec()))
        } else {
            f.site.clone()
        }
    }

    /// The temporary `l` of frame `uid` gets a new cell, and its old cell
    /// `c` stays (`LiveTemp` of a promoted temporary in a loop: the end of
    /// a cell of plain data keeps its value, `docs/ir.md` 5.10). The old
    /// cell keeps the name of the local.
    pub fn retire(&mut self, uid: u64, c: CellId, l: LocalId) {
        if let Some(fr) = self.frames.get_mut(&uid) {
            fr.retired.insert(c, l);
        }
    }

    /// An op of a frame that the oracle does not follow (a copied frame of
    /// a continuation, plan stage F16) runs. A clause that the op runs has
    /// no known site.
    pub const fn untracked_op(&mut self) {
        self.last = None;
        self.light_last = None;
    }

    /// The summary oracle (A3) checks the frames below the frame `uid` of
    /// an op: the frame of the op is the first frame above them.
    pub fn begin_summary(&mut self, uid: u64) {
        self.above = self.site_of(uid);
    }

    /// The summary oracle (A3) skips a frame below an op: the frame below it
    /// has no frame of its component above it.
    pub fn break_summary(&mut self) {
        self.above = None;
    }

    /// The frame `uid` ended.
    pub fn leave(&mut self, uid: u64) {
        self.frames.remove(&uid);
        self.light.remove(&uid);
        self.activation.remove(&uid);
        self.drop_wait(uid);
    }

    /// A4: the clause frame `uid` of task `task`, with the code `code` and
    /// the cells `slots`, starts to wait at its `resume`. The oracle records
    /// the references that its locals hold.
    pub fn wait_begin(
        &mut self,
        uid: u64,
        code: &Code,
        slots: &[Option<CellId>],
        heap: &Heap,
        task: usize,
    ) {
        self.drop_wait(uid);
        let Some(fr) = self.frames.get(&uid) else {
            return;
        };
        let Some(comp) = self.comps.get(fr.comp) else {
            return;
        };
        // The `Main` node of the `resume`: its `lends_mut` and `releases_at`
        // are the summary of the rest of the handled body.
        let nodes: Vec<NodeId> = comp
            .group(&fr.cur)
            .into_iter()
            .filter(|&n| comp.kind_of(n) == "resume" && comp.label_of(n) == "resume")
            .collect();
        if !comp.clause || nodes.is_empty() {
            return;
        }
        let mut refs = Vec::new();
        for (s, cell) in slots.iter().enumerate() {
            let (Some(cell), Some(&l)) = (cell, code.slot_locals.get(s)) else {
                continue;
            };
            let l = LocalId(l);
            if !comp.of_local.contains_key(&l) {
                continue;
            }
            let Ok(x) = heap.slot(*cell) else {
                continue;
            };
            let mut out = Vec::new();
            refs_of(heap, &x.val, &mut Vec::new(), &[], false, 0, &mut out);
            refs.extend(out.into_iter().map(|t| (t, l)));
        }
        if refs.is_empty() {
            return;
        }
        let w = Wait {
            comp: fr.comp,
            nodes,
            task,
            uid,
            refs,
            hits: Vec::new(),
            names: None,
        };
        self.add_wait(uid, w);
    }

    /// A5 (plan stage F17.2): a clause of the local handler of the handled
    /// body of frame `frames[0]` runs; `frames` are the code frames above
    /// the `handle`, the bottom first. The frames of the component of the
    /// handled body wait at their nodes; one such node must have
    /// `performs_at` with the capability of the handler. If none does and
    /// one has `escapes_at` of the effect of the handler, the facts send
    /// the effect past the function: a failure.
    ///
    /// # Errors
    ///
    /// The message of the failure.
    pub fn clause_run(&mut self, frames: &[u64], task: usize) -> Result<(), String> {
        let Some(fr) = frames
            .iter()
            .find(|u| tracked(**u))
            .and_then(|uid| self.frames.get(uid))
        else {
            return Ok(());
        };
        let Some(comp) = self.comps.get(fr.comp) else {
            return Ok(());
        };
        let unit = comp.unit;
        let Some(weft_ir::BodyKind::Handled(h)) = self
            .input
            .built
            .program
            .bodies
            .get(comp.body.index())
            .map(|b| b.kind)
        else {
            return Ok(());
        };
        let effect = self
            .input
            .built
            .program
            .handlers
            .get(h.index())
            .and_then(|d| comp.tys.effects().get(d.effect.index()))
            .map(|e| e.identity.clone())
            .unwrap_or_default();
        let cap = self.input.comps.as_ref().ok().and_then(|cs| {
            cs.get(unit).and_then(|c| {
                c.emitted
                    .handler_caps
                    .iter()
                    .find(|(x, _)| *x == h)
                    .map(|&(_, k)| k)
            })
        });
        // The frames of the component from the handled body up: a frame of
        // another component (a callee) ends them. A frame whose node sends
        // the effect past the function and does not run the clause is a
        // failure (the frame of a closure that runs a function with the
        // effect in its row, too).
        let mut escapes: Option<(NodeId, usize)> = None;
        let mut starts: Vec<(u64, usize, Vec<NodeId>)> = Vec::new();
        // The frames of the callees above the component (follow-up F19.5).
        let mut outer: Vec<(u64, usize)> = Vec::new();
        let mut beyond = false;
        for uid in frames {
            if beyond {
                if let Some(f) = self.frames.get(uid).or_else(|| self.light.get(uid)) {
                    outer.push((*uid, f.comp));
                }
                continue;
            }
            if !tracked(*uid) {
                // A frame of a scope body: the task start check only.
                if let Some(f) = self.light.get(uid) {
                    match self.comps.get(f.comp) {
                        Some(c) if c.unit == unit => {
                            let group = c.group(&f.cur);
                            let runs: Vec<NodeId> = group
                                .iter()
                                .copied()
                                .filter(|&n| {
                                    cap.is_some_and(|k| c.facts.performs_at.contains(&(n, k)))
                                })
                                .collect();
                            starts.push((*uid, f.comp, if runs.is_empty() { group } else { runs }));
                        }
                        Some(_) => outer.push((*uid, f.comp)),
                        None => {}
                    }
                }
                continue;
            }
            let Some(f) = self.frames.get(uid) else {
                break;
            };
            let Some(c) = self.comps.get(f.comp) else {
                break;
            };
            if c.unit != unit {
                beyond = true;
                outer.push((*uid, f.comp));
                continue;
            }
            let group = c.group(&f.cur);
            let runs: Vec<NodeId> = group
                .iter()
                .copied()
                .filter(|&n| cap.is_some_and(|k| c.facts.performs_at.contains(&(n, k))))
                .collect();
            if !runs.is_empty() {
                starts.push((*uid, f.comp, runs));
                continue;
            }
            // A frame that does not run the clause (a closure that performs
            // through a capability that it captures) names the code of the
            // clause at its own nodes.
            starts.push((*uid, f.comp, group.clone()));
            if let Some(&n) = group.iter().find(|&&n| {
                c.facts
                    .escapes_at
                    .iter()
                    .any(|(m, e)| *m == n && *e == effect)
            }) {
                escapes = Some((n, f.comp));
                break;
            }
        }
        self.report.clause += 1;
        self.check_started(&starts, task, h)?;
        self.check_waits(&starts, &outer, task, h)?;
        let Some((n, ci)) = escapes else {
            return Ok(());
        };
        let (text, fname) = self
            .comps
            .get(ci)
            .map(|c| (c.node_text(n), c.facts.name.clone()))
            .unwrap_or_default();
        Err(format!(
            "clause oracle (A5): in `{fname}` at {text}, a clause of the local handler of `{effect}` runs from the node, and the node has `escapes_at` of `{effect}` and no `performs_at` with the capability of the handler"
        ))
    }

    /// A4 of copies (plan stage F17.1): a `multi` operation of task `task`
    /// takes the frames `frames` (the bottom first) into its continuation;
    /// a later `resume` runs copies of them again. For each frame `g` that
    /// the frame `f` below it runs (a callee or a closure; `f` waits at its
    /// run node), the oracle records the references that the locals of `g`
    /// hold, named in the terms of `f`. When a copy of `g` goes on, each
    /// such reference whose target the code in between reached must be used
    /// at the `Copy` node of the run node of `f` (a use of a variable with
    /// a `points_into` place that overlaps it).
    pub fn multi_frames(
        &mut self,
        frames: &[(u64, &Code, &[Option<CellId>])],
        site: Option<(u64, &Code, &[Option<CellId>])>,
        heap: &Heap,
        task: usize,
    ) {
        for pair in frames.windows(2) {
            let (Some(&(fu, fcode, fslots)), Some(&(gu, gcode, gslots))) =
                (pair.first(), pair.get(1))
            else {
                continue;
            };
            if fu == 0 || gu == 0 || self.waits.contains_key(&gu) {
                continue;
            }
            let (Some(f), Some(g)) = (self.frames.get(&fu), self.frames.get(&gu)) else {
                continue;
            };
            let (fc, gc) = (f.comp, g.comp);
            let Some(comp) = self.comps.get(fc) else {
                continue;
            };
            let group = comp.group(&f.cur);
            let nodes: Vec<NodeId> = (0..comp.succ.len())
                .filter(|&m| {
                    comp.facts
                        .nodes
                        .get(m)
                        .is_some_and(|x| x.kind.ends_with(" copy"))
                        && comp
                            .succ
                            .get(m)
                            .is_some_and(|ss| ss.iter().any(|y| group.contains(y)))
                })
                .map(|m| NodeId(u32_of(m)))
                .collect();
            if nodes.is_empty() {
                continue;
            }
            let Some(gcomp) = self.comps.get(gc) else {
                continue;
            };
            let mut refs = Vec::new();
            for (s, cell) in gslots.iter().enumerate() {
                let (Some(cell), Some(&l)) = (cell, gcode.slot_locals.get(s)) else {
                    continue;
                };
                let l = LocalId(l);
                if !gcomp.of_local.contains_key(&l) {
                    continue;
                }
                let Ok(x) = heap.slot(*cell) else {
                    continue;
                };
                let mut out = Vec::new();
                refs_of(heap, &x.val, &mut Vec::new(), &[], false, 0, &mut out);
                refs.extend(out.into_iter().map(|t| (t, l)));
            }
            if refs.is_empty() {
                continue;
            }
            // A handled body names the locals of its site as upvars: the
            // frame of the site (below the continuation, in the same facts)
            // names them.
            let unit = comp.unit;
            let site = site.filter(|(su, _, _)| {
                self.frames
                    .get(su)
                    .and_then(|x| self.comps.get(x.comp))
                    .is_some_and(|c| c.unit == unit)
            });
            let mut names: Vec<Vec<PlaceId>> = Vec::new();
            for (t, _) in &refs {
                if let Some((ns, _)) = self.name(fu, fcode, fslots, heap, t) {
                    names.push(ns);
                    continue;
                }
                // The facts of the site frame are another copy of the facts
                // of the unit: a place maps by its text.
                let Some((su, sc, ss)) = site else {
                    names.push(Vec::new());
                    continue;
                };
                let found = self
                    .name(su, sc, ss, heap, t)
                    .map(|(ns, _)| ns)
                    .unwrap_or_default();
                let (Some(sf), Some(ff)) = (
                    self.frames.get(&su).and_then(|x| self.comps.get(x.comp)),
                    self.comps.get(fc),
                ) else {
                    names.push(Vec::new());
                    continue;
                };
                // A place that the facts of the frame do not have maps to
                // its nearest parent that they have (a change of the parent
                // covers it).
                let mut out: Vec<PlaceId> = Vec::new();
                for &q in &found {
                    let mut at = Some(q);
                    while let Some(x) = at {
                        let text = &sf.facts.place(x).display;
                        let hit: Vec<PlaceId> = (0..ff.facts.places.len())
                            .map(|i| PlaceId(u32_of(i)))
                            .filter(|&y| &ff.facts.place(y).display == text)
                            .collect();
                        if !hit.is_empty() {
                            out.extend(hit);
                            break;
                        }
                        at = sf.facts.place(x).parent;
                    }
                }
                names.push(out);
            }
            let w = Wait {
                comp: fc,
                nodes,
                task,
                uid: gu,
                refs,
                hits: Vec::new(),
                names: Some(names),
            };
            self.add_wait(gu, w);
        }
    }

    /// Records wait `w` with key `key`.
    fn add_wait(&mut self, key: u64, w: Wait) {
        for (i, (t, _)) in w.refs.iter().enumerate() {
            self.wait_cells.entry(t.cell()).or_default().push((key, i));
        }
        self.waits.insert(key, w);
    }

    /// Removes the wait with key `key`, if there is one.
    fn drop_wait(&mut self, key: u64) -> Option<Wait> {
        let w = self.waits.remove(&key)?;
        for (t, _) in &w.refs {
            if let Some(v) = self.wait_cells.get_mut(&t.cell()) {
                v.retain(|(k, _)| *k != key);
                if v.is_empty() {
                    self.wait_cells.remove(&t.cell());
                }
            }
        }
        Some(w)
    }

    /// A4: the op of frame `uid` (0 for a copied frame) of task `task` made
    /// the accesses `events`. An access that reaches the target of a
    /// reference of a waiting clause frame of the task (not the frame of the
    /// op) is a hit of that wait.
    pub fn wait_events(&mut self, task: usize, uid: u64, events: &[HeapEvent]) {
        if self.waits.is_empty() {
            return;
        }
        for e in events {
            let (cell, path, what) = match e {
                HeapEvent::Write(p, false) => (p.cell, Some(p.path.as_slice()), "a write"),
                HeapEvent::Take(p) => (p.cell, Some(p.path.as_slice()), "a move"),
                HeapEvent::Free(c) => (*c, None, "a free"),
                _ => continue,
            };
            let Some(ws) = self.wait_cells.get(&cell) else {
                continue;
            };
            for &(key, i) in ws {
                let Some(w) = self.waits.get_mut(&key) else {
                    continue;
                };
                if w.task != task || (uid != 0 && w.uid == uid) {
                    continue;
                }
                // A copy of a frame (A4 of copies): a write at or below the
                // target keeps the reference valid; a write strictly above
                // it, a move at or above it, and a free end it.
                let reached = w.refs.get(i).is_some_and(|(t, _)| {
                    if w.names.is_none() {
                        return t.reached_by(path);
                    }
                    match (t, path, what) {
                        (_, None, _) => true,
                        (Target::Elems(_), Some(p), _) => p.is_empty(),
                        (Target::Place(tp), Some(p), "a move") => tp.path.starts_with(p),
                        (Target::Place(tp), Some(p), _) => {
                            tp.path.len() > p.len() && tp.path.starts_with(p)
                        }
                    }
                });
                if reached && !w.hits.iter().any(|(j, _)| *j == i) {
                    w.hits.push((i, what));
                }
            }
        }
    }

    /// A4: the frame with wait key `key` (a frame, or a copy of a frame)
    /// continues after its `resume`. Each reference of the frame whose
    /// target the code above reached is inside a place that the `Resume`
    /// node lends or frees: a `lends_mut`, a `mutates_at` or a free of a
    /// place that overlaps a `points_into` place of a variable of its
    /// local.
    ///
    /// # Errors
    ///
    /// The message of a failure.
    pub fn wait_end(&mut self, key: u64) -> Result<(), String> {
        let Some(w) = self.drop_wait(key) else {
            return Ok(());
        };
        let Some(comp) = self.comps.get(w.comp) else {
            return Ok(());
        };
        if let Some(names) = &w.names {
            let used: Vec<PlaceId> = w
                .nodes
                .iter()
                .flat_map(|n| comp.uses.get(n.index()).cloned().unwrap_or_default())
                .flat_map(|v| comp.points.get(&v).cloned().unwrap_or_default())
                .collect();
            for &(i, what) in &w.hits {
                let ns = names.get(i).cloned().unwrap_or_default();
                if ns.is_empty() {
                    self.report.resume_unnamed += 1;
                    continue;
                }
                self.report.resume += 1;
                let ok = ns
                    .iter()
                    .any(|&q| used.iter().any(|&m| comp.below(q, m) || comp.below(m, q)));
                if !ok {
                    let shown: Vec<String> = ns
                        .iter()
                        .map(|&q| comp.facts.place(q).display.clone())
                        .collect();
                    let nodes: Vec<String> = w.nodes.iter().map(|&n| comp.node_text(n)).collect();
                    return Err(format!(
                        "summary oracle (A4): in `{}` at {}, a copy of a frame that the run node runs goes on after a `multi` `resume`, and the code before made {what} of `{}`, which a reference of the copy points into; the `Copy` node uses no variable that points there",
                        comp.facts.name,
                        nodes.join(", "),
                        shown.join("` or `"),
                    ));
                }
            }
            return Ok(());
        }
        let cover: Vec<PlaceId> = w
            .nodes
            .iter()
            .flat_map(|n| {
                let i = n.index();
                let c = comp.changes.get(i).map_or(&[][..], Vec::as_slice);
                let f = comp.frees.get(i).map_or(&[][..], Vec::as_slice);
                c.iter().chain(f).copied()
            })
            .collect();
        for &(i, what) in &w.hits {
            let Some((_, l)) = w.refs.get(i) else {
                continue;
            };
            let vars = comp.of_local.get(l).cloned().unwrap_or_default();
            let mut points: Vec<PlaceId> = vars
                .iter()
                .flat_map(|v| comp.points.get(v).cloned().unwrap_or_default())
                .collect();
            points.sort();
            points.dedup();
            if points.is_empty() {
                self.report.resume_unnamed += 1;
                continue;
            }
            self.report.resume += 1;
            let ok = points
                .iter()
                .any(|&q| cover.iter().any(|&m| comp.below(q, m) || comp.below(m, q)));
            if !ok {
                let name = comp
                    .s_of
                    .get(l)
                    .map_or_else(|| format!("{l:?}"), |v| var_name(&comp.facts, *v));
                let shown: Vec<String> = points
                    .iter()
                    .map(|&q| comp.facts.place(q).display.clone())
                    .collect();
                let nodes: Vec<String> = w.nodes.iter().map(|&n| comp.node_text(n)).collect();
                return Err(format!(
                    "summary oracle (A4): in `{}` at {}, the clause waits at its `resume`, and the rest of the handled body makes {what} of the target of `{name}` (in `{}`); the `resume` node has no `lends_mut` or `releases_at` that covers it",
                    comp.facts.name,
                    nodes.join(", "),
                    shown.join("`, `"),
                ));
            }
        }
        Ok(())
    }

    /// A4: the frame with wait key `key` goes into a copy of a `multi`
    /// continuation, and `map` gives the new cell of each copied cell. The
    /// copy waits too, with the hits of the frame so far. Returns the key of
    /// the copy, or 0 if the frame does not wait.
    pub fn copy_wait(&mut self, key: u64, map: &std::collections::BTreeMap<CellId, CellId>) -> u64 {
        let Some(w) = self.waits.get(&key) else {
            return 0;
        };
        let mut c = w.clone();
        c.uid = 0;
        for (t, _) in &mut c.refs {
            match t {
                Target::Place(p) => {
                    if let Some(&n) = map.get(&p.cell) {
                        p.cell = n;
                    }
                }
                Target::Elems(b) => {
                    if let Some(&n) = map.get(b) {
                        *b = n;
                    }
                }
            }
        }
        self.copy_keys += 1;
        let k = self.copy_keys;
        self.add_wait(k, c);
        k
    }

    /// The next op of frame `uid` is at location (`block`, `stmt`) of a body
    /// with `n_stmts` statements in the block. Returns the nodes of the
    /// location when the location changed, or a failure of trace
    /// conformance.
    ///
    /// # Errors
    ///
    /// The message of a failure.
    pub fn step(&mut self, uid: u64, block: u32, stmt: u32, task: usize) -> Result<bool, String> {
        let Some(fr) = self.frames.get_mut(&uid) else {
            return Ok(false);
        };
        self.last = Some(uid);
        self.light_last = None;
        // A clause frame that leaves a `resume`: the handled body ended, and
        // the code after the `resume` runs at `Post` of the `handle` (plan
        // stage F14).
        if let Some(comp) = self.comps.get(fr.comp) {
            if comp.clause && comp.waits(&fr.cur) {
                fr.site = Some((comp.unit, comp.post.clone()));
            }
        }
        let Some(comp) = self.comps.get(fr.comp) else {
            return Ok(false);
        };
        let n_stmts = self
            .input
            .built
            .program
            .bodies
            .get(comp.body.index())
            .and_then(|b| b.blocks.get(block as usize))
            .map_or(0, |b| u32_of(b.stmts.len()));
        let at = if stmt >= n_stmts { TERM } else { stmt };
        let to = (block, at);
        if fr.at == Some(to) {
            return Ok(false);
        }
        self.report.steps += 1;
        let next = comp.reach(&fr.cur, fr.at, to);
        if next.is_empty() {
            let from: Vec<String> = fr.cur.iter().map(|&n| comp.node_text(n)).collect();
            let want: Vec<String> = comp
                .at_loc
                .get(&to)
                .map(|ns| ns.iter().map(|&n| comp.node_text(n)).collect())
                .unwrap_or_default();
            return Err(format!(
                "trace conformance: in `{}`, the run goes from {} to bb{block} {} ({}), and no `cfg_edge` path of the facts goes there",
                comp.facts.name,
                from.join(", "),
                if at == TERM { "terminator".to_string() } else { format!("statement {at}") },
                if want.is_empty() { "no node".to_string() } else { want.join(", ") },
            ));
        }
        let left = comp.left(&fr.cur, fr.at, to, &next);
        let ci = fr.comp;
        fr.cur = next;
        fr.at = Some(to);
        self.check_joined(uid, ci, &left, task)?;
        Ok(true)
    }

    /// C1 at the entry of the current nodes of frame `uid`, whose slots are
    /// `slots` and whose code is `code`.
    ///
    /// # Errors
    ///
    /// The message of a failure.
    pub fn check_uses(
        &mut self,
        uid: u64,
        code: &Code,
        slots: &[Option<CellId>],
        heap: &Heap,
    ) -> Result<(), String> {
        let Some(fr) = self.cursor(uid) else {
            return Ok(());
        };
        let Some(comp) = self.comps.get(fr.comp) else {
            return Ok(());
        };
        let group = comp.group(&fr.cur);
        let mut used: Vec<VarId> = Vec::new();
        for n in &group {
            used.extend(comp.uses.get(n.index()).map_or(&[][..], Vec::as_slice));
        }
        used.sort();
        used.dedup();
        // The references of each used local and part, with the variables
        // whose places cover them.
        let mut todo: Vec<(String, Vec<VarId>, Vec<Target>)> = Vec::new();
        let mut parts_done: HashSet<usize> = HashSet::new();
        for &v in &used {
            match comp.roles.get(&v) {
                Some(VarRole::Local(l)) => {
                    if !holds_refs(&self.input.built, comp.body, *l) {
                        continue;
                    }
                    let Some(val) = local_value(code, slots, heap, *l) else {
                        continue;
                    };
                    let skip: Vec<Vec<weft_sema::analysis::PathStep>> = comp
                        .parts
                        .iter()
                        .filter(|p| p.key.1 == *l)
                        .map(|p| p.steps.clone())
                        .collect();
                    let mut refs = Vec::new();
                    refs_of(heap, val, &mut Vec::new(), &skip, true, 0, &mut refs);
                    if !refs.is_empty() {
                        todo.push((var_name(&comp.facts, v), vec![v], refs));
                    }
                }
                Some(VarRole::Part(i)) => {
                    if !parts_done.insert(*i) {
                        continue;
                    }
                    let Some(p) = comp.parts.get(*i) else {
                        continue;
                    };
                    let Some(val) = local_value(code, slots, heap, p.key.1) else {
                        continue;
                    };
                    let Some(val) = part_value(val, &p.steps) else {
                        continue;
                    };
                    let mut refs = Vec::new();
                    refs_of(heap, val, &mut Vec::new(), &p.deeper, true, 0, &mut refs);
                    let vars: Vec<VarId> = p
                        .vars
                        .iter()
                        .copied()
                        .filter(|x| used.contains(x))
                        .collect();
                    if !refs.is_empty() {
                        todo.push((var_name(&comp.facts, v), vars, refs));
                    }
                }
                None => {}
            }
        }
        for (name, vars, refs) in todo {
            for t in refs {
                self.report.checks += 1;
                let Some((names, _)) = self.name(uid, code, slots, heap, &t) else {
                    self.report.unnamed += 1;
                    continue;
                };
                let Some(comp) = self.comps.get(fr.comp) else {
                    return Ok(());
                };
                let ok = names.iter().any(|&q| {
                    vars.iter().any(|v| {
                        comp.points
                            .get(v)
                            .is_some_and(|ps| ps.iter().any(|&d| comp.ref_inside(q, d)))
                    })
                });
                if !ok {
                    let shown: Vec<String> = names
                        .iter()
                        .map(|&q| comp.facts.place(q).display.clone())
                        .collect();
                    let have: Vec<String> = vars
                        .iter()
                        .flat_map(|v| comp.points.get(v).cloned().unwrap_or_default())
                        .map(|d| comp.facts.place(d).display.clone())
                        .collect();
                    let nodes: Vec<String> = group.iter().map(|&n| comp.node_text(n)).collect();
                    return Err(format!(
                        "fact oracle (C1): in `{}` at {}, `{name}` holds a reference to `{}`, and no `points_into` place of the variable covers it (it has {})",
                        comp.facts.name,
                        nodes.join(", "),
                        shown.join("` or `"),
                        if have.is_empty() { "none".to_string() } else { format!("`{}`", have.join("`, `")) },
                    ));
                }
            }
        }
        Ok(())
    }

    /// C4: the op of frame `uid` ends the cell of local `l`.
    ///
    /// # Errors
    ///
    /// The message of a failure.
    pub fn check_end(&mut self, uid: u64, l: LocalId) -> Result<(), String> {
        let Some(fr) = self.frames.get(&uid) else {
            return Ok(());
        };
        let Some(comp) = self.comps.get(fr.comp) else {
            return Ok(());
        };
        let Some(&root) = comp.local_roots.get(&l) else {
            return Ok(());
        };
        self.report.checks += 1;
        let group = comp.group(&fr.cur);
        let ok = group.iter().any(|n| {
            comp.frees
                .get(n.index())
                .is_some_and(|ms| ms.iter().any(|&m| comp.below(root, m)))
        });
        if ok {
            return Ok(());
        }
        let nodes: Vec<String> = group.iter().map(|&n| comp.node_text(n)).collect();
        Err(format!(
            "fact oracle (C4): in `{}` at {}, the cell of `{}` ends, and no `frees_at` of the node covers it",
            comp.facts.name,
            nodes.join(", "),
            comp.facts.place(root).display,
        ))
    }

    /// D4: an abort unwinds frame `uid`. If `live`, the frame holds a live
    /// linear value, and a node of the frame has `may_abort`.
    ///
    /// A frame that waits at a `handle` or at a `resume` checks with the
    /// nodes of the frame that unwound before it, if that frame is of the
    /// same component: the abort comes from a node of the handled body or
    /// of a clause, whose nodes are in the facts of this frame (plan stage
    /// F14). Else the check is not made (`abort_skipped`).
    ///
    /// # Errors
    ///
    /// The message of a failure.
    pub fn check_abort(&mut self, uid: u64, live: bool) -> Result<(), String> {
        let Some((ci, own)) = self
            .frames
            .get(&uid)
            .and_then(|fr| Some((fr.comp, self.comps.get(fr.comp)?.group(&fr.cur))))
        else {
            self.unwound = None;
            return Ok(());
        };
        let Some(comp) = self.comps.get(ci) else {
            self.unwound = None;
            return Ok(());
        };
        let waits = comp.waits(&own);
        let group = if waits {
            match &self.unwound {
                Some((u, g)) if *u == comp.unit => g.clone(),
                _ => {
                    if live {
                        self.report.abort_skipped += 1;
                    }
                    self.unwound = None;
                    return Ok(());
                }
            }
        } else {
            own
        };
        let down = self.passed_down(uid, waits, &group);
        self.unwound = down;
        if !live {
            return Ok(());
        }
        let Some(comp) = self.comps.get(ci) else {
            return Ok(());
        };
        self.report.checks += 1;
        if group
            .iter()
            .any(|n| comp.may_abort.get(n.index()).copied().unwrap_or(false))
        {
            return Ok(());
        }
        let nodes: Vec<String> = group.iter().map(|&n| comp.node_text(n)).collect();
        Err(format!(
            "fact oracle (D4): in `{}` at {}, an abort unwinds the frame with a live linear value, and the node has no `may_abort`",
            comp.facts.name,
            nodes.join(", "),
        ))
    }

    /// C5 and D1: the accesses `events` of an op of frame `uid`. `moves` is
    /// false for an op whose take is not a move of the program (a drop, a
    /// native function): the take is a write.
    ///
    /// # Errors
    ///
    /// The message of a failure.
    pub fn check_events(
        &mut self,
        uid: u64,
        code: &Code,
        slots: &[Option<CellId>],
        heap: &Heap,
        events: &[HeapEvent],
        moves: bool,
    ) -> Result<(), String> {
        let Some(fr) = self.cursor(uid) else {
            return Ok(());
        };
        let group = match self.comps.get(fr.comp) {
            Some(c) => c.group(&fr.cur),
            None => return Ok(()),
        };
        // The captured cell of each capture of a frame of a closure body.
        let cap_cells: Vec<(CellId, u32)> = self
            .frames
            .get(&uid)
            .map(|f| {
                f.anchors
                    .iter()
                    .filter(|a| a.param.is_none() && a.place.path.is_empty())
                    .filter_map(|a| match a.proj.as_slice() {
                        [Proj::Field(k)] => Some((a.place.cell, k.0)),
                        _ => None,
                    })
                    .collect()
            })
            .unwrap_or_default();
        for e in events {
            let (place, kind) = match e {
                HeapEvent::Read(p) => (p, "read"),
                HeapEvent::Write(_, true) | HeapEvent::Free(_) => continue,
                HeapEvent::Write(p, false) => (p, "write"),
                HeapEvent::Take(p) => (p, if moves { "move" } else { "write" }),
                HeapEvent::Deref(p) => {
                    self.check_holder(uid, code, slots, heap, &group, p)?;
                    continue;
                }
            };
            // A cell that the op freed (the old buffer of a `Vec` that the
            // memory oracle moves): the write of its owner is the change.
            if heap
                .slot(place.cell)
                .is_ok_and(|x| x.kind == crate::heap::SlotKind::Free)
            {
                continue;
            }
            // A whole write of a local that is not a local of the program (a
            // temporary, `_0`) rebinds its variable: the facts give no
            // `mutates_at` (`docs/ir.md` 6.4, `Assign`). No reference
            // points into such a value when it gets a new one.
            if let (HeapEvent::Write(p, _), Some(comp)) = (e, self.comps.get(fr.comp)) {
                let whole = p.path.is_empty();
                let source = cell_local(code, slots, p.cell).is_some_and(|l| {
                    self.input
                        .built
                        .program
                        .bodies
                        .get(comp.body.index())
                        .and_then(|b| b.locals.get(l.index()))
                        .is_some_and(|d| {
                            matches!(
                                d.kind,
                                weft_ir::LocalKind::User | weft_ir::LocalKind::Param(_)
                            )
                        })
                });
                if whole && cell_local(code, slots, p.cell).is_some() && !source {
                    continue;
                }
            }
            // `Return` gives the value of `_0` to the frame of the caller:
            // the read is the end of the frame value, which no place of
            // the facts can name (`docs/ir.md` 6.9).
            if let (Some(comp), Some((b, TERM))) = (self.comps.get(fr.comp), fr.at) {
                if comp.returns.contains(&b)
                    && cell_local(code, slots, place.cell) == Some(comp.ret)
                {
                    continue;
                }
            }
            self.report.checks += 1;
            let Some((names, ty)) =
                self.name(uid, code, slots, heap, &Target::Place(place.clone()))
            else {
                self.report.unnamed += 1;
                continue;
            };
            // An array is in place: the machine keeps its elements in a
            // buffer cell, and the read of the handle of that buffer reads
            // no place of the facts.
            if kind == "read" && self.is_array(fr.comp, ty) {
                continue;
            }
            // A move of plain data is a copy: the facts give no `moved_at`
            // (`docs/ir.md` 6.4, operands).
            if kind == "move" && !self.not_copy(fr.comp, ty) {
                continue;
            }
            let Some(comp) = self.comps.get(fr.comp) else {
                return Ok(());
            };
            let at = |rel: &Vec<Vec<PlaceId>>| -> Vec<PlaceId> {
                group
                    .iter()
                    .flat_map(|n| rel.get(n.index()).cloned().unwrap_or_default())
                    .collect()
            };
            let ok = match kind {
                "read" => {
                    let rs = at(&comp.reads);
                    names
                        .iter()
                        .any(|&q| rs.iter().any(|&m| comp.below(q, m) || comp.below(m, q)))
                }
                "write" => {
                    let cs = at(&comp.changes);
                    names.iter().any(|&q| cs.iter().any(|&m| comp.below(q, m)))
                }
                _ => {
                    // A move of a whole `ByMove` capture moves its `E`
                    // variable.
                    let cap = cap_cells
                        .iter()
                        .find(|(c, _)| *c == place.cell && place.path.is_empty())
                        .and_then(|(_, k)| comp.e_of.get(k));
                    let cap_moved = cap.is_some_and(|v| {
                        group
                            .iter()
                            .any(|n| comp.moved.get(n.index()).is_some_and(|vs| vs.contains(v)))
                    });
                    let whole =
                        cap_moved || names.iter().any(|&q| comp.facts.place(q).steps.is_empty());
                    let local = cell_local(code, slots, place.cell);
                    let var_moved = local.and_then(|l| comp.s_of.get(&l)).is_some_and(|v| {
                        group
                            .iter()
                            .any(|n| comp.moved.get(n.index()).is_some_and(|vs| vs.contains(v)))
                    });
                    let part_ok = whole || {
                        let ms = at(&comp.moved_part);
                        names
                            .iter()
                            .any(|&q| ms.iter().any(|&m| comp.below(q, m) || comp.below(m, q)))
                    };
                    // A move out of a place that no local owns (a cell of
                    // a `Box`) has its part only.
                    (var_moved || local.is_none()) && part_ok
                }
            };
            if !ok {
                let shown: Vec<String> = names
                    .iter()
                    .map(|&q| comp.facts.place(q).display.clone())
                    .collect();
                let nodes: Vec<String> = group.iter().map(|&n| comp.node_text(n)).collect();
                let (code_id, rel) = match kind {
                    "read" => ("C5", "`reads_at`"),
                    "write" => ("C5", "`mutates_at` or `lends_mut`"),
                    _ => ("D1", "`moved_at` (and `moved_part`)"),
                };
                return Err(format!(
                    "fact oracle ({code_id}): in `{}` at {}, the run makes a {kind} of `{}`, and the node has no {rel} that covers it",
                    comp.facts.name,
                    nodes.join(", "),
                    shown.join("` or `"),
                ));
            }
        }
        Ok(())
    }

    /// A3 (summary cover): the accesses `events` of an op of a callee of
    /// frame `uid`, which waits at a run node, whose slots are `slots` and
    /// whose code is `code`. Each change and each read of a place that the
    /// frame can name is in the facts of its run node.
    ///
    /// # Errors
    ///
    /// The message of a failure.
    pub fn check_summary(
        &mut self,
        uid: u64,
        code: &Code,
        slots: &[Option<CellId>],
        heap: &Heap,
        events: &[HeapEvent],
    ) -> Result<(), String> {
        let Some(fr) = self.cursor(uid) else {
            self.above = None;
            return Ok(());
        };
        let (unit, mut group) = match self.comps.get(fr.comp) {
            Some(c) => (c.unit, c.group(&fr.cur)),
            None => return Ok(()),
        };
        // A frame that waits at a `handle`: the frame above it is its handled
        // body or a clause of the handler. A clause frame that waits at a
        // `resume`: the frame above it is the rest of the handled body. The
        // nodes of that frame are in the facts of this frame (plan stage
        // F14). It checks with their nodes.
        let waits = self.comps.get(fr.comp).is_some_and(|c| c.waits(&group));
        if waits {
            match &self.above {
                Some((u, g)) if *u == unit => group.clone_from(g),
                _ => {
                    self.report.summary_skipped += 1;
                    self.above = None;
                    return Ok(());
                }
            }
        }
        self.above = self.passed_down(uid, waits, &group);
        for e in events {
            let (place, kind) = match e {
                HeapEvent::Read(p) => (p, "read"),
                HeapEvent::Write(_, true) | HeapEvent::Deref(_) | HeapEvent::Free(_) => continue,
                HeapEvent::Write(p, false) | HeapEvent::Take(p) => (p, "write"),
            };
            // A cell that the op freed: the write of its owner is the
            // change.
            if heap
                .slot(place.cell)
                .is_ok_and(|x| x.kind == crate::heap::SlotKind::Free)
            {
                continue;
            }
            let Some((names, ty)) =
                self.name(uid, code, slots, heap, &Target::Place(place.clone()))
            else {
                self.report.summary_unnamed += 1;
                continue;
            };
            if kind == "read" && self.is_array(fr.comp, ty) {
                continue;
            }
            let Some(comp) = self.comps.get(fr.comp) else {
                return Ok(());
            };
            // A clause frame that waits at a `resume` checks with the nodes
            // of the frame above it, in the terms of the site. A place below
            // a parameter of the clause is in the terms of the clause: the
            // facts map it at the node that runs the clause, with the
            // places of the arguments (plan stages F14, F15), and the oracle
            // does not know them there. Such a name does not count.
            let names: Vec<PlaceId> = if waits && comp.clause {
                names.into_iter().filter(|&q| !comp.in_params(q)).collect()
            } else {
                names
            };
            if names.is_empty() {
                self.report.summary_unnamed += 1;
                continue;
            }
            self.report.summary += 1;
            let at = |rel: &Vec<Vec<PlaceId>>| -> Vec<PlaceId> {
                group
                    .iter()
                    .flat_map(|n| rel.get(n.index()).cloned().unwrap_or_default())
                    .collect()
            };
            let ok = if kind == "read" {
                let rs = at(&comp.reads);
                names
                    .iter()
                    .any(|&q| rs.iter().any(|&m| comp.below(q, m) || comp.below(m, q)))
            } else {
                let cs = at(&comp.changes);
                // The run node moved the value of the local into the callee
                // (a frame that waits at a `handle` keeps the cell of a
                // local that its handled body moved, plan stage F14): the
                // callee owns the value.
                let moved = cell_local(code, slots, place.cell)
                    .and_then(|l| comp.s_of.get(&l))
                    .is_some_and(|v| {
                        group
                            .iter()
                            .any(|n| comp.moved.get(n.index()).is_some_and(|vs| vs.contains(v)))
                    });
                moved || names.iter().any(|&q| cs.iter().any(|&m| comp.below(q, m)))
            };
            if !ok {
                let shown: Vec<String> = names
                    .iter()
                    .map(|&q| comp.facts.place(q).display.clone())
                    .collect();
                let nodes: Vec<String> = group.iter().map(|&n| comp.node_text(n)).collect();
                let rel = if kind == "read" {
                    "`reads_at`"
                } else {
                    "`mutates_at` or `lends_mut`"
                };
                return Err(format!(
                    "summary oracle (A3): in `{}` at {}, a callee makes a {kind} of `{}`, and the run node has no {rel} that covers it",
                    comp.facts.name,
                    nodes.join(", "),
                    shown.join("` or `"),
                ));
            }
        }
        for e in events {
            if let HeapEvent::Write(place, _) = e {
                self.check_put(uid, code, slots, heap, place)?;
            }
        }
        Ok(())
    }

    /// A3 for the parts `puts` and `put_fns`: a callee writes a value with
    /// references (or a closure with references in its environment) into
    /// `place` of the frame `uid`, which waits at a run node. Each reference
    /// that the frame can name is inside a `points_into` place of a variable
    /// that holds `place`: a variable of the local that owns it, or a
    /// version of the heap slot that overlaps it.
    ///
    /// # Errors
    ///
    /// The message of a failure.
    fn check_put(
        &mut self,
        uid: u64,
        code: &Code,
        slots: &[Option<CellId>],
        heap: &Heap,
        place: &Place,
    ) -> Result<(), String> {
        let Some(fr) = self.frames.get(&uid) else {
            return Ok(());
        };
        let comp_ix = fr.comp;
        let cur = fr.cur.clone();
        let Ok(v) = heap.peek(place) else {
            return Ok(());
        };
        let mut targets = Vec::new();
        let mut cells = 0;
        put_targets(heap, v, 0, &mut targets, &mut cells);
        self.report.summary_unnamed += cells;
        if targets.is_empty() {
            return Ok(());
        }
        let Some((dest, _)) = self.name(uid, code, slots, heap, &Target::Place(place.clone()))
        else {
            self.report.summary_unnamed += 1;
            return Ok(());
        };
        let Some(comp) = self.comps.get(comp_ix) else {
            return Ok(());
        };
        // The variables that hold the place.
        let mut vars: Vec<VarId> = Vec::new();
        let mut other = false;
        for &q in &dest {
            match comp.roots.path_of(&comp.facts, q) {
                Some((k, _)) if k.0 == comp.body => {
                    vars.extend(comp.of_local.get(&k.1).into_iter().flatten().copied());
                }
                Some(_) => other = true,
                None => {
                    for (key, vs) in &comp.slots {
                        if comp.below(q, *key) || comp.below(*key, q) {
                            vars.extend(vs.iter().copied());
                        }
                    }
                }
            }
        }
        if vars.is_empty() {
            // A place of another body of the component (a variable of the
            // maker of a closure), or a place with no holder: not checked.
            if other || !dest.is_empty() {
                self.report.summary_unnamed += 1;
            }
            return Ok(());
        }
        for t in targets {
            let Some((names, _)) = self.name(uid, code, slots, heap, &t) else {
                self.report.summary_unnamed += 1;
                continue;
            };
            self.report.summary += 1;
            let Some(comp) = self.comps.get(comp_ix) else {
                return Ok(());
            };
            // A closure that captures a local by reference points into the
            // cell root of the local in the facts (`docs/ir.md` 6.5): the run
            // gives the place of the local.
            let cell_of = |q: PlaceId| -> Option<weft_facts::RootId> {
                let root = comp.facts.places.get(q.index())?.root;
                comp.roots.cell_roots().find_map(|(k, c)| {
                    let local = comp.local_roots.get(&k.1)?;
                    (k.0 == comp.body && comp.facts.place(*local).root == root)
                        .then(|| comp.facts.place(c).root)
                })
            };
            let ok = names.iter().any(|&q| {
                let cell = cell_of(q);
                vars.iter().any(|v| {
                    comp.points.get(v).is_some_and(|ps| {
                        ps.iter().any(|&d| {
                            comp.ref_inside(q, d)
                                || cell.is_some_and(|c| comp.facts.place(d).root == c)
                        })
                    })
                })
            });
            if !ok {
                let shown = |ps: &[PlaceId]| -> String {
                    ps.iter()
                        .map(|&q| comp.facts.place(q).display.clone())
                        .collect::<Vec<_>>()
                        .join("` or `")
                };
                let group = comp.group(&cur);
                let nodes: Vec<String> = group.iter().map(|&n| comp.node_text(n)).collect();
                return Err(format!(
                    "summary oracle (A3): in `{}` at {}, a callee puts a reference to `{}` into `{}`, and no `points_into` place of a variable that holds it covers it",
                    comp.facts.name,
                    nodes.join(", "),
                    shown(&names),
                    shown(&dest),
                ));
            }
        }
        Ok(())
    }

    /// C2 (holder cover): the run follows the reference at place `p` of
    /// frame `uid` at the nodes `group`. If a local of the frame holds `p`,
    /// a variable of that local is used at the node.
    ///
    /// # Errors
    ///
    /// The message of a failure.
    fn check_holder(
        &mut self,
        uid: u64,
        code: &Code,
        slots: &[Option<CellId>],
        heap: &Heap,
        group: &[NodeId],
        p: &Place,
    ) -> Result<(), String> {
        let Some(fr) = self.frames.get(&uid) else {
            return Ok(());
        };
        let found = locate(
            code,
            slots,
            heap,
            (&fr.anchors, &fr.retired),
            p.cell,
            &p.path,
        );
        let locals: Vec<LocalId> = found
            .iter()
            .filter_map(|(b, _)| match b {
                Base::Local(l) => Some(*l),
                Base::Anchor(_) => None,
            })
            .collect();
        let Some(comp) = self.comps.get(fr.comp) else {
            return Ok(());
        };
        if locals.is_empty() {
            return Ok(());
        }
        self.report.checks += 1;
        let ok = locals.iter().any(|l| {
            let vars = comp.of_local.get(l).map_or(&[][..], Vec::as_slice);
            group.iter().any(|n| {
                comp.uses
                    .get(n.index())
                    .is_some_and(|us| us.iter().any(|u| vars.contains(u)))
            })
        });
        if ok {
            return Ok(());
        }
        let names: Vec<String> = locals
            .iter()
            .filter_map(|l| comp.s_of.get(l))
            .map(|&v| var_name(&comp.facts, v))
            .collect();
        let nodes: Vec<String> = group.iter().map(|&n| comp.node_text(n)).collect();
        Err(format!(
            "fact oracle (C2): in `{}` at {}, the run follows a reference that `{}` holds, and the node uses no variable of it",
            comp.facts.name,
            nodes.join(", "),
            names.join("` or `"),
        ))
    }

    /// The fact places of the concrete target `t` in frame `uid`, with the
    /// IR type of the place, or `None` if no IR place of the frame reaches
    /// it. Each IR place that reaches it gives its places.
    fn name(
        &mut self,
        uid: u64,
        code: &Code,
        slots: &[Option<CellId>],
        heap: &Heap,
        t: &Target,
    ) -> Option<(Vec<PlaceId>, Option<weft_ir::TyId>)> {
        let fr = self.frames.get(&uid)?;
        let (cell, path, elems) = match t {
            Target::Place(p) => (p.cell, p.path.clone(), false),
            Target::Elems(b) => (*b, Vec::new(), true),
        };
        let found = locate(code, slots, heap, (&fr.anchors, &fr.retired), cell, &path);
        let ci = fr.comp;
        let mut bases = Vec::new();
        for (base, mut proj) in found {
            if elems {
                proj.push(Proj::Elems);
            }
            let (local, param, mut full) = match base {
                Base::Local(l) => (l, None, Vec::new()),
                Base::Anchor(i) => {
                    let Some(a) = fr.anchors.get(i) else {
                        continue;
                    };
                    (a.local, a.param, a.proj.clone())
                }
            };
            full.extend(proj);
            bases.push((weft_ir::Place { local, proj: full }, param));
        }
        let input = Rc::clone(&self.input);
        let p = &input.built.program;
        let comp_body = self.comps.get(ci)?.body;
        let mut out: Vec<PlaceId> = Vec::new();
        let mut ty = None;
        for (place, param) in bases {
            let key = (ci, place.clone(), param);
            if let Some((ps, t)) = self.names.get(&key) {
                out.extend(ps.iter().copied());
                ty = ty.or(*t);
                continue;
            }
            let Some(comp) = self.comps.get_mut(ci) else {
                continue;
            };
            // A place through a `ByRef` capture of a closure body is the
            // place of the captured variable in the maker (second review of
            // the ABC preview, 5): the facts of the instantiated body name
            // the variable itself.
            let (body, place, param) = match param {
                None => through_env(p, comp_body, place),
                Some(i) => (comp_body, place, Some(i)),
            };
            let name_of = p
                .bodies
                .get(body.index())
                .and_then(|b| b.locals.get(place.local.index()))
                .map_or_else(String::new, |d| alpha::local_text(&comp.tys, d));
            // A local of the maker that holds a reference (a capture of a
            // reference, `through_env`): its target is a place that the
            // variable of the local points into (gap FO-G1 of the third
            // review of the ABC preview).
            let held: Option<Vec<PlaceId>> = match (param, place.proj.first()) {
                (None, Some(Proj::Deref(DerefKind::Ref))) => comp
                    .s_any
                    .get(&(body.0, place.local))
                    .and_then(|v| comp.points.get(v))
                    .filter(|ps| !ps.is_empty())
                    .cloned(),
                _ => None,
            };
            let mut derefs = 0u32;
            let mut pointees = |facts: &mut FnFacts,
                                roots: &mut Roots,
                                _: PlaceId,
                                _: Option<(weft_ir::AdtId, u32)>|
             -> Result<Vec<PlaceId>, alpha::AlphaError> {
                let Some(i) = param else {
                    derefs += 1;
                    return match (&held, derefs) {
                        (Some(ps), 1) => Ok(ps.clone()),
                        _ => Err(alpha::AlphaError::Later(
                            "a reference that is not a parameter",
                        )),
                    };
                };
                derefs += 1;
                Ok(vec![if derefs == 1 {
                    roots.param(facts, body, i, &name_of)
                } else {
                    roots.held(facts, body, i, &name_of)
                }])
            };
            let Ok(al) = alpha::alpha_with(
                p,
                &mut comp.tys,
                &mut comp.facts,
                &mut comp.roots,
                body,
                &place,
                &mut pointees,
            ) else {
                continue;
            };
            let t = alpha::place_ty(p, &mut comp.tys, body, &place);
            ty = ty.or(t);
            out.extend(al.places.iter().copied());
            self.names.insert(key, (al.places, t));
        }
        out.sort();
        out.dedup();
        (!out.is_empty()).then_some((out, ty))
    }
}

impl FactOracle {
    /// True if `ty` is a type of component `ci` that is not plain data, or
    /// is not known.
    fn not_copy(&self, ci: usize, ty: Option<weft_ir::TyId>) -> bool {
        match (self.comps.get(ci), ty) {
            (Some(c), Some(t)) => c.tys.not_copy(t),
            _ => true,
        }
    }

    /// True if `ty` is an array type of the types of component `ci`.
    fn is_array(&self, ci: usize, ty: Option<weft_ir::TyId>) -> bool {
        let Some(comp) = self.comps.get(ci) else {
            return false;
        };
        ty.and_then(|t| comp.tys.try_get(t))
            .is_some_and(|t| matches!(t, weft_ir::Ty::Array(..)))
    }
}

/// True if the props of local `l` of body `body` say that its value can
/// hold a reference.
fn holds_refs(built: &Built, body: BodyId, l: LocalId) -> bool {
    built
        .program
        .bodies
        .get(body.index())
        .and_then(|b| b.locals.get(l.index()))
        .is_none_or(|d| d.props.holds_refs)
}

/// The steps `steps` with each side of a split as the element step: the
/// concrete place of a slice names its elements, not the side of a split
/// (the coarse embedding of the proof link, `proofs/link/README.md`).
fn coarse(steps: &[weft_facts::Step]) -> Vec<weft_facts::Step> {
    steps
        .iter()
        .map(|s| match s.kind {
            weft_facts::StepKind::Seg { .. } => weft_facts::Step {
                kind: weft_facts::StepKind::Elem,
                unstable: s.unstable,
            },
            _ => *s,
        })
        .collect()
}

/// The place `place` of body `body` with each step through a capture of a
/// closure body replaced by the source of the capture in the maker
/// (`(*env.k).f` is `x.f` for a `ByRef` capture of `x`, and `(*x).f` for a
/// `ByMove` or `Kept` capture of a reference `x`), and the index of the
/// parameter that the place then starts at, if any.
///
/// A `ByRef` capture holds a reference to the cell of the variable of the
/// maker, so the target is the current value of the variable (`docs/ir.md`
/// 6.3). The facts of an instantiated closure body name it with the place
/// of the variable. A capture that holds a reference names the target of
/// the reference of the variable ([`FactOracle::name`] follows a local of
/// the maker through its `points_into` places).
fn through_env(
    p: &weft_ir::Program,
    mut body: BodyId,
    mut place: weft_ir::Place,
) -> (BodyId, weft_ir::Place, Option<u32>) {
    // Each step goes to the maker, a body with a lower id: the walk ends.
    for _ in 0..=p.bodies.len() {
        let Some((_, decl)) = p.closure_of(body) else {
            break;
        };
        let env = p.body(body).and_then(|b| b.params.first().copied());
        if env != Some(place.local) {
            break;
        }
        let [Proj::Field(k), Proj::Deref(DerefKind::Ref), rest @ ..] = place.proj.as_slice() else {
            break;
        };
        let Some(cap) = decl.captures.get(k.0 as usize) else {
            break;
        };
        let mut proj = cap.source.proj.clone();
        match cap.mode {
            // The reference in the environment points into the cell of the
            // variable: `(*env.k).f` is `x.f`.
            weft_ir::CaptureMode::ByRef => {}
            // The capture holds a reference (a copy of it, or the cell of the
            // variable): `(*env.k).f` is `(*x).f` (gap FO-G1 of the third
            // review of the ABC preview: `fn go(w: &W) { let f = ||
            // w.items.push(10); f() }`).
            weft_ir::CaptureMode::ByMove | weft_ir::CaptureMode::Kept => {
                proj.push(Proj::Deref(DerefKind::Ref));
            }
            _ => break,
        }
        proj.extend(rest.iter().cloned());
        place = weft_ir::Place {
            local: cap.source.local,
            proj,
        };
        body = decl.maker;
    }
    // The environment of a closure has no index: a reference in it stays
    // with no name. A parameter of a function body starts at its `Param`
    // root.
    let param = p.body(body).and_then(|b| {
        let closure = p.closure_of(body).is_some();
        b.params
            .iter()
            .position(|&l| l == place.local)
            .filter(|&i| !(closure && i == 0))
            .map(u32_of)
    });
    (body, place, param)
}

/// The text of variable `v`.
fn var_name(f: &FnFacts, v: VarId) -> String {
    f.vars
        .get(v.index())
        .map_or_else(|| format!("{v}"), |i| i.name.clone())
}

/// The local of the slot that holds cell `c`, if one does.
/// The `Post` nodes of the `handle` of clause body `body` of component
/// `c` (empty for another body).
fn clause_post(built: &Built, c: &Component, body: BodyId) -> Vec<NodeId> {
    let p = &built.program;
    let Some(weft_ir::BodyKind::Clause(h, _)) = p.bodies.get(body.index()).map(|b| b.kind) else {
        return Vec::new();
    };
    let Some(site) = p.handlers.get(h.index()).map(|d| d.site) else {
        return Vec::new();
    };
    let Some(sb) = p.bodies.get(site.index()) else {
        return Vec::new();
    };
    let blocks: Vec<u32> = sb
        .blocks
        .iter()
        .enumerate()
        .filter(|(_, b)| matches!(b.term.kind, weft_ir::TermKind::Handle { handler, .. } if handler == h))
        .map(|(i, _)| u32_of(i))
        .collect();
    let mut out: Vec<NodeId> = c
        .emitted
        .table
        .iter()
        .filter(|(k, _)| {
            k.body == site
                && blocks.contains(&k.block.0)
                && k.phase == weft_sema::factgen::nodes::Phase::Post
        })
        .map(|(_, &id)| id)
        .collect();
    out.sort();
    out.dedup();
    out
}

fn cell_local(code: &Code, slots: &[Option<CellId>], c: CellId) -> Option<LocalId> {
    let s = slots.iter().position(|x| *x == Some(c))?;
    code.slot_locals.get(s).map(|&l| LocalId(l))
}

/// The value of local `l` of a frame.
fn local_value<'h>(
    code: &Code,
    slots: &[Option<CellId>],
    heap: &'h Heap,
    l: LocalId,
) -> Option<&'h Value> {
    let s = code.slot_locals.iter().position(|&x| x == l.0)?;
    let c = (*slots.get(s)?)?;
    heap.slot(c).ok().map(|s| &s.val)
}

/// The value of the move path `steps` of value `v`: `None` if the value is
/// another variant.
fn part_value<'v>(v: &'v Value, steps: &[weft_sema::analysis::PathStep]) -> Option<&'v Value> {
    use weft_sema::analysis::PathStep;
    let mut v = v;
    for s in steps {
        v = match (s, v) {
            (PathStep::Field(i), Value::Struct(o)) => o.fields.get(*i as usize)?,
            (PathStep::Field(i), Value::Tuple(vs)) => vs.get(*i as usize)?,
            (PathStep::Field(i), Value::Enum(e)) => e.fields.get(*i as usize)?,
            (PathStep::Variant(x), Value::Enum(e)) if e.variant == *x => v,
            _ => return None,
        };
    }
    Some(v)
}

/// The references in value `v` (the move path of `v` is `at`), not in the
/// parts at the move paths `skip`. With `path`, the walk is still on a move
/// path (no `Box` or buffer on the way). A value in an `Rc` object belongs
/// to its group, not to the value.
fn refs_of(
    heap: &Heap,
    v: &Value,
    at: &mut Vec<weft_sema::analysis::PathStep>,
    skip: &[Vec<weft_sema::analysis::PathStep>],
    path: bool,
    depth: usize,
    out: &mut Vec<Target>,
) {
    use weft_sema::analysis::PathStep;
    if depth > 64 || out.len() > 4096 {
        return;
    }
    if path && !at.is_empty() && skip.iter().any(|s| s == at) {
        return;
    }
    match v {
        Value::Ref(p) => out.push(Target::Place(p.clone())),
        Value::Slice { buf, .. } => out.push(Target::Elems(*buf)),
        Value::Struct(o) => {
            for (i, f) in o.fields.iter().enumerate() {
                at.push(PathStep::Field(u32_of(i)));
                refs_of(heap, f, at, skip, path, depth + 1, out);
                at.pop();
            }
        }
        Value::Tuple(vs) => {
            for (i, f) in vs.iter().enumerate() {
                at.push(PathStep::Field(u32_of(i)));
                refs_of(heap, f, at, skip, path, depth + 1, out);
                at.pop();
            }
        }
        Value::Enum(e) => {
            at.push(PathStep::Variant(e.variant));
            if path && skip.iter().any(|s| s == at) {
                at.pop();
                return;
            }
            for (i, f) in e.fields.iter().enumerate() {
                at.push(PathStep::Field(u32_of(i)));
                refs_of(heap, f, at, skip, path, depth + 1, out);
                at.pop();
            }
            at.pop();
        }
        Value::Boxed(c) | Value::Vec(c) => {
            if let Ok(s) = heap.slot(*c) {
                refs_of(heap, &s.val, at, skip, false, depth + 1, out);
            }
        }
        Value::List(vs) => {
            for f in vs {
                refs_of(heap, f, at, skip, false, depth + 1, out);
            }
        }
        _ => {}
    }
}

/// The targets of the references in value `v` that a callee writes into a
/// place of a caller ([`FactOracle::check_put`]): the references in it, in its
/// boxes and buffers, and in the captured cells of its closures. A captured
/// cell of a closure (a capture by reference) counts in `cells`: its root is
/// the cell root of the variable, which this check does not name.
fn put_targets(heap: &Heap, v: &Value, depth: usize, out: &mut Vec<Target>, cells: &mut u64) {
    if depth > 64 || out.len() > 4096 {
        return;
    }
    match v {
        Value::Ref(p) => out.push(Target::Place(p.clone())),
        Value::Slice { buf, .. } => out.push(Target::Elems(*buf)),
        Value::Struct(o) => {
            for f in &o.fields {
                put_targets(heap, f, depth + 1, out, cells);
            }
        }
        Value::Tuple(vs) | Value::List(vs) => {
            for f in vs {
                put_targets(heap, f, depth + 1, out, cells);
            }
        }
        Value::Enum(e) => {
            for f in &e.fields {
                put_targets(heap, f, depth + 1, out, cells);
            }
        }
        Value::Boxed(c) | Value::Vec(c) => {
            if let Ok(s) = heap.slot(*c) {
                put_targets(heap, &s.val, depth + 1, out, cells);
            }
        }
        Value::Closure(k) => {
            for c in &k.cells {
                // A capture by reference shares the cell of the variable:
                // the cell itself is not named here, the references in its
                // value are.
                if !k.owned.contains(c) {
                    *cells += 1;
                }
                if let Ok(s) = heap.slot(*c) {
                    put_targets(heap, &s.val, depth + 1, out, cells);
                }
            }
        }
        _ => {}
    }
}

/// The targets of the references in the value of a parameter, with the
/// projections from the parameter (`Deref(Ref)` for each reference), up to
/// a depth of four references.
fn param_targets(
    heap: &Heap,
    v: &Value,
    proj: &mut Vec<Proj>,
    refs: usize,
    out: &mut Vec<(Vec<Proj>, Place)>,
) {
    if refs > 4 || proj.len() > 64 || out.len() > 4096 {
        return;
    }
    match v {
        Value::Ref(p) => {
            proj.push(Proj::Deref(DerefKind::Ref));
            out.push((proj.clone(), Place::new(p.cell, p.path.clone())));
            if let Ok(t) = heap.peek(&Place::new(p.cell, p.path.clone())) {
                param_targets(heap, t, proj, refs + 1, out);
            }
            proj.pop();
        }
        Value::Slice { buf, .. } => {
            proj.push(Proj::Deref(DerefKind::Ref));
            out.push((proj.clone(), Place::root(*buf)));
            proj.pop();
        }
        Value::Struct(o) => {
            for (i, f) in o.fields.iter().enumerate() {
                proj.push(Proj::Field(FieldIdx(u32_of(i))));
                param_targets(heap, f, proj, refs, out);
                proj.pop();
            }
        }
        Value::Tuple(vs) => {
            for (i, f) in vs.iter().enumerate() {
                proj.push(Proj::Field(FieldIdx(u32_of(i))));
                param_targets(heap, f, proj, refs, out);
                proj.pop();
            }
        }
        Value::Enum(e) => {
            for (i, f) in e.fields.iter().enumerate() {
                proj.push(Proj::Variant(VariantIdx(e.variant)));
                proj.push(Proj::Field(FieldIdx(u32_of(i))));
                param_targets(heap, f, proj, refs, out);
                proj.pop();
                proj.pop();
            }
        }
        Value::Boxed(c) => {
            if let Ok(s) = heap.slot(*c) {
                proj.push(Proj::Deref(DerefKind::Box));
                param_targets(heap, &s.val, proj, refs, out);
                proj.pop();
            }
        }
        Value::Vec(c) => {
            if let Ok(s) = heap.slot(*c) {
                param_targets(heap, &s.val, proj, refs, out);
            }
        }
        Value::List(vs) => {
            for f in vs {
                proj.push(Proj::Index(ELEM));
                param_targets(heap, f, proj, refs, out);
                proj.pop();
            }
        }
        _ => {}
    }
}

/// The projections in value `v` along the concrete path `path`, or `None` if
/// the path does not fit the value.
fn translate(v: &Value, path: &[u32]) -> Option<Vec<Proj>> {
    let mut out = Vec::new();
    let mut v = v;
    for &i in path {
        v = match v {
            Value::Struct(o) => {
                out.push(Proj::Field(FieldIdx(i)));
                o.fields.get(i as usize)?
            }
            Value::Tuple(vs) => {
                out.push(Proj::Field(FieldIdx(i)));
                vs.get(i as usize)?
            }
            Value::Enum(e) => {
                out.push(Proj::Variant(VariantIdx(e.variant)));
                out.push(Proj::Field(FieldIdx(i)));
                e.fields.get(i as usize)?
            }
            Value::List(vs) => {
                out.push(Proj::Index(ELEM));
                vs.get(i as usize)?
            }
            _ => return None,
        };
    }
    Some(out)
}

/// The bases and the projections of the concrete place (`cell`, `path`) in
/// a frame with the slots `slots`, the anchors `anchors` and the retired
/// cells `retired` of its temporaries: the slot of a local (or a retired
/// cell of it), each anchor at or above it, and the first owner of the cell
/// in each local and each anchor.
fn locate(
    code: &Code,
    slots: &[Option<CellId>],
    heap: &Heap,
    (anchors, retired): (&[Anchor], &HashMap<CellId, LocalId>),
    cell: CellId,
    path: &[u32],
) -> Vec<(Base, Vec<Proj>)> {
    let in_cell = |c: CellId, at: &[u32]| -> Option<Vec<Proj>> {
        let v = &heap.slot(c).ok()?.val;
        translate(v, at)
    };
    let mut out = Vec::new();
    if let Some(l) = cell_local(code, slots, cell).or_else(|| retired.get(&cell).copied()) {
        if let Some(p) = in_cell(cell, path) {
            out.push((Base::Local(l), p));
        }
        return out;
    }
    for (i, a) in anchors.iter().enumerate() {
        if a.place.cell == cell && path.starts_with(&a.place.path) {
            let rest = path.get(a.place.path.len()..).unwrap_or_default();
            if let Some(p) = heap.peek(&a.place).ok().and_then(|v| translate(v, rest)) {
                out.push((Base::Anchor(i), p));
            }
        }
    }
    // A cell that a value of the frame owns.
    let mut budget = INDEX_LIMIT;
    let mut roots: Vec<(Base, &Value)> = Vec::new();
    for (s, c) in slots.iter().enumerate() {
        let (Some(c), Some(&l)) = (c, code.slot_locals.get(s)) else {
            continue;
        };
        if let Ok(x) = heap.slot(*c) {
            roots.push((Base::Local(LocalId(l)), &x.val));
        }
    }
    for (i, a) in anchors.iter().enumerate() {
        if let Ok(v) = heap.peek(&a.place) {
            roots.push((Base::Anchor(i), v));
        }
    }
    for (base, v) in roots {
        if let Some(mut found) = owner_of(heap, v, &mut Vec::new(), cell, &mut budget) {
            if let Some(rest) = in_cell(cell, path) {
                found.extend(rest);
                out.push((base, found));
            }
        }
        if budget == 0 {
            break;
        }
    }
    out
}

/// The projections from value `v` (at projections `proj`) to the root of
/// the heap cell `cell` that the value owns, if it does.
fn owner_of(
    heap: &Heap,
    v: &Value,
    proj: &mut Vec<Proj>,
    cell: CellId,
    budget: &mut usize,
) -> Option<Vec<Proj>> {
    // A deep value (an inline recursive enum) has no owner of a cell below
    // this depth: the walk does not use the stack of the machine for it.
    if *budget == 0 || proj.len() > OWNER_DEPTH {
        return None;
    }
    *budget -= 1;
    let mut inside = |proj: &mut Vec<Proj>, step: Option<Proj>, c: CellId| -> Option<Vec<Proj>> {
        let pushed = step.is_some();
        if let Some(s) = step {
            proj.push(s);
        }
        let r = if c == cell {
            Some(proj.clone())
        } else {
            heap.slot(c)
                .ok()
                .and_then(|x| owner_of(heap, &x.val, proj, cell, budget))
        };
        if pushed {
            proj.pop();
        }
        r
    };
    match v {
        Value::Boxed(c) => inside(proj, Some(Proj::Deref(DerefKind::Box)), *c),
        Value::Rc(c) => inside(proj, Some(Proj::Deref(DerefKind::Rc)), *c),
        Value::Vec(c) => inside(proj, None, *c),
        Value::Struct(o) => o.fields.iter().enumerate().find_map(|(i, f)| {
            proj.push(Proj::Field(FieldIdx(u32_of(i))));
            let r = owner_of(heap, f, proj, cell, budget);
            proj.pop();
            r
        }),
        Value::Tuple(vs) => vs.iter().enumerate().find_map(|(i, f)| {
            proj.push(Proj::Field(FieldIdx(u32_of(i))));
            let r = owner_of(heap, f, proj, cell, budget);
            proj.pop();
            r
        }),
        Value::Enum(e) => e.fields.iter().enumerate().find_map(|(i, f)| {
            proj.push(Proj::Variant(VariantIdx(e.variant)));
            proj.push(Proj::Field(FieldIdx(u32_of(i))));
            let r = owner_of(heap, f, proj, cell, budget);
            proj.pop();
            proj.pop();
            r
        }),
        Value::List(vs) => vs.iter().find_map(|f| {
            proj.push(Proj::Index(ELEM));
            let r = owner_of(heap, f, proj, cell, budget);
            proj.pop();
            r
        }),
        _ => None,
    }
}
