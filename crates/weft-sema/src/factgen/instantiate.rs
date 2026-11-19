//! Call-site copies of callees (plan stage R0k-a, `docs/ir.md` 6.1).
//!
//! A local handler can serve an operation that a callee performs with a
//! function value or a reference in its arguments or its result (the
//! reasons C2 and D3 of the scope report). A summary of the callee cannot
//! tell what the clause does with such a value, or when the callee runs a
//! value that the clause gives back. So the fact generator puts a copy of
//! the body of the callee at the call: [`instantiate`] gives a program in
//! which each such call is the code of the callee. Then the perform is a
//! perform of the local handler, and the machinery of a handled body
//! applies (the clause runs at the node of the perform, the resume regions,
//! the `multi` re-entry, the abort edges).
//!
//! The copy of the code of a callee at a call (body `b`, block `k`):
//!
//! - Each local of the callee is a new local of `b`. A parameter is a
//!   variable of the source; `_0` is a temporary.
//! - A new block binds the parameters to the operands of the call, then
//!   goes to the entry of the callee. A `Return` of the callee gives `_0` to
//!   the destination of the call and goes to the next block. The
//!   `UnwindExit` of the callee goes to the cleanup block of the call.
//! - Each body inside the callee (a closure, a handled body, a clause, a
//!   scope body) gets a copy, with a copy of its declaration. The root
//!   capability environment of the callee is the environment of the call.
//!   A body inside a closure of the callee is in the environment of the
//!   closure body.
//! - A perform through the row of the callee goes to the capability that
//!   the environment of the call gives for the operation (through upvar
//!   locals in a body inside the callee).
//! - A closure performs through the capabilities of the point where it is
//!   made. So a closure of the callee gets a `Cap` capture for each effect
//!   that the environment of the call serves and that its code can use, as
//!   the builder gives a closure of the site (`Builder::caps_for`).
//!
//! A copy of a closure body at a run of the closure value (stages R0k-a2,
//! R0k-b1' and R0k-b2, `Inst::closure_copy`) names each capture through a
//! place of the site if it can. Else (a source that ends before the run, a
//! source in the frame of a callee that made the closure) it reads the
//! capture through the environment local of its copy region
//! (`LocalKind::CopyEnv`): the cell that the closure value holds.
//!
//! A call is copied only if the callee is not recursive, the chain of
//! copied calls is short ([`DEPTH_BOUND`]), and the copies stay small
//! ([`BLOCK_BOUND`]). The copy is a program of the IR: the verifier checks
//! it, and the fact oracle runs it (`weft-interp`). [`Instantiated::weak_ok`]
//! says if the facts of a callee can use the weak form of a perform through
//! its row (`analysis::transfer::WeakRowOps`).

use std::collections::{BTreeMap, BTreeSet, HashMap};

use weft_ir::{
    BlockId, Body, BodyId, BodyKind, Callee, CapArgs, CapEnv, CapEnvId, CapOperand, ClosureId,
    EffectId, FnId, HandlerId, LocalDecl, LocalId, LocalKind, OpIdx, Operand, Place, Program, Proj,
    Rvalue, ScopeId, SpawnId, Stmt, StmtKind, TempKind, Term, TermKind, TyTable,
};

use crate::irbuild::Built;

/// The most blocks that the copies add to one program.
pub const BLOCK_BOUND: usize = 6000;

/// The longest chain of copied calls.
pub const DEPTH_BOUND: usize = 8;

/// The bounds of the copies ([`instantiate_with`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bounds {
    /// The most blocks that the copies add to one program.
    pub blocks: usize,
    /// The longest chain of copied calls.
    pub depth: usize,
}

impl Default for Bounds {
    fn default() -> Self {
        Self {
            blocks: BLOCK_BOUND,
            depth: DEPTH_BOUND,
        }
    }
}

/// The result of [`instantiate`].
#[derive(Clone, Debug)]
pub struct Instantiated {
    /// The program with the copies.
    pub built: Built,
    /// The number of copied calls of function items.
    pub calls: usize,
    /// The number of copied calls of closures (stage R0k-a2).
    pub closure_calls: usize,
    /// The number of copies of closure bodies that are copy regions (stage
    /// R0k-b1'): the run node is not in the maker body, so the code of the
    /// copy runs with the handlers of the closure value.
    pub regions: usize,
    /// The number of dispatches (plan stage R0z Z6).
    pub dispatches: usize,
    /// True if the facts of a callee can use the weak form of a perform
    /// through its row (`analysis::transfer::WeakRowOps`).
    ///
    /// The weak form says that code of a caller runs the function values of
    /// the operation; it does not say what the clause keeps. It is sound for
    /// the facts of the callee itself. Its summary is not sound where a local
    /// handler serves the operation, so the invariant is: no call that a
    /// local handler serves applies a summary with the weak form, also
    /// through a callee that passes the effect on. This holds if each such
    /// call has a copy (no served call of a callee that gives a function
    /// value to an operation through its row is left), and if no other
    /// code can run such a callee: no closure performs such an operation or
    /// calls such a callee, no function item value names one, and `main`
    /// and the tests do not perform such an operation or call such a callee
    /// through their row (a root handler is code of the runtime). The
    /// analysis checks the invariant again at each call
    /// (`analysis::transfer::note_weak_call`).
    pub weak_ok: bool,
    /// The call site of each block that a copy adds: the body and the block
    /// of the call, and the callee.
    pub sites: BTreeMap<(BodyId, BlockId), (BodyId, BlockId, FnId)>,
    /// The call site of each body that a copy adds.
    pub body_sites: BTreeMap<BodyId, (BodyId, BlockId, FnId)>,
    /// The closures that resume the continuation of their clause and whose
    /// one run got a copy of their body (stage R0k-c1, [`instantiate_kont`]).
    /// No run applies their summary, so the facts of their bodies need no
    /// resume point (`analysis::clause::KontCovered`).
    pub covered: BTreeSet<ClosureId>,
}

/// The effects that the code of a function can perform through its row
/// with a function value or a reference (`any`), or with a function value
/// in an argument (`fns`), also through its callees and the bodies inside
/// it.
#[derive(Clone, Debug, Default)]
struct Needs {
    any: BTreeMap<FnId, BTreeSet<EffectId>>,
    fns: BTreeMap<FnId, BTreeSet<EffectId>>,
    /// Each effect that the code of a function can perform through its row.
    row: BTreeMap<FnId, BTreeSet<EffectId>>,
    /// The functions that call a function value whose type states no row:
    /// their code can perform each effect.
    unknown: BTreeSet<FnId>,
    /// The functions that a function calls, also in the bodies inside it.
    calls: BTreeMap<FnId, BTreeSet<FnId>>,
}

/// True if a value of operation `op` of effect `e` can hold a function
/// value or a reference: `(in an argument or the result, in an argument)`.
fn risky_op(tys: &TyTable, e: EffectId, op: OpIdx) -> (bool, bool) {
    let Some(o) = tys
        .effects()
        .get(e.index())
        .and_then(|d| d.ops.get(op.index()))
    else {
        return (true, true);
    };
    let holds = |t| crate::props::ir_props(tys, t).holds_refs || crate::props::ir_has_fns(tys, t);
    let fns = o.params.iter().any(|&t| crate::props::ir_has_fns(tys, t));
    let any = fns || o.params.iter().any(|&t| holds(t)) || holds(o.ret);
    (any, fns)
}

/// True if capability environment `env` binds effect `e`.
fn env_binds(p: &Program, env: CapEnvId, e: EffectId) -> bool {
    let mut at = Some(env);
    for _ in 0..=p.cap_envs.len() {
        let Some(id) = at else { return false };
        let Some(c) = p.cap_envs.get(id.index()) else {
            return false;
        };
        if c.adds.iter().any(|(x, _)| *x == e) {
            return true;
        }
        at = c.parent;
    }
    false
}

/// The function of each body: the function whose body is the body or a
/// lexical parent of it.
fn body_fns(p: &Program) -> Vec<Option<FnId>> {
    // Follow the parent chain of each body. This does not use the order of
    // the body ids: a copy can append a body after the bodies inside it.
    p.bodies
        .iter()
        .map(|b| {
            let mut at = Some(b);
            for _ in 0..=p.bodies.len() {
                let x = at?;
                if let BodyKind::Fn(f) = x.kind {
                    return Some(f);
                }
                at = x.parent.and_then(|q| p.body(q));
            }
            None
        })
        .collect()
}

/// The bodies inside body `root` (not `root`), in the order of their ids.
fn inner_bodies(p: &Program, root: BodyId) -> Vec<BodyId> {
    // Follow the parent chain of each body. This does not use the order of
    // the body ids: a copy can append a body after the bodies inside it.
    let mut out = Vec::new();
    for (i, b) in p.bodies.iter().enumerate() {
        let mut at = b.parent;
        for _ in 0..p.bodies.len() {
            match at {
                Some(q) if q == root => {
                    out.push(BodyId(u32::try_from(i).unwrap_or(u32::MAX)));
                    break;
                }
                Some(q) => at = p.body(q).and_then(|x| x.parent),
                None => break,
            }
        }
    }
    out
}

impl Needs {
    /// The needs of each function of program `p`: a fixpoint over the calls.
    fn of(p: &Program, tys: &TyTable) -> Self {
        let owner = body_fns(p);
        let mut n = Self::default();
        // The direct performs and the call edges with the environment of the
        // call.
        let mut edges: Vec<(FnId, FnId, CapEnvId)> = Vec::new();
        for (i, b) in p.bodies.iter().enumerate() {
            let Some(f) = owner.get(i).copied().flatten() else {
                continue;
            };
            for blk in &b.blocks {
                match &blk.term.kind {
                    TermKind::Call {
                        callee: Callee::Value(o),
                        ..
                    } => match value_row(tys, b, o) {
                        Some(r) => n.row.entry(f).or_default().extend(r),
                        None => {
                            n.unknown.insert(f);
                        }
                    },
                    TermKind::Perform {
                        cap: CapOperand::Row(e),
                        op,
                        ..
                    } => {
                        n.row.entry(f).or_default().insert(*e);
                        let (any, fns) = risky_op(tys, *e, *op);
                        if any {
                            n.any.entry(f).or_default().insert(*e);
                        }
                        if fns {
                            n.fns.entry(f).or_default().insert(*e);
                        }
                    }
                    TermKind::Call {
                        callee: Callee::Fn(g, _),
                        caps,
                        ..
                    } => {
                        n.calls.entry(f).or_default().insert(*g);
                        if let CapArgs::Lexical(env) = caps {
                            edges.push((f, *g, *env));
                        }
                    }
                    _ => {}
                }
            }
        }
        // A callee passes an effect on where the environment of the call
        // does not bind it.
        loop {
            let mut changed = false;
            for &(f, g, env) in &edges {
                if n.unknown.contains(&g) {
                    changed |= n.unknown.insert(f);
                }
                for set in [&mut n.any, &mut n.fns, &mut n.row] {
                    let add: Vec<EffectId> = set
                        .get(&g)
                        .map(|s| {
                            s.iter()
                                .copied()
                                .filter(|&e| !env_binds(p, env, e))
                                .collect()
                        })
                        .unwrap_or_default();
                    let to = set.entry(f).or_default();
                    for e in add {
                        changed |= to.insert(e);
                    }
                }
            }
            if !changed {
                break;
            }
        }
        n
    }

    /// True if function `f` can call itself.
    fn recursive(&self, f: FnId) -> bool {
        let mut seen: BTreeSet<FnId> = BTreeSet::new();
        let mut work: Vec<FnId> = self
            .calls
            .get(&f)
            .map(|s| s.iter().copied().collect())
            .unwrap_or_default();
        while let Some(g) = work.pop() {
            if g == f {
                return true;
            }
            if seen.insert(g) {
                work.extend(self.calls.get(&g).into_iter().flatten().copied());
            }
        }
        false
    }
}

/// The place of the capability that serves operation `op` of effect `e`
/// in capability environment `env`, in the terms of the body that adds it,
/// with that body: the capability of a handled body whose handler has a
/// clause for `op`, or the `Cap` field of a closure environment.
fn serving_cap(p: &Program, env: CapEnvId, e: EffectId, op: OpIdx) -> Option<(BodyId, Place)> {
    let mut at = Some(env);
    for _ in 0..=p.cap_envs.len() {
        let id = at?;
        let c = p.cap_envs.get(id.index())?;
        if let Some((_, place)) = c.adds.iter().find(|(x, _)| *x == e) {
            let owner = p.bodies.iter().enumerate().find_map(|(i, b)| {
                let yes = b.cap_env == id
                    && match b.kind {
                        BodyKind::Handled(_) => b.caps.iter().any(|(x, _)| *x == e),
                        BodyKind::Closure(_) => true,
                        _ => false,
                    };
                yes.then(|| (BodyId(u32::try_from(i).unwrap_or(u32::MAX)), b.kind))
            })?;
            match owner.1 {
                BodyKind::Handled(h) => {
                    let has = p
                        .handlers
                        .get(h.index())
                        .is_some_and(|d| d.clauses.iter().any(|(o, _)| *o == op));
                    if has {
                        return Some((owner.0, place.clone()));
                    }
                    // A handler with no clause for the operation passes it on
                    // to the environment around it.
                }
                _ => return Some((owner.0, place.clone())),
            }
        }
        at = c.parent;
    }
    None
}

/// The copies of one program.
struct Inst<'a> {
    bounds: Bounds,
    orig: &'a Program,
    tys: TyTable,
    closure_calls: usize,
    needs: Needs,
    p: Program,
    added: usize,
    calls: usize,
    /// The chain of copied callees of each block that a copy adds.
    blk_chain: HashMap<(BodyId, BlockId), Vec<FnId>>,
    /// The chain of copied callees of each body that a copy adds.
    body_chain: HashMap<BodyId, Vec<FnId>>,
    sites: BTreeMap<(BodyId, BlockId), (BodyId, BlockId, FnId)>,
    body_sites: BTreeMap<BodyId, (BodyId, BlockId, FnId)>,
    /// The mode of stage R0k-c1: only the copies of a closure that resumes
    /// the continuation of its clause ([`instantiate_kont`]).
    kont: bool,
    /// The closures whose one run got a copy of their body in that mode.
    covered: BTreeSet<ClosureId>,
    /// The copy of a closure body whose make goes away gets no `Mention` of
    /// the closure value at its entry (the value is not made).
    skip_mention: bool,
    /// The plan of the copy of a closure body that [`Inst::copy`] makes now
    /// (stages R0k-a2 and R0k-b1', [`Inst::closure_copy`]).
    run_plan: Option<RunPlan>,
    /// The number of copies of closure bodies that are copy regions (stage
    /// R0k-b1').
    regions: usize,
    /// The closures of the original program whose body a run got as a copy
    /// region (stage R0k-b1', [`weak_ok`]).
    copied: BTreeSet<ClosureId>,
    /// The ways of the values of the copy regions of each closure
    /// ([`sole_runs`]).
    chains: BTreeMap<ClosureId, BTreeSet<Link>>,
    /// The closure of the original program that each closure of a copy
    /// copies (plan stage R0z Z3). A closure of the original program is not
    /// in the map: it is its own origin.
    origin: BTreeMap<ClosureId, ClosureId>,
    /// The moves of the value of a `once` closure into the local of its copy
    /// region (plan stage R0z Z3, part d): the body, the block and the index
    /// of the statement. Such a move runs the closure, so a way of the value
    /// of another run does not see it as another use.
    run_moves: BTreeSet<(BodyId, BlockId, usize)>,
    /// The second sweep of plan stage R0z Z3, part a: a local of the way can
    /// get more than one value, each a copy of the same closure
    /// ([`Inst::walk_multi`]).
    multi: bool,
    /// The plan of the dispatch that [`Inst::copy`] makes now (plan stage R0z
    /// Z6, [`Inst::dispatch_plan`]).
    dplan: Option<DispatchPlan>,
    /// The blocks of the dispatches (the tests, the arm entries and the miss
    /// blocks): no later copy changes them (plan stage R0z Z6).
    no_copy: BTreeSet<(BodyId, BlockId)>,
    /// The number of runs that [`Inst::dispatch_plan`] looked at.
    dispatch_tries: std::cell::Cell<usize>,
    /// The calls of the pre-scan of Part B ([`Inst::clause_callees`]).
    clause_callees: BTreeSet<(BodyId, BlockId)>,
    /// The writes of each cell that [`Inst::walk_set`] looked at (plan stage
    /// R0z Z6), until the program changes ([`Inst::cell_writes_of`]).
    cell_writes: std::cell::RefCell<CellWrites>,
    /// The number of dispatches.
    dispatches: usize,
}

/// The writes of each cell of [`Inst::walk_set`]: the body and the local of
/// the cell, and the read that the walk follows.
type CellWrites = HashMap<
    (BodyId, LocalId, Option<(BodyId, BlockId, usize)>),
    Option<Vec<(BodyId, BlockId, usize)>>,
>;

/// The most groups of a dispatch (plan stage R0z Z6).
pub const DISPATCH_ARMS: usize = 4;

/// The most runs of one program that `Inst::dispatch_plan` looks at (plan
/// stage R0z Z6): the walk of the writes of a cell scans the bodies inside its
/// owner.
pub const DISPATCH_TRIES: usize = 64;

/// The plan of a dispatch (plan stage R0z Z6, [`Inst::dispatch_plan`]).
#[derive(Clone, Debug)]
struct DispatchPlan {
    /// Each arm, in the order of the tests: the closures of its group, the
    /// plan of the copy of the closure body (`None` for a plain arm: the call
    /// of the value stays), and the static check of a dead arm
    /// (`weft_ir::DispatchArm::killable`).
    arms: Vec<(Vec<ClosureId>, Option<RunPlan>, bool)>,
}

/// A leaf of the value set of a cell (plan stage R0z Z6, [`Inst::walk_set`]):
/// the way of a closure, and the write of the cell that gives it.
#[derive(Clone, Debug)]
struct Leaf {
    /// The way of the closure: a [`Source::Made`].
    walk: Walk,
    /// The write of the cell of the run (the body, the block, the statement).
    write: (BodyId, BlockId, usize),
}

/// The value set of the cell of a run (plan stage R0z Z6, [`Inst::walk_set`]).
#[derive(Clone, Debug)]
struct ValueSet {
    /// The body that owns the cell.
    owner: BodyId,
    /// The bodies from the body of the run to the owner (through upvar locals).
    bodies: Vec<BodyId>,
    /// The locals from the local of the run to the cell.
    chain: Vec<Link>,
    /// The leaves.
    leaves: Vec<Leaf>,
    /// Each write of the cell.
    writes: Vec<(BodyId, BlockId, usize)>,
}

/// The plan of a copy of a closure body at a run node (stages R0k-a2 and
/// R0k-b1', [`Inst::closure_copy`]).
#[derive(Clone, Debug)]
struct RunPlan {
    /// The closure whose body the run gets.
    closure: ClosureId,
    /// The body whose places the captures name: the maker of the closure.
    maker: BodyId,
    /// The static capability environment of the code of the copy: the
    /// environment where the closure is made, or for a closure that a callee
    /// makes, the environment of the call of the callee.
    env: CapEnvId,
    /// The run node is not in the maker body: the copy is a copy region, and
    /// its code runs with the handlers of the closure value.
    region: bool,
    /// The callee whose closure the run gets (a closure that a callee makes
    /// and gives back), for the chain of copied callees.
    callee: Option<FnId>,
    /// The locals that the value goes through, and the blocks of the performs
    /// that give it to a clause ([`Walk::chain`]).
    chain: Vec<Link>,
    /// The captures that the copy reads through the environment local of the
    /// region (plan stage R0k-b2, [`Inst::env_capture_ok`]): a cell that the
    /// closure value holds. The copy names each other capture through a
    /// place of the site.
    env_caps: BTreeSet<usize>,
    /// The closure that the cell of each such capture holds, if the copy
    /// knows it ([`weft_ir::CopyRegion::env_fns`]).
    env_fns: Vec<(u32, ClosureId)>,
    /// The other closures that the value can be (plan stage R0z Z3, part a:
    /// copies of the same closure, [`weft_ir::CopyRegion::also`]).
    also: Vec<ClosureId>,
    /// The run moves the value: a `once` closure (plan stage R0z Z3, parts d
    /// and e). The copy moves the value into a new local first, and the end
    /// of the region ends it.
    moves: bool,
    /// The number of blocks of the closure body and of the bodies inside it.
    size: usize,
}

/// Why [`Inst::plan_run`] gives no plan.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NoPlan {
    /// A rule refuses the copy.
    No,
    /// An arm of a dispatch whose closure needs no copy (plan stage R0z Z6):
    /// the arm keeps the call of the value.
    Plain,
}

/// A step of the way of the value of a run node ([`Walk::chain`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Link {
    /// The value is in local `l` of body `b`.
    Local(BodyId, LocalId),
    /// The perform at block `k` of body `b` gives the value to a clause.
    Perform(BodyId, BlockId),
}

/// Where the value of a run node comes from ([`Inst::walk_value`]).
#[derive(Clone, Debug)]
enum Source {
    /// A closure that statement `si` of block `blk` of body `body` makes.
    Made {
        body: BodyId,
        blk: BlockId,
        si: usize,
        closure: ClosureId,
    },
    /// The result of the call of function `callee` at block `blk` of body
    /// `body`: closure `closure`, which the callee makes and gives back.
    Call {
        body: BodyId,
        blk: BlockId,
        callee: FnId,
        closure: ClosureId,
    },
}

/// The way of the value of a run node ([`Inst::walk_value`]).
#[derive(Clone, Debug)]
struct Walk {
    /// Where the value comes from.
    source: Source,
    /// Each body that the value goes through, from the body of the run node.
    bodies: Vec<BodyId>,
    /// The value goes through a parameter of a clause: the body of the run
    /// node is not inside the maker.
    jumped: bool,
    /// The locals of the way, and the performs that give the value to a
    /// clause.
    chain: Vec<Link>,
}

/// The maps of one copy.
struct Copy {
    /// The first new local of the site body: local `l` of the callee is
    /// `local_base + l`.
    local_base: u32,
    /// The first new block of the site body: block `k` of the callee is
    /// `block_base + 1 + k`, and `block_base` is the entry of the copy.
    block_base: u32,
    bodies: BTreeMap<BodyId, BodyId>,
    closures: BTreeMap<ClosureId, ClosureId>,
    handlers: BTreeMap<HandlerId, HandlerId>,
    scopes: BTreeMap<ScopeId, ScopeId>,
    spawns: BTreeMap<SpawnId, SpawnId>,
    /// The environment of the call.
    call_env: CapEnvId,
    /// The root environment of the callee.
    root_env: CapEnvId,
    envs: BTreeMap<(CapEnvId, Option<ClosureId>), CapEnvId>,
    /// The closure of the copy that each body of the callee is inside (the
    /// closure itself for a closure body), or `None`.
    ctx: BTreeMap<BodyId, Option<ClosureId>>,
    /// The new `Cap` fields of each closure of the copy.
    extra: BTreeMap<ClosureId, Extra>,
    /// The chain of copied callees of the new code.
    chain: Vec<FnId>,
}

/// The new `Cap` fields of a closure of a copy.
#[derive(Clone, Debug)]
struct Extra {
    /// The body that makes the closure, in the copy.
    maker: BodyId,
    /// The environment of the maker where it makes the closure, in the copy.
    env: CapEnvId,
    /// The effect and the field of each new `Cap` field.
    fields: Vec<(EffectId, weft_ir::FieldIdx)>,
    /// The environment of the closure body in the callee.
    body_env: CapEnvId,
    /// The environment of the closure body in the copy.
    new_env: CapEnvId,
}

/// What a copy copies.
#[derive(Clone, Copy, Debug)]
enum What {
    /// The body of a function item at a call of it.
    Fn(FnId),
    /// The body of a closure at a call of a local that holds it.
    Closure(ClosureId),
    /// A dispatch at a call of a local that holds one of more closures (plan
    /// stage R0z Z6): [`Inst::dispatch`].
    Dispatch,
}

/// The function whose body is body `b` or a lexical parent of it.
fn fn_of(p: &Program, b: BodyId) -> Option<FnId> {
    let mut at = b;
    for _ in 0..=p.bodies.len() {
        let body = p.body(at)?;
        match body.kind {
            BodyKind::Fn(f) => return Some(f),
            _ => at = body.parent?,
        }
    }
    None
}

/// Why a copy cannot be made: the program keeps the call.
#[derive(Debug)]
struct NoCopy;

/// The map of the places of a copy: each local with `local`, and for the
/// copy of a closure body, a place of its environment `env.k..` with the
/// place of capture `k` in the site (`env`).
#[derive(Clone, Copy)]
struct PlaceMap<'a> {
    local: &'a dyn Fn(LocalId) -> LocalId,
    env: Option<(LocalId, &'a [Place])>,
}

impl<'a> PlaceMap<'a> {
    /// The map of the locals `local`.
    fn new(local: &'a dyn Fn(LocalId) -> LocalId) -> Self {
        Self { local, env: None }
    }

    /// Local `l` in the copy.
    fn l(&self, l: LocalId) -> LocalId {
        (self.local)(l)
    }

    /// Place `pl` in the copy.
    fn place(&self, pl: &Place) -> Place {
        let rest = |proj: &[Proj]| -> Vec<Proj> {
            proj.iter()
                .map(|x| match x {
                    Proj::Index(l) => Proj::Index(self.l(*l)),
                    other => other.clone(),
                })
                .collect()
        };
        if let Some((env, caps)) = self.env {
            if pl.local == env {
                if let Some(Proj::Field(k)) = pl.proj.first() {
                    if let Some(base) = caps.get(k.index()) {
                        let mut out = base.clone();
                        out.proj.extend(rest(pl.proj.get(1..).unwrap_or(&[])));
                        return out;
                    }
                }
            }
        }
        Place {
            local: self.l(pl.local),
            proj: rest(&pl.proj),
        }
    }
}

/// Changes each local of place `pl` with `f`.
fn map_place(pl: &Place, f: &PlaceMap<'_>) -> Place {
    f.place(pl)
}

fn map_operand(o: &Operand, f: &PlaceMap<'_>) -> Operand {
    match o {
        Operand::Copy(p) => Operand::Copy(map_place(p, f)),
        Operand::Move(p) => Operand::Move(map_place(p, f)),
        Operand::Const(c) => Operand::Const(c.clone()),
    }
}

/// The statement `s` with locals `f` and closures `cl`.
fn map_stmt(s: &Stmt, f: &PlaceMap<'_>, cl: &impl Fn(ClosureId) -> ClosureId) -> Stmt {
    let mp = |p: &Place| map_place(p, f);
    let mo = |o: &Operand| map_operand(o, f);
    let kind = match &s.kind {
        StmtKind::Live(l) => StmtKind::Live(f.l(*l)),
        StmtKind::Dead(l) => StmtKind::Dead(f.l(*l)),
        StmtKind::Assign(p, rv) => {
            let rv = match rv {
                Rvalue::Use(o) => Rvalue::Use(mo(o)),
                Rvalue::Ref(q) => Rvalue::Ref(mp(q)),
                Rvalue::Binary(op, t, a, b) => Rvalue::Binary(*op, *t, mo(a), mo(b)),
                Rvalue::Unary(op, t, a) => Rvalue::Unary(*op, *t, mo(a)),
                Rvalue::Aggregate(k, ops) => {
                    let k = match k {
                        weft_ir::AggKind::Closure(c) => weft_ir::AggKind::Closure(cl(*c)),
                        other => other.clone(),
                    };
                    Rvalue::Aggregate(k, ops.iter().map(mo).collect())
                }
                Rvalue::Len(q) => Rvalue::Len(mp(q)),
                Rvalue::Discriminant(q) => Rvalue::Discriminant(mp(q)),
                Rvalue::ClosureIs(q, cs) => {
                    Rvalue::ClosureIs(mp(q), cs.iter().map(|c| cl(*c)).collect())
                }
                Rvalue::Concat(ops) => Rvalue::Concat(ops.iter().map(mo).collect()),
                Rvalue::Iter(src) => Rvalue::Iter(match src {
                    weft_ir::IterSource::Elems(q) => weft_ir::IterSource::Elems(mp(q)),
                    weft_ir::IterSource::Range(a, b) => weft_ir::IterSource::Range(mo(a), mo(b)),
                }),
            };
            StmtKind::Assign(mp(p), rv)
        }
        StmtKind::Drop(p) => StmtKind::Drop(mp(p)),
        StmtKind::Consume(p) => StmtKind::Consume(mp(p)),
        StmtKind::Uninit(p) => StmtKind::Uninit(mp(p)),
        StmtKind::Bounds(p, o) => StmtKind::Bounds(mp(p), mo(o)),
        StmtKind::Mention(p) => StmtKind::Mention(mp(p)),
        StmtKind::Print(ops) => StmtKind::Print(ops.iter().map(mo).collect()),
        StmtKind::UnwindValue(p, a) => StmtKind::UnwindValue(mp(p), a.clone()),
        StmtKind::UnwindKont(l) => StmtKind::UnwindKont(f.l(*l)),
    };
    Stmt {
        kind,
        origin: s.origin,
    }
}

impl Inst<'_> {
    /// The chain of copied callees of block `k` of body `b`.
    fn chain(&self, b: BodyId, k: BlockId) -> Vec<FnId> {
        self.blk_chain
            .get(&(b, k))
            .or_else(|| self.body_chain.get(&b))
            .cloned()
            .unwrap_or_default()
    }

    /// The callee of the call at block `k` of body `b` if the call needs a
    /// copy: a local handler serves an operation that the callee performs
    /// through its row with a function value or a reference.
    fn wants(&self, b: BodyId, k: BlockId) -> Option<FnId> {
        let body = self.p.body(b)?;
        let blk = body.block(k)?;
        let TermKind::Call {
            callee: Callee::Fn(f, targs),
            caps: CapArgs::Lexical(env),
            unwind: Some(_),
            ..
        } = &blk.term.kind
        else {
            return None;
        };
        // A generic callee needs a type argument for each type parameter
        // (`can_copy`); the copy substitutes them (`subst_program`).
        let _ = targs;
        let served = self
            .needs
            .any
            .get(f)
            .is_some_and(|s| s.iter().any(|&e| env_binds(&self.p, *env, e)));
        let TermKind::Call { args, .. } = &blk.term.kind else {
            return None;
        };
        // A call that runs a clause whose write of a local of a way Z3 fix 3
        // refuses (plan stage R0z Z6, Part B, [`Inst::clause_callees`]).
        let clause = self.clause_callees.contains(&(b, k));
        (served || clause || self.weak_arg(b, k, args, *env)).then_some(*f)
    }

    /// True if an argument `args` of a call in body `b` with environment
    /// `env` is a whole local that holds a closure with the weak form, of an
    /// effect that `env` binds (plan stage R0z Z3, part g): the closure
    /// performs an operation with a function value or a reference through a
    /// captured capability ([`Inst::walk_value`]: one closure on each path).
    ///
    /// The guard of the analysis (`analysis::transfer::note_weak_call`)
    /// refuses such a call: the summary of the callee would run the weak
    /// summary of the closure where a local handler serves the effect. A copy
    /// of the callee at the call puts the run of the closure into `b`, where
    /// it can get a copy of the closure body.
    fn weak_arg(&self, b: BodyId, k: BlockId, args: &[Operand], env: CapEnvId) -> bool {
        args.iter().any(|o| {
            let Some(q) = o.place().filter(|q| q.is_local()) else {
                return false;
            };
            let except = matches!(o, Operand::Move(_)).then_some((k, usize::MAX));
            let Some(Walk {
                source: Source::Made { closure, .. },
                ..
            }) = self.walk_from(b, q.local, except)
            else {
                return false;
            };
            let Some(d) = self.p.closures.get(closure.index()) else {
                return false;
            };
            std::iter::once(d.body)
                .chain(inner_bodies(&self.p, d.body))
                .filter_map(|x| self.p.body(x))
                .any(|xb| {
                    xb.blocks.iter().any(|blk| match &blk.term.kind {
                        TermKind::Perform {
                            cap: CapOperand::Local(c),
                            op,
                            ..
                        } => {
                            weft_ir::print::cap_effect(&self.p, &self.tys, xb, c).is_some_and(|e| {
                                risky_op(&self.tys, e, *op).0 && env_binds(&self.p, env, e)
                            })
                        }
                        _ => false,
                    })
                })
        })
    }

    /// True if the call of `f` at block `k` of body `b` can get a copy.
    fn can_copy(&self, b: BodyId, k: BlockId, f: FnId) -> bool {
        let Some(d) = self.orig.fns.get(f.index()) else {
            return false;
        };
        let targs = match self
            .p
            .body(b)
            .and_then(|x| x.block(k))
            .map(|x| &x.term.kind)
        {
            Some(TermKind::Call {
                callee: Callee::Fn(_, ts),
                ..
            }) => ts.len(),
            _ => return false,
        };
        if d.generics as usize != targs || d.intrinsic.is_some() || d.body.is_none() {
            return false;
        }
        let chain = self.chain(b, k);
        if chain.len() >= self.bounds.depth || chain.contains(&f) || self.needs.recursive(f) {
            return false;
        }
        let Some(cb) = d.body else { return false };
        let size: usize = std::iter::once(cb)
            .chain(inner_bodies(self.orig, cb))
            .filter_map(|x| self.orig.body(x))
            .map(|x| x.blocks.len())
            .sum();
        self.added + size <= self.bounds.blocks
    }

    /// The plan of the copy of the closure body at the call of a function
    /// value at block `k` of body `b` (stage R0k-a2, the static closure copy,
    /// and stage R0k-b1', the copy region).
    ///
    /// The callee is `copy l`, and `l` holds one closure ([`Inst::walk_value`]):
    /// a closure that `b` makes (R0k-a2), or that a body around `b` makes, a
    /// body that gives it to an operation whose clause `b` is, or a callee
    /// that makes it and gives it back (R0k-b1'). The closure performs an
    /// operation with a function value or a reference that a local handler
    /// serves, or calls a callee that performs one.
    ///
    /// The copy is refused (the call keeps the summary of the closure) for
    /// another way to give `l` a value, a `move` or a borrow of `l`, a `once`
    /// closure, a `ByMove` or a `Kont` capture, a source of a `Kept` or a
    /// `ByRef` capture that ends or gets a new cell between the closure and
    /// the call, a use of the whole environment in the closure body, and a
    /// body inside the closure that names the environment.
    ///
    /// A copy region (the run node is not in the maker body) has two more
    /// rules (`docs/ir.md` 6.1, "As built (plan stage R0k-b1')"). The extent
    /// rule: each local handler that the environment of the closure binds
    /// for an effect that its code can use is around each body of the way of
    /// the value, so the handler instance of the make is the one of the run.
    /// The agreement rule: if the code of the closure has a terminator whose
    /// facts take the environment of the body (`join`, `fork`, `spawn`,
    /// `scope`), the environment of the closure and that of the body of the
    /// run node send each effect to the same destination.
    fn closure_copy(&self, b: BodyId, k: BlockId) -> Option<RunPlan> {
        let body = self.p.body(b)?;
        let TermKind::Call {
            callee: Callee::Value(op @ (Operand::Copy(callee) | Operand::Move(callee))),
            caps: CapArgs::Lexical(_),
            unwind: Some(_),
            ..
        } = &body.block(k)?.term.kind
        else {
            return None;
        };
        if !callee.is_local() {
            return None;
        }
        // A `move` of the value runs a `once` closure (plan stage R0z Z3,
        // parts d and e): the run is the one read of the value there.
        let moves = matches!(op, Operand::Move(_));
        let except = moves.then_some((k, usize::MAX));
        let (w, also) = match self.walk_from(b, callee.local, except) {
            Some(w) => (w, Vec::new()),
            None if self.multi => self.walk_multi((b, k), callee.local)?,
            None => return None,
        };
        self.plan_run((b, k), moves, w, also, false).ok()
    }

    /// The plan of a copy of a closure body at the run at block `k` of body
    /// `b` whose value has the way `w` ([`Inst::closure_copy`]), and the
    /// other closures `also` (plan stage R0z Z3). With `arm`, the run is an
    /// arm of a dispatch (plan stage R0z Z6, [`Inst::dispatch_plan`]): the
    /// copy is always a copy region that reads each capture but `Cap`
    /// through its environment local, and a closure that needs no copy (no
    /// served operation) gives [`NoPlan::Plain`], before each other check.
    fn plan_run(
        &self,
        (b, k): (BodyId, BlockId),
        moves: bool,
        w: Walk,
        also: Vec<ClosureId>,
        arm: bool,
    ) -> Result<RunPlan, NoPlan> {
        let body = self.p.body(b).ok_or(NoPlan::No)?;
        let (maker, cid, env, made, fcallee) = match &w.source {
            Source::Made {
                body: m,
                blk,
                si,
                closure,
            } => {
                let d = self.p.closures.get(closure.index()).ok_or(NoPlan::No)?;
                (*m, *closure, d.cap_env, Some((*blk, *si)), None)
            }
            Source::Call {
                body: m,
                blk,
                callee: f,
                closure,
            } => {
                let env = match &self
                    .p
                    .body(*m)
                    .and_then(|x| x.block(*blk))
                    .ok_or(NoPlan::No)?
                    .term
                    .kind
                {
                    TermKind::Call {
                        caps: CapArgs::Lexical(e),
                        ..
                    } => *e,
                    _ => return Err(NoPlan::No),
                };
                if self.chain(b, k).contains(f) {
                    return Err(NoPlan::No);
                }
                (*m, *closure, env, None, Some(*f))
            }
        };
        let decl = self.p.closures.get(cid.index()).ok_or(NoPlan::No)?;
        // A `once` closure runs with a `move` of its value; the copy moves
        // the value too (plan stage R0z Z3, part d).
        if decl.once != moves || (made.is_some() && decl.maker != maker) {
            return Err(NoPlan::No);
        }
        if decl.once && !self.once_ok(decl) {
            return Err(NoPlan::No);
        }
        let mut region = arm || maker != b || made.is_none() || !also.is_empty() || moves;
        let cb = self.p.body(decl.body).ok_or(NoPlan::No)?;
        let envl = *cb.params.first().ok_or(NoPlan::No)?;
        let inner = inner_bodies(&self.p, decl.body);
        let run_env = body.cap_env;
        // An arm of a dispatch: a closure that needs no copy keeps the call
        // (a plain arm), whatever the other checks give.
        if arm && !self.served(decl, &inner, true, run_env) {
            return Err(NoPlan::Plain);
        }
        // The captures. A capture that the copy cannot name through a place
        // of the site (a source that ends before the run, a source in the
        // frame of a callee, a `ByMove` capture) is a cell of the closure
        // value: the copy reads it through the environment local of the
        // region (plan stage R0k-b2). Then the copy is a region.
        let mut env_caps: BTreeSet<usize> = BTreeSet::new();
        for _ in 0..2 {
            env_caps.clear();
            for (ci, cap) in decl.captures.iter().enumerate() {
                // A region whose value can be more than one closure names
                // only a `Cap` capture through a place of the site; it reads
                // each other capture through the environment local.
                let direct = match &w.source {
                    Source::Made { .. }
                        if (also.is_empty() && !arm) || cap.mode == weft_ir::CaptureMode::Cap =>
                    {
                        self.direct_capture(cap, region, maker, made, (b, k), &w)
                    }
                    _ => false,
                };
                if direct {
                    continue;
                }
                if !self.env_capture_ok(&w.source, cid, decl, ci) {
                    return Err(NoPlan::No);
                }
                env_caps.insert(ci);
            }
            if env_caps.is_empty() || region {
                break;
            }
            region = true;
        }
        // No copy region inside another one: the code of the outer region
        // runs with the handlers of its own closure value. A copy in a region
        // is a part of it, so the closure must be made in the region too:
        // then it has the handlers of the region.
        if let Some(outer) = self.p.region_of(b, k) {
            let inner = made.is_some_and(|(mb, _)| outer.blocks.binary_search(&mb).is_ok());
            if region || !inner {
                return Err(NoPlan::No);
            }
        }
        // The environment: only its fields.
        if !body_places(cb)
            .iter()
            .all(|q| q.local != envl || matches!(q.proj.first(), Some(Proj::Field(_))))
        {
            return Err(NoPlan::No);
        }
        for &ib in &inner {
            let x = self.p.body(ib).ok_or(NoPlan::No)?;
            if x.parent == Some(decl.body)
                && x.locals.iter().any(|d| d.kind == LocalKind::Upvar(envl))
            {
                return Err(NoPlan::No);
            }
        }
        if !self.served(decl, &inner, region, run_env) {
            return Err(NoPlan::No);
        }
        if region
            && !(self.extent_ok(decl.body, env, &decl.captures, maker, &w.bodies)
                && self.agrees(decl.body, env, run_env))
        {
            return Err(NoPlan::No);
        }
        if !also.is_empty() && !self.also_ok(decl, env, &also, &env_caps, (b, k), &w) {
            return Err(NoPlan::No);
        }
        let size: usize = std::iter::once(decl.body)
            .chain(inner)
            .filter_map(|x| self.p.body(x))
            .map(|x| x.blocks.len())
            .sum();
        let env_fns = if also.is_empty() && !arm {
            self.env_fns(&w.source, decl, &env_caps, b)
        } else {
            Vec::new()
        };
        if self.added + size > self.bounds.blocks {
            return Err(NoPlan::No);
        }
        Ok(RunPlan {
            closure: cid,
            maker,
            env,
            region,
            callee: fcallee,
            chain: w.chain,
            env_fns,
            env_caps,
            also,
            moves,
            size,
        })
    }

    /// True if the code of the closure `decl` (its body and the bodies
    /// `inner` inside it) performs a served operation with a function value
    /// or a reference, or calls a callee that performs one: the run needs a
    /// copy. With `region`, an operation through the row is served if a local
    /// handler of the run node (environment `run_env`) handles it: the
    /// summary of the closure at the run node gives it to that handler.
    fn served(
        &self,
        decl: &weft_ir::ClosureDecl,
        inner: &[BodyId],
        region: bool,
        run_env: CapEnvId,
    ) -> bool {
        // The closure performs a served operation with a function value or a
        // reference, or calls a callee that performs one. In a copy region,
        // an operation through the row is served if a local handler of the
        // run node handles it: the summary of the closure at the run node
        // gives it to that handler.
        let bound = |e: EffectId, env: CapEnvId| {
            env_binds(&self.p, env, e) || (region && env_binds(&self.p, run_env, e))
        };
        let mut served = false;
        for x in std::iter::once(decl.body).chain(inner.iter().copied()) {
            let Some(xb) = self.p.body(x) else { continue };
            for blk in &xb.blocks {
                match &blk.term.kind {
                    TermKind::Perform {
                        cap: CapOperand::Local(q),
                        op,
                        ..
                    } => {
                        // In a copy region, each operation through a captured
                        // capability: the summary of the closure at a run node
                        // in a clause or an inner handled body does not find
                        // the rest of the handled body of the perform (F17).
                        if let Some(e) = weft_ir::print::cap_effect(&self.p, &self.tys, xb, q) {
                            served |= region || risky_op(&self.tys, e, *op).0;
                        }
                    }
                    TermKind::Perform {
                        cap: CapOperand::Row(e),
                        op,
                        ..
                    } if region => {
                        served |= risky_op(&self.tys, *e, *op).0 && env_binds(&self.p, run_env, *e);
                    }
                    TermKind::Call {
                        callee: Callee::Fn(g, _),
                        caps: CapArgs::Lexical(e),
                        ..
                    } => {
                        served |= self
                            .needs
                            .any
                            .get(g)
                            .is_some_and(|s| s.iter().any(|&x| bound(x, *e)));
                    }
                    _ => {}
                }
            }
        }
        served
    }

    /// True if the copy of the body of the `once` closure `decl` can run
    /// (plan stage R0z Z3, parts d and e): each capture that is not `Cap` is
    /// `ByMove` or `Kept`, and its type has no linear, `once` or resource
    /// value. The copy moves the value of the closure into a new local and
    /// reads such a capture through the environment local: the closure body
    /// moves it, or copies it.
    fn once_ok(&self, decl: &weft_ir::ClosureDecl) -> bool {
        let Some(cb) = self.p.body(decl.body) else {
            return false;
        };
        let Some(&envl) = cb.params.first() else {
            return false;
        };
        let Some(cid) = self
            .p
            .closures
            .iter()
            .position(|d| d.body == decl.body)
            .and_then(|i| u32::try_from(i).ok())
            .map(ClosureId)
        else {
            return false;
        };
        decl.captures.iter().enumerate().all(|(ci, cap)| {
            let Ok(field) = u32::try_from(ci) else {
                return false;
            };
            match cap.mode {
                weft_ir::CaptureMode::Cap => true,
                weft_ir::CaptureMode::ByMove | weft_ir::CaptureMode::Kept => {
                    let mut tys = self.tys.clone();
                    crate::factgen::alpha::capture_ty(&self.p, &mut tys, cid, field).is_some_and(
                        |t| {
                            let pr = crate::props::ir_props(&self.tys, t);
                            !pr.linear && !pr.once && !pr.immovable
                        },
                    ) && whole_reads_only(cb, envl, field)
                }
                _ => false,
            }
        })
    }

    /// True if each closure of `also` can stand for the closure `decl` at
    /// the copy region of the run at block `k` of body `b` (plan stage R0z
    /// Z3, part a; [`Inst::walk_multi`] gives `also`). Each one is a copy of
    /// the same closure ([`Inst::walk_multi`] checks the origin), it has the
    /// captures of `decl` (the same modes, and for a `Cap` capture the same
    /// capability of the site), each capture that is not `Cap` can be read
    /// through the environment local ([`Inst::env_capture_ok`]), its
    /// environment sends each effect to the destination of `env`, and the
    /// extent rule holds for it ([`Inst::extent_ok`]).
    fn also_ok(
        &self,
        decl: &weft_ir::ClosureDecl,
        env: CapEnvId,
        also: &[ClosureId],
        env_caps: &BTreeSet<usize>,
        (b, k): (BodyId, BlockId),
        w: &Walk,
    ) -> bool {
        let cap_root = |d: &weft_ir::ClosureDecl, c: &weft_ir::Capture| {
            root_place(&self.p, d.maker, &c.source)
        };
        for &a in also {
            let Some(ad) = self.p.closures.get(a.index()) else {
                return false;
            };
            if ad.once != decl.once || ad.captures.len() != decl.captures.len() {
                return false;
            }
            for (ci, (x, y)) in ad.captures.iter().zip(&decl.captures).enumerate() {
                if x.mode != y.mode {
                    return false;
                }
                if x.mode == weft_ir::CaptureMode::Cap {
                    let made = None;
                    if env_caps.contains(&ci)
                        || cap_root(ad, x) != cap_root(decl, y)
                        || !self.direct_capture(x, true, ad.maker, made, (b, k), w)
                    {
                        return false;
                    }
                } else {
                    let src = Source::Made {
                        body: ad.maker,
                        blk: BlockId(0),
                        si: 0,
                        closure: a,
                    };
                    if !env_caps.contains(&ci) || !self.env_capture_ok(&src, a, ad, ci) {
                        return false;
                    }
                }
            }
            let same = self.tys.effects().iter().all(|d| {
                super::frames::resolve(&self.p, &self.tys, env, &d.identity, true)
                    == super::frames::resolve(&self.p, &self.tys, ad.cap_env, &d.identity, true)
            });
            if !same || !self.extent_ok(ad.body, ad.cap_env, &ad.captures, ad.maker, &w.bodies) {
                return false;
            }
        }
        self.one_clause_node(decl, (b, k))
    }

    /// True if each operation with a function value or a reference that the
    /// code of the closure `decl` gives to a clause can run that clause at no
    /// other node than the copy at the run at block `k` of body `b` (plan
    /// stage R0z Z3, fix 2).
    ///
    /// The facts of a clause join the values of its parameters over each node
    /// that runs it. So with two nodes, the value that a region with more
    /// closures gives to the clause joins the references of one closure with
    /// those of another one, and a clause that keeps its parameter gets a
    /// false W0301 (issue #79; the same false W0301 is in the program with two
    /// locals). A region whose value can be more than one closure is refused
    /// then, and the program keeps its fallback. The operation must go through
    /// a captured capability of a local handler H: an operation through the
    /// row refuses the region. Another node that can run the clause of H is a
    /// perform of the operation through the capability of H in any body, and,
    /// in a body inside the handled body of H, a perform of the effect through
    /// the row, a call of a callee that can perform the effect, and a call of a
    /// function value whose row can have the effect (the other runs of the
    /// local of the way too). A perform through the environment of a closure
    /// body runs where the closure runs, so the calls count for it.
    fn one_clause_node(&self, decl: &weft_ir::ClosureDecl, (b, k): (BodyId, BlockId)) -> bool {
        let Some(cb) = self.p.body(decl.body) else {
            return false;
        };
        for blk in &cb.blocks {
            let TermKind::Perform { cap, op, .. } = &blk.term.kind else {
                continue;
            };
            let e = match cap {
                CapOperand::Local(q) => weft_ir::print::cap_effect(&self.p, &self.tys, cb, q),
                CapOperand::Row(e) => Some(*e),
            };
            let Some(e) = e else { return false };
            if !risky_op(&self.tys, e, *op).0 {
                continue;
            }
            // The capability of the local handler: a `Cap` capture.
            let CapOperand::Local(q) = cap else {
                return false;
            };
            let Some(Proj::Field(f)) = q.proj.first() else {
                return false;
            };
            let Some(c) = decl
                .captures
                .get(f.index())
                .filter(|c| c.mode == weft_ir::CaptureMode::Cap)
            else {
                return false;
            };
            let Some((hb, capl)) = root_place(&self.p, decl.maker, &c.source) else {
                return false;
            };
            if self.clause_sites(hb, &capl, (e, *op), (b, k)) > 0 {
                return false;
            }
        }
        true
    }

    /// The refusals R-JOIN and R-REF of a copy arm of a dispatch (plan stage
    /// R0z Z6, rounds 1 and 2 of the review). `all` is each closure of the
    /// dispatch: the code of their bodies (and of the bodies inside them) is the
    /// node of the dispatch, at the run at block `k` of body `b`. Each operation
    /// with a function value or a reference that the code of the closure `decl`
    /// performs through a captured capability of a local handler H (a `Cap`
    /// capture) is checked. In the handled body of H (and in each body inside
    /// it but those of the dispatch):
    ///
    /// - R-JOIN: another node can run the clause of the operation: a perform
    ///   of the operation through the capability of H (in any body), a perform of
    ///   the effect through the row, a call of a callee that can perform the
    ///   effect (`Needs::row`) or that gets a function value of the site
    ///   ([`Inst::fn_runs_values`]), or a run of a function value
    ///   whose value can perform it through a capture of the capability of H, or
    ///   whose value the walk does not know. The facts of the clause join its
    ///   parameter over the nodes, and the value of one node reaches the changes
    ///   after the other one (the false W0301 of issue #79).
    /// - R-REF: a run of a function value whose value can hold a reference (a
    ///   capture of a reference, of a type that holds one or a function value, a
    ///   `ByRef` capture, or a value that the walk does not know), or a call of a
    ///   callee that can run a function value. After such a run the facts of the
    ///   perform of the copy give the clause the places below that reference
    ///   ("run: gets v.., and it can mutate through it"): a false W0301 that main
    ///   gives for a region with one value.
    ///
    /// A run of a parameter of a clause that no node can run does not count
    /// ([`Inst::clause_runs_nowhere`]).
    fn arm_join_refused(
        &self,
        decl: &weft_ir::ClosureDecl,
        (b, k): (BodyId, BlockId),
        all: &[ClosureId],
    ) -> bool {
        let Some(cb) = self.p.body(decl.body) else {
            return true;
        };
        // The bodies of the dispatch.
        let mut own: BTreeSet<BodyId> = BTreeSet::new();
        for c in all {
            if let Some(d) = self.p.closures.get(c.index()) {
                own.insert(d.body);
                own.extend(inner_bodies(&self.p, d.body));
            }
        }
        for blk in &cb.blocks {
            let TermKind::Perform {
                cap: CapOperand::Local(q),
                op,
                ..
            } = &blk.term.kind
            else {
                continue;
            };
            let Some(e) = weft_ir::print::cap_effect(&self.p, &self.tys, cb, q) else {
                return true;
            };
            if !risky_op(&self.tys, e, *op).0 {
                continue;
            }
            let Some(Proj::Field(f)) = q.proj.first() else {
                continue;
            };
            let Some(c) = decl
                .captures
                .get(f.index())
                .filter(|c| c.mode == weft_ir::CaptureMode::Cap)
            else {
                continue;
            };
            let Some((hb, capl)) = root_place(&self.p, decl.maker, &c.source) else {
                return true;
            };
            let to_h = |c: &weft_ir::ClosureDecl| {
                let Some(xb) = self.p.body(c.body) else {
                    return true;
                };
                xb.blocks.iter().any(|x| match &x.term.kind {
                    TermKind::Perform {
                        cap: CapOperand::Local(q2),
                        op: o2,
                        ..
                    } if o2 == op => match q2.proj.first() {
                        Some(Proj::Field(f2)) => c.captures.get(f2.index()).is_some_and(|cc| {
                            cc.mode == weft_ir::CaptureMode::Cap
                                && root_place(&self.p, c.maker, &cc.source)
                                    .is_some_and(|(a, pl)| a == hb && pl.local == capl.local)
                        }),
                        _ => false,
                    },
                    _ => false,
                })
            };
            for (bi, x) in self.p.bodies.iter().enumerate() {
                let id = BodyId(u32::try_from(bi).unwrap_or(u32::MAX));
                let under = (id == hb || inside(&self.p, id, hb)) && !own.contains(&id);
                for (ki, xblk) in x.blocks.iter().enumerate() {
                    let kid = BlockId(u32::try_from(ki).unwrap_or(u32::MAX));
                    if (id, kid) == (b, k) {
                        continue;
                    }
                    match &xblk.term.kind {
                        TermKind::Perform {
                            cap: CapOperand::Local(q2),
                            op: o2,
                            ..
                        } if o2 == op => {
                            if root_place(&self.p, id, q2)
                                .is_some_and(|(a, pl)| a == hb && pl.local == capl.local)
                            {
                                return true;
                            }
                        }
                        TermKind::Perform {
                            cap: CapOperand::Row(e2),
                            ..
                        } if under && *e2 == e => return true,
                        TermKind::Call {
                            callee: Callee::Fn(g, _),
                            args,
                            ..
                        } if under => {
                            // A callee runs the clause through its row, or runs a
                            // function value of the site (also one with no known
                            // row: `Needs::unknown`). Its own closures perform
                            // through its row.
                            if self.needs.row.get(g).is_some_and(|r| r.contains(&e))
                                || self.fn_runs_values(*g, x, args)
                            {
                                return true;
                            }
                        }
                        TermKind::Call {
                            callee: Callee::Value(o),
                            ..
                        } if under => {
                            let Some(v) = o.place().filter(|v| v.is_local()) else {
                                return true;
                            };
                            if self.clause_param_runs_nowhere(id, v.local) {
                                continue;
                            }
                            let closures: Option<Vec<ClosureId>> =
                                match self.walk_value(id, v.local) {
                                    Some(Walk {
                                        source: Source::Made { closure, .. },
                                        ..
                                    }) => Some(vec![closure]),
                                    Some(_) => None,
                                    None => self
                                        .walk_set((id, kid), id, v.local, 0, None, None)
                                        .map(|set| {
                                            set.leaves
                                                .iter()
                                                .filter_map(|l| match l.walk.source {
                                                    Source::Made { closure, .. } => Some(closure),
                                                    Source::Call { .. } => None,
                                                })
                                                .collect()
                                        }),
                                };
                            // An unknown value can do each of it (R-JOIN, R-REF).
                            let Some(closures) = closures else {
                                return true;
                            };
                            let decls: Vec<&weft_ir::ClosureDecl> = closures
                                .iter()
                                .filter_map(|c| self.p.closures.get(c.index()))
                                .collect();
                            if decls.len() != closures.len()
                                || decls.iter().any(|c| to_h(c) || self.closure_holds_refs(c))
                            {
                                return true;
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        false
    }

    /// True if a value of closure `c` can hold a reference (plan stage R0z Z6,
    /// R-REF): a `ByRef` capture, a `Kont` capture, or a `Kept` or `ByMove`
    /// capture whose type is a reference, holds one, or holds a function value.
    fn closure_holds_refs(&self, c: &weft_ir::ClosureDecl) -> bool {
        c.captures.iter().any(|x| match x.mode {
            weft_ir::CaptureMode::Cap => false,
            weft_ir::CaptureMode::ByRef | weft_ir::CaptureMode::Kont => true,
            _ => {
                let ty = super::alpha::place_ty(&self.p, &mut self.tys.clone(), c.maker, &x.source);
                ty.is_none_or(|t| {
                    crate::analysis::sig::is_ref(&self.tys, t)
                        || crate::analysis::sig::holds_refs(&self.tys, t)
                        || crate::props::ir_has_fns(&self.tys, t)
                })
            }
        })
    }

    /// True if the call of function `g` in body `x` with the arguments `args`
    /// can run a function value of the site (plan stage R0z Z6, R-REF): an
    /// argument is a function value or holds one (a place with no type counts).
    /// A closure that the callee makes and runs itself is a part of its summary,
    /// not a run of the site (`z6rev2/b/b03`).
    fn fn_runs_values(&self, _g: FnId, x: &Body, args: &[Operand]) -> bool {
        args.iter().any(|a| match a {
            Operand::Copy(q) | Operand::Move(q) => {
                let ty = if q.is_local() {
                    x.local(q.local).map(|l| l.ty)
                } else {
                    None
                };
                ty.is_none_or(|t| crate::props::ir_has_fns(&self.tys, t))
            }
            Operand::Const(weft_ir::Const::Fn(..)) => true,
            Operand::Const(_) => false,
        })
    }

    /// True if local `l` of body `x` is a parameter of a clause that no node
    /// can run (plan stage R0z Z6): no perform of the operation through the
    /// capability of the handler, no perform of the effect through the row in
    /// its handled body, no call there of a callee or a function value that can
    /// perform the effect (a run whose value has an exact way to closures that
    /// do not perform it does not count).
    fn clause_param_runs_nowhere(&self, x: BodyId, l: LocalId) -> bool {
        let Some(xb) = self.p.body(x) else {
            return false;
        };
        let (BodyKind::Clause(h, op), Some(LocalKind::Param(_))) = (xb.kind, xb.local_kind(l))
        else {
            return false;
        };
        let Some(hd) = self.p.handlers.get(h.index()) else {
            return false;
        };
        let Some(&(eff, cap)) = self.p.body(hd.handled).and_then(|y| y.caps.first()) else {
            return false;
        };
        let performs = |c: &weft_ir::ClosureDecl| {
            std::iter::once(c.body)
                .chain(inner_bodies(&self.p, c.body))
                .any(|y| {
                    self.p.body(y).is_none_or(|yb| {
                        yb.blocks.iter().any(|blk| match &blk.term.kind {
                            TermKind::Perform {
                                cap: CapOperand::Row(e),
                                ..
                            } => *e == eff,
                            TermKind::Perform {
                                cap: CapOperand::Local(q),
                                ..
                            } => {
                                // A captured capability names one handler.
                                let field = match q.proj.first() {
                                    Some(Proj::Field(f)) if y == c.body => {
                                        c.captures.get(f.index())
                                    }
                                    _ => None,
                                };
                                match field {
                                    Some(cc) if cc.mode == weft_ir::CaptureMode::Cap => root_place(
                                        &self.p, c.maker, &cc.source,
                                    )
                                    .is_none_or(|(a, pl)| a == hd.handled && pl.local == cap),
                                    _ => weft_ir::print::cap_effect(&self.p, &self.tys, yb, q)
                                        .is_none_or(|e| e == eff),
                                }
                            }
                            TermKind::Call {
                                callee: Callee::Fn(g, _),
                                ..
                            } => {
                                self.needs.unknown.contains(g)
                                    || self.needs.row.get(g).is_some_and(|r| r.contains(&eff))
                            }
                            TermKind::Call { .. } => true,
                            _ => false,
                        })
                    })
                })
        };
        for (bi, y) in self.p.bodies.iter().enumerate() {
            let id = BodyId(u32::try_from(bi).unwrap_or(u32::MAX));
            let under = id == hd.handled || inside(&self.p, id, hd.handled);
            for (ki, blk) in y.blocks.iter().enumerate() {
                let kid = BlockId(u32::try_from(ki).unwrap_or(u32::MAX));
                match &blk.term.kind {
                    TermKind::Perform {
                        cap: CapOperand::Local(q),
                        op: o,
                        ..
                    } => {
                        let to_h = root_place(&self.p, id, q)
                            .is_some_and(|(a, pl)| a == hd.handled && pl.local == cap);
                        if (to_h && *o == op)
                            || (under
                                && !to_h
                                && weft_ir::print::cap_effect(&self.p, &self.tys, y, q)
                                    .is_none_or(|e| e == eff))
                        {
                            return false;
                        }
                    }
                    TermKind::Perform {
                        cap: CapOperand::Row(e),
                        ..
                    } if under && *e == eff => return false,
                    TermKind::Call {
                        callee: Callee::Fn(g, _),
                        ..
                    } if under => {
                        if self.needs.unknown.contains(g)
                            || self.needs.row.get(g).is_some_and(|r| r.contains(&eff))
                        {
                            return false;
                        }
                    }
                    TermKind::Call {
                        callee: Callee::Value(o),
                        ..
                    } if under => {
                        let Some(v) = o.place().filter(|v| v.is_local()) else {
                            return false;
                        };
                        let closures: Option<Vec<ClosureId>> = match self.walk_value(id, v.local) {
                            Some(Walk {
                                source: Source::Made { closure, .. },
                                ..
                            }) => Some(vec![closure]),
                            Some(_) => None,
                            None => {
                                self.walk_set((id, kid), id, v.local, 0, None, None)
                                    .map(|set| {
                                        set.leaves
                                            .iter()
                                            .filter_map(|lf| match lf.walk.source {
                                                Source::Made { closure, .. } => Some(closure),
                                                Source::Call { .. } => None,
                                            })
                                            .collect()
                                    })
                            }
                        };
                        let Some(closures) = closures else {
                            return false;
                        };
                        if closures
                            .iter()
                            .any(|c| self.p.closures.get(c.index()).is_none_or(&performs))
                        {
                            return false;
                        }
                    }
                    TermKind::Spawn { .. } | TermKind::Fork { .. } if under => return false,
                    _ => {}
                }
            }
        }
        // A closure that captures the capability of the handler can perform
        // the operation where it runs.
        !self.p.closures.iter().any(|d| {
            d.captures.iter().any(|c| {
                c.mode == weft_ir::CaptureMode::Cap
                    && root_place(&self.p, d.maker, &c.source)
                        .is_some_and(|(a, pl)| a == hd.handled && pl.local == cap)
            })
        })
    }

    /// The number of the nodes but the run at block `k` of body `b` that can
    /// run the clause of operation `op` of effect `e` of the local handler
    /// whose handled body is `hb` and whose capability is `cap`
    /// ([`Inst::one_clause_node`]).
    fn clause_sites(
        &self,
        hb: BodyId,
        cap: &Place,
        (e, op): (EffectId, OpIdx),
        (b, k): (BodyId, BlockId),
    ) -> usize {
        let mut n = 0usize;
        for (bi, x) in self.p.bodies.iter().enumerate() {
            let id = BodyId(u32::try_from(bi).unwrap_or(u32::MAX));
            let under = inside(&self.p, id, hb);
            for (ki, blk) in x.blocks.iter().enumerate() {
                let kid = BlockId(u32::try_from(ki).unwrap_or(u32::MAX));
                if (id, kid) == (b, k) {
                    continue;
                }
                match &blk.term.kind {
                    TermKind::Perform {
                        cap: CapOperand::Local(q),
                        op: o,
                        ..
                    } => {
                        let root = root_place(&self.p, id, q);
                        let to_h = root.as_ref().is_some_and(|(a, pl)| *a == hb && pl == cap);
                        // A perform through the environment of a closure runs
                        // where the closure runs: a call of a function value.
                        let env = root.as_ref().is_some_and(|(a, pl)| {
                            body_kind_of(&self.p, *a, pl.local) == Some(LocalKind::Env)
                        });
                        let same = weft_ir::print::cap_effect(&self.p, &self.tys, x, q) == Some(e);
                        n += usize::from((to_h && *o == op) || (under && same && !to_h && !env));
                    }
                    TermKind::Perform {
                        cap: CapOperand::Row(e2),
                        ..
                    } if under => n += usize::from(*e2 == e),
                    TermKind::Call { callee, .. } if under => {
                        let can = match callee {
                            Callee::Fn(g, _) => {
                                self.needs.unknown.contains(g)
                                    || self.needs.row.get(g).is_some_and(|r| r.contains(&e))
                            }
                            Callee::Value(o) => {
                                value_row(&self.tys, x, o).is_none_or(|r| r.contains(&e))
                            }
                        };
                        n += usize::from(can);
                    }
                    _ => {}
                }
            }
        }
        n
    }

    /// The closure that the cell of each capture of `env_caps` holds, if one
    /// closure of the function of body `site` gives the cell its one value
    /// (plan stage R0k-b2, [`weft_ir::CopyRegion::env_fns`]).
    fn env_fns(
        &self,
        source: &Source,
        decl: &weft_ir::ClosureDecl,
        env_caps: &BTreeSet<usize>,
        site: BodyId,
    ) -> Vec<(u32, ClosureId)> {
        let mut out = Vec::new();
        let Source::Made { .. } = source else {
            return out;
        };
        for &ci in env_caps {
            let Some(cap) = decl.captures.get(ci) else {
                continue;
            };
            if cap.mode != weft_ir::CaptureMode::Kept {
                continue;
            }
            let Some((a, src)) = root_place(&self.p, decl.maker, &cap.source) else {
                continue;
            };
            let Some(Walk {
                source: Source::Made { closure, .. },
                ..
            }) = self.walk_value(a, src.local)
            else {
                continue;
            };
            let same = self.p.closures.get(closure.index()).is_some_and(|d| {
                fn_of(&self.p, d.body).is_some() && fn_of(&self.p, d.body) == fn_of(&self.p, site)
            });
            if let (true, Ok(k)) = (same, u32::try_from(ci)) {
                out.push((k, closure));
            }
        }
        out
    }

    /// True if the copy of a closure body at the run at block `k` of body `b`
    /// can name capture `cap` through a place of the site (stages R0k-a2 and
    /// R0k-b1'): a `Kept` or a `ByRef` capture is its source, through upvar
    /// locals, and a `Cap` capture the capability of a local handler around
    /// the run node. The source must be a cell of a body around the maker, or
    /// of the maker if the source does not end or get a new cell between the
    /// make and the terminator of the maker that runs the body of the run
    /// node.
    fn direct_capture(
        &self,
        cap: &weft_ir::Capture,
        region: bool,
        maker: BodyId,
        made: Option<(BlockId, usize)>,
        (b, k): (BodyId, BlockId),
        w: &Walk,
    ) -> bool {
        match cap.mode {
            weft_ir::CaptureMode::Cap if !region => true,
            weft_ir::CaptureMode::Cap => {
                // The capability of a local handler around the run node.
                let Some((a, _)) = root_place(&self.p, maker, &cap.source) else {
                    return false;
                };
                upvar_path(&self.p, b, a) && w.bodies.iter().all(|&x| inside(&self.p, x, a))
            }
            weft_ir::CaptureMode::Kept | weft_ir::CaptureMode::ByRef => {
                if cap.source.has_deref() {
                    return false;
                }
                let Some((a, src)) = root_place(&self.p, maker, &cap.source) else {
                    return false;
                };
                if region && !upvar_path(&self.p, b, a) {
                    return false;
                }
                if a != maker {
                    // The cell of a body around the maker: it does not end
                    // while the maker runs.
                    return true;
                }
                if w.jumped {
                    return false;
                }
                let Some((mb, mi)) = made else { return false };
                let Some(mbody) = self.p.body(maker) else {
                    return false;
                };
                // The block of the maker that runs the body of the run node
                // (the run node itself in the maker).
                let gate = if maker == b {
                    k
                } else {
                    match gateway(&self.p, maker, b) {
                        Some(g) => g,
                        None => return false,
                    }
                };
                let (fwd, bwd) = (reach(mbody, mb, true), reach(mbody, gate, false));
                for (bi, blk) in mbody.blocks.iter().enumerate() {
                    if !(fwd.get(bi).copied().unwrap_or(false)
                        && bwd.get(bi).copied().unwrap_or(false))
                    {
                        continue;
                    }
                    for (si, st) in blk.stmts.iter().enumerate() {
                        if bi == mb.index() && si <= mi {
                            continue;
                        }
                        if matches!(st.kind, StmtKind::Dead(x) | StmtKind::Live(x) if x == src.local)
                        {
                            return false;
                        }
                    }
                }
                true
            }
            weft_ir::CaptureMode::ByMove | weft_ir::CaptureMode::Kont => false,
        }
    }

    /// True if the copy of the body of closure `decl` can read capture `ci`
    /// through the environment local of a copy region (plan stage R0k-b2):
    /// the cell that the closure value holds.
    ///
    /// The capture is `Kept` (or `ByMove`), of a type with no linear value,
    /// and the closure body reads it only as a whole copy (`copy e.k`). The
    /// cell does not change after the make: for a `Kept` capture, its source
    /// is a whole local that gets at most one value, and no statement or body
    /// moves, borrows or writes it in another way. Then the value of the cell
    /// is the value at the make, and the references of the closure value are
    /// its references (`analysis::transfer`: the value of `e.k`).
    fn env_capture_ok(
        &self,
        source: &Source,
        cid: ClosureId,
        decl: &weft_ir::ClosureDecl,
        ci: usize,
    ) -> bool {
        let Some(cap) = decl.captures.get(ci) else {
            return false;
        };
        if cap.source.has_deref() {
            return false;
        }
        let Some(cb) = self.p.body(decl.body) else {
            return false;
        };
        let Some(&envl) = cb.params.first() else {
            return false;
        };
        let Ok(field) = u32::try_from(ci) else {
            return false;
        };
        // The body of a `once` closure can move a capture (plan stage R0z
        // Z3, parts d and e): the run moves the value of the closure.
        let reads = if decl.once {
            self.once_ok(decl) && whole_reads_only(cb, envl, field)
        } else {
            copy_reads_only(cb, envl, field)
        };
        if !reads {
            return false;
        }
        let mut tys = self.tys.clone();
        let Some(t) = crate::factgen::alpha::capture_ty(&self.p, &mut tys, cid, field) else {
            return false;
        };
        if crate::props::ir_props(&self.tys, t).linear {
            return false;
        }
        match cap.mode {
            weft_ir::CaptureMode::ByMove => true,
            weft_ir::CaptureMode::Kept => {
                // The cell of the variable: a whole local of the maker, or of
                // a body around it, that does not change after the make.
                let maker = match source {
                    Source::Made { .. } => decl.maker,
                    Source::Call { callee, .. } => {
                        match self.p.fns.get(callee.index()).and_then(|d| d.body) {
                            Some(fb) if fb == decl.maker => fb,
                            _ => return false,
                        }
                    }
                };
                let Some((a, src)) = root_place(&self.p, maker, &cap.source) else {
                    return false;
                };
                src.proj.is_empty() && cell_constant(&self.p, a, src.local)
            }
            _ => false,
        }
    }

    /// The way of the value of local `l` of body `b` up to the closure that
    /// it holds (stage R0k-b1'). Each step is exact, so the value at the run
    /// node is always that closure:
    ///
    /// - a local with one value ([`single_value`]): a closure that the body
    ///   makes, or a copy of another whole local;
    /// - an upvar local: the local of the parent body;
    /// - a parameter of a clause that its body does not write, move or
    ///   borrow: the argument of the one perform that can run the clause
    ///   ([`Inst::clause_arg`]);
    /// - a local that one call of a function item gives a value, if the
    ///   callee gives back one closure that it makes, with no capture
    ///   ([`ret_closure`]).
    ///
    /// A body inside a body on the way must not write, move or borrow the
    /// local there ([`nested_writes`]).
    fn walk_value(&self, b: BodyId, l: LocalId) -> Option<Walk> {
        self.walk_from(b, l, None)
    }

    /// [`Inst::walk_value`], where `except` is the one read of the value of
    /// `l` (a `move` of it at a statement, or at a terminator with the index
    /// `usize::MAX`).
    fn walk_from(&self, b: BodyId, l: LocalId, except: Option<(BlockId, usize)>) -> Option<Walk> {
        let (mut x, mut at) = (b, l);
        let mut bodies = vec![b];
        let mut jumped = false;
        let mut except = except;
        let mut chain: Vec<Link> = Vec::new();
        // The part of the value of `at` that holds the closure (plan stage
        // R0k-b2, form 3): the field and variant steps from the value of
        // `at` down to the closure. Empty for the whole value.
        let mut path: Vec<Proj> = Vec::new();
        for _ in 0..32 {
            let body = self.p.body(x)?;
            chain.push(Link::Local(x, at));
            match body.local_kind(at)? {
                LocalKind::Upvar(s) => {
                    if !body.kind.has_upvars() {
                        return None;
                    }
                    x = body.parent?;
                    at = s;
                    except = None;
                    bodies.push(x);
                    continue;
                }
                LocalKind::Param(i) if matches!(body.kind, BodyKind::Clause(..)) => {
                    if nested_writes_but(&self.p, x, at, &self.run_moves) || !param_kept(body, at) {
                        return None;
                    }
                    let (y, blk, arg) = self.clause_arg(x, i)?;
                    chain.push(Link::Perform(y, blk));
                    let q = arg.place().filter(|q| q.is_local())?;
                    x = y;
                    at = q.local;
                    // A `move` of the argument at the perform is the one read
                    // of the value (the index of the terminator).
                    except = matches!(arg, Operand::Move(_)).then_some((blk, usize::MAX));
                    jumped = true;
                    bodies.push(x);
                    continue;
                }
                _ => {}
            }
            if nested_writes_but(&self.p, x, at, &self.run_moves) {
                return None;
            }
            if let Some(blk) = call_value_of(body, at, except) {
                let TermKind::Call {
                    callee: Callee::Fn(f, ts),
                    caps: CapArgs::Lexical(_),
                    ..
                } = &body.block(blk)?.term.kind
                else {
                    return None;
                };
                if !ts.is_empty() || self.needs.recursive(*f) {
                    return None;
                }
                let c = ret_closure(&self.p, *f, &path)?;
                return Some(Walk {
                    source: Source::Call {
                        body: x,
                        blk,
                        callee: *f,
                        closure: c,
                    },
                    bodies,
                    jumped,
                    chain,
                });
            }
            let skip: BTreeSet<(BlockId, usize)> = self
                .run_moves
                .iter()
                .filter(|(y, _, _)| *y == x)
                .map(|&(_, k, i)| (k, i))
                .collect();
            match single_value_but(body, at, except, &skip)? {
                One::Closure(blk, si, c) => {
                    if !path.is_empty() {
                        return None;
                    }
                    return Some(Walk {
                        source: Source::Made {
                            body: x,
                            blk,
                            si,
                            closure: c,
                        },
                        bodies,
                        jumped,
                        chain,
                    });
                }
                One::Copy(next) => {
                    at = next;
                    except = None;
                }
                One::Moved(next, pos) => {
                    at = next;
                    except = Some(pos);
                }
                One::Part(next, proj) => {
                    // A copy of a part of another local (form 3, plan stage
                    // R0k-b2): the value of that part.
                    let mut p2 = proj;
                    p2.extend(path);
                    path = p2;
                    at = next;
                    except = None;
                }
                One::Aggregate(kind, ops, pos) => {
                    // A struct, a tuple or a variant (form 3): the operand of
                    // the first step of the path.
                    let (o, rest) = agg_operand(&kind, &ops, &path)?;
                    let q = o.place()?;
                    if q.proj
                        .iter()
                        .any(|x| !matches!(x, Proj::Field(_) | Proj::Variant(_)))
                    {
                        return None;
                    }
                    let mut p2 = q.proj.clone();
                    p2.extend(rest);
                    path = p2;
                    // A `move` of a whole local into the aggregate is the one
                    // read of its value.
                    except = (matches!(o, Operand::Move(_)) && q.is_local()).then_some(pos);
                    if matches!(o, Operand::Move(_)) && !q.is_local() {
                        return None;
                    }
                    at = q.local;
                }
            }
        }
        None
    }

    /// True if a write at block `wblk` of clause body `cl` gives the local of
    /// the way its value before the run at block `run` of body `b` (plan stage
    /// R0z Z3, fix 3; the form of `u13`): one direct perform can run the
    /// clause ([`Inst::clause_perform`]: no callee, closure or function value
    /// that performs the effect), it runs in `b` or in a body inside `b`
    /// whose terminator in `b` comes before the run on each path and not after
    /// it, and the write comes before each `resume` of the clause. Then the
    /// write is done when the clause resumes the perform, before the run, and
    /// the facts of the node that runs the clause have it.
    fn clause_write_ok(&self, cl: BodyId, wblk: BlockId, (b, run): (BodyId, BlockId)) -> bool {
        let Some((y, pk, _)) = self.clause_perform(cl) else {
            return false;
        };
        let gate = if y == b {
            Some(pk)
        } else if inside(&self.p, y, b) {
            gateway(&self.p, b, y)
        } else {
            None
        };
        let (Some(g), Some(bb), Some(cb)) = (gate, self.p.body(b), self.p.body(cl)) else {
            return false;
        };
        let to_run = reach(bb, g, true);
        let back = reach(bb, run, true);
        if g == run
            || !to_run.get(run.index()).copied().unwrap_or(false)
            || back.get(g.index()).copied().unwrap_or(true)
        {
            return false;
        }
        // No path from a `resume` reaches the write.
        cb.blocks.iter().all(|blk| {
            if !matches!(blk.term.kind, TermKind::Resume { .. }) {
                return true;
            }
            blk.term.kind.successors().iter().all(|&s| {
                s != wblk
                    && !reach(cb, s, true)
                        .get(wblk.index())
                        .copied()
                        .unwrap_or(true)
            })
        })
    }

    /// The value set of local `l` of body `b0` (plan stage R0z Z6), for the
    /// run at block `run` of body `b`: each closure that the cell of `l` can
    /// hold at the run, each with an exact way, and the writes of the cell.
    ///
    /// As [`Inst::walk_multi`] (the cell through upvar locals, each write in
    /// the owner or in a body inside it, a write in a clause only in the form
    /// of `u13`, no other write, move or borrow of the cell, no write by a
    /// terminator), with these steps for a write: a make of a closure; a
    /// whole `move` or `copy` of a local with an exact way to a closure that
    /// the program makes ([`Inst::walk_from`]; a closure that a callee gives
    /// back, `Source::Call`, refuses); or, if that local has more writes, the
    /// value set of that local (at most 4 levels). The read of the local
    /// that the walk follows (`skip_read`) is not another use of it. `None`
    /// if a write is of another form: a value of a caller, of a heap slot, of
    /// a perform or a `resume`, of a call (the walk takes no leaf from the
    /// destination of a terminator).
    fn walk_set(
        &self,
        (b, run): (BodyId, BlockId),
        b0: BodyId,
        l: LocalId,
        depth: usize,
        skip_read: Option<(BodyId, BlockId, usize)>,
        mut refused: Option<&mut Vec<BodyId>>,
    ) -> Option<ValueSet> {
        if depth > 4 {
            return None;
        }
        let (mut o, mut lo) = (b0, l);
        let mut bodies = vec![b0];
        let mut chain = vec![Link::Local(b0, l)];
        for _ in 0..32 {
            let body = self.p.body(o)?;
            match body.local_kind(lo)? {
                LocalKind::Upvar(s) if body.kind.has_upvars() => {
                    o = body.parent?;
                    lo = s;
                    bodies.push(o);
                    chain.push(Link::Local(o, lo));
                }
                LocalKind::User | LocalKind::Temp(_) => break,
                _ => return None,
            }
        }
        if !matches!(
            body_kind_of(&self.p, o, lo),
            Some(LocalKind::User | LocalKind::Temp(_))
        ) {
            return None;
        }
        let key = (o, lo, skip_read);
        let cached = self.cell_writes.borrow().get(&key).cloned();
        let writes = if let Some(w) = cached {
            w?
        } else {
            let w = self.cell_writes_of(o, lo, skip_read);
            self.cell_writes.borrow_mut().insert(key, w.clone());
            w?
        };
        if writes.is_empty() {
            return None;
        }
        // A write in a clause: only in the form of `u13` (plan stage R0z Z3,
        // fix 3).
        for &(x, blk, _) in &writes {
            let mut at = x;
            for _ in 0..=self.p.bodies.len() {
                if at == o {
                    break;
                }
                let xb = self.p.body(at)?;
                if matches!(xb.kind, BodyKind::Clause(..))
                    && (at != x || !self.clause_write_ok(x, blk, (b, run)))
                {
                    // The pre-scan of Part B ([`Inst::clause_callees`]) notes
                    // the clause.
                    match refused.as_deref_mut() {
                        Some(r) if at == x => r.push(x),
                        _ => return None,
                    }
                }
                at = xb.parent?;
            }
        }
        let mut leaves: Vec<Leaf> = Vec::new();
        for &(x, blk, si) in &writes {
            let st = self.p.body(x)?.block(blk)?.stmts.get(si)?;
            let StmtKind::Assign(_, rv) = &st.kind else {
                return None;
            };
            let (t, except, skip) = match rv {
                Rvalue::Aggregate(weft_ir::AggKind::Closure(c), _) => {
                    leaves.push(Leaf {
                        walk: Walk {
                            source: Source::Made {
                                body: x,
                                blk,
                                si,
                                closure: *c,
                            },
                            bodies: vec![x],
                            jumped: false,
                            chain: Vec::new(),
                        },
                        write: (x, blk, si),
                    });
                    continue;
                }
                Rvalue::Use(Operand::Move(t)) => (t.local, Some((blk, si)), Some((x, blk, si))),
                Rvalue::Use(Operand::Copy(t)) => (t.local, None, None),
                _ => return None,
            };
            if let Some(w) = self.walk_from(x, t, except) {
                if !matches!(w.source, Source::Made { .. }) {
                    return None;
                }
                leaves.push(Leaf {
                    walk: w,
                    write: (x, blk, si),
                });
            } else {
                let sub = self.walk_set((b, run), x, t, depth + 1, skip, refused.as_deref_mut())?;
                for mut leaf in sub.leaves {
                    for &y in &sub.bodies {
                        if !leaf.walk.bodies.contains(&y) {
                            leaf.walk.bodies.push(y);
                        }
                    }
                    leaf.walk.chain.extend(sub.chain.iter().copied());
                    leaf.write = (x, blk, si);
                    leaves.push(leaf);
                }
            }
        }
        Some(ValueSet {
            owner: o,
            bodies,
            chain,
            leaves,
            writes,
        })
    }

    /// The writes of the cell of local `lo` of body `o` for [`Inst::walk_set`]
    /// (plan stage R0z Z6), or `None` if a statement or a terminator writes,
    /// moves or borrows the cell in another way. The read `skip_read` is not a
    /// use. [`Inst::cell_writes`] keeps the result until the program changes.
    fn cell_writes_of(
        &self,
        o: BodyId,
        lo: LocalId,
        skip_read: Option<(BodyId, BlockId, usize)>,
    ) -> Option<Vec<(BodyId, BlockId, usize)>> {
        let mut writes: Vec<(BodyId, BlockId, usize)> = Vec::new();
        for x in std::iter::once(o).chain(inner_bodies(&self.p, o)) {
            let xb = self.p.body(x)?;
            let cell = |q: &Place| {
                if x == o {
                    q.local == lo
                } else {
                    cell_of(&self.p, x, q) == Some((o, lo))
                }
            };
            let mut accepted = 0usize;
            for (bi, blk) in xb.blocks.iter().enumerate() {
                let id = BlockId(u32::try_from(bi).ok()?);
                for (si, st) in blk.stmts.iter().enumerate() {
                    if self.run_moves.contains(&(x, id, si)) {
                        continue;
                    }
                    if let StmtKind::Assign(q, rv) = &st.kind {
                        if q.proj.is_empty() && cell(q) {
                            let ok = match rv {
                                Rvalue::Use(Operand::Move(t) | Operand::Copy(t)) => {
                                    t.is_local() && !cell(t)
                                }
                                Rvalue::Aggregate(weft_ir::AggKind::Closure(_), _) => true,
                                _ => false,
                            };
                            if !ok {
                                return None;
                            }
                            writes.push((x, id, si));
                            accepted += 1;
                        }
                    }
                }
                if x == o && runs_moved(&blk.term.kind, lo) {
                    accepted += 1;
                }
            }
            let named = if x == o {
                let mut n = 0usize;
                for (bi, blk) in xb.blocks.iter().enumerate() {
                    let id = BlockId(u32::try_from(bi).ok()?);
                    for (si, st) in blk.stmts.iter().enumerate() {
                        if self.run_moves.contains(&(x, id, si)) || skip_read == Some((x, id, si)) {
                            continue;
                        }
                        n += usize::from(stmt_writes(st, lo).0 || stmt_borrows_or_moves(st, lo));
                    }
                    if blk.term.kind.dest().is_some_and(|d| d.local == lo) {
                        return None;
                    }
                    n += usize::from(term_moves(&blk.term.kind, lo));
                }
                n
            } else {
                body_writes_but(xb, x, &self.run_moves)
                    .iter()
                    .filter(|q| cell(q))
                    .count()
            };
            if named != accepted {
                return None;
            }
        }
        Some(writes)
    }

    /// The pre-scan of plan stage R0z Z6, Part B: the calls of function items
    /// that get a copy so that a clause write of the way has the form of
    /// `u13`. For each run of a local of a function value in the original
    /// program whose value set ([`Inst::walk_set`]) has more than one value,
    /// and whose only refusal is a write in a clause that Z3 fix 3 refuses
    /// (`clause_write_ok`), each call of a callee that can run that clause
    /// ([`Inst::clause_calls`]) is in the result. A copy of such a callee at
    /// its call puts the perform into the handled body, so the clause can
    /// have one direct perform.
    fn clause_callees(&self) -> BTreeSet<(BodyId, BlockId)> {
        let mut out = BTreeSet::new();
        let mut tries = 0usize;
        for (bi, body) in self.p.bodies.iter().enumerate() {
            let b = BodyId(u32::try_from(bi).unwrap_or(u32::MAX));
            for (ki, blk) in body.blocks.iter().enumerate() {
                let k = BlockId(u32::try_from(ki).unwrap_or(u32::MAX));
                let TermKind::Call {
                    callee: Callee::Value(Operand::Copy(q) | Operand::Move(q)),
                    ..
                } = &blk.term.kind
                else {
                    continue;
                };
                if !q.is_local() || super::alpha::unit_closure(&self.p, b).is_some() {
                    continue;
                }
                tries += 1;
                if tries > DISPATCH_TRIES {
                    return out;
                }
                let mut refused: Vec<BodyId> = Vec::new();
                let Some(set) = self.walk_set((b, k), b, q.local, 0, None, Some(&mut refused))
                else {
                    continue;
                };
                if refused.is_empty() || set.leaves.len() < 2 {
                    continue;
                }
                for cl in refused {
                    out.extend(self.clause_calls(cl));
                }
            }
        }
        out
    }

    /// The calls of function items that can run the clause body `cl` (plan
    /// stage R0z Z6, Part B), if they are the only nodes that can run it
    /// besides the direct performs of its operation through the capability of
    /// its handler: a call in the handled body (or in a body inside it) whose
    /// environment sends the effect to the handler and whose callee can
    /// perform it ([`Inst::clause_perform`] refuses such a call). Empty if
    /// another node can run the clause: a call of a function value, a task, a
    /// perform through another capability, a closure that captures the
    /// capability.
    fn clause_calls(&self, cl: BodyId) -> Vec<(BodyId, BlockId)> {
        let Some(BodyKind::Clause(h, _)) = self.p.body(cl).map(|x| x.kind) else {
            return Vec::new();
        };
        let Some(hd) = self.p.handlers.get(h.index()) else {
            return Vec::new();
        };
        let Some(&(eff, cap)) = self.p.body(hd.handled).and_then(|x| x.caps.first()) else {
            return Vec::new();
        };
        let Some(id_e) = self.ident(eff) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for (bi, x) in self.p.bodies.iter().enumerate() {
            let id = BodyId(u32::try_from(bi).unwrap_or(u32::MAX));
            if !inside(&self.p, id, hd.handled) {
                continue;
            }
            for (ki, blk) in x.blocks.iter().enumerate() {
                let k = BlockId(u32::try_from(ki).unwrap_or(u32::MAX));
                match &blk.term.kind {
                    TermKind::Call {
                        callee,
                        caps: CapArgs::Lexical(e),
                        ..
                    } => {
                        let served = matches!(
                            super::frames::resolve(&self.p, &self.tys, *e, id_e, true),
                            super::frames::Dest::Handler { .. }
                        );
                        if !served {
                            continue;
                        }
                        match callee {
                            Callee::Fn(g, _) => {
                                if self.needs.unknown.contains(g) {
                                    return Vec::new();
                                }
                                if self.needs.row.get(g).is_some_and(|r| r.contains(&eff)) {
                                    out.push((id, k));
                                }
                            }
                            Callee::Value(o) => {
                                if value_row(&self.tys, x, o).is_none_or(|r| r.contains(&eff)) {
                                    return Vec::new();
                                }
                            }
                        }
                    }
                    TermKind::Perform {
                        cap: CapOperand::Local(q),
                        ..
                    } => {
                        let to_h = root_place(&self.p, id, q)
                            .is_some_and(|(a, pl)| a == hd.handled && pl.local == cap);
                        if !to_h
                            && weft_ir::print::cap_effect(&self.p, &self.tys, x, q) == Some(eff)
                        {
                            return Vec::new();
                        }
                    }
                    TermKind::Spawn { .. } | TermKind::Fork { .. } => return Vec::new(),
                    _ => {}
                }
            }
        }
        for d in &self.p.closures {
            for c in &d.captures {
                if c.mode == weft_ir::CaptureMode::Cap
                    && root_place(&self.p, d.maker, &c.source)
                        .is_some_and(|(a, pl)| a == hd.handled && pl.local == cap)
                {
                    return Vec::new();
                }
            }
        }
        out
    }

    /// The plan of a dispatch at the run at block `k` of body `b` (plan stage
    /// R0z Z6): the value set of the local of the run ([`Inst::walk_set`])
    /// has closures of two to [`DISPATCH_ARMS`] origins ([`Inst::origin`]),
    /// each of a function with no type parameters; the closures of one origin
    /// are one group (an arm, as `CopyRegion::also` of Z3). Each arm is a copy
    /// region ([`Inst::plan_run`] with `arm`) or a plain arm (a closure that
    /// needs no copy), and one arm at least is a copy. The refusals: a run in a
    /// copy region or in a closure body, a closure whose `once` flag is not
    /// the `move` of the run, the rule R-ROW ([`Inst::row_refused`]), a copy
    /// arm that its rules refuse, the bounds.
    fn dispatch_plan(&self, b: BodyId, k: BlockId) -> Option<DispatchPlan> {
        let body = self.p.body(b)?;
        let TermKind::Call {
            callee: Callee::Value(op @ (Operand::Copy(callee) | Operand::Move(callee))),
            caps: CapArgs::Lexical(_),
            unwind: Some(_),
            ..
        } = &body.block(k)?.term.kind
        else {
            return None;
        };
        if !callee.is_local()
            || self.p.region_of(b, k).is_some()
            || super::alpha::unit_closure(&self.p, b).is_some()
        {
            return None;
        }
        let tries = self.dispatch_tries.get();
        if tries >= DISPATCH_TRIES {
            return None;
        }
        self.dispatch_tries.set(tries + 1);
        let moves = matches!(op, Operand::Move(_));
        let set = self.walk_set((b, k), b, callee.local, 0, None, None)?;
        // The groups, by origin, in the order of the writes.
        let origin = |c: ClosureId| self.origin.get(&c).copied().unwrap_or(c);
        let mut groups: Vec<(ClosureId, Vec<Leaf>)> = Vec::new();
        for leaf in &set.leaves {
            let Source::Made { closure, .. } = leaf.walk.source else {
                return None;
            };
            let o0 = origin(closure);
            match groups.iter_mut().find(|(g, _)| *g == o0) {
                Some((_, ls)) => ls.push(leaf.clone()),
                None => groups.push((o0, vec![leaf.clone()])),
            }
        }
        if groups.len() < 2 || groups.len() > DISPATCH_ARMS {
            return None;
        }
        let mut all: Vec<ClosureId> = Vec::new();
        for (o0, ls) in &groups {
            let od = self.orig.closures.get(o0.index())?;
            let generic = fn_of(self.orig, od.body)
                .and_then(|f| self.orig.fns.get(f.index()))
                .is_none_or(|d| d.generics != 0);
            if generic {
                return None;
            }
            for leaf in ls {
                let Source::Made { closure, .. } = leaf.walk.source else {
                    return None;
                };
                let d = self.p.closures.get(closure.index())?;
                if d.once != moves {
                    return None;
                }
                if !all.contains(&closure) {
                    all.push(closure);
                }
            }
        }
        if self.row_refused(b, &all) {
            return None;
        }
        let mut arms: Vec<(Vec<ClosureId>, Option<RunPlan>, bool)> = Vec::new();
        let mut size = 0usize;
        for (_, ls) in &groups {
            let first = ls.first()?;
            let Source::Made { closure: c0, .. } = first.walk.source else {
                return None;
            };
            let mut also: Vec<ClosureId> = Vec::new();
            let mut main = first.walk.clone();
            main.bodies.clone_from(&set.bodies);
            main.chain.clone_from(&set.chain);
            for leaf in ls {
                if let Source::Made { closure, .. } = leaf.walk.source {
                    if closure != c0 && !also.contains(&closure) {
                        also.push(closure);
                    }
                }
                main.jumped |= leaf.walk.jumped;
                for &x in &leaf.walk.bodies {
                    if !main.bodies.contains(&x) {
                        main.bodies.push(x);
                    }
                }
                main.chain.extend(leaf.walk.chain.iter().copied());
            }
            let mut closures = vec![c0];
            closures.extend(also.iter().copied());
            let mine: Vec<(BodyId, BlockId, usize)> = ls.iter().map(|x| x.write).collect();
            let killable = self.killable(set.owner, (b, k), &mine, &set.writes);
            match self.plan_run((b, k), moves, main, also, true) {
                Ok(plan) => {
                    // The refusals R-JOIN and R-REF of the review of plan stage
                    // R0z Z6 ([`Inst::arm_join_refused`]).
                    let decl = self.p.closures.get(plan.closure.index())?;
                    if self.arm_join_refused(decl, (b, k), &all) {
                        return None;
                    }
                    size += plan.size;
                    arms.push((closures, Some(plan), killable));
                }
                Err(NoPlan::Plain) => arms.push((closures, None, killable)),
                Err(NoPlan::No) => return None,
            }
        }
        if !arms.iter().any(|(_, x, _)| x.is_some()) {
            return None;
        }
        // R-LOOP: a run in a loop whose copy arm gives a function value or a
        // reference to an operation. The facts of a clause that keeps such a
        // value join the value of one turn with the change of the next turn
        // (a false W0301 of main for the form with one value, issue #79), so
        // the dispatch is refused, and the program keeps its fallback.
        let gives = arms
            .iter()
            .filter(|(_, x, _)| x.is_some())
            .flat_map(|(cs, _, _)| cs.iter())
            .any(|c| self.gives_to_operation(*c));
        if gives && self.in_loop(b, k) {
            return None;
        }
        let blocks = size + 2 * arms.len() + 1;
        (self.added + blocks <= self.bounds.blocks).then_some(DispatchPlan { arms })
    }

    /// True if the code of closure `c` (its body and the bodies inside it)
    /// gives a function value or a reference to an operation: a perform of
    /// such an operation, or a call of a callee that performs one through its
    /// row (`Needs::any`) (plan stage R0z Z6, R-LOOP).
    fn gives_to_operation(&self, c: ClosureId) -> bool {
        let Some(d) = self.p.closures.get(c.index()) else {
            return true;
        };
        std::iter::once(d.body)
            .chain(inner_bodies(&self.p, d.body))
            .any(|x| {
                let Some(xb) = self.p.body(x) else {
                    return true;
                };
                xb.blocks.iter().any(|blk| match &blk.term.kind {
                    TermKind::Perform {
                        cap: CapOperand::Local(q),
                        op,
                        ..
                    } => weft_ir::print::cap_effect(&self.p, &self.tys, xb, q)
                        .is_none_or(|e| risky_op(&self.tys, e, *op).0),
                    TermKind::Perform {
                        cap: CapOperand::Row(e),
                        op,
                        ..
                    } => risky_op(&self.tys, *e, *op).0,
                    TermKind::Call {
                        callee: Callee::Fn(g, _),
                        ..
                    } => self.needs.any.get(g).is_some_and(|s| !s.is_empty()),
                    TermKind::Call {
                        callee: Callee::Value(_),
                        ..
                    } => true,
                    _ => false,
                })
            })
    }

    /// True if the run at block `k` of body `b` is in a loop (plan stage R0z
    /// Z6, R-LOOP): the block is on a cycle of its body, or the terminator
    /// that runs the body (in a body around it, up to the function body or a
    /// closure body) is on a cycle there.
    fn in_loop(&self, b: BodyId, k: BlockId) -> bool {
        let (mut x, mut at) = (b, k);
        for _ in 0..=self.p.bodies.len() {
            let Some(xb) = self.p.body(x) else {
                return true;
            };
            let back = xb
                .block(at)
                .map(|blk| blk.term.kind.successors())
                .unwrap_or_default()
                .into_iter()
                .any(|s| reach(xb, s, true).get(at.index()).copied().unwrap_or(true));
            if back {
                return true;
            }
            match (xb.kind, xb.parent) {
                (BodyKind::Fn(_) | BodyKind::Closure(_), _) | (_, None) => return false,
                (_, Some(up)) => {
                    let Some(g) = gateway(&self.p, up, x) else {
                        return true;
                    };
                    x = up;
                    at = g;
                }
            }
        }
        true
    }

    /// The rule R-ROW of plan stage R0z Z6, in its syntactic form: no dispatch
    /// if the program declares a `multi` operation and the run is in a clause
    /// or in a body that splices into one (a handled body or a scope body
    /// inside a clause), or in the handled body of a local handler of an effect
    /// with a `multi` operation (or a body that splices into it), or if a closure of `closures` (its body or a body
    /// inside it) can perform an effect with a `multi` operation: a perform,
    /// a call of a callee that can (`Needs::row`, `Needs::unknown`), or a call
    /// of a function value whose row can have one. Then no block of a
    /// dispatch is a part of a re-entry of stage R0k-c2 or Z7. After the emit,
    /// `factgen::DISPATCH_ROW` checks the rows that the analysis finds.
    fn row_refused(&self, b: BodyId, closures: &[ClosureId]) -> bool {
        let multi: BTreeSet<EffectId> = self
            .tys
            .effects()
            .iter()
            .enumerate()
            .filter(|(_, e)| e.ops.iter().any(|o| o.multi))
            .filter_map(|(i, _)| u32::try_from(i).ok().map(EffectId))
            .collect();
        if multi.is_empty() {
            return false;
        }
        let mut at = Some(b);
        for _ in 0..=self.p.bodies.len() {
            let Some(x) = at.and_then(|y| self.p.body(y)) else {
                break;
            };
            match x.kind {
                BodyKind::Clause(..) => return true,
                // The handled body of a local handler of an effect with a
                // `multi` operation (the review of Z6, N1): a later `resume`
                // runs the rest of the handled body again, also the dispatch.
                BodyKind::Handled(_) if x.caps.iter().any(|(e, _)| multi.contains(e)) => {
                    return true;
                }
                BodyKind::Handled(_) | BodyKind::Scope(_) => at = x.parent,
                _ => break,
            }
        }
        for c in closures {
            let Some(d) = self.p.closures.get(c.index()) else {
                return true;
            };
            for x in std::iter::once(d.body).chain(inner_bodies(&self.p, d.body)) {
                let Some(xb) = self.p.body(x) else {
                    return true;
                };
                for blk in &xb.blocks {
                    let can = match &blk.term.kind {
                        TermKind::Perform {
                            cap: CapOperand::Row(e),
                            ..
                        } => multi.contains(e),
                        TermKind::Perform {
                            cap: CapOperand::Local(q),
                            ..
                        } => weft_ir::print::cap_effect(&self.p, &self.tys, xb, q)
                            .is_none_or(|e| multi.contains(&e)),
                        TermKind::Call {
                            callee: Callee::Fn(g, _),
                            ..
                        } => {
                            self.needs.unknown.contains(g)
                                || self
                                    .needs
                                    .row
                                    .get(g)
                                    .is_some_and(|r| r.iter().any(|e| multi.contains(e)))
                        }
                        TermKind::Call {
                            callee: Callee::Value(o),
                            ..
                        } => value_row(&self.tys, xb, o)
                            .is_none_or(|r| r.iter().any(|e| multi.contains(e))),
                        _ => false,
                    };
                    if can {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// The static check of a dead arm (plan stage R0z Z6,
    /// `weft_ir::DispatchArm::killable`): each path in the owner `o` of the
    /// cell from each write of `mine` to the run at block `run` of body `b`
    /// passes a write of `all` that is not in `mine`. A write (or the run) in
    /// a body inside `o` counts at the terminator of `o` that runs that body
    /// ([`gateway`]); two writes at the same terminator do not order, so they
    /// are no kill of each other, and a write at the terminator of the run
    /// is never dead.
    fn killable(
        &self,
        o: BodyId,
        (b, run): (BodyId, BlockId),
        mine: &[(BodyId, BlockId, usize)],
        all: &[(BodyId, BlockId, usize)],
    ) -> bool {
        let point = |(x, blk, si): (BodyId, BlockId, usize)| -> Option<(BlockId, usize)> {
            if x == o {
                Some((blk, si))
            } else {
                gateway(&self.p, o, x).map(|g| (g, usize::MAX))
            }
        };
        let Some(ob) = self.p.body(o) else {
            return false;
        };
        let rp = if b == o {
            Some((run, usize::MAX))
        } else {
            gateway(&self.p, o, b).map(|g| (g, usize::MAX))
        };
        let Some(rp) = rp else {
            return false;
        };
        for &w in mine {
            let Some(wp) = point(w) else {
                return false;
            };
            if wp == rp {
                return false;
            }
            let kills: Vec<(BlockId, usize)> = all
                .iter()
                .filter(|x| !mine.contains(x))
                .filter_map(|&x| point(x))
                .filter(|&x| x != wp)
                .collect();
            let kill_in = |blk: BlockId, lo: Option<usize>, hi: usize| {
                kills
                    .iter()
                    .any(|&(kb, kp)| kb == blk && lo.is_none_or(|l| kp > l) && kp < hi)
            };
            // The rest of the block of the write.
            if wp.0 == rp.0 && rp.1 > wp.1 {
                if !kill_in(wp.0, Some(wp.1), rp.1) {
                    return false;
                }
                continue;
            }
            // A kill after the write in its block, or at its terminator.
            let term_kill =
                |blk: BlockId| kills.iter().any(|&(kb, kp)| kb == blk && kp == usize::MAX);
            if kill_in(wp.0, Some(wp.1), usize::MAX) || (wp.1 != usize::MAX && term_kill(wp.0)) {
                continue;
            }
            let mut seen = vec![false; ob.blocks.len()];
            let mut work: Vec<BlockId> = ob
                .block(wp.0)
                .map(|x| x.term.kind.successors())
                .unwrap_or_default();
            while let Some(s) = work.pop() {
                match seen.get_mut(s.index()) {
                    Some(v) if !*v => *v = true,
                    _ => continue,
                }
                if s == rp.0 {
                    if !kill_in(s, None, rp.1) {
                        return false;
                    }
                    continue;
                }
                if kill_in(s, None, usize::MAX) || term_kill(s) {
                    continue;
                }
                if let Some(x) = ob.block(s) {
                    work.extend(x.term.kind.successors());
                }
            }
        }
        true
    }

    /// The copy of a dispatch at the run at block `k` of body `b` (plan stage
    /// R0z Z6), with the plan [`Inst::dplan`]. Block `k` gets the first test;
    /// the new blocks are the other tests, the arm entries (each one a copy of
    /// the call) and the miss block. Each copy arm gets the copy of
    /// [`Inst::copy_code`] at its entry, with its plan. Then the record
    /// `weft_ir::Dispatch`.
    fn dispatch(&mut self, b: BodyId, k: BlockId) -> Result<(), NoCopy> {
        let plan = self.dplan.take().ok_or(NoCopy)?;
        let site = self.p.body(b).ok_or(NoCopy)?;
        let call = site.block(k).ok_or(NoCopy)?.term.clone();
        let TermKind::Call {
            callee: Callee::Value(op),
            ..
        } = &call.kind
        else {
            return Err(NoCopy);
        };
        let value = op.place().filter(|q| q.is_local()).ok_or(NoCopy)?.clone();
        let origin = call.origin;
        let n = plan.arms.len();
        let bool_ty = self.tys.intern(weft_ir::Ty::Bool);
        let props = crate::props::ir_props(&self.tys, bool_ty);
        let lbase = u32::try_from(site.locals.len()).map_err(|_| NoCopy)?;
        let bbase = u32::try_from(site.blocks.len()).map_err(|_| NoCopy)?;
        let n32 = u32::try_from(n).map_err(|_| NoCopy)?;
        let g = |i: usize| LocalId(lbase + u32::try_from(i).unwrap_or(0));
        // The test of arm `i`: block `k` for the first arm.
        let test = |i: usize| {
            if i == 0 {
                k
            } else {
                BlockId(bbase + u32::try_from(i).unwrap_or(0) - 1)
            }
        };
        let entry = |i: usize| BlockId(bbase + n32 - 1 + u32::try_from(i).unwrap_or(0));
        let miss = BlockId(bbase + 2 * n32 - 1);
        let chain = self.chain(b, k);
        let site_of = self.sites.get(&(b, k)).copied();
        let stmt = |kind: StmtKind| Stmt { kind, origin };
        let site = self.p.bodies.get_mut(b.index()).ok_or(NoCopy)?;
        for _ in 0..n {
            site.locals.push(LocalDecl {
                ty: bool_ty,
                kind: LocalKind::Temp(TempKind::Operand),
                name: None,
                props,
                in_place: false,
                origin,
            });
        }
        let test_stmts = |i: usize, closures: &[ClosureId]| -> Vec<Stmt> {
            let mut v = Vec::new();
            if i > 0 {
                v.push(stmt(StmtKind::Dead(g(i - 1))));
            }
            v.push(stmt(StmtKind::Live(g(i))));
            v.push(stmt(StmtKind::Assign(
                Place::local(g(i)),
                Rvalue::ClosureIs(value.clone(), closures.to_vec()),
            )));
            v
        };
        let switch = |i: usize| Term {
            kind: TermKind::Switch {
                on: Operand::Move(Place::local(g(i))),
                arms: vec![(1, entry(i))],
                otherwise: if i + 1 < n { test(i + 1) } else { miss },
            },
            origin,
        };
        {
            let blk = site.blocks.get_mut(k.index()).ok_or(NoCopy)?;
            let first = plan.arms.first().ok_or(NoCopy)?;
            blk.stmts.extend(test_stmts(0, &first.0));
            blk.term = switch(0);
        }
        for (i, arm) in plan.arms.iter().enumerate().skip(1) {
            site.blocks.push(weft_ir::Block {
                stmts: test_stmts(i, &arm.0),
                term: switch(i),
                cleanup: false,
            });
        }
        for i in 0..n {
            site.blocks.push(weft_ir::Block {
                stmts: vec![stmt(StmtKind::Dead(g(i)))],
                term: call.clone(),
                cleanup: false,
            });
        }
        site.blocks.push(weft_ir::Block {
            stmts: vec![stmt(StmtKind::Dead(g(n - 1)))],
            term: Term {
                kind: TermKind::Unreachable,
                origin,
            },
            cleanup: false,
        });
        self.added += 2 * n;
        let mut blocks: Vec<BlockId> = (0..n).map(&test).collect();
        blocks.extend((0..n).map(&entry));
        blocks.push(miss);
        for &x in &blocks {
            self.blk_chain.insert((b, x), chain.clone());
            if let Some(s) = site_of {
                self.sites.insert((b, x), s);
            }
            self.no_copy.insert((b, x));
        }
        let mut arms: Vec<weft_ir::DispatchArm> = Vec::new();
        for (i, (closures, run, killable)) in plan.arms.into_iter().enumerate() {
            let region = match run {
                Some(r) => {
                    let c = r.closure;
                    self.run_plan = Some(r);
                    let before = self.p.regions.len();
                    let snap = self.p.clone();
                    let done = self.copy_code(&snap, b, entry(i), What::Closure(c));
                    self.run_plan = None;
                    done?;
                    if self.p.regions.len() != before + 1 {
                        return Err(NoCopy);
                    }
                    Some(before)
                }
                None => None,
            };
            arms.push(weft_ir::DispatchArm {
                closures,
                test: test(i),
                entry: entry(i),
                region,
                killable,
            });
        }
        self.p.dispatches.push(weft_ir::Dispatch {
            body: b,
            value,
            arms,
            miss,
        });
        self.dispatches += 1;
        Ok(())
    }

    /// The ways of the values of local `l` of body `b` (plan stage R0z Z3,
    /// part a), if the local (through upvar locals: the cell of a local of a
    /// body around `b`) gets more than one value and each value is a closure
    /// that is a copy of the same closure of a function with no type
    /// parameters ([`Inst::origin`]). Each write is a whole `move` or `copy`
    /// of a local (or a make of the closure), in the body that owns the
    /// local or in a body inside it, and its way is exact
    /// ([`Inst::walk_from`]). No statement or terminator moves, borrows or
    /// writes the cell in another way, but a `move` that runs it (the run of
    /// a `once` closure).
    ///
    /// The result is the way of the first value, with the bodies and the
    /// steps of each way, and the other closures. `None` if the values are
    /// one closure.
    fn walk_multi(
        &self,
        (b, run): (BodyId, BlockId),
        l: LocalId,
    ) -> Option<(Walk, Vec<ClosureId>)> {
        let (mut o, mut lo) = (b, l);
        let mut bodies = vec![b];
        let mut chain = vec![Link::Local(b, l)];
        for _ in 0..32 {
            let body = self.p.body(o)?;
            match body.local_kind(lo)? {
                LocalKind::Upvar(s) if body.kind.has_upvars() => {
                    o = body.parent?;
                    lo = s;
                    bodies.push(o);
                    chain.push(Link::Local(o, lo));
                }
                LocalKind::User | LocalKind::Temp(_) => break,
                _ => return None,
            }
        }
        if !matches!(
            body_kind_of(&self.p, o, lo),
            Some(LocalKind::User | LocalKind::Temp(_))
        ) {
            return None;
        }
        // The writes of the cell: (body, block, statement, the value).
        let mut writes: Vec<(BodyId, BlockId, usize)> = Vec::new();
        for x in std::iter::once(o).chain(inner_bodies(&self.p, o)) {
            let xb = self.p.body(x)?;
            let cell = |q: &Place| {
                if x == o {
                    q.local == lo
                } else {
                    cell_of(&self.p, x, q) == Some((o, lo))
                }
            };
            let mut accepted = 0usize;
            for (bi, blk) in xb.blocks.iter().enumerate() {
                let id = BlockId(u32::try_from(bi).ok()?);
                for (si, st) in blk.stmts.iter().enumerate() {
                    if self.run_moves.contains(&(x, id, si)) {
                        continue;
                    }
                    if let StmtKind::Assign(q, rv) = &st.kind {
                        if q.proj.is_empty() && cell(q) {
                            let ok = match rv {
                                Rvalue::Use(Operand::Move(t) | Operand::Copy(t)) => {
                                    t.is_local() && !cell(t)
                                }
                                Rvalue::Aggregate(weft_ir::AggKind::Closure(_), _) => true,
                                _ => false,
                            };
                            if !ok {
                                return None;
                            }
                            writes.push((x, id, si));
                            accepted += 1;
                        }
                    }
                }
                if x == o && runs_moved(&blk.term.kind, lo) {
                    accepted += 1;
                }
            }
            // Each other write, move or borrow of the cell refuses the way.
            let named = if x == o {
                let mut n = 0usize;
                for (bi, blk) in xb.blocks.iter().enumerate() {
                    let id = BlockId(u32::try_from(bi).ok()?);
                    for (si, st) in blk.stmts.iter().enumerate() {
                        if self.run_moves.contains(&(x, id, si)) {
                            continue;
                        }
                        n += usize::from(stmt_writes(st, lo).0 || stmt_borrows_or_moves(st, lo));
                    }
                    if blk.term.kind.dest().is_some_and(|d| d.local == lo) {
                        return None;
                    }
                    n += usize::from(term_moves(&blk.term.kind, lo));
                }
                n
            } else {
                body_writes_but(xb, x, &self.run_moves)
                    .iter()
                    .filter(|q| cell(q))
                    .count()
            };
            if named != accepted {
                return None;
            }
        }
        if writes.len() < 2 {
            return None;
        }
        // A write in a clause (plan stage R0z Z3, fix 3): only in the form of
        // `u13` (`Inst::clause_write_ok`). Else the facts give the cell a weak
        // update at the node that runs the clause, and the copy would join the
        // value before the write with the value of the write.
        for &(x, blk, _) in &writes {
            let mut at = x;
            for _ in 0..=self.p.bodies.len() {
                if at == o {
                    break;
                }
                let xb = self.p.body(at)?;
                if matches!(xb.kind, BodyKind::Clause(..))
                    && (at != x || !self.clause_write_ok(x, blk, (b, run)))
                {
                    return None;
                }
                at = xb.parent?;
            }
        }
        // The way of each value.
        let mut ways: Vec<Walk> = Vec::new();
        for &(x, blk, si) in &writes {
            let st = self.p.body(x)?.block(blk)?.stmts.get(si)?;
            let StmtKind::Assign(_, rv) = &st.kind else {
                return None;
            };
            let w = match rv {
                Rvalue::Aggregate(weft_ir::AggKind::Closure(c), _) => Walk {
                    source: Source::Made {
                        body: x,
                        blk,
                        si,
                        closure: *c,
                    },
                    bodies: vec![x],
                    jumped: false,
                    chain: Vec::new(),
                },
                Rvalue::Use(Operand::Move(t)) => self.walk_from(x, t.local, Some((blk, si)))?,
                Rvalue::Use(Operand::Copy(t)) => self.walk_from(x, t.local, None)?,
                _ => return None,
            };
            if !matches!(w.source, Source::Made { .. }) {
                return None;
            }
            ways.push(w);
        }
        // Each value is a copy of the same closure, of a function with no
        // type parameters: the copies have the same code and the same types.
        let origin = |c: ClosureId| self.origin.get(&c).copied().unwrap_or(c);
        let closure_of = |w: &Walk| match w.source {
            Source::Made { closure, .. } => Some(closure),
            Source::Call { .. } => None,
        };
        let first = ways.first().and_then(closure_of)?;
        let o0 = origin(first);
        let od = self.orig.closures.get(o0.index())?;
        let generic = fn_of(self.orig, od.body)
            .and_then(|f| self.orig.fns.get(f.index()))
            .is_none_or(|d| d.generics != 0);
        if generic {
            return None;
        }
        let mut also: Vec<ClosureId> = Vec::new();
        for w in &ways {
            let c = closure_of(w)?;
            if origin(c) != o0 {
                return None;
            }
            if c != first && !also.contains(&c) {
                also.push(c);
            }
        }
        if also.is_empty() {
            return None;
        }
        let mut main = ways.first()?.clone();
        main.bodies = bodies;
        main.chain = chain;
        for w in &ways {
            main.jumped |= w.jumped;
            for &x in &w.bodies {
                if !main.bodies.contains(&x) {
                    main.bodies.push(x);
                }
            }
            main.chain.extend(w.chain.iter().copied());
        }
        Some((main, also))
    }

    /// The body, the block and the argument `i` of the one perform that can run the
    /// clause body `cl` (stage R0k-b1'): a perform of the operation of the
    /// clause through the capability of its handler, in the handled body or
    /// in a body inside it that names the capability through upvar locals.
    /// `None` if another perform or a call can run the clause: a perform
    /// through a closure environment, a callee or a function value that
    /// performs the effect through its row where the handler serves it, a
    /// task.
    fn clause_arg(&self, cl: BodyId, i: u32) -> Option<(BodyId, BlockId, Operand)> {
        let (y, k, args) = self.clause_perform(cl)?;
        Some((y, k, args.get(i as usize)?.clone()))
    }

    /// The body, the block and the arguments of the one perform that can run
    /// the clause body `cl` ([`Inst::clause_arg`]).
    fn clause_perform(&self, cl: BodyId) -> Option<(BodyId, BlockId, Vec<Operand>)> {
        let BodyKind::Clause(h, op) = self.p.body(cl)?.kind else {
            return None;
        };
        let hd = self.p.handlers.get(h.index())?;
        let hb = self.p.body(hd.handled)?;
        let (eff, cap) = *hb.caps.first()?;
        let mut found: Option<(BodyId, BlockId, Vec<Operand>)> = None;
        for (bi, x) in self.p.bodies.iter().enumerate() {
            let id = BodyId(u32::try_from(bi).ok()?);
            let under = inside(&self.p, id, hd.handled);
            for (ki, blk) in x.blocks.iter().enumerate() {
                match &blk.term.kind {
                    TermKind::Perform {
                        cap: CapOperand::Local(q),
                        op: o,
                        args,
                        ..
                    } => {
                        let to_h = root_place(&self.p, id, q)
                            .is_some_and(|(a, pl)| a == hd.handled && pl.local == cap);
                        if !to_h {
                            // A perform of the effect through another capability
                            // can reach the clause too: through a closure
                            // environment, or through an inner handler with no
                            // clause for the operation.
                            if under
                                && weft_ir::print::cap_effect(&self.p, &self.tys, x, q) == Some(eff)
                            {
                                return None;
                            }
                            continue;
                        }
                        if *o != op {
                            continue;
                        }
                        if found.is_some() {
                            return None;
                        }
                        let k = BlockId(u32::try_from(ki).ok()?);
                        found = Some((id, k, args.clone()));
                    }
                    // A callee or a function value that the handler serves.
                    TermKind::Call {
                        callee,
                        caps: CapArgs::Lexical(e),
                        ..
                    } if under => {
                        let served = matches!(
                            super::frames::resolve(&self.p, &self.tys, *e, self.ident(eff)?, true),
                            super::frames::Dest::Handler { .. }
                        );
                        if !served {
                            continue;
                        }
                        let can = match callee {
                            Callee::Fn(g, _) => {
                                self.needs.unknown.contains(g)
                                    || self.needs.row.get(g).is_some_and(|r| r.contains(&eff))
                            }
                            Callee::Value(o) => {
                                value_row(&self.tys, x, o).is_none_or(|r| r.contains(&eff))
                            }
                        };
                        if can {
                            return None;
                        }
                    }
                    TermKind::Spawn { .. } | TermKind::Fork { .. } if under => return None,
                    _ => {}
                }
            }
        }
        // A closure that captures the capability of the handler can perform
        // the operation where it runs.
        for d in &self.p.closures {
            for c in &d.captures {
                if c.mode == weft_ir::CaptureMode::Cap
                    && root_place(&self.p, d.maker, &c.source)
                        .is_some_and(|(a, pl)| a == hd.handled && pl.local == cap)
                {
                    return None;
                }
            }
        }
        found
    }

    /// The identity of effect `e`.
    fn ident(&self, e: EffectId) -> Option<&str> {
        self.tys
            .effects()
            .get(e.index())
            .map(|d| d.identity.as_str())
    }

    /// The extent rule of a copy region (stage R0k-b1'): for each effect that
    /// the code of closure body `cb` can use through the handlers of its
    /// value (its operations through the row, the rows of its calls, `Fail`)
    /// and that environment `env` binds, and for each `Cap` capture, the
    /// body that opens the capability is around each body of the way of the
    /// value (`bodies`). Then the run node sees the handler instance of the
    /// make: a closure value that leaves a handled body, or a new instance
    /// of the handler in a loop, goes to the next handler of the chain at run
    /// time, and the facts would name a static handler.
    fn extent_ok(
        &self,
        cb: BodyId,
        env: CapEnvId,
        captures: &[weft_ir::Capture],
        maker: BodyId,
        bodies: &[BodyId],
    ) -> bool {
        let mut used = self.closure_uses(&self.p, cb);
        for (i, d) in self.tys.effects().iter().enumerate() {
            if d.identity == super::frames::FAIL {
                used.insert(EffectId(u32::try_from(i).unwrap_or(u32::MAX)));
            }
        }
        let around = |a: BodyId| bodies.iter().all(|&x| inside(&self.p, x, a));
        for e in used {
            let mut at = Some(env);
            for _ in 0..=self.p.cap_envs.len() {
                let Some(id) = at else { break };
                let Some(c) = self.p.cap_envs.get(id.index()) else {
                    return false;
                };
                if c.adds.iter().any(|(x, _)| *x == e) {
                    match owner_of_env(&self.p, id, e) {
                        Some(a) if around(a) => {}
                        _ => return false,
                    }
                }
                at = c.parent;
            }
        }
        captures
            .iter()
            .filter(|c| c.mode == weft_ir::CaptureMode::Cap)
            .all(|c| root_place(&self.p, maker, &c.source).is_some_and(|(a, _)| around(a)))
    }

    /// The agreement rule of a copy region (stage R0k-b1'): the facts of a
    /// `join`, a `fork`, a `spawn` and a `scope` take the capability
    /// environment of the body, not that of the region. So if the code of
    /// closure body `cb` has one of them, environments `env` (the region)
    /// and `run_env` (the body of the run node) must send each effect to the
    /// same destination.
    fn agrees(&self, cb: BodyId, env: CapEnvId, run_env: CapEnvId) -> bool {
        let Some(body) = self.p.body(cb) else {
            return false;
        };
        let reads = body.blocks.iter().any(|blk| {
            matches!(
                blk.term.kind,
                TermKind::Join { .. }
                    | TermKind::Fork { .. }
                    | TermKind::Spawn { .. }
                    | TermKind::Scope { .. }
                    | TermKind::ScopeWait { .. }
            )
        });
        !reads
            || self.tys.effects().iter().all(|d| {
                super::frames::resolve(&self.p, &self.tys, env, &d.identity, true)
                    == super::frames::resolve(&self.p, &self.tys, run_env, &d.identity, true)
            })
    }

    /// The callee of the call at block `k` of body `b` that gets a copy in
    /// the mode of [`instantiate_kont`] (D1c): `b` is a clause, and an
    /// argument is a whole local that holds a closure that `b` makes and that
    /// captures the continuation of `b` ([`kont_closure`]).
    fn kont_wants(&self, b: BodyId, k: BlockId) -> Option<FnId> {
        let body = self.p.body(b)?;
        if !matches!(body.kind, BodyKind::Clause(..)) {
            return None;
        }
        let TermKind::Call {
            callee: Callee::Fn(f, _),
            args,
            caps: CapArgs::Lexical(_),
            unwind: Some(_),
            ..
        } = &body.block(k)?.term.kind
        else {
            return None;
        };
        args.iter()
            .filter_map(|a| a.place().filter(|q| q.is_local()).map(|q| q.local))
            .any(|l| kont_closure(&self.p, b, l).is_some())
            .then_some(*f)
    }

    /// The copy of stage R0k-c1 at block `k` of body `b` (D1a, and D1c in the
    /// copy of a callee): the call runs a closure that clause `b` makes and
    /// that captures the continuation of `b`. Each condition is a hard rule
    /// (`docs/ir.md` 6.1, "As built (plan stage R0k-c1)"); if one fails, the
    /// call keeps the summary of the closure and the program its fallback.
    ///
    /// - The run is a call of a function value `copy l` or `move l`.
    /// - The value goes from the make to `l` along a chain of whole locals
    ///   (`x = move y` or `x = copy y`): no field, no container, no
    ///   reference. Each local of the chain has one write, and one read
    ///   (the next step of the chain or the run) besides `Live`, `Dead` and
    ///   the drops of the cleanup blocks; no body inside `b` names it.
    /// - The closure is made by `b`, captures the `Kont` local of `b` and no
    ///   value `ByMove`, and its body uses only fields of its environment.
    /// - The `Kont` local appears after the make only in `Dead` and
    ///   `UnwindKont`, in no other statement or terminator, and no body
    ///   inside `b` names it.
    /// - Each path of the CFG from the make reaches the run, with no cycle,
    ///   through blocks whose terminators are `Goto` or `Switch` (no unwind
    ///   edge, no abort edge, no perform), and with no statement but `Live`
    ///   and `Dead` of other locals and the steps of the chain.
    ///
    /// A `once` continuation (a `move` capture) moves into the closure value:
    /// the copy resumes the `Kont` local, so the make and the steps of the
    /// chain go ([`KontPlan::removals`]). A `multi` continuation (a `copy`
    /// capture) keeps the make, and the copy reads the source, as in R0k-a2.
    fn kont_copy(&self, b: BodyId, k: BlockId) -> Option<KontPlan> {
        let body = self.p.body(b)?;
        if !matches!(body.kind, BodyKind::Clause(..)) {
            return None;
        }
        let TermKind::Call {
            callee: Callee::Value(op),
            caps: CapArgs::Lexical(_),
            unwind: Some(_),
            ..
        } = &body.block(k)?.term.kind
        else {
            return None;
        };
        let q = op.place()?;
        if !q.is_local() {
            return None;
        }
        let ch = kont_closure(&self.p, b, q.local)?;
        // The run is the one read of the last local of the chain.
        if !ch
            .locals
            .iter()
            .all(|&l| local_reads(body, l) == 1 && !nested_uses(&self.p, b, l))
        {
            return None;
        }
        let decl = self.p.closures.get(ch.closure.index())?;
        if nested_uses(&self.p, b, ch.kont) || kont_uses_after(body, ch.kont, ch.make) {
            return None;
        }
        // The captures: one `Kont` capture of the continuation, and `Kept`,
        // `ByRef` and `Cap` captures (as R0k-a2).
        for cap in &decl.captures {
            match cap.mode {
                weft_ir::CaptureMode::Kont | weft_ir::CaptureMode::Cap => {}
                weft_ir::CaptureMode::Kept | weft_ir::CaptureMode::ByRef => {
                    if cap.source.has_deref() {
                        return None;
                    }
                }
                weft_ir::CaptureMode::ByMove => return None,
            }
        }
        // The path from the make to the run.
        let mut sources: BTreeSet<LocalId> = decl.captures.iter().map(|c| c.source.local).collect();
        sources.insert(ch.kont);
        if !kont_region_ok(body, ch.make, k, &ch.steps, &sources) {
            return None;
        }
        // The body of the closure: only fields of its environment, and no
        // body inside it names the environment (as R0k-a2).
        let cb = self.p.body(decl.body)?;
        let env = *cb.params.first()?;
        if !body_places(cb)
            .iter()
            .all(|x| x.local != env || matches!(x.proj.first(), Some(Proj::Field(_))))
        {
            return None;
        }
        let inner = inner_bodies(&self.p, decl.body);
        for &ib in &inner {
            let x = self.p.body(ib)?;
            if x.parent == Some(decl.body)
                && x.locals.iter().any(|d| d.kind == LocalKind::Upvar(env))
            {
                return None;
            }
        }
        let size: usize = std::iter::once(decl.body)
            .chain(inner)
            .filter_map(|x| self.p.body(x))
            .map(|x| x.blocks.len())
            .sum();
        if self.added + size > self.bounds.blocks {
            return None;
        }
        let removals = if ch.once {
            std::iter::once(ch.make)
                .chain(ch.steps.iter().copied())
                .collect()
        } else {
            Vec::new()
        };
        Some(KontPlan {
            closure: ch.closure,
            removals,
        })
    }

    /// Removes the statements `at` (block, index) of body `b`: the make of a
    /// closure with a `once` continuation and the steps of its chain
    /// ([`KontPlan::removals`]).
    fn remove_make(&mut self, b: BodyId, at: &[(BlockId, usize)]) {
        let Some(body) = self.p.bodies.get_mut(b.index()) else {
            return;
        };
        let mut sorted = at.to_vec();
        sorted.sort_by_key(|y| std::cmp::Reverse((y.0, y.1)));
        for (blk, si) in sorted {
            if let Some(x) = body.blocks.get_mut(blk.index()) {
                if si < x.stmts.len() {
                    x.stmts.remove(si);
                }
            }
        }
    }

    /// The environment `e` of the callee, in the copy, for a body inside
    /// closure `ctx` of the copy: the root environment of the callee is the
    /// environment of the call, and the environment of the closure body is
    /// its new environment.
    fn env(&mut self, c: &mut Copy, e: CapEnvId, ctx: Option<ClosureId>) -> CapEnvId {
        if let Some(x) = ctx.and_then(|k| c.extra.get(&k)) {
            if e == x.body_env {
                return x.new_env;
            }
        }
        if e == c.root_env {
            return c.call_env;
        }
        if let Some(&x) = c.envs.get(&(e, ctx)) {
            return x;
        }
        let Some(old) = self.p.cap_envs.get(e.index()).cloned() else {
            return e;
        };
        let parent = old.parent.map(|q| self.env(c, q, ctx));
        let id = CapEnvId(u32::try_from(self.p.cap_envs.len()).unwrap_or(u32::MAX));
        self.p.cap_envs.push(CapEnv {
            parent,
            adds: old.adds,
        });
        c.envs.insert((e, ctx), id);
        id
    }

    /// The place in body `x` of the capability that serves operation `op`
    /// of effect `e` in environment `env`.
    fn cap_place(
        &mut self,
        x: BodyId,
        env: CapEnvId,
        e: EffectId,
        op: OpIdx,
    ) -> Result<Place, NoCopy> {
        let (owner, place) = serving_cap(&self.p, env, e, op).ok_or(NoCopy)?;
        self.upvar_chain(x, owner, place)
    }

    /// Place `place` of body `owner` in body `x`, a body inside it: an
    /// upvar local in each body on the way.
    fn upvar_chain(&mut self, x: BodyId, owner: BodyId, place: Place) -> Result<Place, NoCopy> {
        // The bodies from `x` up to `owner`.
        let mut path: Vec<BodyId> = vec![x];
        let mut at = x;
        while at != owner {
            let parent = self.p.body(at).and_then(|b| b.parent).ok_or(NoCopy)?;
            path.push(parent);
            at = parent;
            if path.len() > self.p.bodies.len() {
                return Err(NoCopy);
            }
        }
        // From the owner down: the local in each body.
        let mut local = place.local;
        for w in path.iter().rev().skip(1) {
            let parent = self.p.body(*w).and_then(|b| b.parent).ok_or(NoCopy)?;
            let body = self.p.body(*w).ok_or(NoCopy)?;
            if !body.kind.has_upvars() {
                return Err(NoCopy);
            }
            let found = body
                .locals
                .iter()
                .position(|d| d.kind == LocalKind::Upvar(local));
            local = if let Some(i) = found {
                LocalId(u32::try_from(i).unwrap_or(u32::MAX))
            } else {
                let decl = self
                    .p
                    .body(parent)
                    .and_then(|b| b.local(local))
                    .cloned()
                    .ok_or(NoCopy)?;
                let b = self.p.bodies.get_mut(w.index()).ok_or(NoCopy)?;
                let id = LocalId(u32::try_from(b.locals.len()).unwrap_or(u32::MAX));
                b.locals.push(LocalDecl {
                    kind: LocalKind::Upvar(local),
                    in_place: false,
                    ..decl
                });
                id
            };
        }
        Ok(Place {
            local,
            proj: place.proj,
        })
    }

    /// The terminator `t` of the copy in body `x`: the blocks with `blk`,
    /// the locals with `f`, and a perform
    /// through the row that environment `env` serves goes to its capability.
    fn map_term(
        &mut self,
        c: &mut Copy,
        x: BodyId,
        t: &TermKind,
        f: &PlaceMap<'_>,
        blk: &impl Fn(BlockId) -> BlockId,
        (env, ctx): (CapEnvId, Option<ClosureId>),
    ) -> Result<TermKind, NoCopy> {
        let mp = |p: &Place| map_place(p, f);
        let mo = |o: &Operand| map_operand(o, f);
        let mu = |u: &Option<BlockId>| u.map(blk);
        Ok(match t {
            TermKind::Goto(b) => TermKind::Goto(blk(*b)),
            TermKind::Switch {
                on,
                arms,
                otherwise,
            } => TermKind::Switch {
                on: mo(on),
                arms: arms.iter().map(|(v, b)| (*v, blk(*b))).collect(),
                otherwise: blk(*otherwise),
            },
            TermKind::Return => TermKind::Return,
            TermKind::UnwindExit => TermKind::UnwindExit,
            TermKind::Unreachable => TermKind::Unreachable,
            TermKind::Call {
                callee,
                args,
                dest,
                caps,
                next,
                unwind,
            } => TermKind::Call {
                callee: match callee {
                    Callee::Fn(g, ts) => Callee::Fn(*g, ts.clone()),
                    Callee::Value(o) => Callee::Value(mo(o)),
                },
                args: args.iter().map(mo).collect(),
                dest: mp(dest),
                caps: match caps {
                    CapArgs::Lexical(e) => CapArgs::Lexical(self.env(c, *e, ctx)),
                    CapArgs::Root => CapArgs::Root,
                },
                next: next.map(blk),
                unwind: mu(unwind),
            },
            TermKind::Perform {
                cap,
                op,
                args,
                dest,
                next,
                unwind,
            } => {
                let cap = match cap {
                    CapOperand::Row(e) if env_binds(&self.p, env, *e) => {
                        CapOperand::Local(self.cap_place(x, env, *e, *op)?)
                    }
                    CapOperand::Row(e) => CapOperand::Row(*e),
                    CapOperand::Local(q) => CapOperand::Local(mp(q)),
                };
                TermKind::Perform {
                    cap,
                    op: *op,
                    args: args.iter().map(mo).collect(),
                    dest: mp(dest),
                    next: blk(*next),
                    unwind: mu(unwind),
                }
            }
            TermKind::Resume {
                kont,
                arg,
                dest,
                next,
                unwind,
            } => TermKind::Resume {
                kont: mp(kont),
                arg: mo(arg),
                dest: mp(dest),
                next: blk(*next),
                unwind: mu(unwind),
            },
            TermKind::Handle {
                handler,
                dest,
                next,
                unwind,
            } => TermKind::Handle {
                handler: c.handlers.get(handler).copied().ok_or(NoCopy)?,
                dest: mp(dest),
                next: blk(*next),
                unwind: mu(unwind),
            },
            TermKind::Scope {
                scope,
                dest,
                next,
                unwind,
            } => TermKind::Scope {
                scope: c.scopes.get(scope).copied().ok_or(NoCopy)?,
                dest: mp(dest),
                next: blk(*next),
                unwind: mu(unwind),
            },
            TermKind::ScopeWait {
                scope,
                orphans,
                next,
                unwind,
            } => TermKind::ScopeWait {
                scope: mp(scope),
                orphans: orphans.iter().map(|l| f.l(*l)).collect(),
                next: blk(*next),
                unwind: mu(unwind),
            },
            TermKind::Spawn {
                site,
                scope,
                task,
                dest,
                next,
            } => TermKind::Spawn {
                site: c.spawns.get(site).copied().ok_or(NoCopy)?,
                scope: mo(scope),
                task: mo(task),
                dest: dest.as_ref().map(mp),
                next: blk(*next),
            },
            TermKind::Join {
                task,
                dest,
                next,
                unwind,
            } => TermKind::Join {
                task: mo(task),
                dest: mp(dest),
                next: blk(*next),
                unwind: mu(unwind),
            },
            TermKind::Detach { task, next } => TermKind::Detach {
                task: mo(task),
                next: blk(*next),
            },
            TermKind::Fork {
                sites,
                branches,
                dest,
                next,
                unwind,
            } => TermKind::Fork {
                sites: sites
                    .iter()
                    .map(|s| c.spawns.get(s).copied().ok_or(NoCopy))
                    .collect::<Result<_, _>>()?,
                branches: branches.iter().map(mo).collect(),
                dest: mp(dest),
                next: blk(*next),
                unwind: mu(unwind),
            },
            TermKind::Assert { cond, next, unwind } => TermKind::Assert {
                cond: mo(cond),
                next: blk(*next),
                unwind: mu(unwind),
            },
            TermKind::IterNext {
                iter,
                dest,
                next,
                done,
            } => TermKind::IterNext {
                iter: mp(iter),
                dest: mp(dest),
                next: blk(*next),
                done: blk(*done),
            },
        })
    }

    /// The kind of local `d` of a body of the copy.
    fn map_local(c: &Copy, d: &LocalDecl, upvar: &impl Fn(LocalId) -> LocalId) -> LocalDecl {
        let kind = match d.kind {
            LocalKind::Upvar(l) => LocalKind::Upvar(upvar(l)),
            LocalKind::TaskResult(s) => {
                LocalKind::TaskResult(c.spawns.get(&s).copied().unwrap_or(s))
            }
            k => k,
        };
        LocalDecl { kind, ..d.clone() }
    }

    /// Copies the callee of the call at block `k` of body `b` into `b`.
    fn copy(&mut self, b: BodyId, k: BlockId, what: What) -> Result<(), NoCopy> {
        match what {
            What::Fn(f) => {
                let ts = match self
                    .p
                    .body(b)
                    .and_then(|x| x.block(k))
                    .map(|x| &x.term.kind)
                {
                    Some(TermKind::Call {
                        callee: Callee::Fn(_, ts),
                        ..
                    }) => ts.clone(),
                    _ => return Err(NoCopy),
                };
                if ts.is_empty() {
                    let orig = self.orig;
                    self.copy_code(orig, b, k, what)
                } else {
                    // A generic callee: its body with the type arguments of the
                    // call (stage R0k-a2, `fixes/r0k/c09`).
                    let snap = subst_program(self.orig, &mut self.tys, f, &ts)?;
                    self.copy_code(&snap, b, k, what)
                }
            }
            What::Closure(_) => {
                let snap = self.p.clone();
                self.copy_code(&snap, b, k, what)
            }
            What::Dispatch => self.dispatch(b, k),
        }
    }

    fn copy_code(
        &mut self,
        orig: &Program,
        b: BodyId,
        k: BlockId,
        what: What,
    ) -> Result<(), NoCopy> {
        let (cb, callee) = match what {
            What::Dispatch => return Err(NoCopy),
            What::Fn(f) => (
                orig.fns.get(f.index()).and_then(|d| d.body).ok_or(NoCopy)?,
                f,
            ),
            What::Closure(cid) => {
                let cb = orig.closures.get(cid.index()).ok_or(NoCopy)?.body;
                (cb, fn_of(orig, cb).ok_or(NoCopy)?)
            }
        };
        let cbody = orig.body(cb).ok_or(NoCopy)?.clone();
        // A body with a copy region gets no copy (stage R0k-b1'): the blocks of
        // a copy would run with the handlers of the site, not those of the
        // closure value of the region.
        if orig
            .regions
            .iter()
            .any(|r| r.body == cb || inside(orig, r.body, cb))
        {
            return Err(NoCopy);
        }
        // A body with a dispatch gets no copy either (plan stage R0z Z6): the
        // ids of the tests and of the record then never change.
        if orig
            .dispatches
            .iter()
            .any(|d| d.body == cb || inside(orig, d.body, cb))
        {
            return Err(NoCopy);
        }
        // The environment of a closure body: its capability environment is
        // the one where the closure is made, in the site.
        let closure = match what {
            What::Closure(cid) => orig.closures.get(cid.index()).cloned(),
            What::Fn(_) | What::Dispatch => None,
        };
        let site = self.p.body(b).ok_or(NoCopy)?;
        let call = site.block(k).ok_or(NoCopy)?.term.clone();
        let TermKind::Call {
            args,
            dest,
            caps: CapArgs::Lexical(call_env),
            next,
            unwind: Some(unwind),
            ..
        } = call.kind.clone()
        else {
            return Err(NoCopy);
        };
        // The plan of a closure copy (stage R0k-b1'): the environment where
        // the closure is made, and the maker whose places the captures name.
        let plan = self.run_plan.clone().filter(|_| closure.is_some());
        let call_env = match (&plan, &closure) {
            (Some(r), _) => r.env,
            (None, Some(d)) => d.cap_env,
            (None, None) => call_env,
        };
        let inner = inner_bodies(orig, cb);
        let mut chain = self.chain(b, k);
        if matches!(what, What::Fn(_)) {
            chain.push(callee);
        }
        if let Some(f) = plan.as_ref().and_then(|r| r.callee) {
            chain.push(f);
        }
        let region = plan.as_ref().filter(|r| r.region).map(|r| r.maker);
        let mut c = Copy {
            local_base: u32::try_from(site.locals.len()).map_err(|_| NoCopy)?,
            block_base: u32::try_from(site.blocks.len()).map_err(|_| NoCopy)?,
            bodies: BTreeMap::new(),
            closures: BTreeMap::new(),
            handlers: BTreeMap::new(),
            scopes: BTreeMap::new(),
            spawns: BTreeMap::new(),
            call_env,
            root_env: cbody.cap_env,
            envs: BTreeMap::new(),
            ctx: BTreeMap::new(),
            extra: BTreeMap::new(),
            chain,
        };
        // The new ids of the bodies and the declarations inside the callee.
        let first = self.p.bodies.len();
        for (i, &ib) in inner.iter().enumerate() {
            c.bodies
                .insert(ib, BodyId(u32::try_from(first + i).map_err(|_| NoCopy)?));
        }
        for (ci, d) in orig.closures.iter().enumerate() {
            if c.bodies.contains_key(&d.body) {
                let id = ClosureId(u32::try_from(self.p.closures.len()).map_err(|_| NoCopy)?);
                let old = ClosureId(u32::try_from(ci).map_err(|_| NoCopy)?);
                c.closures.insert(old, id);
                let first = self.origin.get(&old).copied().unwrap_or(old);
                self.origin.insert(id, first);
                self.p.closures.push(d.clone());
            }
        }
        for &ib in &inner {
            let own = orig
                .closure_of(ib)
                .and_then(|(x, _)| c.closures.get(&x).copied());
            let up = orig
                .body(ib)
                .and_then(|x| x.parent)
                .and_then(|q| c.ctx.get(&q).copied())
                .flatten();
            c.ctx.insert(ib, own.or(up));
        }
        c.ctx.insert(cb, None);
        for (hi, d) in orig.handlers.iter().enumerate() {
            if c.bodies.contains_key(&d.handled) {
                let id = HandlerId(u32::try_from(self.p.handlers.len()).map_err(|_| NoCopy)?);
                c.handlers
                    .insert(HandlerId(u32::try_from(hi).map_err(|_| NoCopy)?), id);
                self.p.handlers.push(d.clone());
            }
        }
        for (si, d) in orig.scopes.iter().enumerate() {
            if c.bodies.contains_key(&d.body) {
                let id = ScopeId(u32::try_from(self.p.scopes.len()).map_err(|_| NoCopy)?);
                c.scopes
                    .insert(ScopeId(u32::try_from(si).map_err(|_| NoCopy)?), id);
                self.p.scopes.push(d.clone());
            }
        }
        // The spawn sites of the callee and of its bodies.
        let mut sites: BTreeSet<SpawnId> = BTreeSet::new();
        for x in std::iter::once(&cbody).chain(inner.iter().filter_map(|&x| orig.body(x))) {
            for blk in &x.blocks {
                match &blk.term.kind {
                    TermKind::Spawn { site, .. } => {
                        sites.insert(*site);
                    }
                    TermKind::Fork { sites: s, .. } => sites.extend(s.iter().copied()),
                    _ => {}
                }
            }
            for d in &x.locals {
                if let LocalKind::TaskResult(s) = d.kind {
                    sites.insert(s);
                }
            }
        }
        for s in sites {
            let mut d = orig.spawns.get(s.index()).cloned().ok_or(NoCopy)?;
            d.scope = d.scope.map(|q| c.scopes.get(&q).copied().unwrap_or(q));
            let id = SpawnId(u32::try_from(self.p.spawns.len()).map_err(|_| NoCopy)?);
            c.spawns.insert(s, id);
            self.p.spawns.push(d);
        }
        let body_map = c.bodies.clone();
        let bm = move |x: BodyId| -> BodyId {
            if x == cb {
                b
            } else {
                body_map.get(&x).copied().unwrap_or(x)
            }
        };
        // The new locals of the site go in first: an upvar local that a
        // perform of the copy needs comes after them.
        let base = c.local_base;
        let fl = move |l: LocalId| LocalId(base + l.0);
        let mut new_locals: Vec<LocalDecl> = Vec::new();
        for d in &cbody.locals {
            let mut nd = Self::map_local(&c, d, &fl);
            nd.kind = match d.kind {
                LocalKind::Return => LocalKind::Temp(TempKind::Value),
                LocalKind::Param(_) | LocalKind::Env => LocalKind::User,
                _ => nd.kind,
            };
            new_locals.push(nd);
        }
        // The places of the captures of a closure in the site: the source of
        // a `Kept` capture (the closure shares the cell of the variable), a
        // new reference to the source of a `ByRef` capture, the capability of
        // a `Cap` capture (`closure_copyable` refuses the other modes).
        let mut env_places: Vec<Place> = Vec::new();
        let mut borrows: Vec<(LocalId, Place)> = Vec::new();
        // In a copy region (stage R0k-b1') the sources are places of the
        // maker: they go to the site through upvar locals, after the new
        // locals of the site (`deferred`: the index in `env_places`, or in
        // `borrows` for a `ByRef` capture).
        let mut deferred: Vec<(bool, usize, Place)> = Vec::new();
        // The environment local of the region (plan stage R0k-b2): a view of
        // the closure value, for the captures that the copy reads as cells of
        // the value.
        let env_caps: BTreeSet<usize> = plan
            .as_ref()
            .map(|r| r.env_caps.clone())
            .unwrap_or_default();
        // The callee of the run, and for a `once` closure the new local that
        // the copy moves the value into (plan stage R0z Z3, part d): the
        // region reads the value there, and its end ends the value.
        let callee_place = match &call.kind {
            TermKind::Call {
                callee: Callee::Value(Operand::Copy(q) | Operand::Move(q)),
                ..
            } => Some(q.clone()),
            _ => None,
        };
        let moved_to: Option<LocalId> = match &plan {
            Some(r) if r.moves => {
                if !r.region {
                    return Err(NoCopy);
                }
                let q = callee_place.clone().filter(Place::is_local).ok_or(NoCopy)?;
                let ty = self
                    .p
                    .body(b)
                    .and_then(|x| x.local(q.local))
                    .ok_or(NoCopy)?
                    .ty;
                let mut props = crate::props::ir_props(&self.tys, ty);
                props.copy = false;
                props.once = true;
                let id = LocalId(base + u32::try_from(new_locals.len()).map_err(|_| NoCopy)?);
                new_locals.push(LocalDecl {
                    ty,
                    kind: LocalKind::Temp(TempKind::Value),
                    name: None,
                    props,
                    in_place: false,
                    origin: call.origin,
                });
                Some(id)
            }
            _ => None,
        };
        let copy_env: Option<LocalId> = if let (Some(r), false) = (&plan, env_caps.is_empty()) {
            if !r.region {
                return Err(NoCopy);
            }
            let q = callee_place.clone().filter(Place::is_local).ok_or(NoCopy)?;
            let ty = self
                .p
                .body(b)
                .and_then(|x| x.local(q.local))
                .ok_or(NoCopy)?
                .ty;
            let id = LocalId(base + u32::try_from(new_locals.len()).map_err(|_| NoCopy)?);
            new_locals.push(LocalDecl {
                ty,
                kind: LocalKind::CopyEnv(r.closure),
                name: None,
                props: crate::props::ir_props(&self.tys, ty),
                in_place: false,
                origin: call.origin,
            });
            Some(id)
        } else {
            None
        };
        if let Some(d) = &closure {
            let mut next_local = base + u32::try_from(new_locals.len()).map_err(|_| NoCopy)?;
            for (ci, cap) in d.captures.iter().enumerate() {
                if let (true, Some(e)) = (env_caps.contains(&ci), copy_env) {
                    env_places.push(Place {
                        local: e,
                        proj: vec![Proj::Field(weft_ir::FieldIdx(
                            u32::try_from(ci).map_err(|_| NoCopy)?,
                        ))],
                    });
                    continue;
                }
                match cap.mode {
                    // A `Kont` capture (stage R0k-c1, only in the mode of
                    // `instantiate_kont`): the continuation of the clause.
                    weft_ir::CaptureMode::Kept
                    | weft_ir::CaptureMode::Cap
                    | weft_ir::CaptureMode::Kont => {
                        if region.is_some() {
                            deferred.push((false, env_places.len(), cap.source.clone()));
                        }
                        env_places.push(cap.source.clone());
                    }
                    weft_ir::CaptureMode::ByRef => {
                        let ty_src = match region {
                            Some(m) => {
                                deferred.push((true, borrows.len(), cap.source.clone()));
                                (m, cap.source.clone())
                            }
                            None => (b, cap.source.clone()),
                        };
                        let t = crate::factgen::alpha::place_ty(
                            &self.p,
                            &mut self.tys,
                            ty_src.0,
                            &ty_src.1,
                        )
                        .ok_or(NoCopy)?;
                        let rt = self.tys.intern(weft_ir::Ty::Ref(t));
                        let origin = self
                            .p
                            .body(b)
                            .and_then(|x| x.block(k))
                            .map(|x| x.term.origin)
                            .unwrap_or_default();
                        new_locals.push(LocalDecl {
                            ty: rt,
                            kind: LocalKind::User,
                            name: None,
                            props: crate::props::ir_props(&self.tys, rt),
                            in_place: false,
                            origin,
                        });
                        let l = LocalId(next_local);
                        next_local += 1;
                        borrows.push((l, cap.source.clone()));
                        env_places.push(Place::local(l));
                    }
                    weft_ir::CaptureMode::ByMove => return Err(NoCopy),
                }
            }
        }
        let env_local = closure.as_ref().and_then(|_| cbody.params.first().copied());
        self.p
            .bodies
            .get_mut(b.index())
            .ok_or(NoCopy)?
            .locals
            .extend(new_locals);
        if let Some(m) = region {
            for (borrow, i, src) in deferred {
                let (a, q) = root_place(&self.p, m, &src).ok_or(NoCopy)?;
                let mapped = self.upvar_chain(b, a, q)?;
                let slot = if borrow {
                    borrows.get_mut(i).map(|x| &mut x.1)
                } else {
                    env_places.get_mut(i)
                };
                *slot.ok_or(NoCopy)? = mapped;
            }
        }
        let pm = PlaceMap {
            local: &fl,
            env: env_local.map(|e| (e, env_places.as_slice())),
        };
        // The declarations of the copy name the new bodies. A closure of the
        // callee performs through the capabilities of the point where it is
        // made: in the copy, it gets a `Cap` field for each effect that the
        // environment of the call serves and that its code can use.
        let mut pairs: Vec<(ClosureId, ClosureId)> =
            c.closures.iter().map(|(x, y)| (*x, *y)).collect();
        pairs.sort_by_key(|(x, _)| orig.closures.get(x.index()).map(|d| d.body));
        for (old, new) in pairs {
            let d = orig.closures.get(old.index()).ok_or(NoCopy)?.clone();
            let captures: Vec<weft_ir::Capture> = d
                .captures
                .iter()
                .map(|cap| weft_ir::Capture {
                    source: if d.maker == cb {
                        map_place(&cap.source, &pm)
                    } else {
                        cap.source.clone()
                    },
                    mode: cap.mode,
                })
                .collect();
            let maker_ctx = c.ctx.get(&d.maker).copied().flatten();
            let maker_env = self.env(&mut c, d.cap_env, maker_ctx);
            let used = self.closure_uses(orig, d.body);
            let own: Vec<(EffectId, Place)> = orig
                .body(d.body)
                .filter(|x| x.cap_env != d.cap_env)
                .and_then(|x| orig.cap_envs.get(x.cap_env.index()))
                .map(|e| e.adds.clone())
                .unwrap_or_default();
            let extra: Vec<EffectId> = used
                .into_iter()
                .filter(|&e| !own.iter().any(|(x, _)| *x == e) && env_binds(&self.p, maker_env, e))
                .collect();
            let nd = self.p.closures.get_mut(new.index()).ok_or(NoCopy)?;
            nd.body = bm(d.body);
            nd.maker = bm(d.maker);
            let first_field = captures.len();
            nd.captures = captures;
            nd.cap_env = maker_env;
            let mut fields = Vec::new();
            for (i, e) in extra.into_iter().enumerate() {
                let field = weft_ir::FieldIdx(u32::try_from(first_field + i).map_err(|_| NoCopy)?);
                fields.push((e, field));
            }
            let ob = orig.body(d.body).ok_or(NoCopy)?;
            let new_env = self.closure_env(ob, maker_env, own, &fields)?;
            c.extra.insert(
                new,
                Extra {
                    maker: bm(d.maker),
                    env: maker_env,
                    fields,
                    body_env: ob.cap_env,
                    new_env,
                },
            );
        }
        // The maker body of a closure that a body of the copy makes goes into
        // the program below; the site is there now.
        self.add_cap_sources(&c, b)?;
        for (&old, &new) in &c.handlers {
            let d = orig.handlers.get(old.index()).ok_or(NoCopy)?;
            let nd = self.p.handlers.get_mut(new.index()).ok_or(NoCopy)?;
            nd.handled = bm(d.handled);
            nd.site = bm(d.site);
            nd.clauses = d.clauses.iter().map(|&(o, x)| (o, bm(x))).collect();
        }
        for (&old, &new) in &c.scopes {
            let d = orig.scopes.get(old.index()).ok_or(NoCopy)?;
            let nd = self.p.scopes.get_mut(new.index()).ok_or(NoCopy)?;
            nd.body = bm(d.body);
            nd.site = bm(d.site);
        }
        // The blocks of the copy.
        let bb = c.block_base;
        let fb = move |x: BlockId| BlockId(bb + 1 + x.0);
        let origin = call.origin;
        let mut entry_stmts: Vec<Stmt> = Vec::new();
        // The entry of a copy region reads the closure value first: the
        // interpreter takes its handlers there (`docs/ir.md` 6.1).
        let value = match moved_to {
            Some(t) => Some(Place::local(t)),
            None => call_value_place(&call.kind),
        };
        // The end of a value that the copy moved (plan stage R0z Z3, part
        // d): at a normal exit, and on the cleanup path.
        let moved_end: Vec<Stmt> = moved_to
            .map(|t| Stmt {
                kind: StmtKind::Dead(t),
                origin,
            })
            .into_iter()
            .collect();
        let moved_unwind: Vec<Stmt> = moved_to
            .map(|t| {
                vec![
                    Stmt {
                        kind: StmtKind::UnwindValue(Place::local(t), weft_ir::UnwindAction::Drop),
                        origin,
                    },
                    Stmt {
                        kind: StmtKind::Dead(t),
                        origin,
                    },
                ]
            })
            .unwrap_or_default();
        if let (Some(_), Some(q)) = (region, &value) {
            entry_stmts.push(Stmt {
                kind: StmtKind::Mention(q.clone()),
                origin,
            });
        }
        for &(l, ref q) in &borrows {
            entry_stmts.push(Stmt {
                kind: StmtKind::Live(l),
                origin,
            });
            entry_stmts.push(Stmt {
                kind: StmtKind::Assign(Place::local(l), Rvalue::Ref(q.clone())),
                origin,
            });
        }
        // The run of a closure uses the closure value: its references (a
        // `ByRef` capture) are live up to the run, as before the copy.
        if let (Some(_), Some(q), false, None) = (
            &closure,
            call_value_place(&call.kind),
            self.skip_mention,
            region,
        ) {
            entry_stmts.push(Stmt {
                kind: StmtKind::Mention(q),
                origin,
            });
        }
        let skip = usize::from(closure.is_some());
        if cbody.params.len() != args.len() + skip {
            return Err(NoCopy);
        }
        for (i, &pl) in cbody.params.iter().enumerate().skip(skip) {
            let arg = args.get(i - skip).cloned().ok_or(NoCopy)?;
            entry_stmts.push(Stmt {
                kind: StmtKind::Live(fl(pl)),
                origin,
            });
            entry_stmts.push(Stmt {
                kind: StmtKind::Assign(Place::local(fl(pl)), Rvalue::Use(arg)),
                origin,
            });
        }
        entry_stmts.push(Stmt {
            kind: StmtKind::Live(fl(cbody.ret)),
            origin,
        });
        let mut blocks: Vec<weft_ir::Block> = vec![weft_ir::Block {
            stmts: entry_stmts,
            term: Term {
                kind: TermKind::Goto(fb(cbody.entry)),
                origin,
            },
            cleanup: false,
        }];
        let closures_map = c.closures.clone();
        let clm = move |x: ClosureId| closures_map.get(&x).copied().unwrap_or(x);
        for blk in &cbody.blocks {
            let mut stmts: Vec<Stmt> = Vec::new();
            for st in &blk.stmts {
                stmts.push(self.copy_stmt(&c, st, &pm, &clm)?);
            }
            let ends: Vec<Stmt> = borrows
                .iter()
                .map(|&(l, _)| Stmt {
                    kind: StmtKind::Dead(l),
                    origin,
                })
                .collect();
            let term = match &blk.term.kind {
                TermKind::Return => match &next {
                    Some(n) => {
                        stmts.push(Stmt {
                            kind: StmtKind::Assign(
                                dest.clone(),
                                Rvalue::Use(Operand::Move(Place::local(fl(cbody.ret)))),
                            ),
                            origin,
                        });
                        stmts.push(Stmt {
                            kind: StmtKind::Dead(fl(cbody.ret)),
                            origin: blk.term.origin,
                        });
                        stmts.extend(ends.iter().cloned());
                        stmts.extend(moved_end.iter().cloned());
                        TermKind::Goto(*n)
                    }
                    None => TermKind::Unreachable,
                },
                TermKind::UnwindExit => {
                    stmts.extend(ends.iter().cloned());
                    stmts.extend(moved_unwind.iter().cloned());
                    TermKind::Goto(unwind)
                }
                t => self.map_term(&mut c, b, t, &pm, &fb, (call_env, None))?,
            };
            blocks.push(weft_ir::Block {
                stmts,
                term: Term {
                    kind: term,
                    origin: blk.term.origin,
                },
                cleanup: blk.cleanup,
            });
        }
        // The bodies inside the callee.
        for &ib in &inner {
            let ob = orig.body(ib).ok_or(NoCopy)?.clone();
            let nid = bm(ib);
            let parent_is_callee = ob.parent == Some(cb);
            let up = move |l: LocalId| {
                if parent_is_callee {
                    LocalId(base + l.0)
                } else {
                    l
                }
            };
            let locals: Vec<LocalDecl> = ob
                .locals
                .iter()
                .map(|d| Self::map_local(&c, d, &up))
                .collect();
            let kind = match ob.kind {
                BodyKind::Closure(x) => BodyKind::Closure(clm(x)),
                BodyKind::Clause(h, o) => {
                    BodyKind::Clause(c.handlers.get(&h).copied().ok_or(NoCopy)?, o)
                }
                BodyKind::Handled(h) => {
                    BodyKind::Handled(c.handlers.get(&h).copied().ok_or(NoCopy)?)
                }
                BodyKind::Scope(s) => BodyKind::Scope(c.scopes.get(&s).copied().ok_or(NoCopy)?),
                k => k,
            };
            let ctx = c.ctx.get(&ib).copied().flatten();
            let env = self.env(&mut c, ob.cap_env, ctx);
            // The new body goes into the program first, so that a perform in it
            // can add the upvar locals of the capability.
            if self.p.bodies.len() != nid.index() {
                return Err(NoCopy);
            }
            self.p.bodies.push(Body {
                kind,
                parent: ob.parent.map(&bm),
                locals,
                blocks: Vec::new(),
                cap_env: env,
                ..ob.clone()
            });
            // The `Cap` captures of the closures that this body makes.
            self.add_cap_sources(&c, nid)?;
            let same_l = |l: LocalId| l;
            let same = PlaceMap::new(&same_l);
            let id = |x: BlockId| x;
            let mut nblocks = Vec::new();
            for blk in &ob.blocks {
                let mut stmts = Vec::new();
                for st in &blk.stmts {
                    stmts.push(self.copy_stmt(&c, st, &same, &clm)?);
                }
                let term = self.map_term(&mut c, nid, &blk.term.kind, &same, &id, (env, ctx))?;
                nblocks.push(weft_ir::Block {
                    stmts,
                    term: Term {
                        kind: term,
                        origin: blk.term.origin,
                    },
                    cleanup: blk.cleanup,
                });
            }
            if let Some(x) = self.p.bodies.get_mut(nid.index()) {
                x.blocks = nblocks;
            }
        }
        // The code goes into the site.
        let nblocks = blocks.len();
        let site = self.p.bodies.get_mut(b.index()).ok_or(NoCopy)?;
        let entry = BlockId(c.block_base);
        if let Some(blk) = site.blocks.get_mut(k.index()) {
            blk.term.kind = TermKind::Goto(entry);
            // The copy of a `once` closure moves the value first (plan stage
            // R0z Z3, part d), as the run did.
            if let (Some(t), Some(q)) = (moved_to, &callee_place) {
                blk.stmts.push(Stmt {
                    kind: StmtKind::Live(t),
                    origin,
                });
                self.run_moves.insert((b, k, blk.stmts.len()));
                blk.stmts.push(Stmt {
                    kind: StmtKind::Assign(Place::local(t), Rvalue::Use(Operand::Move(q.clone()))),
                    origin,
                });
            }
        }
        site.blocks.extend(blocks);
        // A copy at a call inside a copy region is a part of the region: its
        // code runs with the handlers of the closure value of the region.
        let first = c.block_base;
        let last = first + u32::try_from(nblocks).map_err(|_| NoCopy)?;
        if let Some(r) = self
            .p
            .regions
            .iter_mut()
            .find(|r| r.body == b && r.blocks.binary_search(&k).is_ok())
        {
            r.blocks.extend((first..last).map(BlockId));
        }
        if let (Some(_), Some(q), Some(r)) = (region, value, &plan) {
            self.p.regions.push(weft_ir::CopyRegion {
                body: b,
                entry: BlockId(first),
                blocks: (first..last).map(BlockId).collect(),
                env: call_env,
                value: q,
                closure: r.closure,
                sole: false,
                env_local: copy_env,
                env_fns: r.env_fns.clone(),
                also: r.also.clone(),
            });
            // The way of a value that the copy moves goes through the new
            // local.
            let mut chain = r.chain.clone();
            if let Some(t) = moved_to {
                chain.push(Link::Local(b, t));
            }
            for c in std::iter::once(r.closure).chain(r.also.iter().copied()) {
                self.chains
                    .entry(c)
                    .or_default()
                    .extend(chain.iter().copied());
                self.copied.insert(c);
            }
            self.regions += 1;
        }
        for i in 0..nblocks {
            let id = BlockId(c.block_base + u32::try_from(i).unwrap_or(u32::MAX));
            self.blk_chain.insert((b, id), c.chain.clone());
            self.sites.insert((b, id), (b, k, callee));
        }
        for &nid in c.bodies.values() {
            self.body_chain.insert(nid, c.chain.clone());
            self.body_sites.insert(nid, (b, k, callee));
        }
        self.added += nblocks
            + inner
                .iter()
                .filter_map(|&x| orig.body(x))
                .map(|x| x.blocks.len())
                .sum::<usize>();
        if matches!(what, What::Fn(_)) {
            self.calls += 1;
        } else {
            self.closure_calls += 1;
        }
        Ok(())
    }

    /// The statement `st` of the copy: the locals with `f`, the closures with
    /// `cl`, and a closure with new `Cap` captures gets their operands.
    fn copy_stmt(
        &self,
        c: &Copy,
        st: &Stmt,
        f: &PlaceMap<'_>,
        cl: &impl Fn(ClosureId) -> ClosureId,
    ) -> Result<Stmt, NoCopy> {
        let mut out = map_stmt(st, f, cl);
        if let StmtKind::Assign(_, Rvalue::Aggregate(weft_ir::AggKind::Closure(cid), ops)) =
            &mut out.kind
        {
            if let Some(Extra { fields, .. }) = c.extra.get(cid) {
                let d = self.p.closures.get(cid.index()).ok_or(NoCopy)?;
                let have = ops.len();
                for cap in d.captures.iter().skip(have) {
                    ops.push(Operand::Copy(cap.source.clone()));
                }
                if ops.len() != have + fields.len() {
                    return Err(NoCopy);
                }
            }
        }
        Ok(out)
    }

    /// The `Cap` capture sources of each closure of the copy that body `maker`
    /// makes, now that `maker` is in the program.
    fn add_cap_sources(&mut self, c: &Copy, maker: BodyId) -> Result<(), NoCopy> {
        let keys: Vec<ClosureId> = c
            .extra
            .iter()
            .filter(|(_, x)| x.maker == maker && !x.fields.is_empty())
            .map(|(k, _)| *k)
            .collect();
        for cid in keys {
            let Some(Extra { env, fields, .. }) = c.extra.get(&cid).cloned() else {
                continue;
            };
            let mut srcs = Vec::new();
            for &(e, _) in &fields {
                srcs.push(self.cap_source(maker, env, e)?);
            }
            let nd = self.p.closures.get_mut(cid.index()).ok_or(NoCopy)?;
            for src in srcs {
                nd.captures.push(weft_ir::Capture {
                    source: src,
                    mode: weft_ir::CaptureMode::Cap,
                });
            }
        }
        Ok(())
    }

    /// The place in body `x` of the capability of effect `e` that
    /// environment `env` binds first (the capability that a closure made in
    /// `x` captures, as `Builder::cap_of`).
    fn cap_source(&mut self, x: BodyId, env: CapEnvId, e: EffectId) -> Result<Place, NoCopy> {
        let (owner, place) = first_cap(&self.p, env, e).ok_or(NoCopy)?;
        self.upvar_chain(x, owner, place)
    }

    /// The environment of closure body `ob` in the copy: its own `Cap`
    /// fields `own` and the new ones `fields`, on environment `maker_env` of
    /// its maker.
    fn closure_env(
        &mut self,
        ob: &Body,
        maker_env: CapEnvId,
        own: Vec<(EffectId, Place)>,
        fields: &[(EffectId, weft_ir::FieldIdx)],
    ) -> Result<CapEnvId, NoCopy> {
        let mut adds = own;
        let env_local = ob.params.first().copied().ok_or(NoCopy)?;
        for &(e, field) in fields {
            adds.push((
                e,
                Place {
                    local: env_local,
                    proj: vec![Proj::Field(field)],
                },
            ));
        }
        if adds.is_empty() {
            return Ok(maker_env);
        }
        let id = CapEnvId(u32::try_from(self.p.cap_envs.len()).map_err(|_| NoCopy)?);
        self.p.cap_envs.push(CapEnv {
            parent: Some(maker_env),
            adds,
        });
        Ok(id)
    }

    /// The effects that the code of closure body `cb` of the original
    /// program can perform through the capabilities of its maker: its
    /// performs through the row, the rows of its calls, also in the bodies
    /// inside it.
    fn closure_uses(&self, orig: &Program, cb: BodyId) -> BTreeSet<EffectId> {
        let all: BTreeSet<EffectId> = (0..self.tys.effects().len())
            .map(|i| EffectId(u32::try_from(i).unwrap_or(u32::MAX)))
            .collect();
        let mut out = BTreeSet::new();
        for x in std::iter::once(cb).chain(inner_bodies(orig, cb)) {
            let Some(body) = orig.body(x) else {
                continue;
            };
            for blk in &body.blocks {
                match &blk.term.kind {
                    TermKind::Perform {
                        cap: CapOperand::Row(e),
                        ..
                    } => {
                        out.insert(*e);
                    }
                    TermKind::Call {
                        callee: Callee::Fn(g, _),
                        ..
                    } => {
                        if self.needs.unknown.contains(g) {
                            return all;
                        }
                        out.extend(self.needs.row.get(g).into_iter().flatten().copied());
                    }
                    TermKind::Call {
                        callee: Callee::Value(o),
                        ..
                    } => match value_row(&self.tys, body, o) {
                        Some(r) => out.extend(r),
                        None => return all,
                    },
                    _ => {}
                }
            }
        }
        out
    }
}

/// The stated row of the function value of operand `o` of body `body`, or
/// `None` if the type states no row (a call passes each effect through) or
/// the operand is not a whole local.
fn value_row(tys: &TyTable, body: &Body, o: &Operand) -> Option<Vec<EffectId>> {
    let pl = o.place()?;
    if !pl.is_local() {
        return None;
    }
    let t = body.local(pl.local)?.ty;
    match tys.try_get(t)? {
        weft_ir::Ty::Fn(f) => f.row.clone(),
        _ => None,
    }
}

/// The first environment of the chain of `env` that adds effect `e`, as the
/// body that adds it and the place of the capability there.
fn first_cap(p: &Program, env: CapEnvId, e: EffectId) -> Option<(BodyId, Place)> {
    let mut at = Some(env);
    for _ in 0..=p.cap_envs.len() {
        let id = at?;
        let c = p.cap_envs.get(id.index())?;
        if let Some((_, place)) = c.adds.iter().find(|(x, _)| *x == e) {
            let owner = owner_of_env(p, id, e)?;
            return Some((owner, place.clone()));
        }
        at = c.parent;
    }
    None
}

/// The body that opens environment `id` with the capability of effect `e`:
/// a handled body, or a closure body with a `Cap` field.
fn owner_of_env(p: &Program, id: CapEnvId, e: EffectId) -> Option<BodyId> {
    p.bodies.iter().enumerate().find_map(|(i, b)| {
        let yes = b.cap_env == id
            && match b.kind {
                BodyKind::Handled(_) => b.caps.iter().any(|(x, _)| *x == e),
                BodyKind::Closure(_) => true,
                _ => false,
            };
        yes.then(|| BodyId(u32::try_from(i).unwrap_or(u32::MAX)))
    })
}

/// The program of `built` with the copies of the callees at their calls.
///
/// A call gets a copy if a local handler serves an operation that the
/// callee performs with a function value or a reference (see the module
/// text). `None` if no call gets a copy or a copy breaks a rule of the IR.
pub fn instantiate(built: &Built) -> Option<Instantiated> {
    instantiate_with(built, Bounds::default())
}

/// [`instantiate`] with the bounds `bounds`.
pub fn instantiate_with(built: &Built, bounds: Bounds) -> Option<Instantiated> {
    instantiate_mode(built, bounds, false)
}

/// The copies of stage R0k-c1 (`docs/ir.md` 6.1).
///
/// A closure that a clause makes and that resumes the continuation of the
/// clause gets a copy of its body at its one run in the clause (D1a), also
/// in the copy of a callee that gets the closure (D1c). Then the `resume` is
/// a resume point of the clause. `None` if no copy is made.
pub fn instantiate_kont(built: &Built) -> Option<Instantiated> {
    instantiate_mode(built, Bounds::default(), true)
}

/// [`instantiate_with`], or [`instantiate_kont`] with `kont`.
fn instantiate_mode(built: &Built, bounds: Bounds, kont: bool) -> Option<Instantiated> {
    let orig = &built.program;
    let needs = Needs::of(orig, &built.tys);
    let mut inst = Inst {
        bounds,
        orig,
        tys: built.tys.clone(),
        closure_calls: 0,
        needs,
        p: orig.clone(),
        added: 0,
        calls: 0,
        blk_chain: HashMap::new(),
        body_chain: HashMap::new(),
        sites: BTreeMap::new(),
        body_sites: BTreeMap::new(),
        kont,
        covered: BTreeSet::new(),
        skip_mention: false,
        run_plan: None,
        regions: 0,
        copied: BTreeSet::new(),
        chains: BTreeMap::new(),
        origin: BTreeMap::new(),
        run_moves: BTreeSet::new(),
        multi: false,
        dplan: None,
        no_copy: BTreeSet::new(),
        dispatch_tries: std::cell::Cell::new(0),
        clause_callees: BTreeSet::new(),
        cell_writes: std::cell::RefCell::new(HashMap::new()),
        dispatches: 0,
    };
    // The pre-scan of plan stage R0z Z6, Part B.
    if !inst.kont {
        inst.clause_callees = inst.clause_callees();
    }
    sweep(&mut inst);
    // The second sweep (plan stage R0z Z3, part a): the runs whose value can
    // be one of more copies of the same closure. The first sweep makes the
    // copies of the makers first.
    if !inst.kont {
        inst.multi = true;
        sweep(&mut inst);
        inst.multi = false;
    }
    finish_inst(inst, orig, built)
}

/// One sweep of the copies over the bodies and the blocks of the program of
/// `inst`. In the second sweep ([`Inst::multi`]) a block that is in the
/// program at its start gets only a copy of a closure body whose value can
/// be one of more copies of the same closure; a block that a copy adds gets
/// each kind of copy.
fn sweep(inst: &mut Inst<'_>) {
    let sizes: Vec<usize> = inst.p.bodies.iter().map(|x| x.blocks.len()).collect();
    let mut bi = 0usize;
    while bi < inst.p.bodies.len() {
        let b = BodyId(u32::try_from(bi).unwrap_or(u32::MAX));
        let mut k = 0usize;
        while k < inst.p.bodies.get(bi).map_or(0, |x| x.blocks.len()) {
            let blk = BlockId(u32::try_from(k).unwrap_or(u32::MAX));
            let mut plan: Option<KontPlan> = None;
            let old = inst.multi && sizes.get(bi).is_some_and(|&n| k < n);
            let what = if inst.no_copy.contains(&(b, blk)) {
                // A block of a dispatch (plan stage R0z Z6).
                None
            } else if old {
                // The first sweep tried each kind of copy at this block.
                let run = inst.closure_copy(b, blk).filter(|x| !x.also.is_empty());
                let w = run.as_ref().map(|x| What::Closure(x.closure));
                inst.run_plan = run;
                // A run whose value can be closures of more origins: a
                // dispatch (plan stage R0z Z6).
                if w.is_none() {
                    inst.dplan = inst.dispatch_plan(b, blk);
                    inst.dplan.as_ref().map(|_| What::Dispatch)
                } else {
                    w
                }
            } else if inst.kont {
                match inst.kont_wants(b, blk) {
                    Some(f) if inst.can_copy(b, blk, f) => Some(What::Fn(f)),
                    Some(_) => None,
                    None => {
                        plan = inst.kont_copy(b, blk);
                        plan.as_ref().map(|x| What::Closure(x.closure))
                    }
                }
            } else {
                match inst.wants(b, blk) {
                    Some(f) if inst.can_copy(b, blk, f) => Some(What::Fn(f)),
                    Some(_) => None,
                    None => {
                        let run = inst.closure_copy(b, blk);
                        let w = run.as_ref().map(|x| What::Closure(x.closure));
                        inst.run_plan = run;
                        if w.is_none() && inst.multi {
                            inst.dplan = inst.dispatch_plan(b, blk);
                            inst.dplan.as_ref().map(|_| What::Dispatch)
                        } else {
                            w
                        }
                    }
                }
            };
            if let Some(what) = what {
                {
                    let save = (
                        (
                            inst.p.clone(),
                            inst.tys.clone(),
                            inst.closure_calls,
                            inst.regions,
                        ),
                        (
                            inst.added,
                            inst.copied.clone(),
                            inst.chains.clone(),
                            inst.origin.clone(),
                            inst.run_moves.clone(),
                        ),
                        inst.calls,
                        inst.blk_chain.clone(),
                        inst.body_chain.clone(),
                        inst.sites.clone(),
                        inst.body_sites.clone(),
                    );
                    let save_d = (inst.no_copy.clone(), inst.dispatches);
                    inst.skip_mention = plan.as_ref().is_some_and(|x| !x.removals.is_empty());
                    let done = inst.copy(b, blk, what);
                    inst.dplan = None;
                    inst.cell_writes.borrow_mut().clear();
                    if done.is_err() && std::env::var_os("WEFT_INST_DEBUG").is_some() {
                        eprintln!("instantiate: no copy at b{} bb{}: {what:?}", b.0, blk.0);
                    }
                    inst.skip_mention = false;
                    inst.run_plan = None;
                    if let (Ok(()), Some(x)) = (&done, &plan) {
                        inst.covered.insert(x.closure);
                        inst.remove_make(b, &x.removals);
                    }
                    if done.is_err() {
                        inst.p = save.0 .0;
                        inst.tys = save.0 .1;
                        inst.closure_calls = save.0 .2;
                        inst.regions = save.0 .3;
                        inst.copied = save.1 .1;
                        inst.chains = save.1 .2;
                        inst.origin = save.1 .3;
                        inst.run_moves = save.1 .4;
                        inst.added = save.1 .0;
                        inst.calls = save.2;
                        inst.blk_chain = save.3;
                        inst.body_chain = save.4;
                        inst.sites = save.5;
                        inst.body_sites = save.6;
                        inst.no_copy = save_d.0;
                        inst.dispatches = save_d.1;
                    }
                }
            }
            inst.run_plan = None;
            inst.dplan = None;
            k += 1;
        }
        bi += 1;
    }
}

/// The result of the sweeps of `inst` over the program of `built`
/// ([`instantiate_mode`]).
fn finish_inst(mut inst: Inst<'_>, orig: &Program, built: &Built) -> Option<Instantiated> {
    if inst.calls + inst.closure_calls == 0 {
        return None;
    }
    // The closures whose only runs are copy regions.
    let sole: BTreeSet<ClosureId> = inst
        .chains
        .iter()
        .filter(|(c, ch)| sole_runs(&inst.p, &inst.tys, **c, ch))
        .map(|(c, _)| *c)
        .collect();
    for r in &mut inst.p.regions {
        // A region whose value can be more than one closure (plan stage R0z
        // Z3) does not make its closure sole.
        r.sole = sole.contains(&r.closure) && r.also.is_empty();
    }
    let tys = &inst.tys;
    let before = weft_ir::verify::verify_program(orig, &built.tys).len();
    // The cleanup chain of a copy ends the values of the callee first, then
    // those of the site: the order of one frame (V16) does not hold across
    // the two, and the machine ends them in the same order as before.
    let broken: Vec<weft_ir::verify::Broken> = weft_ir::verify::verify_program(&inst.p, tys)
        .into_iter()
        .filter(|x| {
            !(x.rule == weft_ir::verify::Rule::UnwindOrder
                && inst.sites.keys().any(|(b, _)| *b == x.body))
        })
        // The cleanup chain of a copy of a closure body in a clause (stages
        // R0k-c1 and R0k-b1') ends the values of the closure frame, then goes
        // to the chain of the clause, which starts with `UnwindKont`: the
        // order of the machine, as before the copy.
        .filter(|x| {
            !((inst.kont || inst.regions > 0)
                && x.rule == weft_ir::verify::Rule::KontNotFirst
                && x.block
                    .is_some_and(|k| inst.sites.contains_key(&(x.body, k))))
        })
        .collect();
    if broken.len() > before {
        if std::env::var_os("WEFT_INST_DEBUG").is_some() {
            eprintln!("instantiate: broken {broken:?}");
        }
        return None;
    }
    if std::env::var_os("WEFT_INST_PRINT").is_some() {
        eprintln!("{}", weft_ir::print::print_program(&inst.p, tys));
    }
    let weak_ok = weak_ok(&inst.p, tys, &inst.needs, &inst.copied);
    if std::env::var_os("WEFT_INST_DEBUG").is_some() {
        eprintln!("instantiate: weak_ok {weak_ok}");
    }
    let mut out = built.clone();
    out.program = inst.p;
    out.tys = inst.tys;
    Some(Instantiated {
        built: out,
        calls: inst.calls,
        closure_calls: inst.closure_calls,
        regions: inst.regions,
        dispatches: inst.dispatches,
        weak_ok,
        sites: inst.sites,
        body_sites: inst.body_sites,
        covered: inst.covered,
    })
}

/// True if no code of program `p` can run a callee that gives a function
/// value to an operation through its row where a local handler serves it
/// (see [`Instantiated::weak_ok`]).
fn weak_ok(p: &Program, tys: &TyTable, needs: &Needs, copied: &BTreeSet<ClosureId>) -> bool {
    let has = |f: &FnId| needs.fns.get(f).is_some_and(|s| !s.is_empty());
    // The direct performs of each closure body and of the bodies inside it.
    // A closure whose run got a copy of its body (stage R0k-b1') is not in
    // the check: at that run the copy performs, and the guard of the
    // analysis (`note_weak_call`, `weak_values_stay`) checks each other run
    // of its summary, as for a closure that performs through a captured
    // capability (stage R0k-a2).
    let mut closure_needs: BTreeMap<BodyId, BTreeSet<EffectId>> = BTreeMap::new();
    let mut closure_of: Vec<Option<BodyId>> = vec![None; p.bodies.len()];
    // The functions that code can run: the callees of the calls, the function
    // item values, `main` and the tests. A closure of another function is
    // never made (plan stage R0k-b2: each call of its maker has a copy, so
    // the closure of the copy is the one that runs).
    let mut live: BTreeSet<FnId> = BTreeSet::new();
    for b in &p.bodies {
        for blk in &b.blocks {
            if let TermKind::Call {
                callee: Callee::Fn(f, _),
                ..
            } = &blk.term.kind
            {
                live.insert(*f);
            }
        }
        for o in body_operands(b) {
            if let Operand::Const(weft_ir::Const::Fn(f, _)) = o {
                live.insert(*f);
            }
        }
    }
    for (i, d) in p.fns.iter().enumerate() {
        if d.name == "main" {
            live.insert(FnId(u32::try_from(i).unwrap_or(u32::MAX)));
        }
    }
    let owner = body_fns(p);
    for (i, b) in p.bodies.iter().enumerate() {
        let id = BodyId(u32::try_from(i).unwrap_or(u32::MAX));
        let unmade = owner
            .get(i)
            .copied()
            .flatten()
            .is_some_and(|f| !live.contains(&f));
        let c = match b.kind {
            BodyKind::Closure(_) if unmade => None,
            BodyKind::Closure(c) if copied.contains(&c) => None,
            BodyKind::Closure(_) => Some(id),
            BodyKind::Fn(_) | BodyKind::Test(_) => None,
            _ => b
                .parent
                .and_then(|q| closure_of.get(q.index()).copied().flatten()),
        };
        if let Some(s) = closure_of.get_mut(i) {
            *s = c;
        }
    }
    for (i, b) in p.bodies.iter().enumerate() {
        let entry = matches!(b.kind, BodyKind::Test(_))
            || matches!(b.kind, BodyKind::Fn(f) if p.fns.get(f.index()).is_some_and(|d| d.name == "main"));
        for blk in &b.blocks {
            for s in &blk.stmts {
                if let StmtKind::Assign(_, rv) = &s.kind {
                    let ops: Vec<&Operand> = match rv {
                        Rvalue::Use(o) => vec![o],
                        Rvalue::Aggregate(_, os) | Rvalue::Concat(os) => os.iter().collect(),
                        _ => Vec::new(),
                    };
                    for o in ops {
                        if let Operand::Const(weft_ir::Const::Fn(f, _)) = o {
                            if has(f) {
                                return false;
                            }
                        }
                    }
                }
            }
            match &blk.term.kind {
                TermKind::Call {
                    callee: Callee::Fn(f, _),
                    caps,
                    args,
                    ..
                } => {
                    for o in args {
                        if let Operand::Const(weft_ir::Const::Fn(g, _)) = o {
                            if has(g) {
                                return false;
                            }
                        }
                    }
                    let env = match caps {
                        CapArgs::Lexical(e) => Some(*e),
                        CapArgs::Root => None,
                    };
                    let set = needs.fns.get(f).cloned().unwrap_or_default();
                    for e in set {
                        let served = env.is_some_and(|env| env_binds(p, env, e));
                        if served || entry {
                            return false;
                        }
                        if let Some(c) = closure_of.get(i).copied().flatten() {
                            closure_needs.entry(c).or_default().insert(e);
                        }
                    }
                }
                TermKind::Perform {
                    cap: CapOperand::Row(e),
                    op,
                    ..
                } if risky_op(tys, *e, *op).1 => {
                    if entry {
                        return false;
                    }
                    if let Some(c) = closure_of.get(i).copied().flatten() {
                        closure_needs.entry(c).or_default().insert(*e);
                    }
                }
                _ => {}
            }
        }
    }
    closure_needs.values().all(BTreeSet::is_empty)
}

/// True if a copy at the call can remove the reason `u` of a fallback.
///
/// The reasons are a function value that an operation gives to a handler of
/// a caller (C2), and a call that runs a clause of a local handler that
/// gives a function value or a reference back to the callee (D3).
pub fn wanted(u: &super::Unsupported) -> bool {
    u.reason == crate::analysis::transfer::OP_KEPT
        || u.reason == crate::analysis::clause::GIVES_BACK
}

/// The place of the callee of a call of a function value `copy q`.
fn call_value_place(t: &TermKind) -> Option<Place> {
    match t {
        TermKind::Call {
            callee: Callee::Value(Operand::Copy(q)),
            ..
        } => Some(q.clone()),
        _ => None,
    }
}

/// `(writes, made)` for statement `st` and local `l`: the statement writes
/// `l` or a part of it, and the closure that it makes into the whole `l`.
fn stmt_writes(st: &Stmt, l: LocalId) -> (bool, Option<ClosureId>) {
    match &st.kind {
        StmtKind::Assign(q, rv) if q.local == l => {
            let made = match rv {
                Rvalue::Aggregate(weft_ir::AggKind::Closure(c), _) if q.is_local() => Some(*c),
                _ => None,
            };
            (true, made)
        }
        StmtKind::Drop(q) | StmtKind::Uninit(q) | StmtKind::Consume(q) if q.local == l => {
            (true, None)
        }
        _ => (false, None),
    }
}

/// True if statement `st` borrows or moves local `l` (or a part of it).
fn stmt_borrows_or_moves(st: &Stmt, l: LocalId) -> bool {
    let moved = |o: &Operand| matches!(o, Operand::Move(q) if q.local == l);
    match &st.kind {
        StmtKind::Assign(_, rv) => match rv {
            Rvalue::Ref(q) | Rvalue::Iter(weft_ir::IterSource::Elems(q)) => q.local == l,
            Rvalue::Use(o) | Rvalue::Unary(_, _, o) => moved(o),
            Rvalue::Binary(_, _, a, b) => moved(a) || moved(b),
            Rvalue::Aggregate(_, ops) | Rvalue::Concat(ops) => ops.iter().any(moved),
            _ => false,
        },
        StmtKind::Print(ops) => ops.iter().any(moved),
        _ => false,
    }
}

/// True if terminator `t` runs the `once` closure in local `l` (plan stage
/// R0z Z3, part d): a call of `move l`, whole, that moves `l` in no other
/// operand. The move ends the value; it gives the cell no other value.
fn runs_moved(t: &TermKind, l: LocalId) -> bool {
    let moved = |o: &Operand| matches!(o, Operand::Move(q) if q.local == l);
    matches!(t, TermKind::Call {
        callee: Callee::Value(Operand::Move(q)),
        args,
        ..
    } if *q == Place::local(l) && !args.iter().any(moved))
}

/// True if terminator `t` moves local `l` (or a part of it).
fn term_moves(t: &TermKind, l: LocalId) -> bool {
    let moved = |o: &Operand| matches!(o, Operand::Move(q) if q.local == l);
    match t {
        TermKind::Call { callee, args, .. } => {
            matches!(callee, Callee::Value(o) if moved(o)) || args.iter().any(moved)
        }
        TermKind::Perform { args, .. } => args.iter().any(moved),
        TermKind::Resume { arg, .. } => moved(arg),
        TermKind::Spawn { task, scope, .. } => moved(task) || moved(scope),
        TermKind::Join { task, .. } | TermKind::Detach { task, .. } => moved(task),
        TermKind::Fork { branches, .. } => branches.iter().any(moved),
        TermKind::Switch { on, .. } => moved(on),
        TermKind::Assert { cond, .. } => moved(cond),
        _ => false,
    }
}

/// The blocks of body `b` that a path reaches from block `from` (`fwd`), or
/// that reach block `from` (not `fwd`), with `from` itself.
fn reach(b: &Body, from: BlockId, fwd: bool) -> Vec<bool> {
    let n = b.blocks.len();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    if !fwd {
        for (i, blk) in b.blocks.iter().enumerate() {
            for s in blk.term.kind.successors() {
                if let Some(p) = preds.get_mut(s.index()) {
                    p.push(i);
                }
            }
        }
    }
    let mut seen = vec![false; n];
    let mut work = vec![from.index()];
    while let Some(x) = work.pop() {
        match seen.get_mut(x) {
            Some(v) if !*v => *v = true,
            _ => continue,
        }
        if fwd {
            if let Some(blk) = b.blocks.get(x) {
                work.extend(blk.term.kind.successors().iter().map(|s| s.index()));
            }
        } else if let Some(p) = preds.get(x) {
            work.extend(p.iter().copied());
        }
    }
    seen
}

/// Each place that a statement or a terminator of body `b` names.
fn body_places(b: &Body) -> Vec<Place> {
    let mut out = Vec::new();
    for blk in &b.blocks {
        for st in &blk.stmts {
            stmt_places(st, &mut out);
        }
        term_places(&blk.term.kind, &mut out);
    }
    out
}

/// Adds the place of operand `o` to `out`.
fn op_place(o: &Operand, out: &mut Vec<Place>) {
    if let Some(q) = o.place() {
        out.push(q.clone());
    }
}

/// Adds each place that statement `st` names to `out`.
fn stmt_places(st: &Stmt, out: &mut Vec<Place>) {
    match &st.kind {
        StmtKind::Assign(q, rv) => {
            out.push(q.clone());
            match rv {
                Rvalue::Use(o) | Rvalue::Unary(_, _, o) => op_place(o, out),
                Rvalue::Binary(_, _, a, c) | Rvalue::Iter(weft_ir::IterSource::Range(a, c)) => {
                    op_place(a, out);
                    op_place(c, out);
                }
                Rvalue::Aggregate(_, os) | Rvalue::Concat(os) => {
                    for o in os {
                        op_place(o, out);
                    }
                }
                Rvalue::Ref(q)
                | Rvalue::Len(q)
                | Rvalue::Discriminant(q)
                | Rvalue::ClosureIs(q, _) => {
                    out.push(q.clone());
                }
                Rvalue::Iter(weft_ir::IterSource::Elems(q)) => out.push(q.clone()),
            }
        }
        StmtKind::Drop(q)
        | StmtKind::Consume(q)
        | StmtKind::Uninit(q)
        | StmtKind::Mention(q)
        | StmtKind::UnwindValue(q, _) => out.push(q.clone()),
        StmtKind::Bounds(q, o) => {
            out.push(q.clone());
            op_place(o, out);
        }
        StmtKind::Print(os) => {
            for o in os {
                op_place(o, out);
            }
        }
        StmtKind::Live(l) | StmtKind::Dead(l) | StmtKind::UnwindKont(l) => {
            out.push(Place::local(*l));
        }
    }
}

/// Adds each place that terminator `t` names to `out`.
fn term_places(t: &TermKind, out: &mut Vec<Place>) {
    if let Some(d) = t.dest() {
        out.push(d.clone());
    }
    match t {
        TermKind::Call { callee, args, .. } => {
            if let Callee::Value(o) = callee {
                op_place(o, out);
            }
            for o in args {
                op_place(o, out);
            }
        }
        TermKind::Perform { cap, args, .. } => {
            if let CapOperand::Local(q) = cap {
                out.push(q.clone());
            }
            for o in args {
                op_place(o, out);
            }
        }
        TermKind::Resume { kont, arg, .. } => {
            out.push(kont.clone());
            op_place(arg, out);
        }
        TermKind::Switch { on, .. } => op_place(on, out),
        TermKind::Assert { cond, .. } => op_place(cond, out),
        TermKind::ScopeWait { scope, .. } => out.push(scope.clone()),
        TermKind::Spawn { scope, task, .. } => {
            op_place(scope, out);
            op_place(task, out);
        }
        TermKind::Join { task, .. } | TermKind::Detach { task, .. } => op_place(task, out),
        TermKind::Fork { branches, .. } => {
            for o in branches {
                op_place(o, out);
            }
        }
        TermKind::IterNext { iter, .. } => out.push(iter.clone()),
        _ => {}
    }
}

/// Type `t` with the type arguments `targs` for its type parameters.
fn subst_ty(tys: &mut TyTable, t: weft_ir::TyId, targs: &[weft_ir::TyId]) -> weft_ir::TyId {
    use weft_ir::Ty;
    if !tys.mentions_param(t) {
        return t;
    }
    let Some(ty) = tys.try_get(t).cloned() else {
        return t;
    };
    let s = |x: weft_ir::TyId, tys: &mut TyTable| subst_ty(tys, x, targs);
    let new = match ty {
        Ty::Param(i) => return targs.get(i as usize).copied().unwrap_or(t),
        Ty::Tuple(v) => Ty::Tuple(v.into_iter().map(|x| s(x, tys)).collect()),
        Ty::Array(a, n) => Ty::Array(s(a, tys), n),
        Ty::Slice(a) => Ty::Slice(s(a, tys)),
        Ty::Ref(a) => Ty::Ref(s(a, tys)),
        Ty::Adt(id, args) => Ty::Adt(id, args.into_iter().map(|x| s(x, tys)).collect()),
        Ty::Fn(f) => Ty::Fn(weft_ir::ty::FnTy {
            params: f.params.into_iter().map(|x| s(x, tys)).collect(),
            ret: s(f.ret, tys),
            row: f.row,
        }),
        Ty::Cont(a, c) => Ty::Cont(s(a, tys), s(c, tys)),
        Ty::Iter(a) => Ty::Iter(s(a, tys)),
        other => other,
    };
    tys.intern(new)
}

/// The program `p` with the body of the generic function `f` and the bodies
/// inside it under the type arguments `targs`: the types of the locals, of
/// the aggregates, and the type arguments of the calls and of the function
/// item values. A local whose type changes gets the properties of its new
/// type (`props::ir_props`).
fn subst_program(
    p: &Program,
    tys: &mut TyTable,
    f: FnId,
    targs: &[weft_ir::TyId],
) -> Result<Program, NoCopy> {
    let cb = p.fns.get(f.index()).and_then(|d| d.body).ok_or(NoCopy)?;
    let mut out = p.clone();
    let st = |t: weft_ir::TyId, tys: &mut TyTable| subst_ty(tys, t, targs);
    let sub_op = |o: &mut Operand, tys: &mut TyTable| {
        if let Operand::Const(weft_ir::Const::Fn(_, ts)) = o {
            for t in ts.iter_mut() {
                *t = st(*t, tys);
            }
        }
    };
    for x in std::iter::once(cb).chain(inner_bodies(p, cb)) {
        let body = out.bodies.get_mut(x.index()).ok_or(NoCopy)?;
        for d in &mut body.locals {
            let nt = st(d.ty, tys);
            if nt != d.ty {
                d.ty = nt;
                d.props = crate::props::ir_props(tys, nt);
            }
        }
        for blk in &mut body.blocks {
            for s in &mut blk.stmts {
                match &mut s.kind {
                    StmtKind::Assign(_, rv) => match rv {
                        Rvalue::Aggregate(k, ops) => {
                            match k {
                                weft_ir::AggKind::Struct(t) | weft_ir::AggKind::Variant(t, _) => {
                                    *t = st(*t, tys);
                                }
                                _ => {}
                            }
                            for o in ops.iter_mut() {
                                sub_op(o, tys);
                            }
                        }
                        Rvalue::Use(o) | Rvalue::Unary(_, _, o) => sub_op(o, tys),
                        Rvalue::Binary(_, _, a, c) => {
                            sub_op(a, tys);
                            sub_op(c, tys);
                        }
                        Rvalue::Concat(ops) => {
                            for o in ops.iter_mut() {
                                sub_op(o, tys);
                            }
                        }
                        _ => {}
                    },
                    StmtKind::Print(ops) => {
                        for o in ops.iter_mut() {
                            sub_op(o, tys);
                        }
                    }
                    _ => {}
                }
            }
            match &mut blk.term.kind {
                TermKind::Call { callee, args, .. } => {
                    match callee {
                        Callee::Fn(_, ts) => {
                            for t in ts.iter_mut() {
                                *t = st(*t, tys);
                            }
                        }
                        Callee::Value(o) => sub_op(o, tys),
                    }
                    for o in args.iter_mut() {
                        sub_op(o, tys);
                    }
                }
                TermKind::Perform { args, .. } => {
                    for o in args.iter_mut() {
                        sub_op(o, tys);
                    }
                }
                TermKind::Resume { arg, .. } => sub_op(arg, tys),
                _ => {}
            }
        }
    }
    // A `move` of a place of a type that is a copy type now is a copy (V9).
    for x in std::iter::once(cb).chain(inner_bodies(p, cb)) {
        let Some(mut body) = out.body(x).cloned() else {
            continue;
        };
        let is_copy = |q: &Place, tys: &mut TyTable| -> bool {
            let temp = matches!(body_kind_of(&out, x, q.local), Some(LocalKind::Temp(_)));
            !temp
                && crate::factgen::alpha::place_ty(&out, tys, x, q)
                    .is_some_and(|t| !tys.not_copy(t))
        };
        let fix = |o: &mut Operand, tys: &mut TyTable| {
            if let Operand::Move(q) = o {
                if is_copy(q, tys) {
                    *o = Operand::Copy(q.clone());
                }
            }
        };
        for blk in &mut body.blocks {
            for s in &mut blk.stmts {
                if let StmtKind::Assign(_, rv) = &mut s.kind {
                    match rv {
                        Rvalue::Use(o) | Rvalue::Unary(_, _, o) => fix(o, tys),
                        Rvalue::Binary(_, _, a, c) => {
                            fix(a, tys);
                            fix(c, tys);
                        }
                        Rvalue::Aggregate(_, ops) | Rvalue::Concat(ops) => {
                            for o in ops.iter_mut() {
                                fix(o, tys);
                            }
                        }
                        _ => {}
                    }
                }
            }
            match &mut blk.term.kind {
                TermKind::Call { args, .. } | TermKind::Perform { args, .. } => {
                    for o in args.iter_mut() {
                        fix(o, tys);
                    }
                }
                TermKind::Resume { arg, .. } => fix(arg, tys),
                _ => {}
            }
        }
        if let Some(slot) = out.bodies.get_mut(x.index()) {
            *slot = body;
        }
    }
    Ok(out)
}

/// The kind of local `l` of body `b` of program `p`.
fn body_kind_of(p: &Program, b: BodyId, l: LocalId) -> Option<LocalKind> {
    p.body(b).and_then(|x| x.local_kind(l))
}

/// The one value that a local gets ([`single_value`]).
enum One {
    /// A closure that the statement `si` of block `blk` makes.
    Closure(BlockId, usize, ClosureId),
    /// A copy of another local.
    Copy(LocalId),
    /// A move of another local whole, by the statement at (block, index).
    Moved(LocalId, (BlockId, usize)),
    /// A copy of a part of another local: its field and variant steps (plan
    /// stage R0k-b2, form 3).
    Part(LocalId, Vec<Proj>),
    /// A struct, a tuple or a variant, by the statement at (block, index)
    /// (plan stage R0k-b2, form 3).
    Aggregate(weft_ir::AggKind, Vec<Operand>, (BlockId, usize)),
}

/// The one value of local `l` of body `body`: `l` is a variable or a
/// temporary that one statement gives a whole value (a closure, or a copy of
/// a whole local), and no statement or terminator moves it, borrows it or
/// writes it (also a part of it) in another way.
///
/// `except` is a statement that moves `l` whole into the next local of a
/// chain (stage R0k-b1'): that move is the one read of the value. An index
/// of `usize::MAX` is the terminator of the block: a perform that moves `l`
/// into the parameter of a clause.
fn single_value(body: &Body, l: LocalId, except: Option<(BlockId, usize)>) -> Option<One> {
    single_value_but(body, l, except, &BTreeSet::new())
}

/// [`single_value`], but the statements of `skip` (the block and the index):
/// the moves of the value of a `once` closure into the local of its copy
/// region (plan stage R0z Z3, part d).
fn single_value_but(
    body: &Body,
    l: LocalId,
    except: Option<(BlockId, usize)>,
    skip: &BTreeSet<(BlockId, usize)>,
) -> Option<One> {
    if !matches!(
        body.local_kind(l)?,
        LocalKind::User | LocalKind::Temp(_) | LocalKind::Return
    ) {
        return None;
    }
    let mut one: Option<One> = None;
    let mut writes = 0usize;
    for (bi, blk) in body.blocks.iter().enumerate() {
        let id = BlockId(u32::try_from(bi).ok()?);
        for (si, st) in blk.stmts.iter().enumerate() {
            if skip.contains(&(id, si)) {
                continue;
            }
            let (w, made) = stmt_writes(st, l);
            if w {
                writes += 1;
                one = match (&st.kind, made) {
                    (_, Some(c)) => Some(One::Closure(id, si, c)),
                    (StmtKind::Assign(_, Rvalue::Use(Operand::Copy(q))), None) if q.is_local() => {
                        Some(One::Copy(q.local))
                    }
                    (StmtKind::Assign(_, Rvalue::Use(Operand::Move(q))), None) if q.is_local() => {
                        Some(One::Moved(q.local, (id, si)))
                    }
                    (StmtKind::Assign(d, Rvalue::Use(Operand::Copy(q))), None)
                        if d.is_local()
                            && q.local != l
                            && q.proj
                                .iter()
                                .all(|x| matches!(x, Proj::Field(_) | Proj::Variant(_))) =>
                    {
                        Some(One::Part(q.local, q.proj.clone()))
                    }
                    (StmtKind::Assign(d, Rvalue::Aggregate(k, ops)), None)
                        if d.is_local()
                            && matches!(
                                k,
                                weft_ir::AggKind::Struct(_)
                                    | weft_ir::AggKind::Tuple
                                    | weft_ir::AggKind::Variant(..)
                            ) =>
                    {
                        Some(One::Aggregate(k.clone(), ops.clone(), (id, si)))
                    }
                    _ => None,
                };
            }
            if stmt_borrows_or_moves(st, l) && except != Some((id, si)) {
                return None;
            }
        }
        if blk.term.kind.dest().is_some_and(|d| d.local == l)
            || (term_moves(&blk.term.kind, l)
                && except != Some((id, usize::MAX))
                && !runs_moved(&blk.term.kind, l))
        {
            return None;
        }
    }
    if writes == 1 {
        one
    } else {
        None
    }
}

/// The cell that place `q` of body `x` names, as a local of the body that
/// owns it: an upvar local goes to the local of the parent, a field `env.k`
/// of a closure body goes to the source of a `Kept` capture `k`, and
/// `(*env.k)` to the source of a `ByRef` capture `k`, in the maker. `None`
/// for a place that names no local cell (a place behind a reference).
pub(crate) fn cell_of(p: &Program, x: BodyId, q: &Place) -> Option<(BodyId, LocalId)> {
    let (mut body, mut q) = (x, q.clone());
    for _ in 0..=p.bodies.len() {
        let b = p.body(body)?;
        match b.local_kind(q.local)? {
            LocalKind::Upvar(t) => {
                body = b.parent?;
                q.local = t;
            }
            LocalKind::Env => {
                let (_, d) = p.closure_of(body)?;
                let Some(Proj::Field(k)) = q.proj.first() else {
                    return None;
                };
                let cap = d.captures.get(k.index())?;
                let rest: Vec<Proj> = match cap.mode {
                    weft_ir::CaptureMode::Kept => q.proj.get(1..)?.to_vec(),
                    weft_ir::CaptureMode::ByRef => match q.proj.get(1) {
                        Some(Proj::Deref(weft_ir::DerefKind::Ref)) => q.proj.get(2..)?.to_vec(),
                        _ => return None,
                    },
                    _ => return None,
                };
                let mut src = cap.source.clone();
                src.proj.extend(rest);
                body = d.maker;
                q = src;
            }
            _ => {
                if q.proj.first() == Some(&Proj::Deref(weft_ir::DerefKind::Ref))
                    || q.proj.first() == Some(&Proj::Deref(weft_ir::DerefKind::Box))
                    || q.proj.first() == Some(&Proj::Deref(weft_ir::DerefKind::Rc))
                {
                    return None;
                }
                return Some((body, q.local));
            }
        }
    }
    None
}

/// [`cell_of`] for a place that names the whole cell: no projection is left
/// after the upvar locals and the environment fields (stage R0k-d2). `None`
/// for a part of a cell, a place behind a reference, or no cell.
pub(crate) fn whole_cell_of(p: &Program, x: BodyId, q: &Place) -> Option<(BodyId, LocalId)> {
    let (mut body, mut q) = (x, q.clone());
    for _ in 0..=p.bodies.len() {
        let b = p.body(body)?;
        match b.local_kind(q.local)? {
            LocalKind::Upvar(t) => {
                body = b.parent?;
                q.local = t;
            }
            LocalKind::Env => {
                let (_, d) = p.closure_of(body)?;
                let Some(Proj::Field(k)) = q.proj.first() else {
                    return None;
                };
                let cap = d.captures.get(k.index())?;
                let rest: Vec<Proj> = match cap.mode {
                    weft_ir::CaptureMode::Kept => q.proj.get(1..)?.to_vec(),
                    weft_ir::CaptureMode::ByRef => match q.proj.get(1) {
                        Some(Proj::Deref(weft_ir::DerefKind::Ref)) => q.proj.get(2..)?.to_vec(),
                        _ => return None,
                    },
                    _ => return None,
                };
                let mut src = cap.source.clone();
                src.proj.extend(rest);
                body = d.maker;
                q = src;
            }
            _ => return q.proj.is_empty().then_some((body, q.local)),
        }
    }
    None
}

/// The places that body `b` (with the id `id`) writes, moves or borrows:
/// the targets of the assignments and of the terminators, the places of
/// `drop`, `uninit` and `consume`, each `move` operand but the whole callee
/// of a call, each borrow, and the place of an iterator over elements.
///
/// The statements of `skip` are not read: the moves of the value of a
/// `once` closure into the local of its copy region (plan stage R0z Z3,
/// part d). Such a move, and a call of a whole `move` callee, runs the
/// closure; it gives the cell no other value.
fn body_writes_but(b: &Body, id: BodyId, skip: &BTreeSet<(BodyId, BlockId, usize)>) -> Vec<Place> {
    let mut out = Vec::new();
    let mv = |o: &Operand, out: &mut Vec<Place>| {
        if let Operand::Move(q) = o {
            out.push(q.clone());
        }
    };
    for (bi, blk) in b.blocks.iter().enumerate() {
        let bid = BlockId(u32::try_from(bi).unwrap_or(u32::MAX));
        for (si, st) in blk.stmts.iter().enumerate() {
            if skip.contains(&(id, bid, si)) {
                continue;
            }
            match &st.kind {
                StmtKind::Assign(q, rv) => {
                    out.push(q.clone());
                    match rv {
                        Rvalue::Use(o) | Rvalue::Unary(_, _, o) => mv(o, &mut out),
                        Rvalue::Binary(_, _, a, c)
                        | Rvalue::Iter(weft_ir::IterSource::Range(a, c)) => {
                            mv(a, &mut out);
                            mv(c, &mut out);
                        }
                        Rvalue::Aggregate(_, os) | Rvalue::Concat(os) => {
                            for o in os {
                                mv(o, &mut out);
                            }
                        }
                        Rvalue::Ref(q) | Rvalue::Iter(weft_ir::IterSource::Elems(q)) => {
                            out.push(q.clone());
                        }
                        Rvalue::Len(_) | Rvalue::Discriminant(_) | Rvalue::ClosureIs(..) => {}
                    }
                }
                StmtKind::Drop(q) | StmtKind::Consume(q) | StmtKind::Uninit(q) => {
                    out.push(q.clone());
                }
                StmtKind::Print(os) => {
                    for o in os {
                        mv(o, &mut out);
                    }
                }
                _ => {}
            }
        }
        let t = &blk.term.kind;
        if let Some(d) = t.dest() {
            out.push(d.clone());
        }
        match t {
            TermKind::Call { callee, args, .. } => {
                // The run of a `once` closure moves a whole value: it gives
                // the cell no other value (plan stage R0z Z3, part d).
                if let Callee::Value(o) = callee {
                    if o.place().is_none_or(|q| !q.proj.is_empty()) {
                        mv(o, &mut out);
                    }
                }
                for o in args {
                    mv(o, &mut out);
                }
            }
            TermKind::Perform { args, .. } => {
                for o in args {
                    mv(o, &mut out);
                }
            }
            TermKind::Resume { arg, .. } => mv(arg, &mut out),
            TermKind::Spawn { scope, task, .. } => {
                mv(scope, &mut out);
                mv(task, &mut out);
            }
            TermKind::Join { task, .. } | TermKind::Detach { task, .. } => mv(task, &mut out),
            TermKind::Fork { branches, .. } => {
                for o in branches {
                    mv(o, &mut out);
                }
            }
            TermKind::Switch { on, .. } => mv(on, &mut out),
            TermKind::Assert { cond, .. } => mv(cond, &mut out),
            TermKind::IterNext { iter, .. } => out.push(iter.clone()),
            _ => {}
        }
    }
    out
}

/// Each operand of a statement or a terminator of body `b`.
fn body_operands(b: &Body) -> Vec<&Operand> {
    let mut out: Vec<&Operand> = Vec::new();
    for blk in &b.blocks {
        for st in &blk.stmts {
            match &st.kind {
                StmtKind::Assign(_, rv) => match rv {
                    Rvalue::Use(o) | Rvalue::Unary(_, _, o) => out.push(o),
                    Rvalue::Binary(_, _, a, c) | Rvalue::Iter(weft_ir::IterSource::Range(a, c)) => {
                        out.push(a);
                        out.push(c);
                    }
                    Rvalue::Aggregate(_, os) | Rvalue::Concat(os) => out.extend(os.iter()),
                    _ => {}
                },
                StmtKind::Bounds(_, o) => out.push(o),
                StmtKind::Print(os) => out.extend(os.iter()),
                _ => {}
            }
        }
        match &blk.term.kind {
            TermKind::Call { callee, args, .. } => {
                if let Callee::Value(o) = callee {
                    out.push(o);
                }
                out.extend(args.iter());
            }
            TermKind::Perform { args, .. } => out.extend(args.iter()),
            TermKind::Resume { arg, .. } => out.push(arg),
            TermKind::Switch { on, .. } => out.push(on),
            TermKind::Assert { cond, .. } => out.push(cond),
            TermKind::Spawn { scope, task, .. } => {
                out.push(scope);
                out.push(task);
            }
            TermKind::Join { task, .. } | TermKind::Detach { task, .. } => out.push(task),
            TermKind::Fork { branches, .. } => out.extend(branches.iter()),
            _ => {}
        }
    }
    out
}

/// True if body `b` names field `k` of local `l` only as a whole copy, an
/// operand `copy l.k` (plan stage R0k-b2): no write, no move, no borrow, and
/// no place below the field.
fn copy_reads_only(b: &Body, l: LocalId, k: u32) -> bool {
    let at_k =
        |q: &Place| q.local == l && q.proj.first() == Some(&Proj::Field(weft_ir::FieldIdx(k)));
    let whole = Place {
        local: l,
        proj: vec![Proj::Field(weft_ir::FieldIdx(k))],
    };
    let named = body_places(b).iter().filter(|q| at_k(q)).count();
    let copies = body_operands(b)
        .iter()
        .filter(|o| matches!(o, Operand::Copy(q) if *q == whole))
        .count();
    named == copies
}

/// True if body `b` names field `k` of local `l` only as a whole operand,
/// `copy l.k` or `move l.k` (plan stage R0z Z3, parts d and e): no write,
/// no borrow, and no place below the field.
fn whole_reads_only(b: &Body, l: LocalId, k: u32) -> bool {
    let whole = Place {
        local: l,
        proj: vec![Proj::Field(weft_ir::FieldIdx(k))],
    };
    let at_k = |q: &Place| q.local == l && q.proj.first() == whole.proj.first();
    let named = body_places(b).iter().filter(|q| at_k(q)).count();
    let reads = body_operands(b)
        .iter()
        .filter(|o| matches!(o, Operand::Copy(q) | Operand::Move(q) if *q == whole))
        .count();
    named == reads
}

/// True if the cell of local `l` of body `a` keeps one value (plan stage
/// R0k-b2): `l` is a variable, a parameter or a temporary with at most one
/// write, no statement or terminator moves or borrows it, and no body inside
/// `a` writes, moves or borrows it ([`nested_writes`]).
fn cell_constant(p: &Program, a: BodyId, l: LocalId) -> bool {
    let Some(body) = p.body(a) else {
        return false;
    };
    if !matches!(
        body.local_kind(l),
        Some(LocalKind::User | LocalKind::Param(_) | LocalKind::Temp(_))
    ) {
        return false;
    }
    let mut writes = 0usize;
    for blk in &body.blocks {
        for st in &blk.stmts {
            if stmt_writes(st, l).0 {
                writes += 1;
            }
            if stmt_borrows_or_moves(st, l) {
                return false;
            }
        }
        if blk.term.kind.dest().is_some_and(|d| d.local == l) {
            writes += 1;
        }
        if term_moves(&blk.term.kind, l) {
            return false;
        }
    }
    writes <= 1 && !nested_writes(p, a, l)
}

/// True if a body inside body `b` (each body whose lexical parent chain goes
/// to `b`: clauses, handled bodies, scope bodies, closures, and the bodies
/// inside them) writes, moves or borrows the cell of local `l` of `b`,
/// through an upvar local or a capture of a closure (stage R0k-a2 fix).
fn nested_writes(p: &Program, b: BodyId, l: LocalId) -> bool {
    nested_writes_but(p, b, l, &BTreeSet::new())
}

/// [`nested_writes`], but the statements of `skip` ([`body_writes_but`]).
fn nested_writes_but(
    p: &Program,
    b: BodyId,
    l: LocalId,
    skip: &BTreeSet<(BodyId, BlockId, usize)>,
) -> bool {
    inner_bodies(p, b).into_iter().any(|x| {
        p.body(x).is_some_and(|xb| {
            body_writes_but(xb, x, skip)
                .iter()
                .any(|q| cell_of(p, x, q) == Some((b, l)))
        })
    })
}

/// True if the copy regions are the only runs of the closure value whose
/// ways are `chain` (stage R0k-b1', [`weft_ir::CopyRegion::sole`]): each use
/// of a local of the ways, or of an upvar local that names one, is a step of
/// a way (the make, a copy or a move into the next local, the perform that
/// gives the value to a clause), a `Mention`, the start or the end of the
/// cell, or a value of a cleanup chain. The run nodes are copies now, so no
/// terminator runs the value; another use (an argument, a field, a capture)
/// can give it to code that runs it.
///
/// A place of a local of a way whose type holds no function value (a part
/// of an aggregate, as `b.n`) reads no closure (plan stage R0z Z3, part c).
fn sole_runs(p: &Program, tys: &TyTable, c: ClosureId, chain: &BTreeSet<Link>) -> bool {
    let locals: BTreeSet<(BodyId, LocalId)> = chain
        .iter()
        .filter_map(|x| match x {
            Link::Local(b, l) => Some((*b, *l)),
            Link::Perform(..) => None,
        })
        .collect();
    // The names of the cells of the way: the locals, and each upvar local
    // that names one of them.
    let mut names: BTreeSet<(BodyId, LocalId)> = locals.clone();
    loop {
        let mut grew = false;
        for (bi, b) in p.bodies.iter().enumerate() {
            let id = BodyId(u32::try_from(bi).unwrap_or(u32::MAX));
            let Some(parent) = b.parent else { continue };
            for (li, d) in b.locals.iter().enumerate() {
                if let LocalKind::Upvar(s) = d.kind {
                    let me = (id, LocalId(u32::try_from(li).unwrap_or(u32::MAX)));
                    if names.contains(&(parent, s)) && names.insert(me) {
                        grew = true;
                    }
                }
            }
        }
        if !grew {
            break;
        }
    }
    let mut tys = tys.clone();
    let mut named = |b: BodyId, q: &Place| {
        names.contains(&(b, q.local)) && (q.proj.is_empty() || fn_part(p, &mut tys, b, q))
    };
    for (bi, b) in p.bodies.iter().enumerate() {
        let id = BodyId(u32::try_from(bi).unwrap_or(u32::MAX));
        for (ki, blk) in b.blocks.iter().enumerate() {
            let k = BlockId(u32::try_from(ki).unwrap_or(u32::MAX));
            // The entry of an arm of a dispatch whose group does not hold `c`
            // (plan stage R0z Z6): the test before it is total, so the value
            // there is not `c`. The arm runs (a plain arm) or moves (a copy arm
            // of `once` closures) only the closures of its group.
            let other_arm = p.dispatches.iter().any(|d| {
                d.body == id
                    && d.arms
                        .iter()
                        .any(|a| a.entry == k && !a.closures.contains(&c))
            });
            if other_arm {
                continue;
            }
            for st in &blk.stmts {
                let ok = match &st.kind {
                    StmtKind::Live(_)
                    | StmtKind::Dead(_)
                    | StmtKind::Mention(_)
                    | StmtKind::UnwindValue(..) => true,
                    // A test of the variant of a local of a way reads no
                    // closure (plan stage R0k-b2: a `match` on an `Option`).
                    // The test of a dispatch reads the code of the value, and
                    // it does not run it (plan stage R0z Z6).
                    StmtKind::Assign(q, Rvalue::Discriminant(_) | Rvalue::ClosureIs(..)) => {
                        !named(id, q)
                    }
                    StmtKind::Assign(q, rv) => {
                        let step = locals.contains(&(id, q.local))
                            && q.is_local()
                            && matches!(
                                rv,
                                Rvalue::Use(Operand::Copy(_) | Operand::Move(_))
                                    | Rvalue::Aggregate(
                                        weft_ir::AggKind::Closure(_)
                                            | weft_ir::AggKind::Struct(_)
                                            | weft_ir::AggKind::Tuple
                                            | weft_ir::AggKind::Variant(..),
                                        _
                                    )
                            );
                        let mut ps = Vec::new();
                        stmt_places(st, &mut ps);
                        step || !ps.iter().any(|x| named(id, x))
                    }
                    _ => {
                        let mut ps = Vec::new();
                        stmt_places(st, &mut ps);
                        !ps.iter().any(|x| named(id, x))
                    }
                };
                if !ok {
                    return false;
                }
            }
            if chain.contains(&Link::Perform(id, k)) {
                continue;
            }
            let mut ps = Vec::new();
            term_places(&blk.term.kind, &mut ps);
            if ps.iter().any(|x| named(id, x)) {
                return false;
            }
        }
    }
    true
}

/// True if place `q` of body `b` can hold a function value: its type holds
/// one, names a type parameter, or is not known (plan stage R0z Z3, part c).
fn fn_part(p: &Program, tys: &mut TyTable, b: BodyId, q: &Place) -> bool {
    crate::factgen::alpha::place_ty(p, tys, b, q)
        .is_none_or(|t| tys.mentions_param(t) || crate::props::ir_has_fns(tys, t))
}

/// Place `q` of body `x` in the terms of the body that owns its local: each
/// upvar local goes to the local of the parent (stage R0k-b1'). The place of
/// an environment field stays a place of the closure body.
fn root_place(p: &Program, x: BodyId, q: &Place) -> Option<(BodyId, Place)> {
    let (mut body, mut local) = (x, q.local);
    for _ in 0..=p.bodies.len() {
        match p.body(body)?.local_kind(local)? {
            LocalKind::Upvar(t) => {
                body = p.body(body)?.parent?;
                local = t;
            }
            _ => {
                return Some((
                    body,
                    Place {
                        local,
                        proj: q.proj.clone(),
                    },
                ))
            }
        }
    }
    None
}

/// True if body `x` is body `a` or a body inside it (through the parent
/// chain). A clause is inside the site of its handler, not inside the
/// handled body.
fn inside(p: &Program, x: BodyId, a: BodyId) -> bool {
    let mut at = Some(x);
    for _ in 0..=p.bodies.len() {
        match at {
            Some(y) if y == a => return true,
            Some(y) => at = p.body(y).and_then(|b| b.parent),
            None => return false,
        }
    }
    false
}

/// True if body `x` can name a local of body `a` through upvar locals: `x`
/// is `a`, or each body from `x` up to `a` (not `a`) can have upvar locals.
fn upvar_path(p: &Program, x: BodyId, a: BodyId) -> bool {
    let mut at = x;
    for _ in 0..=p.bodies.len() {
        if at == a {
            return true;
        }
        let Some(b) = p.body(at) else {
            return false;
        };
        if !b.kind.has_upvars() {
            return false;
        }
        let Some(q) = b.parent else {
            return false;
        };
        at = q;
    }
    false
}

/// The block of body `m` whose terminator runs the body around body `x`
/// that is a child of `m` (stage R0k-b1'): the `handle` of a handled body or
/// of a clause, the `scope` of a scope body. `None` if `x` is not inside `m`
/// through such bodies.
fn gateway(p: &Program, m: BodyId, x: BodyId) -> Option<BlockId> {
    let mut child = x;
    for _ in 0..=p.bodies.len() {
        let parent = p.body(child)?.parent?;
        if parent == m {
            break;
        }
        child = parent;
    }
    let mb = p.body(m)?;
    let want = |t: &TermKind| match (p.body(child).map(|b| b.kind), t) {
        (Some(BodyKind::Handled(h) | BodyKind::Clause(h, _)), TermKind::Handle { handler, .. }) => {
            *handler == h
        }
        (Some(BodyKind::Scope(s)), TermKind::Scope { scope, .. }) => *scope == s,
        _ => false,
    };
    let at = mb.blocks.iter().position(|blk| want(&blk.term.kind))?;
    Some(BlockId(u32::try_from(at).ok()?))
}

/// The block of the call that gives local `l` of body `body` its one value
/// (stage R0k-b1'): `l` is a variable or a temporary, the destination of
/// one terminator, a call of a function item, as a whole, and no statement
/// writes, moves or borrows it (but `except`, the move into the next local
/// of the chain), and no other terminator moves it.
fn call_value_of(body: &Body, l: LocalId, except: Option<(BlockId, usize)>) -> Option<BlockId> {
    if !matches!(body.local_kind(l)?, LocalKind::User | LocalKind::Temp(_)) {
        return None;
    }
    let mut found = None;
    for (bi, blk) in body.blocks.iter().enumerate() {
        let id = BlockId(u32::try_from(bi).ok()?);
        for (si, st) in blk.stmts.iter().enumerate() {
            if stmt_writes(st, l).0 || (stmt_borrows_or_moves(st, l) && except != Some((id, si))) {
                return None;
            }
        }
        if term_moves(&blk.term.kind, l) && except != Some((id, usize::MAX)) {
            return None;
        }
        if blk.term.kind.dest().is_some_and(|d| d.local == l) {
            let whole = blk.term.kind.dest().is_some_and(Place::is_local);
            let call = matches!(
                blk.term.kind,
                TermKind::Call {
                    callee: Callee::Fn(..),
                    ..
                }
            );
            if !whole || !call || found.is_some() {
                return None;
            }
            found = Some(BlockId(u32::try_from(bi).ok()?));
        }
    }
    found
}

/// The closure that function `f` makes and gives back on each path (stage
/// R0k-b1'): the body of `f` gives `_0` one value, a closure that the body
/// (not a body inside it) makes in its capability environment at the entry,
/// directly or through one temporary or variable that it moves into `_0`.
/// A copy of its body at the call site reads each capture as a cell of the
/// closure value (plan stage R0k-b2, [`Inst::env_capture_ok`]): the frame of
/// `f` is gone there.
fn ret_closure(p: &Program, f: FnId, path: &[Proj]) -> Option<ClosureId> {
    let d = p.fns.get(f.index())?;
    if d.generics != 0 || d.intrinsic.is_some() {
        return None;
    }
    let fb_id = d.body?;
    let fb = p.body(fb_id)?;
    // The way of the result in the body of `f`: each local on it gets one
    // value, and a part of a struct, a tuple or a variant names the operand
    // of its aggregate (form 3, plan stage R0k-b2).
    let (mut at, mut except) = (fb.ret, None);
    let mut path = path.to_vec();
    for _ in 0..16 {
        match single_value(fb, at, except)? {
            One::Closure(_, _, c) => {
                if !path.is_empty() {
                    return None;
                }
                let cd = p.closures.get(c.index())?;
                return (cd.maker == fb_id && cd.cap_env == fb.cap_env && !cd.once).then_some(c);
            }
            One::Copy(n) => {
                at = n;
                except = None;
            }
            One::Moved(n, pos) => {
                at = n;
                except = Some(pos);
            }
            One::Part(n, proj) => {
                let mut p2 = proj;
                p2.extend(path);
                path = p2;
                at = n;
                except = None;
            }
            One::Aggregate(kind, ops, pos) => {
                let (o, rest) = agg_operand(&kind, &ops, &path)?;
                let q = o.place()?;
                if q.proj
                    .iter()
                    .any(|x| !matches!(x, Proj::Field(_) | Proj::Variant(_)))
                    || (matches!(o, Operand::Move(_)) && !q.is_local())
                {
                    return None;
                }
                except = matches!(o, Operand::Move(_)).then_some(pos);
                let mut p2 = q.proj.clone();
                p2.extend(rest);
                path = p2;
                at = q.local;
            }
        }
    }
    None
}

/// The operand of aggregate `ops` of kind `kind` that the first steps of
/// `path` name, and the rest of the path (plan stage R0k-b2, form 3): a
/// field of a struct or a tuple, or a field of the payload of the variant.
fn agg_operand<'o>(
    kind: &weft_ir::AggKind,
    ops: &'o [Operand],
    path: &[Proj],
) -> Option<(&'o Operand, Vec<Proj>)> {
    match (kind, path) {
        (weft_ir::AggKind::Struct(_) | weft_ir::AggKind::Tuple, [Proj::Field(f), rest @ ..]) => {
            Some((ops.get(f.index())?, rest.to_vec()))
        }
        (weft_ir::AggKind::Variant(_, v), [Proj::Variant(w), Proj::Field(f), rest @ ..])
            if v == w =>
        {
            Some((ops.get(f.index())?, rest.to_vec()))
        }
        _ => None,
    }
}

/// True if parameter `l` of clause body `body` keeps the value of its
/// argument: no statement or terminator writes, moves or borrows it.
fn param_kept(body: &Body, l: LocalId) -> bool {
    body.blocks.iter().all(|blk| {
        blk.stmts
            .iter()
            .all(|st| !stmt_writes(st, l).0 && !stmt_borrows_or_moves(st, l))
            && !term_moves(&blk.term.kind, l)
            && blk.term.kind.dest().is_none_or(|d| d.local != l)
    })
}

/// A copy of stage R0k-c1 ([`Inst::kont_copy`]).
#[derive(Clone, Debug)]
struct KontPlan {
    /// The closure whose body the run gets.
    closure: ClosureId,
    /// The make and the steps of the chain, which go for a `once`
    /// continuation; empty for a `multi` one.
    removals: Vec<(BlockId, usize)>,
}

/// The chain of a closure that a clause makes and that captures the
/// continuation of the clause ([`kont_closure`]).
#[derive(Clone, Debug)]
struct KontChain {
    closure: ClosureId,
    /// The make: the block and the index of the statement.
    make: (BlockId, usize),
    /// The steps `x = move y` or `x = copy y` after the make, in order.
    steps: Vec<(BlockId, usize)>,
    /// The locals of the chain: the local of the make first.
    locals: Vec<LocalId>,
    /// The `Kont` local of the clause.
    kont: LocalId,
    /// True if the closure moves the continuation (a `once` one).
    once: bool,
}

/// The one write of local `l` of body `body`: a statement that gives the
/// whole `l` a value. `None` if `l` is not a variable or a temporary, or if
/// another statement or a terminator writes `l` or a part of it.
fn one_write(body: &Body, l: LocalId) -> Option<(BlockId, usize)> {
    if !matches!(body.local_kind(l)?, LocalKind::User | LocalKind::Temp(_)) {
        return None;
    }
    let mut found = None;
    for (bi, blk) in body.blocks.iter().enumerate() {
        for (si, st) in blk.stmts.iter().enumerate() {
            if stmt_writes(st, l).0 {
                let whole = matches!(&st.kind, StmtKind::Assign(q, _) if q.is_local());
                if found.is_some() || !whole {
                    return None;
                }
                found = Some((BlockId(u32::try_from(bi).ok()?), si));
            }
        }
        if blk.term.kind.dest().is_some_and(|d| d.local == l) {
            return None;
        }
    }
    found
}

/// The chain from the make of a closure to local `l` of clause `b`, if the
/// closure captures the `Kont` local of `b` ([`KontChain`]).
fn kont_closure(p: &Program, b: BodyId, l: LocalId) -> Option<KontChain> {
    let body = p.body(b)?;
    let mut locals = vec![l];
    let mut steps = Vec::new();
    let mut at = l;
    for _ in 0..16 {
        let (blk, si) = one_write(body, at)?;
        let StmtKind::Assign(_, rv) = &body.block(blk)?.stmts.get(si)?.kind else {
            return None;
        };
        match rv {
            Rvalue::Aggregate(weft_ir::AggKind::Closure(c), ops) => {
                let decl = p.closures.get(c.index())?;
                if decl.maker != b {
                    return None;
                }
                let mut kont = None;
                for (cap, o) in decl.captures.iter().zip(ops) {
                    if cap.mode != weft_ir::CaptureMode::Kont {
                        continue;
                    }
                    let src = &cap.source;
                    let own = src.is_local()
                        && matches!(body.local_kind(src.local), Some(LocalKind::Kont(_)));
                    if !own || kont.is_some() {
                        return None;
                    }
                    kont = Some((src.local, matches!(o, Operand::Move(_))));
                }
                let (kont, once) = kont?;
                steps.reverse();
                locals.reverse();
                return Some(KontChain {
                    closure: *c,
                    make: (blk, si),
                    steps,
                    locals,
                    kont,
                    once,
                });
            }
            Rvalue::Use(Operand::Move(q) | Operand::Copy(q)) if q.is_local() => {
                steps.push((blk, si));
                at = q.local;
                locals.push(at);
            }
            _ => return None,
        }
    }
    None
}

/// The number of reads of local `l` in body `body`: each statement or
/// terminator that names `l`, but `Live`, `Dead`, the one write of `l`, and
/// the drops of a cleanup block (`UnwindValue`).
fn local_reads(body: &Body, l: LocalId) -> usize {
    let mut n = 0usize;
    for blk in &body.blocks {
        for st in &blk.stmts {
            match &st.kind {
                StmtKind::Live(_) | StmtKind::Dead(_) => continue,
                StmtKind::UnwindValue(_, _) if blk.cleanup => continue,
                StmtKind::Assign(q, rv) if q.local == l && q.is_local() => {
                    let mut out = Vec::new();
                    stmt_places(
                        &Stmt {
                            kind: StmtKind::Assign(Place::local(LocalId(u32::MAX)), rv.clone()),
                            origin: st.origin,
                        },
                        &mut out,
                    );
                    n += usize::from(out.iter().any(|x| x.local == l));
                    continue;
                }
                _ => {}
            }
            let mut out = Vec::new();
            stmt_places(st, &mut out);
            n += usize::from(out.iter().any(|x| x.local == l));
        }
        let mut out = Vec::new();
        term_places(&blk.term.kind, &mut out);
        n += usize::from(out.iter().any(|x| x.local == l));
    }
    n
}

/// True if `Kont` local `kont` of body `body` appears after the make `make`
/// in a statement or a terminator but `Dead` and `UnwindKont` (anywhere but
/// the make itself: the rule of R0k-c1 is stricter than "after").
fn kont_uses_after(body: &Body, kont: LocalId, make: (BlockId, usize)) -> bool {
    for (bi, blk) in body.blocks.iter().enumerate() {
        for (si, st) in blk.stmts.iter().enumerate() {
            if (bi, si) == (make.0.index(), make.1) {
                continue;
            }
            if matches!(st.kind, StmtKind::Dead(_) | StmtKind::UnwindKont(_)) {
                continue;
            }
            let mut out = Vec::new();
            stmt_places(st, &mut out);
            if out.iter().any(|x| x.local == kont) {
                return true;
            }
        }
        let mut out = Vec::new();
        term_places(&blk.term.kind, &mut out);
        if out.iter().any(|x| x.local == kont) {
            return true;
        }
    }
    false
}

/// True if a body inside body `b` names the cell of local `l` of `b`
/// through an upvar local or a capture ([`cell_of`]).
fn nested_uses(p: &Program, b: BodyId, l: LocalId) -> bool {
    inner_bodies(p, b).into_iter().any(|x| {
        p.body(x).is_some_and(|xb| {
            body_places(xb)
                .iter()
                .any(|q| cell_of(p, x, q) == Some((b, l)))
        })
    })
}

/// True if each path of the CFG of `body` from the make `make` reaches the
/// run at block `run`, with no cycle, through blocks that are not cleanup
/// blocks and whose terminators are `Goto` or `Switch`, and with no
/// statement but `Live` and `Dead` of a local that is not in `sources` and
/// the steps `steps` of the chain (R0k-c1).
fn kont_region_ok(
    body: &Body,
    make: (BlockId, usize),
    run: BlockId,
    steps: &[(BlockId, usize)],
    sources: &BTreeSet<LocalId>,
) -> bool {
    let stmt_ok = |blk: BlockId, si: usize, st: &Stmt| match &st.kind {
        StmtKind::Live(x) | StmtKind::Dead(x) => !sources.contains(x),
        _ => steps.contains(&(blk, si)),
    };
    let block_ok = |id: BlockId, from: usize| -> bool {
        body.block(id).is_some_and(|x| {
            !x.cleanup
                && x.stmts
                    .iter()
                    .enumerate()
                    .skip(from)
                    .all(|(si, st)| stmt_ok(id, si, st))
        })
    };
    if !block_ok(make.0, make.1 + 1) {
        return false;
    }
    if make.0 == run {
        return true;
    }
    // A depth-first walk with colors: grey on the path, black when done.
    let n = body.blocks.len();
    let mut color = vec![0u8; n];
    let mut stack: Vec<(BlockId, usize)> = vec![(make.0, 0)];
    while let Some(&mut (x, ref mut i)) = stack.last_mut() {
        let Some(blk) = body.block(x) else {
            return false;
        };
        if *i == 0 {
            if let Some(c) = color.get_mut(x.index()) {
                *c = 1;
            }
            if !matches!(blk.term.kind, TermKind::Goto(_) | TermKind::Switch { .. }) {
                return false;
            }
            if blk.term.kind.unwind().is_some() {
                return false;
            }
        }
        let succs = blk.term.kind.normal_successors();
        let Some(&next) = succs.get(*i) else {
            if let Some(c) = color.get_mut(x.index()) {
                *c = 2;
            }
            stack.pop();
            continue;
        };
        *i += 1;
        if next == run {
            if !block_ok(run, 0) {
                return false;
            }
            continue;
        }
        match color.get(next.index()).copied() {
            Some(0) => {
                if !block_ok(next, 0) {
                    return false;
                }
                stack.push((next, 0));
            }
            Some(1) | None => return false,
            _ => {}
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A program with a closure inside a closure inside `main`.
    fn nested() -> Program {
        let src = "fn main() {\n    let a = 1;\n    let f = || {\n        let g = || { print(a); };\n        g();\n    };\n    f();\n}\n";
        let a = crate::analyze_source(src, crate::Options::default())
            .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
        crate::irbuild::build(&a).program
    }

    #[test]
    fn inner_bodies_and_body_fns_do_not_use_the_order_of_the_ids() {
        let mut p = nested();
        let main = p
            .bodies
            .iter()
            .position(|b| matches!(b.kind, BodyKind::Fn(_)) && b.parent.is_none())
            .map(|i| BodyId(u32::try_from(i).unwrap_or(u32::MAX)));
        let main = main.unwrap_or_else(|| panic!("no body for `main`"));
        let before = inner_bodies(&p, main);
        assert!(before.len() >= 2, "two closures inside main: {before:?}");
        let fns = body_fns(&p);
        // Append a copy of the first inner body, and make it the parent of
        // that body: the parent now has a higher id than the child.
        let first = before[0];
        let Some(copy) = p.body(first).cloned() else {
            panic!("no body {first:?}");
        };
        let new = BodyId(u32::try_from(p.bodies.len()).unwrap_or(u32::MAX));
        p.bodies.push(copy);
        if let Some(b) = p.bodies.get_mut(first.index()) {
            b.parent = Some(new);
        }
        let after = inner_bodies(&p, main);
        for x in &before {
            assert!(after.contains(x), "{x:?} is still inside main: {after:?}");
        }
        assert!(after.contains(&new));
        let fns2 = body_fns(&p);
        assert_eq!(fns2.get(first.index()), fns.get(first.index()));
        assert_eq!(fns2.get(new.index()), fns.get(first.index()));
    }
}
