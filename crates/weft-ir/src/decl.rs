//! The program and its declarations: functions, closures, handlers, scopes, spawn
//! sites, capability environments and tests (`docs/ir.md` 3.2).

use crate::{
    BlockId, Body, BodyId, CapEnvId, ClosureId, EffectId, OpIdx, Origin, Place, ScopeId, TyId,
};

/// A whole program: each body of each unit, and the declarations.
#[derive(Clone, Debug, Default)]
pub struct Program {
    /// The bodies. The index is the [`BodyId`].
    pub bodies: Vec<Body>,
    /// The function items. The index is the [`FnId`](crate::FnId).
    pub fns: Vec<FnDecl>,
    /// The closure literals. The index is the [`ClosureId`].
    pub closures: Vec<ClosureDecl>,
    /// The `handle` expressions. The index is the [`HandlerId`](crate::HandlerId).
    pub handlers: Vec<HandlerDecl>,
    /// The `scope` expressions. The index is the [`ScopeId`].
    pub scopes: Vec<ScopeDecl>,
    /// The spawn sites. The index is the [`SpawnId`](crate::SpawnId).
    pub spawns: Vec<SpawnDecl>,
    /// The static capability environments. The index is the [`CapEnvId`].
    pub cap_envs: Vec<CapEnv>,
    /// The test blocks. The index is the [`TestId`](crate::TestId).
    pub tests: Vec<TestDecl>,
    /// The copy regions (plan stage R0k-b1'). Only a program with the copies of
    /// the fact generator has them: the builder makes none.
    pub regions: Vec<CopyRegion>,
    /// The dispatches (plan stage R0z Z6). Only a program with the copies of the
    /// fact generator has them.
    pub dispatches: Vec<Dispatch>,
    /// The runtime resume nodes (plan stage R0z Z4b). Only a program with the
    /// copies of the fact generator has them.
    pub resume_runs: Vec<ResumeRun>,
}

/// A runtime resume node (plan stage R0z Z4b, `docs/ir.md` 6.1).
///
/// The terminator of block [`ResumeRun::block`] of clause body
/// [`ResumeRun::body`] is a call of `sim.run` or `with_timeout`. Its block
/// argument is a closure value of [`ResumeRun::closure`] that the clause made
/// just before the call, and the closure resumes the continuation of the
/// clause. The runtime runs the block at the call, on this task. So the
/// `resume` of the block is a resume point of the clause at the call node. The
/// fact generator gives the call the facts of that resume point, and it does
/// not apply the summary of the block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResumeRun {
    /// The clause body.
    pub body: BodyId,
    /// The block of the call.
    pub block: BlockId,
    /// The closure of the block argument.
    pub closure: ClosureId,
    /// The index of the `Kont` capture of [`ResumeRun::closure`].
    pub kont: u32,
}

/// A dispatch (plan stage R0z Z6, `docs/ir.md` 6.1).
///
/// It is the run of a closure value that can be a closure of two or more
/// groups. A test block for each group
/// tests the closure of the value ([`crate::Rvalue::ClosureIs`]) and goes to the
/// arm of the group if the test is true, else to the next test. The `otherwise`
/// of the last test is the miss block: its terminator is `Unreachable`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dispatch {
    /// The body of the run.
    pub body: BodyId,
    /// The closure value that the run runs, a whole local of [`Dispatch::body`].
    pub value: Place,
    /// The arms, in the order of the tests.
    pub arms: Vec<DispatchArm>,
    /// The miss block: no test is true. Control cannot come here.
    pub miss: BlockId,
}

/// An arm of a [`Dispatch`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DispatchArm {
    /// The closures of the group of the arm.
    pub closures: Vec<ClosureId>,
    /// The test block of the arm: its last statement is the `ClosureIs` of the
    /// group, and its terminator is a `Switch` on that result.
    pub test: BlockId,
    /// The entry of the arm: the block that the test goes to if it is true. Its
    /// one edge in is from the test.
    pub entry: BlockId,
    /// The arm runs a copy region of the closure body (the index in
    /// [`Program::regions`]), or `None` for a call of the value (a plain arm).
    pub region: Option<usize>,
    /// The static check of a dead arm: each path from each write of a closure
    /// of the group into the cell of the value, to the run, passes another
    /// write of the cell (a write in a body inside the owner of the cell counts
    /// at the terminator that runs that body). Only then can the analysis find
    /// the arm dead.
    pub killable: bool,
}

impl Dispatch {
    /// Each block of the dispatch that is not a block of a copy region: the test
    /// blocks, the arm entries and the miss block.
    pub fn blocks(&self) -> impl Iterator<Item = BlockId> + '_ {
        self.arms
            .iter()
            .flat_map(|a| [a.test, a.entry])
            .chain(std::iter::once(self.miss))
    }
}

/// A copy region (plan stage R0k-b1', `docs/ir.md` 6.1): the blocks of a body that
/// are a copy of the body of a closure at a run of the closure.
///
/// A closure runs with the handlers of the point where it is made, not with the
/// handlers of its run node. So the code of the region runs with the handler
/// environment of the closure value [`CopyRegion::value`]: the interpreter takes
/// it at the entry and gives the handlers of the frame back at each exit. The
/// static capability environment of the code is [`CopyRegion::env`], not the
/// environment of the body: a `Row` perform of the region is valid if `env` does
/// not bind the effect (the operation goes past the function).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CopyRegion {
    /// The body that holds the blocks.
    pub body: BodyId,
    /// The first block. Only this block has an edge from a block outside the
    /// region.
    pub entry: BlockId,
    /// The blocks, sorted. An edge out of the region is a `Goto`.
    pub blocks: Vec<BlockId>,
    /// The static capability environment of the code of the region: the
    /// environment where the closure is made.
    pub env: CapEnvId,
    /// The closure value that the run node runs, a place of [`CopyRegion::body`].
    pub value: Place,
    /// The closure whose body the region copies.
    pub closure: ClosureId,
    /// The copy regions of the closure are its only runs: no other code
    /// reads the value of the closure, so its own body never runs.
    pub sole: bool,
    /// The environment local of the region (plan stage R0k-b2), a local of
    /// [`CopyRegion::body`] of kind [`LocalKind::CopyEnv`](crate::LocalKind::CopyEnv):
    /// the code of the region reads a capture through it, as a cell of the
    /// closure value. `None` if the region names each capture through a place
    /// of the body.
    pub env_local: Option<crate::LocalId>,
    /// For a capture `k` that the region reads through [`CopyRegion::env_local`]:
    /// the closure that the cell holds, if one closure of the same function
    /// gives the cell its one value (plan stage R0k-b2). The facts take the
    /// function values of the capture from it.
    pub env_fns: Vec<(u32, ClosureId)>,
    /// The other closures that the value can be (plan stage R0z Z3): copies
    /// of the same closure, with the same code, the same captures and the
    /// same `Cap` sources. The region reads each other capture through
    /// [`CopyRegion::env_local`], so its code is the code of a run of each of
    /// them. Empty if the value is always [`CopyRegion::closure`].
    pub also: Vec<ClosureId>,
    /// A kont region (plan stage R0z Z4): the index of the `Kont` capture of
    /// [`CopyRegion::closure`] that the region reads through
    /// [`CopyRegion::env_local`]. The `resume` of the closure body is a
    /// `Resume` of that field of the environment local in the region: a
    /// resume point of the clause that made the closure. `None` for another
    /// region.
    pub kont: Option<u32>,
}

impl CopyRegion {
    /// Each closure that the value of the region can be:
    /// [`CopyRegion::closure`], then [`CopyRegion::also`].
    pub fn closures(&self) -> impl Iterator<Item = ClosureId> + '_ {
        std::iter::once(self.closure).chain(self.also.iter().copied())
    }
}

impl Program {
    /// Returns true if body `b` is the body of a closure whose only runs are
    /// copy regions ([`CopyRegion::sole`]), or a body inside one: it never
    /// runs (plan stage R0k-b1').
    pub fn never_runs(&self, b: BodyId) -> bool {
        if !self.regions.iter().any(|r| r.sole) {
            return false;
        }
        let mut at = Some(b);
        for _ in 0..=self.bodies.len() {
            let Some(x) = at else { return false };
            let Some(body) = self.body(x) else {
                return false;
            };
            if let crate::BodyKind::Closure(c) = body.kind {
                if self.regions.iter().any(|r| r.sole && r.closure == c) {
                    return true;
                }
            }
            at = body.parent;
        }
        false
    }
}

/// A test block: its name (the interpreter runs tests by name) and its body.
#[derive(Clone, Debug)]
pub struct TestDecl {
    /// The name of the test.
    pub name: String,
    /// The body of the test.
    pub body: BodyId,
}

/// A function item.
#[derive(Clone, Debug)]
pub struct FnDecl {
    /// The path, for diagnostics.
    pub name: String,
    /// The body. `None` for an extern function: its summary comes from its signature.
    pub body: Option<BodyId>,
    /// The parameter types, in order.
    pub params: Vec<TyId>,
    /// The result type.
    pub ret: TyId,
    /// The number of type parameters.
    pub generics: u32,
    /// The stated row, if the signature states one. The analysis infers the rest.
    pub stated_row: Option<Vec<EffectId>>,
    /// A function that the runtime gives a special meaning.
    pub intrinsic: Option<Intrinsic>,
}

/// A function with a run-time meaning that its signature does not show.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Intrinsic {
    /// `sim.run`: runs its block with the root handlers of a simulation.
    SimRun,
    /// `with_timeout`: runs its block once, and can fail at a deadline.
    WithTimeout,
}

/// A closure literal.
#[derive(Clone, Debug)]
pub struct ClosureDecl {
    /// The body of the closure.
    pub body: BodyId,
    /// The body that makes the closure.
    pub maker: BodyId,
    /// The captures, in the order of the fields of the environment.
    pub captures: Vec<Capture>,
    /// The closure is `once`: it moves a capture that is not plain data, or it holds a
    /// `once` value.
    pub once: bool,
    /// The capability environment where the closure is made. The closure performs
    /// through it (handlers are lexical).
    pub cap_env: CapEnvId,
}

/// One capture: one field of an environment.
#[derive(Clone, Debug)]
pub struct Capture {
    /// The captured place, in the maker body: a local, an upvar local, or a
    /// capture of the maker when the maker is a closure body (`env.j` for a
    /// `ByMove` or a `Kept` capture, `(*env.j)` for a `ByRef` capture).
    pub source: Place,
    /// How the environment holds it.
    pub mode: CaptureMode,
}

/// How an environment holds a capture. One function (`capture_mode`) decides it; the
/// builder and the interpreter read the decision from the IR.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CaptureMode {
    /// A reference to the cell of the variable. In the closure body the capture is
    /// `(*env.k)`. The end of the variable ends the cell.
    ByRef,
    /// The value moves into the environment when the closure is made. In the closure
    /// body the capture is `env.k`.
    ByMove,
    /// The cell of a plain-data variable that no body borrows. The cell stays readable
    /// for the closure after the end of the variable. In the closure body the capture
    /// is `env.k`. No reference can point into it (verifier rule V13), so it is
    /// outside the reference fragment of B1.
    Kept,
    /// A copy of a capability value.
    Cap,
    /// A copy (or, for a `once` continuation, a move) of a continuation value.
    Kont,
}

/// A `handle` expression.
#[derive(Clone, Debug)]
pub struct HandlerDecl {
    /// The handled effect.
    pub effect: EffectId,
    /// The clause of each operation.
    pub clauses: Vec<(OpIdx, BodyId)>,
    /// The handled body.
    pub handled: BodyId,
    /// The body that holds the `handle` terminator.
    pub site: BodyId,
    /// The effect has a `multi` operation.
    pub multi: bool,
}

/// A `scope` expression.
#[derive(Clone, Debug)]
pub struct ScopeDecl {
    /// The scope body. Its parameter is the scope capability.
    pub body: BodyId,
    /// The body that holds the `scope` terminator.
    pub site: BodyId,
}

/// A spawn site.
#[derive(Clone, Debug)]
pub struct SpawnDecl {
    /// The scope that joins the task. `None` for a `fork` branch, and for a
    /// spawn on a scope capability that does not name a scope binder (a
    /// parameter).
    pub scope: Option<ScopeId>,
    /// The task is a branch of a `fork`: it runs on another thread.
    pub fork: bool,
    /// Where the task starts: the task argument of the spawn (the closure
    /// or the function value), or the branch of the `fork`. The checker
    /// names the task by the span of this expression (`stealable`).
    pub origin: Origin,
}

/// A static capability environment. Handlers are lexical, so the builder knows the
/// capability of each effect at each point.
#[derive(Clone, Debug)]
pub struct CapEnv {
    /// The environment around this one. `None` at the entry of a function or a test.
    pub parent: Option<CapEnvId>,
    /// The capabilities that this environment adds: the capability local of a handled
    /// body, or the capability field of a closure environment.
    pub adds: Vec<(EffectId, Place)>,
}

impl Program {
    /// Returns the runtime resume node at the terminator of block `b` of body
    /// `body` (plan stage R0z Z4b), if one is there.
    pub fn resume_run_at(&self, body: BodyId, b: BlockId) -> Option<&ResumeRun> {
        self.resume_runs
            .iter()
            .find(|r| r.body == body && r.block == b)
    }

    /// Returns the dispatch of block `b` of body `body` (plan stage R0z Z6): a
    /// test block, an arm entry or the miss block of it.
    pub fn dispatch_at(&self, body: BodyId, b: BlockId) -> Option<&Dispatch> {
        self.dispatches
            .iter()
            .find(|d| d.body == body && d.blocks().any(|x| x == b))
    }

    /// Returns the copy region that holds block `b` of body `body`, if one does.
    pub fn region_of(&self, body: BodyId, b: BlockId) -> Option<&CopyRegion> {
        self.regions
            .iter()
            .find(|r| r.body == body && r.blocks.binary_search(&b).is_ok())
    }

    /// Returns the closure value whose environment local `l` of body `body` is
    /// ([`CopyRegion::env_local`], plan stage R0k-b2): the value of its region.
    pub fn copy_env_value(&self, body: BodyId, l: crate::LocalId) -> Option<&Place> {
        self.regions
            .iter()
            .find(|r| r.body == body && r.env_local == Some(l))
            .map(|r| &r.value)
    }

    /// Returns each closure that the value of the region of environment local
    /// `l` of body `body` can be ([`CopyRegion::closures`], plan stage R0z
    /// Z3). Empty if `l` is no environment local.
    pub fn copy_env_closures(&self, body: BodyId, l: crate::LocalId) -> Vec<ClosureId> {
        self.regions
            .iter()
            .find(|r| r.body == body && r.env_local == Some(l))
            .map(|r| r.closures().collect())
            .unwrap_or_default()
    }

    /// Returns the static capability environment of the code of block `b` of body
    /// `body`: the environment of its copy region, else that of the body.
    pub fn env_at(&self, body: BodyId, b: BlockId) -> Option<CapEnvId> {
        match self.region_of(body, b) {
            Some(r) => Some(r.env),
            None => self.body(body).map(|x| x.cap_env),
        }
    }

    /// Returns body `id`, or `None` if the program has no such body.
    pub fn body(&self, id: BodyId) -> Option<&Body> {
        self.bodies.get(id.index())
    }

    /// Returns the closure that body `id` belongs to, if the body is a closure body.
    pub fn closure_of(&self, id: BodyId) -> Option<(ClosureId, &ClosureDecl)> {
        match self.body(id)?.kind {
            crate::BodyKind::Closure(c) => self.closures.get(c.index()).map(|d| (c, d)),
            _ => None,
        }
    }
}
