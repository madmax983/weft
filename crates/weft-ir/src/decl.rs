//! The program and its declarations: functions, closures, handlers, scopes, spawn
//! sites, capability environments and tests (`docs/ir.md` 3.2).

use crate::{
    Body, BodyId, CapEnvId, ClosureId, EffectId, LocalId, OpIdx, Origin, Place, ScopeId, TyId,
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
    /// The captured place, in the maker body: a local or an upvar local.
    pub source: LocalId,
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
    /// The scope that joins the task. `None` for a `fork` branch.
    pub scope: Option<ScopeId>,
    /// The task is a branch of a `fork`: it runs on another thread.
    pub fork: bool,
    /// Where the task starts.
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
