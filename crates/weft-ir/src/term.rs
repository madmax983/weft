//! Terminators and capability operands (`docs/ir.md` 3.2).

use crate::{
    BlockId, CapEnvId, EffectId, FnId, HandlerId, LocalId, OpIdx, Operand, Origin, Place, ScopeId,
    SpawnId, TyId,
};

/// The capability of a perform.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CapOperand {
    /// A capability value in a place: the capability local of a handled body, an
    /// upvar local that names one, or a `Cap` field of a closure environment.
    Local(Place),
    /// The capability of the effect that the caller of the function gives: a
    /// parameter of the row. The row is inferred, so these parameters are not
    /// locals. The effects model numbers them (`Sig::caps`). Valid in each body whose
    /// capability environment does not bind the effect.
    Row(EffectId),
}

/// The capabilities that a call gives to its callee.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CapArgs {
    /// The lexical environment at the call. The callee gets the capability of each
    /// effect of its row from it.
    Lexical(CapEnvId),
    /// The root handlers only. An `on abort` function gets these.
    Root,
}

/// A terminator.
#[derive(Clone, Debug)]
pub struct Term {
    /// What the terminator does.
    pub kind: TermKind,
    /// Where it comes from. For `Return`, the expression whose value the frame gives
    /// back (the tail, or the operand of `return`): W0204 reports this span.
    pub origin: Origin,
}

/// What a terminator does. A terminator with an `unwind` block can abort its frame.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermKind {
    /// Go to a block.
    Goto(BlockId),
    /// Go to the block of the value of the operand.
    Switch {
        /// The tested value: a `bool`, an integer or a discriminant.
        on: Operand,
        /// The block for each value.
        arms: Vec<(u128, BlockId)>,
        /// The block for each other value.
        otherwise: BlockId,
    },
    /// The frame ends normally. `_0` holds the value; it is the only local with a cell.
    Return,
    /// The unwinding leaves this frame. Only in [`Body::unwind_exit`](crate::Body::unwind_exit).
    UnwindExit,
    /// Control cannot come here.
    Unreachable,
    /// A call of a function item or of a function value.
    Call {
        /// What the call runs.
        callee: Callee,
        /// The arguments, in the order of the parameters.
        args: Vec<Operand>,
        /// The place that gets the result.
        dest: Place,
        /// The capabilities that the callee gets.
        caps: CapArgs,
        /// The next block. `None` if the callee never returns.
        next: Option<BlockId>,
        /// The cleanup block of an abort.
        unwind: Option<BlockId>,
    },
    /// A perform of an operation.
    Perform {
        /// The capability.
        cap: CapOperand,
        /// The operation.
        op: OpIdx,
        /// The arguments, in the order of the parameters.
        args: Vec<Operand>,
        /// The place that gets the result: the value of a `resume`.
        dest: Place,
        /// The next block.
        next: BlockId,
        /// The cleanup block of an abort.
        unwind: Option<BlockId>,
    },
    /// A `resume`: a call of the continuation. It runs the rest of the handled body.
    Resume {
        /// The continuation: the `Kont` local of a clause, an upvar local of one in a
        /// body inside the clause, or a `Kont` field of a closure environment.
        kont: Place,
        /// The value for the perform.
        arg: Operand,
        /// The place that gets the value of the handled body.
        dest: Place,
        /// The next block.
        next: BlockId,
        /// The cleanup block of an abort.
        unwind: Option<BlockId>,
    },
    /// A `handle`: make the capability, run the handled body in a new frame. The
    /// handled body and the clauses name the locals of this body as upvar locals.
    Handle {
        /// The handler.
        handler: HandlerId,
        /// The place that gets the value of the `handle`.
        dest: Place,
        /// The next block: after the body, or after a clause that did not resume.
        next: BlockId,
        /// The cleanup block of an abort that goes past this handler.
        unwind: Option<BlockId>,
    },
    /// A `scope`: run the scope body in a new frame. The scope body names the locals
    /// of this body as upvar locals.
    Scope {
        /// The scope.
        scope: ScopeId,
        /// The place that gets the value.
        dest: Place,
        /// The next block.
        next: BlockId,
        /// The cleanup block of an abort.
        unwind: Option<BlockId>,
    },
    /// Wait for the tasks of a scope. Then raise the failure of a task, once. The last
    /// terminator of a scope body before the end of its locals.
    ScopeWait {
        /// The scope capability.
        scope: Place,
        /// The results of the tasks with no handle. The wait gives them their values;
        /// the frame end drops them.
        orphans: Vec<LocalId>,
        /// The next block.
        next: BlockId,
        /// The cleanup block of an abort.
        unwind: Option<BlockId>,
    },
    /// Start a task in a scope. A spawn does not suspend the task that spawns.
    Spawn {
        /// The spawn site.
        site: SpawnId,
        /// The scope capability.
        scope: Operand,
        /// The closure or function value that the task runs. It moves into the task.
        task: Operand,
        /// The place that gets the task handle. `None`: the scope keeps the task, and
        /// its result goes to a `TaskResult` local of the scope body.
        dest: Option<Place>,
        /// The next block.
        next: BlockId,
    },
    /// Wait for a task and take its result. It consumes the handle.
    Join {
        /// The handle.
        task: Operand,
        /// The place that gets the result.
        dest: Place,
        /// The next block.
        next: BlockId,
        /// The cleanup block of an abort.
        unwind: Option<BlockId>,
    },
    /// Let a task run on. It consumes the handle and drops the result.
    Detach {
        /// The handle.
        task: Operand,
        /// The next block.
        next: BlockId,
    },
    /// Run the branches as tasks on other threads and wait for all of them.
    Fork {
        /// The spawn site of each branch.
        sites: Vec<SpawnId>,
        /// The branch values. Each one moves into its task.
        branches: Vec<Operand>,
        /// The place that gets the tuple of the results.
        dest: Place,
        /// The next block.
        next: BlockId,
        /// The cleanup block of an abort.
        unwind: Option<BlockId>,
    },
    /// `assert`: a false condition aborts the task.
    Assert {
        /// The condition.
        cond: Operand,
        /// The next block.
        next: BlockId,
        /// The cleanup block of the abort.
        unwind: Option<BlockId>,
    },
    /// Advance an iterator: the next element, or the exit.
    IterNext {
        /// The iterator.
        iter: Place,
        /// The place that gets the element.
        dest: Place,
        /// The block for an element.
        next: BlockId,
        /// The block after the last element.
        done: BlockId,
    },
}

/// What a call runs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Callee {
    /// A function item with type arguments.
    Fn(FnId, Vec<TyId>),
    /// A function value: a closure, a function item, a function parameter, or a
    /// value that the body does not follow.
    Value(Operand),
}

impl TermKind {
    /// Returns the blocks of the normal successors: not the cleanup block.
    pub fn normal_successors(&self) -> Vec<BlockId> {
        match self {
            Self::Goto(b) => vec![*b],
            Self::Switch {
                arms, otherwise, ..
            } => {
                let mut v: Vec<BlockId> = arms.iter().map(|(_, b)| *b).collect();
                v.push(*otherwise);
                v
            }
            Self::Return | Self::UnwindExit | Self::Unreachable => Vec::new(),
            Self::Call { next, .. } => next.iter().copied().collect(),
            Self::Perform { next, .. }
            | Self::Resume { next, .. }
            | Self::Handle { next, .. }
            | Self::Scope { next, .. }
            | Self::ScopeWait { next, .. }
            | Self::Spawn { next, .. }
            | Self::Join { next, .. }
            | Self::Detach { next, .. }
            | Self::Fork { next, .. }
            | Self::Assert { next, .. } => vec![*next],
            Self::IterNext { next, done, .. } => vec![*next, *done],
        }
    }

    /// Returns the cleanup block of an abort, if the terminator can abort.
    pub const fn unwind(&self) -> Option<BlockId> {
        match self {
            Self::Call { unwind, .. }
            | Self::Perform { unwind, .. }
            | Self::Resume { unwind, .. }
            | Self::Handle { unwind, .. }
            | Self::Scope { unwind, .. }
            | Self::ScopeWait { unwind, .. }
            | Self::Join { unwind, .. }
            | Self::Fork { unwind, .. }
            | Self::Assert { unwind, .. } => *unwind,
            Self::Goto(_)
            | Self::Switch { .. }
            | Self::Return
            | Self::UnwindExit
            | Self::Unreachable
            | Self::Spawn { .. }
            | Self::Detach { .. }
            | Self::IterNext { .. } => None,
        }
    }

    /// Returns all successors: the normal successors, then the cleanup block.
    pub fn successors(&self) -> Vec<BlockId> {
        let mut v = self.normal_successors();
        v.extend(self.unwind());
        v
    }

    /// Returns true if the terminator can suspend the frame: another frame runs
    /// before it goes on. These are the suspension points of the effects model.
    pub const fn suspends(&self) -> bool {
        matches!(
            self,
            Self::Call { .. }
                | Self::Perform { .. }
                | Self::Resume { .. }
                | Self::Handle { .. }
                | Self::Scope { .. }
                | Self::ScopeWait { .. }
                | Self::Join { .. }
                | Self::Fork { .. }
        )
    }

    /// Returns true if the terminator can abort by its kind. The builder gives each
    /// such terminator an `unwind` block (verifier rule V10). The fact generator keeps
    /// the abort edge of a `Call` or a `Resume` only if the summary can abort.
    pub const fn can_abort(&self) -> bool {
        self.suspends() || matches!(self, Self::Assert { .. })
    }

    /// Returns the place that the terminator writes on its normal edge, if it writes
    /// one.
    pub const fn dest(&self) -> Option<&Place> {
        match self {
            Self::Call { dest, .. }
            | Self::Perform { dest, .. }
            | Self::Resume { dest, .. }
            | Self::Handle { dest, .. }
            | Self::Scope { dest, .. }
            | Self::Join { dest, .. }
            | Self::Fork { dest, .. }
            | Self::IterNext { dest, .. } => Some(dest),
            Self::Spawn { dest, .. } => dest.as_ref(),
            Self::Goto(_)
            | Self::Switch { .. }
            | Self::Return
            | Self::UnwindExit
            | Self::Unreachable
            | Self::ScopeWait { .. }
            | Self::Detach { .. }
            | Self::Assert { .. } => None,
        }
    }
}
