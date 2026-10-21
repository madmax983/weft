//! Bodies and locals (`docs/ir.md` 3.2). One body is one frame.

use crate::{
    id_of, Block, BlockId, BodyId, CapEnvId, ClosureId, EffectId, FnId, HandlerId, LocalId, OpIdx,
    Origin, Props, ScopeId, SpawnId, TestId, TyId,
};

/// What a body is. Each kind is one `CodeKind` of the interpreter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BodyKind {
    /// A function body.
    Fn(FnId),
    /// A test body.
    Test(TestId),
    /// A closure body. Its first parameter is the environment.
    Closure(ClosureId),
    /// A handler clause. Its parameters are the operation arguments; its continuation
    /// is [`Body::kont`]; it names the locals of the site as upvar locals.
    Clause(HandlerId, OpIdx),
    /// A handled body. Its capability is [`Body::caps`]; it names the locals of the
    /// site as upvar locals.
    Handled(HandlerId),
    /// A scope body. Its parameter is the scope capability; it names the locals of
    /// the site as upvar locals.
    Scope(ScopeId),
}

impl BodyKind {
    /// Returns true for a body that can name upvar locals: it runs while the frame
    /// of its site runs, so the cells of the site outlive it.
    pub const fn has_upvars(self) -> bool {
        matches!(self, Self::Clause(..) | Self::Handled(_) | Self::Scope(_))
    }

    /// Returns true for a once-run frame: the fact generator splices it into the
    /// component of its site.
    pub const fn spliced(self) -> bool {
        matches!(self, Self::Handled(_) | Self::Scope(_))
    }
}

/// One body: one frame.
#[derive(Clone, Debug)]
pub struct Body {
    /// What the body is.
    pub kind: BodyKind,
    /// The lexical parent: the body that makes this body.
    pub parent: Option<BodyId>,
    /// The locals. The index is the [`LocalId`].
    pub locals: Vec<LocalDecl>,
    /// The return slot `_0`.
    pub ret: LocalId,
    /// The parameters, in order. A closure body has its environment first.
    pub params: Vec<LocalId>,
    /// The capability values that the frame gets as parameters. Only a handled body
    /// has one: the capability that its `handle` makes.
    pub caps: Vec<(EffectId, LocalId)>,
    /// The continuation of a clause and its mode (`multi`).
    pub kont: Option<(LocalId, bool)>,
    /// The blocks. The index is the [`BlockId`].
    pub blocks: Vec<Block>,
    /// The first block.
    pub entry: BlockId,
    /// The block that ends the unwinding of this frame
    /// ([`TermKind::UnwindExit`](crate::TermKind::UnwindExit)).
    pub unwind_exit: BlockId,
    /// The capability environment at the entry.
    pub cap_env: CapEnvId,
    /// Where the body comes from.
    pub origin: Origin,
}

impl Body {
    /// Returns the locals that have a cell at the entry: the parameters (the
    /// environment of a closure among them), `_0`, the capability parameters, the
    /// continuation and the upvar locals.
    pub fn entry_locals(&self) -> Vec<LocalId> {
        let mut v: Vec<LocalId> = self.params.clone();
        v.push(self.ret);
        v.extend(self.caps.iter().map(|(_, l)| *l));
        v.extend(self.kont.iter().map(|(k, _)| *k));
        for (i, d) in self.locals.iter().enumerate() {
            if matches!(d.kind, LocalKind::Upvar(_) | LocalKind::Env) {
                v.push(LocalId(id_of(i)));
            }
        }
        v.sort();
        v.dedup();
        v
    }

    /// Returns local `l`, or `None` if the body has no such local.
    pub fn local(&self, l: LocalId) -> Option<&LocalDecl> {
        self.locals.get(l.index())
    }

    /// Returns block `b`, or `None` if the body has no such block.
    pub fn block(&self, b: BlockId) -> Option<&Block> {
        self.blocks.get(b.index())
    }

    /// Returns the kind of local `l`, or `None` if the body has no such local.
    pub fn local_kind(&self, l: LocalId) -> Option<LocalKind> {
        self.local(l).map(|d| d.kind)
    }

    /// Returns the ids of the blocks, in order.
    pub fn block_ids(&self) -> impl Iterator<Item = BlockId> {
        (0..self.blocks.len()).map(|i| BlockId(id_of(i)))
    }

    /// Returns the ids of the locals, in order.
    pub fn local_ids(&self) -> impl Iterator<Item = LocalId> {
        (0..self.locals.len()).map(|i| LocalId(id_of(i)))
    }
}

/// A local.
#[derive(Clone, Debug)]
pub struct LocalDecl {
    /// The final type.
    pub ty: TyId,
    /// What the local is.
    pub kind: LocalKind,
    /// The source name, if one exists.
    pub name: Option<String>,
    /// The properties of the type. The builder computes them once, from the final type.
    pub props: Props,
    /// The value of the local is built for one call, in place (`Box.new(S { .. })`).
    /// A move of it into that call is not a move of a `!Move` value (W0604).
    pub in_place: bool,
    /// Where the local comes from.
    pub origin: Origin,
}

/// What a local is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LocalKind {
    /// The return slot `_0`.
    Return,
    /// A parameter of a function, a closure or a clause.
    Param(u32),
    /// The environment of a closure body. It names the closure value of the run node:
    /// it has a cell at the entry and no `Live` or `Dead` (the closure value outlives
    /// the run). A `Move` of a place below it is valid only in a `once` closure.
    Env,
    /// A variable of the source.
    User,
    /// A temporary.
    Temp(TempKind),
    /// The iterator of a `for` loop.
    Iterator,
    /// A capability value of an effect. A handled body gets the new one as a parameter.
    Cap(EffectId),
    /// A continuation (`resume`). The flag is `multi`.
    Kont(bool),
    /// The capability of a scope (`s` in `scope { s => .. }`).
    ScopeCap,
    /// The result of a task that has no handle. `ScopeWait` gives it its value, and
    /// the end of the scope body ends it.
    TaskResult(SpawnId),
    /// The cell of a local of the parent body (a local or an upvar local there). Only
    /// a clause, a handled body and a scope body have upvar locals. An upvar local
    /// has its cell at the entry and has no `Live` or `Dead`: the cell belongs to the
    /// parent. A move of it moves the value of the parent local.
    Upvar(LocalId),
}

/// Why a temporary exists. Diagnostics use it to name the value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TempKind {
    /// An operand of a call, an operator or an aggregate.
    Operand,
    /// The callee of a call of a function value.
    Callee,
    /// A method receiver.
    Receiver,
    /// The scrutinee of a `match`.
    Scrutinee,
    /// A value that a borrow (`&e`) puts into a cell.
    Borrowed,
    /// A value that nothing keeps: its `Dead` drops it.
    Discarded,
    /// The value of a branch, an arm, a block or a frame body.
    Value,
}
