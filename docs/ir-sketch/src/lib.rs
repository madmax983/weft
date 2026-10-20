//! The core IR of Weft (final design sketch for ADR 0012).
//!
//! The IR goes between the typed tree (THIR) and fact generation. The interpreter
//! runs it too. Its shapes copy the proof models:
//!
//! - One [`Body`] is one frame of the interpreter (`CodeKind`) and one block of the
//!   effects model (`proofs/effects/src/model.rs`, `Block`).
//! - Each statement and each terminator is one node of the B1 CFG model
//!   (`proofs/borrowing/src/cfg.rs`, `Node`). Some terminators have a fixed list of
//!   more nodes (`facts::Phase`).
//! - Capabilities and continuations are values with storage ([`LocalKind::Cap`],
//!   [`LocalKind::Kont`]). A perform names its capability ([`CapOperand`]). A call
//!   passes capabilities ([`CapArgs`]), as `Call { block, caps }` of the effects model.
//! - Unwinding is code: each terminator that can abort names a cleanup block. A
//!   cleanup chain finishes the values of its frame ([`StmtKind::UnwindValue`]) and
//!   ends with [`TermKind::UnwindExit`], as the unwinder steps of the effects model.
//! - A clause, a handled body and a scope body name the locals of the frame around
//!   them as upvar locals ([`LocalKind::Upvar`]). A closure holds its captures in its
//!   environment ([`CaptureMode`]).
//!
//! Changes from the machine sketch (`ir/work/machine/weft_ir_sketch`), each from a
//! judge report of the design round:
//!
//! - upvar locals replace the environment operands of `Handle` and `Scope` (proofs
//!   judge, graft 4);
//! - `CaptureMode::Kept` only for plain data that no body borrows (soundness judge,
//!   graft 1; rule CAPTURE of the minimal design);
//! - `Dead` always ends the value and emits `scope_end`; `Drop` exists only for a
//!   place behind a pointer, right before a new value (soundness judge, H9);
//! - `CapOperand::Row` is valid in each body whose capability environment does not
//!   bind the effect (proofs judge, fix 10); `CapOperand::Root` is gone (root
//!   capabilities come from `CapArgs::Root` and from the driver);
//! - in a clause, the cleanup chain starts with `UnwindKont` (proofs judge, graft 7).

#![forbid(unsafe_code)]

pub mod example;
pub mod facts;
pub mod rels;
pub mod verify;

macro_rules! id {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub u32);

        impl $name {
            /// Returns the index into the owning table.
            pub const fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

id!(
    /// A body: a frame of the interpreter.
    BodyId
);
id!(
    /// A basic block of one body.
    BlockId
);
id!(
    /// A local of one body: a parameter, a variable, a temporary or a hidden value.
    LocalId
);
id!(
    /// A function item (also an extern function and an `on abort` function).
    FnId
);
id!(
    /// A closure literal.
    ClosureId
);
id!(
    /// A `handle` expression.
    HandlerId
);
id!(
    /// A `scope` expression.
    ScopeId
);
id!(
    /// A `test` block.
    TestId
);
id!(
    /// A spawn site: a `spawn` call or a `fork` branch.
    SpawnId
);
id!(
    /// An interned final type: no inference variables and no closure summaries.
    TyId
);
id!(
    /// An effect.
    EffectId
);
id!(
    /// An operation of an effect.
    OpIdx
);
id!(
    /// A field of a struct, a part of a tuple, or a field of a closure environment.
    FieldIdx
);
id!(
    /// A variant of an enum.
    VariantIdx
);
id!(
    /// One split of a slice (`split_at`): the two sides of one split do not overlap.
    SplitId
);
id!(
    /// A static capability environment: the capability of each effect at a point.
    CapEnvId
);
id!(
    /// An expression of the typed tree.
    ExprId
);

/// A source location.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Span {
    /// The source unit.
    pub unit: u32,
    /// The first byte.
    pub lo: u32,
    /// The byte after the last byte.
    pub hi: u32,
}

/// Where an IR item comes from. Diagnostics use it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Origin {
    /// The source location.
    pub span: Span,
    /// The expression of the typed tree, if one exists.
    pub expr: Option<ExprId>,
}

/// An integer type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IntTy {
    /// `u8`.
    U8,
    /// `u16`.
    U16,
    /// `u32`.
    U32,
    /// `u64`.
    U64,
    /// `usize`.
    Usize,
    /// `i8`.
    I8,
    /// `i16`.
    I16,
    /// `i32`.
    I32,
    /// `i64`.
    I64,
}

// ---------------------------------------------------------------------------
// The program
// ---------------------------------------------------------------------------

/// A whole program: each body of each unit, and the declarations.
#[derive(Clone, Debug, Default)]
pub struct Program {
    /// The bodies. The index is the [`BodyId`].
    pub bodies: Vec<Body>,
    /// The function items. The index is the [`FnId`].
    pub fns: Vec<FnDecl>,
    /// The closure literals. The index is the [`ClosureId`].
    pub closures: Vec<ClosureDecl>,
    /// The `handle` expressions. The index is the [`HandlerId`].
    pub handlers: Vec<HandlerDecl>,
    /// The `scope` expressions. The index is the [`ScopeId`].
    pub scopes: Vec<ScopeDecl>,
    /// The spawn sites. The index is the [`SpawnId`].
    pub spawns: Vec<SpawnDecl>,
    /// The static capability environments. The index is the [`CapEnvId`].
    pub cap_envs: Vec<CapEnv>,
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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

// ---------------------------------------------------------------------------
// Bodies
// ---------------------------------------------------------------------------

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
    /// The block that ends the unwinding of this frame ([`TermKind::UnwindExit`]).
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
                v.push(LocalId(i as u32));
            }
        }
        v.sort();
        v.dedup();
        v
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

/// The properties of a type that the facts need. One function computes them
/// (`props.rs`), from the final type.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[allow(clippy::struct_excessive_bools)]
pub struct Props {
    /// The value is copied when it is read (plain data).
    pub copy: bool,
    /// The value is linear.
    pub linear: bool,
    /// The type declares `on abort` for each linear part.
    pub on_abort: bool,
    /// The value is not `many`.
    pub once: bool,
    /// The type is `!Move`.
    pub immovable: bool,
    /// The value cannot cross threads.
    pub nonportable: bool,
    /// The value is `@ uniq`.
    pub uniq: bool,
    /// The value can be a function value.
    pub callable: bool,
    /// The type mentions a type parameter.
    pub generic: bool,
    /// The value can hold a reference.
    pub holds_refs: bool,
}

// ---------------------------------------------------------------------------
// Places and operands
// ---------------------------------------------------------------------------

/// A place: a local and projections.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Place {
    /// The local. An upvar local names the cell of a local of the parent body.
    pub local: LocalId,
    /// The projections, from the local outwards.
    pub proj: Vec<Proj>,
}

impl Place {
    /// A place with no projection.
    pub const fn local(local: LocalId) -> Self {
        Self { local, proj: Vec::new() }
    }

    /// Returns true if a projection follows a pointer.
    pub fn has_deref(&self) -> bool {
        self.proj.iter().any(|p| matches!(p, Proj::Deref(_)))
    }

    /// Returns true if the place is a move path: no `Deref` and no `Index`.
    pub fn is_move_path(&self) -> bool {
        self.proj.iter().all(|p| matches!(p, Proj::Field(_) | Proj::Variant(_)))
    }
}

/// One projection. Each one is one step of the place model (ADR 0003), except
/// [`Proj::Deref`] of a reference, which goes to the places that the reference
/// points into.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Proj {
    /// Follow a pointer.
    Deref(DerefKind),
    /// A field of a struct, a part of a tuple, or a field of a closure environment. A
    /// stable step.
    Field(FieldIdx),
    /// The payload of a variant. An unstable step. Valid only after a test of the
    /// variant.
    Variant(VariantIdx),
    /// An element. The stability comes from the type (`Vec`: unstable; array: stable).
    /// The bounds check is a statement before it ([`StmtKind::Bounds`]).
    Index(LocalId),
    /// All elements (`&v[]`).
    Elems,
    /// One side of a split.
    Split(SplitId, Side),
}

/// A pointer kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DerefKind {
    /// A reference: the place moves to the places that the reference points into.
    Ref,
    /// A `Box`: an unstable step below the owner.
    Box,
    /// An `Rc`: the `rc` group root of the inner type. The handle stays a dependence.
    Rc,
}

/// A side of a split.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Side {
    /// `[..k]`.
    Left,
    /// `[k..]`.
    Right,
}

/// An operand. Each read of a place is an operand at one statement or terminator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operand {
    /// Read and copy. Only for a type with [`Props::copy`].
    Copy(Place),
    /// Read and move. The place has no value after it.
    Move(Place),
    /// A constant.
    Const(Const),
}

/// A constant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Const {
    /// `()`.
    Unit,
    /// A boolean.
    Bool(bool),
    /// An integer with its type.
    Int(i128, IntTy),
    /// A string.
    Str(String),
    /// A duration in milliseconds.
    Duration(u64),
    /// A function item as a value, with its type arguments.
    Fn(FnId, Vec<TyId>),
}

/// The right side of an assignment. No right side can change memory or suspend.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rvalue {
    /// An operand.
    Use(Operand),
    /// A reference to a place.
    Ref(Place),
    /// A binary operator. An integer result is checked against its type: a fault
    /// stops the run.
    Binary(BinOp, Option<IntTy>, Operand, Operand),
    /// A unary operator.
    Unary(UnOp, Option<IntTy>, Operand),
    /// A tuple, an array, a `Vec`, a struct, a variant or a closure.
    Aggregate(AggKind, Vec<Operand>),
    /// The length of a buffer. It reads the buffer.
    Len(Place),
    /// The variant of an enum value. It reads the tag.
    Discriminant(Place),
    /// A string interpolation: the text of each operand, joined.
    Concat(Vec<Operand>),
    /// A new iterator over the elements of a place, or over a range.
    Iter(IterSource),
}

/// A binary operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    /// `+`.
    Add,
    /// `-`.
    Sub,
    /// `*`.
    Mul,
    /// `/`.
    Div,
    /// `%`.
    Rem,
    /// `==`.
    Eq,
    /// `!=`.
    Ne,
    /// `<`.
    Lt,
    /// `<=`.
    Le,
    /// `>`.
    Gt,
    /// `>=`.
    Ge,
}

/// A unary operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    /// `-x`.
    Neg,
    /// `!x`.
    Not,
}

/// What an aggregate builds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AggKind {
    /// A tuple.
    Tuple,
    /// A fixed array.
    Array,
    /// A new `Vec` with these elements.
    Vec,
    /// A struct. The operands are in the order of the fields of the struct.
    Struct(TyId),
    /// A variant.
    Variant(TyId, VariantIdx),
    /// A closure. The operands are the fields of its environment, in the order of
    /// [`ClosureDecl::captures`]: `&x` for `ByRef`, `move x` for `ByMove`, a kept
    /// cell for `Kept` (`Operand::Copy` of the variable, which the interpreter reads as
    /// its cell), a copy for `Cap`, a copy or move for `Kont`.
    Closure(ClosureId),
}

/// The source of an iterator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IterSource {
    /// The elements of a place. A scalar element is a copy; another element is a
    /// reference into the buffer.
    Elems(Place),
    /// A range `lo..hi`.
    Range(Operand, Operand),
}

// ---------------------------------------------------------------------------
// Capabilities
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Statements and terminators
// ---------------------------------------------------------------------------

/// A basic block.
#[derive(Clone, Debug)]
pub struct Block {
    /// The statements.
    pub stmts: Vec<Stmt>,
    /// The terminator.
    pub term: Term,
    /// The block is on a cleanup path. Only an abort edge enters a cleanup block.
    pub cleanup: bool,
}

/// A statement. It cannot suspend and has one successor.
#[derive(Clone, Debug)]
pub struct Stmt {
    /// What the statement does.
    pub kind: StmtKind,
    /// Where it comes from.
    pub origin: Origin,
}

/// What a statement does.
#[derive(Clone, Debug)]
pub enum StmtKind {
    /// The local gets a new cell. It has no value yet.
    Live(LocalId),
    /// The value that is still in the local goes away (a drop), and the cell of the
    /// local ends. On a normal path this is the end of the scope of the local; on a
    /// cleanup path the unwinder ends the cell after [`StmtKind::UnwindValue`].
    Dead(LocalId),
    /// The place gets a value. The old value at the place goes away first (a drop).
    Assign(Place, Rvalue),
    /// The value at a place behind a pointer goes away, and the place has no value
    /// until the next statement, which is an `Assign` of the same place. Only for a
    /// place with a `Deref` (ADR 0007: behind a reference the old value is always
    /// there, so a linear old value is an error).
    Drop(Place),
    /// A linear value is finished: a destructuring of a linear struct, or a `match`
    /// arm that takes a variant with no payload.
    Consume(Place),
    /// The place has no value from here (`let x: T`, a place field of a value that is
    /// built in place).
    Uninit(Place),
    /// A check of an index against the length of a buffer. A failure is a fault.
    Bounds(Place, Operand),
    /// A place in statement position: the place is named and not read.
    Mention(Place),
    /// `print`: reads each operand.
    Print(Vec<Operand>),
    /// The unwinder finishes the value at the place: it runs its `on abort`, or drops
    /// it. Only on a cleanup path.
    UnwindValue(Place, UnwindAction),
    /// The unwinder aborts a fresh continuation that the clause frame holds: the
    /// frames of the continuation unwind now. Only on a cleanup path, and first in
    /// the chain of a clause (the order of the effects model).
    UnwindKont(LocalId),
}

/// What the unwinder does with one value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnwindAction {
    /// Run this `on abort` function with the root handlers.
    OnAbort(FnId),
    /// Drop the value: it has no linear part.
    Drop,
    /// The value is linear and has no `on abort`: a fault. W0602 rejects each program
    /// that can reach it.
    Fault,
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
#[derive(Clone, Debug)]
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
    /// The unwinding leaves this frame. Only in [`Body::unwind_exit`].
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
        /// The continuation: the `Kont` local of a clause, or a `Kont` field of a
        /// closure environment.
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
            Self::Switch { arms, otherwise, .. } => {
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
}
