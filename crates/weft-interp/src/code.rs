//! Compiled code: a stack machine with explicit frames.
//!
//! Each function, closure, handler clause, `handle` body and `scope` body is one
//! [`Code`] unit. A frame runs one unit. Because the frames are data, a perform
//! can capture the frames up to its handler as a delimited continuation.

use std::rc::Rc;

use weft_sema::program::{EffectId, FnId};
use weft_sema::types::{AdtId, IntTy};
use weft_syntax::ast::{BinOp, Span};

use crate::value::CodeId;

/// A variable reference: a local slot or a captured cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VarRef {
    /// A slot of the frame.
    Local(u32),
    /// A captured cell of the closure.
    Cap(u32),
}

/// A literal in a pattern.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LitPat {
    /// An integer.
    Int(i64),
    /// A boolean.
    Bool(bool),
    /// A string.
    Str(Rc<str>),
    /// `()`.
    Unit,
}

/// A compiled `match` pattern.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CPat {
    /// `_`.
    Wild,
    /// A binding into a slot.
    Bind(u32),
    /// A literal.
    Lit(LitPat),
    /// A tuple.
    Tuple(Vec<Self>),
    /// A variant or a positional struct pattern.
    Variant {
        /// The variant or struct name.
        name: Rc<str>,
        /// The payload patterns.
        fields: Vec<Self>,
    },
}

/// One handler clause of a `handle` expression.
#[derive(Clone, Debug)]
pub struct ClauseSpec {
    /// The operation index in the effect.
    pub op: usize,
    /// The clause code. Its parameters are the operation arguments, then `resume`.
    pub code: CodeId,
    /// The captured variables.
    pub caps: Vec<VarRef>,
}

/// A compiled `handle` expression.
#[derive(Clone, Debug)]
pub struct HandleSpec {
    /// The handled effect.
    pub effect: EffectId,
    /// The clauses.
    pub clauses: Vec<ClauseSpec>,
    /// The handled computation, as a closure with no parameters.
    pub body: CodeId,
    /// The variables that the body captures.
    pub body_caps: Vec<VarRef>,
}

/// One instruction.
#[derive(Clone, Debug)]
pub enum Op {
    /// Pushes `()`.
    Unit,
    /// Pushes an integer.
    Int(i64),
    /// Pushes a boolean.
    Bool(bool),
    /// Pushes a string.
    Str(Rc<str>),
    /// Pushes a duration in milliseconds.
    Dur(u64),
    /// Pushes the place of a variable.
    Var(VarRef),
    /// Pops a value into a new cell for a slot.
    Bind(u32),
    /// Makes a slot with no value (`let x` without `=`).
    BindEmpty(u32),
    /// Ends the life of slots at the end of a scope.
    DropSlots(Vec<u32>),
    /// Place to place: a field by name. Follows references, boxes and `Rc`.
    Field(Rc<str>),
    /// `[place, index]` to place: an element.
    Index,
    /// Value to place: a temporary cell.
    ToTemp,
    /// Place to value: copies a copy value and moves any other value.
    Read,
    /// Place to reference.
    Borrow,
    /// Place to a slice of all its elements (`&x[]`).
    BorrowAll,
    /// `[value, place]`: stores the value and drops the old one.
    Store,
    /// `[value, place]`: a compound assignment. The new value must fit in the
    /// integer type, if any (see [`Op::CheckInt`]).
    CompoundStore(BinOp, Option<IntTy>),
    /// Drops the top value.
    Pop,
    /// Drops the value under the top value.
    Nip,
    /// A binary operator.
    Bin(BinOp),
    /// `-x`.
    Neg,
    /// Faults if the integer on top of the stack does not fit in the integer
    /// type that semantic analysis gives the expression (`FnFacts::int_ops`).
    CheckInt(IntTy),
    /// `!x`.
    Not,
    /// Jumps.
    Jump(usize),
    /// Pops a boolean and jumps if it is false.
    JumpIfFalse(usize),
    /// Pops a boolean and jumps if it is true.
    JumpIfTrue(usize),
    /// A loop back-edge: the scheduler may preempt here.
    BackEdge,
    /// Records the stack heights at the start of a loop.
    LoopEnter,
    /// Forgets the innermost loop.
    LoopExit,
    /// Leaves a loop: restores the stack heights, then jumps.
    Break(usize),
    /// Starts a statement: temporaries made after this point belong to it.
    StmtBegin,
    /// Ends a statement: drops its temporaries.
    StmtEnd,
    /// Returns the top value from the frame.
    Return,
    /// Pops `n` values into a tuple.
    Tuple(u32),
    /// Pops `n` values into a new `Vec`.
    MakeVec(u32),
    /// Pops values into a struct. `fields[i]` is the field of the `i`-th value.
    MakeStruct {
        /// The struct.
        adt: AdtId,
        /// The field index of each popped value, in push order.
        fields: Vec<u32>,
        /// The number of fields.
        total: u32,
    },
    /// Pops `n` values into an enum variant.
    MakeEnum {
        /// The enum.
        adt: AdtId,
        /// The variant.
        variant: u32,
        /// The number of payload values.
        n: u32,
    },
    /// Splits a tuple (or a reference to one) into `n` values. The first is on top.
    Untuple(u32),
    /// Destructures a struct into `n` field values and consumes a linear struct.
    Unstruct(u32),
    /// Pops `n` strings and pushes their concatenation.
    Concat(u32),
    /// Converts the top value to its display string.
    ToStr,
    /// Tests the place on top against a pattern; binds on success, else jumps.
    Match {
        /// The pattern.
        pat: Rc<CPat>,
        /// Where to go if the pattern does not match.
        fail: usize,
    },
    /// Calls a function item with `n` arguments.
    Call {
        /// The function.
        f: FnId,
        /// The number of arguments.
        n: u32,
    },
    /// Calls `[callee, args...]`.
    CallValue(u32),
    /// Calls a method on `[receiver place, args...]`.
    CallMethod {
        /// The method name.
        name: Rc<str>,
        /// The number of arguments after the receiver.
        n: u32,
        /// The span of the first argument (a spawned closure).
        arg_span: Span,
    },
    /// Performs an effect operation with `n` arguments.
    Perform {
        /// The effect.
        effect: EffectId,
        /// The operation index.
        op: usize,
        /// The number of arguments.
        n: u32,
    },
    /// Makes a closure.
    MakeClosure {
        /// The code.
        code: CodeId,
        /// The captured variables.
        caps: Vec<VarRef>,
        /// The indexes in `caps` of the captures that the closure takes by
        /// value: it moves each value into a cell of its own.
        owned: Vec<u32>,
        /// The closure expression. The checker names the tasks that run the
        /// closure by it (`stealable`).
        span: Span,
    },
    /// Pushes a function item as a value.
    FnValue(FnId),
    /// Installs a handler and runs its body.
    Handle(Rc<HandleSpec>),
    /// Starts a scope and runs its body. The body takes the scope capability.
    Scope {
        /// The body code.
        code: CodeId,
        /// The captured variables.
        caps: Vec<VarRef>,
    },
    /// Waits for the children of the scope in a slot.
    ScopeWait(u32),
    /// Runs `n` closures as tasks and waits for all of them.
    Fork {
        /// The number of branches.
        n: u32,
        /// The span of each branch.
        spans: Vec<Span>,
    },
    /// Prints `n` values.
    Print(u32),
    /// Pops a boolean and fails if it is false.
    Assert,
    /// `[lo, hi]` to a range iterator.
    RangeIter,
    /// Place to an iterator over references to the elements.
    ElemIter,
    /// Advances the iterator in a slot, or jumps to the exit.
    IterNext {
        /// The slot of the iterator.
        slot: u32,
        /// The loop exit.
        exit: usize,
    },
    /// A compile-time error that becomes a run-time error here.
    Fault(Rc<str>),
}

/// What a code unit is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CodeKind {
    /// A function body.
    Fn(FnId),
    /// A test body.
    Test,
    /// A closure.
    Closure,
    /// A handler clause.
    Clause,
    /// The body of a `handle` expression.
    HandleBody,
    /// The body of a `scope`.
    ScopeBody,
}

/// One compiled code unit.
#[derive(Clone, Debug)]
pub struct Code {
    /// The name, for errors.
    pub name: String,
    /// The kind.
    pub kind: CodeKind,
    /// The instructions.
    pub ops: Vec<Op>,
    /// The source span of each instruction.
    pub spans: Vec<Span>,
    /// The number of slots.
    pub n_slots: u32,
    /// The number of parameters: they are slots `0..n_params`.
    pub n_params: u32,
    /// The source unit of the code. Its spans are byte offsets in that unit.
    pub unit: usize,
}
