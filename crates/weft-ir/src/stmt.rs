//! Blocks, statements and right sides (`docs/ir.md` 3.2).

use crate::{ClosureId, FnId, IntTy, LocalId, Operand, Origin, Place, Term, TyId, VariantIdx};

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
    /// [`ClosureDecl::captures`](crate::ClosureDecl::captures): `&x` for `ByRef`,
    /// `move x` for `ByMove`, a kept cell for `Kept` (`Operand::Copy` of the variable,
    /// which the interpreter reads as its cell), a copy for `Cap`, a copy or move for
    /// `Kont`.
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
