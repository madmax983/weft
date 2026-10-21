//! The core IR of Weft (ADR 0012, `docs/ir.md`).
//!
//! The IR goes between the typed tree (THIR) and fact generation. The
//! interpreter runs it too. This crate holds the IR types, the final type
//! table ([`ty`]), the printer ([`mod@print`]) and the verifier. It does not depend
//! on `weft-sema`: `weft-sema` makes the IR from its typed tree.
//!
//! The shapes of the IR copy the proof models:
//!
//! - One [`Body`] is one frame of the interpreter (`CodeKind`) and one block of the
//!   effects model (`proofs/effects/src/model.rs`, `Block`).
//! - Each statement and each terminator is one node of the B1 CFG model
//!   (`proofs/borrowing/src/cfg.rs`, `Node`). Some terminators have a fixed list of
//!   more nodes.
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
//! `docs/ir.md` section 3.2 lists the changes from the machine sketch and the
//! reason for each change.

#![forbid(unsafe_code)]

pub mod body;
pub mod decl;
pub mod place;
pub mod print;
pub mod stmt;
pub mod term;
pub mod ty;
pub mod verify;

pub use body::{Body, BodyKind, LocalDecl, LocalKind, TempKind};
pub use decl::{
    CapEnv, Capture, CaptureMode, ClosureDecl, FnDecl, HandlerDecl, Intrinsic, Program, ScopeDecl,
    SpawnDecl, TestDecl,
};
pub use place::{Const, DerefKind, Operand, Place, Proj, Side};
pub use stmt::{AggKind, BinOp, Block, IterSource, Rvalue, Stmt, StmtKind, UnOp, UnwindAction};
pub use term::{Callee, CapArgs, CapOperand, Term, TermKind};
pub use ty::{AdtId, EffectId, IntTy, Props, Ty, TyId, TyTable};
pub use weft_syntax::ast::{ExprId, PatId};

/// Makes a `u32` index type.
macro_rules! id {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
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

/// Returns the id of item `i` of a table: an index that does not fit in `u32` gives
/// `u32::MAX`, which is the id of no item.
pub(crate) fn id_of(i: usize) -> u32 {
    u32::try_from(i).unwrap_or(u32::MAX)
}

/// A source location.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    /// The source unit.
    pub unit: u32,
    /// The first byte.
    pub lo: u32,
    /// The byte after the last byte.
    pub hi: u32,
}

impl Span {
    /// Returns true if this span holds all of span `other`.
    pub const fn contains(self, other: Self) -> bool {
        self.unit == other.unit && self.lo <= other.lo && other.hi <= self.hi
    }
}

/// Where an IR item comes from. Diagnostics use it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Origin {
    /// The source location.
    pub span: Span,
    /// The expression of the typed tree, if one exists.
    pub expr: Option<ExprId>,
}
