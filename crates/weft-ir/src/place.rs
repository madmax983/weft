//! Places, projections, operands and constants (`docs/ir.md` 3.2).

use crate::{FieldIdx, FnId, IntTy, LocalId, SplitId, TyId, VariantIdx};

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
        Self {
            local,
            proj: Vec::new(),
        }
    }

    /// Returns true if a projection follows a pointer.
    pub fn has_deref(&self) -> bool {
        self.proj.iter().any(|p| matches!(p, Proj::Deref(_)))
    }

    /// Returns true if the place is a move path: no `Deref` and no `Index`.
    pub fn is_move_path(&self) -> bool {
        self.proj
            .iter()
            .all(|p| matches!(p, Proj::Field(_) | Proj::Variant(_)))
    }

    /// Returns true if the place is a whole local: it has no projection.
    pub fn is_local(&self) -> bool {
        self.proj.is_empty()
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
    /// The bounds check is a statement before it
    /// ([`StmtKind::Bounds`](crate::StmtKind::Bounds)).
    Index(LocalId),
    /// All elements (`&v[]`).
    Elems,
    /// One side of a split. Only in the interface places of a summary (a signature
    /// place `v[..k]`); no expression writes it.
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
    /// Read and copy. Only for a type with [`Props::copy`](crate::Props::copy).
    Copy(Place),
    /// Read and move. The place has no value after it.
    Move(Place),
    /// A constant.
    Const(Const),
}

impl Operand {
    /// Returns the place that the operand reads, if it reads one.
    pub const fn place(&self) -> Option<&Place> {
        match self {
            Self::Copy(p) | Self::Move(p) => Some(p),
            Self::Const(_) => None,
        }
    }
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
