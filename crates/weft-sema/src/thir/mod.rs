//! The typed tree (THIR): the side tables of each body (`docs/ir.md` 2.1).
//!
//! The THIR is the syntax tree plus the tables of this module, keyed by
//! [`ExprId`] and [`PatId`]. The builder of the IR reads only the tree and the
//! tables. It never infers a type.
//!
//! Until plan stage R2 the old lowering (`body/`) fills the tables: it records
//! its decisions during each lowering (`record.rs`), and the analysis keeps the
//! tables of the last lowering of each body (`docs/ir.md` 2.2, phase 1). Test D0
//! ([`d0`]) checks the tables against the syntax tree and the facts.
//!
//! The old lowering can visit an expression more than once in one lowering: the
//! passes of a loop, a handled body that runs again, a place that the lowering
//! reads again. The recorder keeps each different value. A key with two
//! different values is a conflict ([`Tables::conflicts`]): D0 fails on it.

pub mod d0;
pub(crate) mod record;

use std::collections::BTreeMap;

pub use weft_ir::{AdtId, EffectId, IntTy, TyId, TyTable};
pub use weft_syntax::ast::{ExprId, PatId};

use crate::ids::{FnId, ModId};

/// A binding of a body: an index into [`Tables::bindings`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BindingId(pub u32);

impl BindingId {
    /// Returns the index into [`Tables::bindings`].
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// The syntax that makes a binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Binder {
    /// Parameter `i` of the function of the body.
    Param(u32),
    /// A name pattern: `x` in `let`, `match`, `for`, and the hidden locals of
    /// a long chain.
    Pat(PatId),
    /// Parameter `i` of a closure literal.
    ClosureParam(ExprId, u32),
    /// Parameter `i` of clause `c` of a `handle`: `(handle, c, i)`.
    ClauseParam(ExprId, u32, u32),
    /// The continuation `resume` of clause `c` of a `handle`.
    Resume(ExprId, u32),
    /// The capability `s` of `scope { s => .. }`.
    Scope(ExprId),
}

/// A binding: its syntax, its name and its type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding {
    /// The syntax that makes it.
    pub binder: Binder,
    /// The name.
    pub name: String,
    /// The type of the local. A pattern that binds by reference has a
    /// reference type here: [`Tables::pat_ty`] has the type of the value.
    pub ty: TyId,
}

/// A built-in callee or name.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Builtin {
    /// `print(..)`.
    Print,
    /// `fork(..)`.
    Fork,
    /// `s.spawn(..)` on a scope capability.
    Spawn,
    /// `t.join()` on a task handle.
    Join,
    /// `t.detach()` on a task handle.
    Detach,
}

/// What a name means.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Res {
    /// A local of the body.
    Local(BindingId),
    /// A function item, with its type arguments.
    Fn {
        /// The function.
        item: FnId,
        /// The type arguments.
        targs: Vec<TyId>,
    },
    /// A variant of an enum: a value with no payload, or a constructor.
    Variant {
        /// The enum.
        adt: AdtId,
        /// The index of the variant.
        variant: u32,
    },
    /// A struct as a constructor: `S(a, b)`.
    Struct(AdtId),
    /// An operation of an effect.
    Op {
        /// The effect.
        effect: EffectId,
        /// The index of the operation.
        op: u32,
    },
    /// A built-in callee.
    Builtin(Builtin),
    /// A module in a path.
    Mod(ModId),
    /// A type definition in a path.
    Adt(AdtId),
    /// An effect in a path.
    Effect(EffectId),
}

/// The callee of a call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Callee {
    /// A function item, with its type arguments.
    Item {
        /// The function.
        item: FnId,
        /// The type arguments.
        targs: Vec<TyId>,
    },
    /// A function value in a local. The type of the callee name gives its
    /// parameters.
    Value(BindingId),
    /// The continuation of a clause.
    Resume(BindingId),
    /// An operation: a perform.
    Op {
        /// The effect.
        effect: EffectId,
        /// The index of the operation.
        op: u32,
    },
    /// A struct constructor `S(a, b)`, with its type arguments.
    Struct {
        /// The struct.
        adt: AdtId,
        /// The type arguments.
        targs: Vec<TyId>,
    },
    /// A variant constructor `Some(x)`, with its type arguments.
    Variant {
        /// The enum.
        adt: AdtId,
        /// The index of the variant.
        variant: u32,
        /// The type arguments.
        targs: Vec<TyId>,
    },
    /// A built-in.
    Builtin(Builtin),
}

/// How a method call gives its receiver to the parameter `self`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RecvMode {
    /// `self` is a reference and the receiver is a place: the call borrows it.
    Borrow,
    /// `self` is a reference and the receiver is a reference: it passes.
    Ref,
    /// `self` is a value: the receiver moves or is copied.
    Value,
    /// `self` is a value and the receiver is a reference: the call copies the
    /// value through the reference.
    Deref,
}

/// The receiver of a method call.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Recv {
    /// How the call gives it.
    pub mode: RecvMode,
    /// The references that the method lookup follows from the type of the
    /// receiver place ([`Tables::adjust`] of the receiver has the steps).
    pub derefs: u32,
}

/// A call or a method call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallInfo {
    /// The callee.
    pub callee: Callee,
    /// The receiver of a method call on a value.
    pub recv: Option<Recv>,
    /// For each parameter after the receiver, the index of its argument (ADR
    /// 0009): an index into the arguments, or the number of arguments for the
    /// trailing block. `None`: no argument.
    pub args: Vec<Option<u32>>,
}

/// An implicit dereference (`docs/plan/core-ir-inputs/semantics.md` 2.4).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum DerefKind {
    /// Through a reference.
    Ref,
    /// Through a `Box` or another extern type with a stable or unstable deref.
    Box,
    /// Through an `Rc` (an extern type with a group deref).
    Rc,
}

/// The part that a field expression names, after its dereferences.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FieldIdx {
    /// A field of a struct or a tuple.
    Field(u32),
    /// The payload of a variant: `o.Some`.
    Variant(u32),
}

/// A closure literal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosureInfo {
    /// The parameters.
    pub params: Vec<BindingId>,
    /// The result type.
    pub ret: TyId,
    /// The stated row of the type of the closure, if any.
    pub row: Option<Vec<EffectId>>,
}

/// A `handle` expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandleInfo {
    /// The effect.
    pub effect: EffectId,
    /// The identity of the effect (`effects::identity`).
    pub identity: String,
    /// The operation of each clause, in the order of the clauses. `None`: the
    /// effect has no operation with the name of the clause.
    pub clauses: Vec<Option<u32>>,
    /// The effect has a `multi` operation.
    pub multi: bool,
}

/// A key of a table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Key {
    /// An expression.
    Expr(ExprId),
    /// A pattern.
    Pat(PatId),
    /// A parameter of the function of the body.
    Param(u32),
}

/// Two visits of one key gave two different values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Conflict {
    /// The table.
    pub table: &'static str,
    /// The key.
    pub key: Key,
    /// The values, as text.
    pub values: Vec<String>,
}

/// The THIR tables of one body.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Tables {
    /// The final type of each expression.
    pub expr_ty: BTreeMap<ExprId, TyId>,
    /// The type of the value that each pattern matches, before its
    /// dereferences ([`Tables::pat_adjust`]).
    pub pat_ty: BTreeMap<PatId, TyId>,
    /// The binding of each name pattern.
    pub binding: BTreeMap<PatId, BindingId>,
    /// The bindings of the body.
    pub bindings: Vec<Binding>,
    /// What each name means.
    pub res: BTreeMap<ExprId, Res>,
    /// Each call and method call.
    pub call: BTreeMap<ExprId, CallInfo>,
    /// The implicit dereferences of the value of each expression, in order:
    /// at a field, an index, a method receiver, a borrow, a compound store, an
    /// operator, a condition and a call argument.
    pub adjust: BTreeMap<ExprId, Vec<DerefKind>>,
    /// The implicit dereferences of the value at each pattern, before its test.
    pub pat_adjust: BTreeMap<PatId, Vec<DerefKind>>,
    /// The part that each field expression names.
    pub field: BTreeMap<ExprId, FieldIdx>,
    /// The integer type of each arithmetic operation. A compound assignment has
    /// its entry at its right side.
    pub int_ty: BTreeMap<ExprId, IntTy>,
    /// Each closure literal.
    pub closure: BTreeMap<ExprId, ClosureInfo>,
    /// Each `handle`.
    pub handle: BTreeMap<ExprId, HandleInfo>,
    /// The effect of each operation name, effect path and `handle`.
    pub effect: BTreeMap<ExprId, EffectId>,
    /// The keys whose visits gave different values.
    pub conflicts: Vec<Conflict>,
    /// A recorded type holds the error type: the body has no IR.
    pub error: bool,
    /// The expressions whose type had a free type variable: the table gives it
    /// the unit type (`docs/ir.md` 2.3).
    pub free: Vec<ExprId>,
}

impl Tables {
    /// Returns the binding of `id`.
    pub fn binding_of(&self, id: BindingId) -> Option<&Binding> {
        self.bindings.get(id.index())
    }
}
