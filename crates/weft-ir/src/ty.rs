//! The final type table (`docs/ir.md` section 2.3).
//!
//! A [`Ty`] has no inference variables, no error type and no closure summary.
//! The table interns each type: two equal types get the same [`TyId`]. A type
//! names its parts by id, so a comparison of two types is a comparison of two
//! ids.
//!
//! The table also holds the declarations of the type definitions
//! ([`AdtDecl`]) and of the effects ([`EffectDecl`]). The index of a
//! declaration is the index of the definition in the program of `weft-sema`.
//!
//! The prelude types `Vec`, `Box`, `Rc`, `Weak`, `String`, `Duration`, `Task`,
//! `Scope` and the raw pointer `*T` are definitions too. [`AdtDecl::lang`]
//! names them, so that the builder can find a `Box` or an `Rc` without a
//! search by name.

use std::collections::HashMap;
use std::fmt::Write as _;

/// Makes a `u32` index type.
macro_rules! id {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub u32);

        impl $name {
            /// Returns the index into the table.
            pub const fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

id!(
    /// An interned final type: no inference variables and no closure summaries.
    TyId
);
id!(
    /// A type definition: a struct, an enum or an extern type.
    AdtId
);
id!(
    /// An effect.
    EffectId
);

/// An integer type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
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

impl IntTy {
    /// All integer types.
    pub const ALL: [Self; 9] = [
        Self::U8,
        Self::U16,
        Self::U32,
        Self::U64,
        Self::Usize,
        Self::I8,
        Self::I16,
        Self::I32,
        Self::I64,
    ];

    /// Parses an integer type name.
    pub fn from_name(s: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|i| i.name() == s)
    }

    /// Returns the type name.
    pub const fn name(self) -> &'static str {
        match self {
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::Usize => "usize",
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
        }
    }

    /// Returns the smallest and the largest value of the type.
    pub const fn range(self) -> (i128, i128) {
        match self {
            Self::U8 => (0, u8::MAX as i128),
            Self::U16 => (0, u16::MAX as i128),
            Self::U32 => (0, u32::MAX as i128),
            Self::U64 | Self::Usize => (0, u64::MAX as i128),
            Self::I8 => (i8::MIN as i128, i8::MAX as i128),
            Self::I16 => (i16::MIN as i128, i16::MAX as i128),
            Self::I32 => (i32::MIN as i128, i32::MAX as i128),
            Self::I64 => (i64::MIN as i128, i64::MAX as i128),
        }
    }
}

/// A function type: parameters, result and the stated row.
///
/// It has no closure summary and no function item: the analysis finds the
/// function values that a value of the type can be (`docs/ir.md` 2.1).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FnTy {
    /// The parameter types, in order.
    pub params: Vec<TyId>,
    /// The result type.
    pub ret: TyId,
    /// The stated effect row, in the order of the ids, each effect one time.
    /// `None`: the type states no row, and a call passes the effects of the
    /// caller through.
    pub row: Option<Vec<EffectId>>,
}

/// A final type.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    /// `()`.
    Unit,
    /// `bool`.
    Bool,
    /// The type of an expression that does not return.
    Never,
    /// An integer.
    Int(IntTy),
    /// A tuple.
    Tuple(Vec<TyId>),
    /// A fixed array.
    Array(TyId, u64),
    /// A slice `[T]`, only behind a reference.
    Slice(TyId),
    /// A reference. It has no place: the analysis finds the places.
    Ref(TyId),
    /// A struct, an enum or an extern type, with type arguments. The prelude
    /// types (`String`, `Box`, `Vec`, ...) and raw pointers are definitions too
    /// ([`AdtDecl::lang`]).
    Adt(AdtId, Vec<TyId>),
    /// A function value.
    Fn(FnTy),
    /// A type parameter of the signature of the body.
    Param(u32),
    /// The capability of a `scope` (`s` in `scope { s => .. }`).
    Scope,
    /// A capability value of an effect: the `Cap` local of a handled body.
    Cap(EffectId),
    /// A continuation: `resume` takes the first type and gives the second.
    Cont(TyId, TyId),
    /// The iterator of a `for` loop. The type is the type of each item.
    Iter(TyId),
}

/// A prelude definition that the IR knows.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Lang {
    /// `Vec<T>`.
    Vec,
    /// `Box<T>`.
    Box,
    /// `Rc<T>`.
    Rc,
    /// `Weak<T>`.
    Weak,
    /// `String`.
    String,
    /// `Duration`.
    Duration,
    /// `Task<T>`.
    Task,
    /// The extern type `Scope` of the prelude.
    Scope,
    /// A raw pointer `*T`: an opaque copy value with no place and no `Deref`.
    Ptr,
}

/// How `*x` works for an extern pointer type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ExternDeref {
    /// The target never moves: references through it survive mutation.
    Stable,
    /// A mutation can replace the target, as for a reassignable `Box`.
    Unstable,
    /// The target is in the `rc` group of its type.
    Group,
}

/// A field of a struct.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldDecl {
    /// The field name.
    pub name: String,
    /// The field type, with type parameters as [`Ty::Param`].
    pub ty: TyId,
    /// The field is a place field: a reference with an `in` place in terms of
    /// `self` (a field of a `!Move` struct).
    pub place: bool,
}

/// A variant of an enum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariantDecl {
    /// The variant name.
    pub name: String,
    /// The payload types, with type parameters as [`Ty::Param`].
    pub fields: Vec<TyId>,
}

/// The shape of a type definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdtKind {
    /// A struct.
    Struct(Vec<FieldDecl>),
    /// An enum.
    Enum(Vec<VariantDecl>),
    /// An extern type.
    Extern {
        /// The stability of `x[]`, if the type has elements.
        elem_unstable: Option<bool>,
        /// How `*x` works, if the type is a pointer.
        deref: Option<ExternDeref>,
    },
}

/// A property of a type that a part of the type passes on. The rows of
/// [`AdtDecl::props`] use this order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TyProp {
    /// A part is a linear value.
    Linear,
    /// A part cannot cross threads.
    Nonportable,
    /// A part keeps its address (`!Move`).
    Immovable,
    /// A part is a reference or a slice.
    Refs,
    /// A part is a function value.
    Fns,
    /// A part is not plain data: the value moves, it is not copied.
    NotCopy,
    /// A linear part has no `on abort`, and no type around it on the way has one.
    NoOnAbort,
    /// A part is a resource that a `multi` resume cannot copy.
    Resource,
}

impl TyProp {
    /// The properties, in the order of the rows.
    pub const ALL: [Self; 8] = [
        Self::Linear,
        Self::Nonportable,
        Self::Immovable,
        Self::Refs,
        Self::Fns,
        Self::NotCopy,
        Self::NoOnAbort,
        Self::Resource,
    ];

    /// Returns the index of the row of the property.
    pub const fn index(self) -> usize {
        match self {
            Self::Linear => 0,
            Self::Nonportable => 1,
            Self::Immovable => 2,
            Self::Refs => 3,
            Self::Fns => 4,
            Self::NotCopy => 5,
            Self::NoOnAbort => 6,
            Self::Resource => 7,
        }
    }
}

/// When a property holds for the instances of a definition.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct PropRow {
    /// The property holds for every instance.
    pub always: bool,
    /// The type parameters that pass the property on, in order: the property
    /// holds for an instance if it holds for one of these arguments.
    pub params: Vec<u32>,
}

/// A type definition: a struct, an enum or an extern type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdtDecl {
    /// The name.
    pub name: String,
    /// The number of type parameters.
    pub generics: u32,
    /// The shape.
    pub kind: AdtKind,
    /// The prelude definition, if the IR knows it.
    pub lang: Option<Lang>,
    /// The type is declared `linear`.
    pub linear: bool,
    /// The name of the `on abort` function.
    pub on_abort: Option<String>,
    /// The type has `on abort` (for an extern type: the runtime gives it).
    pub has_on_abort: bool,
    /// The type is declared `!Move`.
    pub immovable: bool,
    /// The type is declared `copy` (only an extern type).
    pub copy: bool,
    /// The type is declared `nonportable`.
    pub nonportable: bool,
    /// The property rows of the definition, in the order of [`TyProp::ALL`]:
    /// the least fixpoint over all definitions of the program.
    pub props: [PropRow; 8],
}

impl AdtDecl {
    /// Returns the row of property `p`.
    pub const fn row(&self, p: TyProp) -> &PropRow {
        &self.props[p.index()]
    }
}

/// An operation of an effect.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpDecl {
    /// The name.
    pub name: String,
    /// The parameter types.
    pub params: Vec<TyId>,
    /// The result type.
    pub ret: TyId,
    /// The operation is `multi`.
    pub multi: bool,
}

/// An effect.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EffectDecl {
    /// The name as the source writes it.
    pub name: String,
    /// The identity of the effect in the facts (`main.Log`; a standard effect
    /// keeps its name).
    pub identity: String,
    /// The operations, by `OpIdx`.
    pub ops: Vec<OpDecl>,
}

/// The final type table: the interned types and the declarations.
#[derive(Clone, Debug)]
pub struct TyTable {
    /// The types, by [`TyId`].
    tys: Vec<Ty>,
    /// The id of each type.
    ids: HashMap<Ty, TyId>,
    /// The type definitions, by [`AdtId`].
    adts: Vec<AdtDecl>,
    /// The effects, by [`EffectId`].
    effects: Vec<EffectDecl>,
}

impl Default for TyTable {
    fn default() -> Self {
        Self::new()
    }
}

/// The id of `()` in each table.
const UNIT: TyId = TyId(0);

impl TyTable {
    /// Makes a table that holds only `()`.
    pub fn new() -> Self {
        let mut t = Self {
            tys: Vec::new(),
            ids: HashMap::new(),
            adts: Vec::new(),
            effects: Vec::new(),
        };
        let unit = t.intern(Ty::Unit);
        debug_assert_eq!(unit, UNIT);
        t
    }

    /// Returns the id of type `t`. A type that is not in the table gets a new id.
    pub fn intern(&mut self, t: Ty) -> TyId {
        if let Some(&id) = self.ids.get(&t) {
            return id;
        }
        let id = TyId(u32::try_from(self.tys.len()).unwrap_or(u32::MAX));
        self.tys.push(t.clone());
        self.ids.insert(t, id);
        id
    }

    /// Returns the id of type `t` if it is in the table.
    pub fn find(&self, t: &Ty) -> Option<TyId> {
        self.ids.get(t).copied()
    }

    /// Returns the id of `()`.
    pub const fn unit(&self) -> TyId {
        UNIT
    }

    /// Returns type `id`.
    ///
    /// # Panics
    ///
    /// If `id` is not an id of this table.
    pub fn get(&self, id: TyId) -> &Ty {
        &self.tys[id.index()]
    }

    /// Returns type `id`, or `None` if `id` is not an id of this table.
    pub fn try_get(&self, id: TyId) -> Option<&Ty> {
        self.tys.get(id.index())
    }

    /// Returns the number of types.
    pub fn len(&self) -> usize {
        self.tys.len()
    }

    /// Returns true if the table has no types. A table always holds `()`.
    pub fn is_empty(&self) -> bool {
        self.tys.is_empty()
    }

    /// Returns the ids of all types, in order.
    pub fn ids(&self) -> impl Iterator<Item = TyId> {
        (0..u32::try_from(self.tys.len()).unwrap_or(u32::MAX)).map(TyId)
    }

    /// Adds a type definition and returns its id.
    pub fn push_adt(&mut self, d: AdtDecl) -> AdtId {
        let id = AdtId(u32::try_from(self.adts.len()).unwrap_or(u32::MAX));
        self.adts.push(d);
        id
    }

    /// Returns type definition `a`.
    ///
    /// # Panics
    ///
    /// If `a` is not a definition of this table.
    pub fn adt(&self, a: AdtId) -> &AdtDecl {
        &self.adts[a.index()]
    }

    /// Returns the type definitions, by [`AdtId`].
    pub fn adts(&self) -> &[AdtDecl] {
        &self.adts
    }

    /// Adds an effect and returns its id.
    pub fn push_effect(&mut self, e: EffectDecl) -> EffectId {
        let id = EffectId(u32::try_from(self.effects.len()).unwrap_or(u32::MAX));
        self.effects.push(e);
        id
    }

    /// Returns effect `e`.
    ///
    /// # Panics
    ///
    /// If `e` is not an effect of this table.
    pub fn effect(&self, e: EffectId) -> &EffectDecl {
        &self.effects[e.index()]
    }

    /// Returns the effects, by [`EffectId`].
    pub fn effects(&self) -> &[EffectDecl] {
        &self.effects
    }

    /// Returns the prelude definition of type `id` and its type arguments, if
    /// the type is an instance of one.
    pub fn lang(&self, id: TyId) -> Option<(Lang, &[TyId])> {
        match self.try_get(id)? {
            Ty::Adt(a, args) => Some((self.adts.get(a.index())?.lang?, args.as_slice())),
            _ => None,
        }
    }

    /// Returns true if type `id` names a type parameter.
    pub fn mentions_param(&self, id: TyId) -> bool {
        let Some(t) = self.try_get(id) else {
            return false;
        };
        let m = |x: &TyId| self.mentions_param(*x);
        match t {
            Ty::Param(_) => true,
            Ty::Tuple(ts) | Ty::Adt(_, ts) => ts.iter().any(m),
            Ty::Array(x, _) | Ty::Slice(x) | Ty::Ref(x) | Ty::Iter(x) => m(x),
            Ty::Cont(a, b) => m(a) || m(b),
            Ty::Fn(f) => f.params.iter().any(m) || m(&f.ret),
            Ty::Unit | Ty::Bool | Ty::Never | Ty::Int(_) | Ty::Scope | Ty::Cap(_) => false,
        }
    }

    /// Returns the text of type `id`, as diagnostics show a type.
    pub fn show(&self, id: TyId) -> String {
        let mut s = String::new();
        self.write(&mut s, id);
        s
    }

    fn write_list(&self, out: &mut String, ts: &[TyId]) {
        for (i, &t) in ts.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            self.write(out, t);
        }
    }

    fn effect_name(&self, e: EffectId) -> &str {
        self.effects
            .get(e.index())
            .map_or("?", |d| d.identity.as_str())
    }

    fn write(&self, out: &mut String, id: TyId) {
        let Some(t) = self.try_get(id) else {
            out.push('?');
            return;
        };
        match t {
            Ty::Unit => out.push_str("()"),
            Ty::Bool => out.push_str("bool"),
            Ty::Never => out.push('!'),
            Ty::Int(i) => out.push_str(i.name()),
            Ty::Tuple(ts) => {
                out.push('(');
                self.write_list(out, ts);
                out.push(')');
            }
            Ty::Array(x, n) => {
                out.push('[');
                self.write(out, *x);
                let _ = write!(out, "; {n}]");
            }
            Ty::Slice(x) => {
                out.push('[');
                self.write(out, *x);
                out.push(']');
            }
            Ty::Ref(x) => {
                out.push('&');
                self.write(out, *x);
            }
            Ty::Adt(a, args) => {
                let d = self.adts.get(a.index());
                if let (Some(Lang::Ptr), [x]) = (d.and_then(|d| d.lang), args.as_slice()) {
                    out.push('*');
                    self.write(out, *x);
                    return;
                }
                out.push_str(d.map_or("?", |d| d.name.as_str()));
                if !args.is_empty() {
                    out.push('<');
                    self.write_list(out, args);
                    out.push('>');
                }
            }
            Ty::Fn(f) => {
                out.push_str("fn(");
                self.write_list(out, &f.params);
                out.push_str(") -> ");
                self.write(out, f.ret);
                if let Some(row) = &f.row {
                    out.push_str(" / ");
                    if row.is_empty() {
                        out.push_str("()");
                    }
                    for (i, &e) in row.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        out.push_str(self.effect_name(e));
                    }
                }
            }
            Ty::Param(i) => {
                let _ = write!(out, "T{i}");
            }
            Ty::Scope => out.push_str("Scope"),
            Ty::Cap(e) => {
                let _ = write!(out, "Cap<{}>", self.effect_name(*e));
            }
            Ty::Cont(a, b) => {
                out.push_str("resume(");
                self.write(out, *a);
                out.push_str(") -> ");
                self.write(out, *b);
            }
            Ty::Iter(x) => {
                out.push_str("Iter<");
                self.write(out, *x);
                out.push('>');
            }
        }
    }
}

/// The properties of a type that the facts need (`docs/ir.md` 3.2). One
/// function computes them from the final type (`weft_sema::props::ir_props`).
/// The builder stores them in each local.
///
/// The modes of a declaration (`@ uniq`, `@ once`) and the closures that a
/// function value can be are not parts of the type. The builder and the
/// analysis add them.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
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
