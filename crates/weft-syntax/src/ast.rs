//! Abstract syntax tree for Weft source files.
//!
//! The parser makes these nodes. Semantic analysis and the interpreter read them.

use std::fmt;

/// A byte range in one source file.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default, PartialOrd, Ord)]
pub struct Span {
    /// The first byte.
    pub lo: u32,
    /// One past the last byte.
    pub hi: u32,
}

impl Span {
    /// Makes a span from byte offsets.
    pub const fn new(lo: u32, hi: u32) -> Self {
        Self { lo, hi }
    }

    /// Returns the smallest span that contains both spans.
    #[must_use]
    pub const fn to(self, other: Self) -> Self {
        let lo = if self.lo < other.lo {
            self.lo
        } else {
            other.lo
        };
        let hi = if self.hi > other.hi {
            self.hi
        } else {
            other.hi
        };
        Self { lo, hi }
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.lo, self.hi)
    }
}

/// A name with its location.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Ident {
    /// The text of the name.
    pub name: String,
    /// The location.
    pub span: Span,
}

/// The prefix of the hidden locals that hold the parts of a long chain of
/// binary operators. A `'` cannot start or continue a name in source, so no
/// program can name them.
pub const CHAIN_PART_PREFIX: &str = "chain'";

/// Returns true if `name` is a hidden local of a long chain.
pub fn is_chain_part(name: &str) -> bool {
    name.starts_with(CHAIN_PART_PREFIX)
}

impl Ident {
    /// Makes a name.
    pub fn new(name: impl Into<String>, span: Span) -> Self {
        Self {
            name: name.into(),
            span,
        }
    }
}

/// One parsed source file.
#[derive(Clone, Debug, PartialEq, Default)]
pub struct File {
    /// The top-level items, in source order.
    pub items: Vec<Item>,
}

/// A top-level or nested item.
#[derive(Clone, Debug, PartialEq)]
pub struct Item {
    /// The kind of item.
    pub kind: ItemKind,
    /// True if the item has `pub`.
    pub is_pub: bool,
    /// The location of the full item.
    pub span: Span,
}

/// The kinds of item.
#[derive(Clone, Debug, PartialEq)]
pub enum ItemKind {
    /// `fn`, `fip fn` or `extern fn`.
    Fn(FnDecl),
    /// `struct`, `linear struct`, `rc struct`.
    Struct(StructDecl),
    /// `enum`.
    Enum(EnumDecl),
    /// `effect Name { ... }`.
    Effect(EffectDecl),
    /// `impl Type { ... }`.
    Impl(ImplBlock),
    /// `mod name { ... }`.
    Mod(ModDecl),
    /// `test "name" { ... }`.
    Test(TestDecl),
    /// `extern type Name<T> { key: value, ... }`.
    ExternType(ExternTypeDecl),
}

/// A function declaration.
#[derive(Clone, Debug, PartialEq)]
pub struct FnDecl {
    /// The function name.
    pub name: Ident,
    /// Type parameters: `fn f<T, U>`.
    pub generics: Vec<Ident>,
    /// The parameters.
    pub params: Vec<Param>,
    /// The return type. `None` means unit.
    pub ret: Option<TypeExpr>,
    /// The effect row after `/`. `None` means "not stated".
    pub effects: Option<EffectRow>,
    /// The body. `None` for `extern fn`.
    pub body: Option<Block>,
    /// True for `extern fn`.
    pub is_extern: bool,
    /// True for `fip fn`.
    pub is_fip: bool,
}

/// A function or closure parameter.
#[derive(Clone, Debug, PartialEq)]
pub struct Param {
    /// The parameter name. `self` is a normal name here.
    pub name: Ident,
    /// The declared type. `None` for a bare `self`, closure and handler parameters.
    pub ty: Option<TypeExpr>,
    /// The location.
    pub span: Span,
}

/// A mode written after `@`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Mode {
    /// `uniq`: no other reference to the value exists.
    Uniq,
    /// `aliased`: other references can exist.
    Aliased,
    /// `portable`: the value can cross to another thread.
    Portable,
    /// `nonportable`: the value stays on its thread.
    Nonportable,
    /// `uncontended`: one thread uses the value.
    Uncontended,
    /// `shared`: every thread can only read the value.
    Shared,
    /// `once`: the value can be used at most once.
    Once,
    /// `many`: the value can be used more than once.
    Many,
}

impl Mode {
    /// Returns the mode keyword.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Uniq => "uniq",
            Self::Aliased => "aliased",
            Self::Portable => "portable",
            Self::Nonportable => "nonportable",
            Self::Uncontended => "uncontended",
            Self::Shared => "shared",
            Self::Once => "once",
            Self::Many => "many",
        }
    }

    /// Parses a mode keyword.
    pub fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            "uniq" => Self::Uniq,
            "aliased" => Self::Aliased,
            "portable" => Self::Portable,
            "nonportable" => Self::Nonportable,
            "uncontended" => Self::Uncontended,
            "shared" => Self::Shared,
            "once" => Self::Once,
            "many" => Self::Many,
            _ => return None,
        })
    }
}

/// A type expression with optional modes (`T @ uniq portable`).
#[derive(Clone, Debug, PartialEq)]
pub struct TypeExpr {
    /// The kind of type.
    pub kind: TypeExprKind,
    /// Modes after `@`.
    pub modes: Vec<Mode>,
    /// The location.
    pub span: Span,
}

/// The kinds of type expression.
#[derive(Clone, Debug, PartialEq)]
pub enum TypeExprKind {
    /// A named type with optional arguments: `Vec<Entity>`, `u32`, `T`.
    Path {
        /// The name segments: `["Vec"]` or `["http", "Request"]`.
        segments: Vec<Ident>,
        /// Type arguments in `<...>`.
        args: Vec<TypeExpr>,
    },
    /// `&T` or `&T in place`.
    Ref {
        /// The referent type.
        inner: Box<TypeExpr>,
        /// The place after `in`.
        place: Option<PlaceExpr>,
    },
    /// `*T`: a raw pointer for foreign functions. It is an opaque value.
    Ptr(Box<TypeExpr>),
    /// `(A, B)`. The empty tuple `()` is unit.
    Tuple(Vec<TypeExpr>),
    /// `[T; N]`.
    Array {
        /// The element type.
        elem: Box<TypeExpr>,
        /// The length.
        len: u64,
    },
    /// `[T]`, only behind a reference.
    Slice(Box<TypeExpr>),
    /// `fn(A, B) -> R / effects`.
    Fn {
        /// Parameter types.
        params: Vec<TypeExpr>,
        /// The return type. `None` means unit.
        ret: Option<Box<TypeExpr>>,
        /// The effect row. `None` means "pass through the caller's effects".
        effects: Option<EffectRow>,
    },
    /// `Self` inside an `impl`.
    SelfType,
}

/// A place written in a type or effect: `world.entities[]`, `opt.Some`, `world..`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlaceExpr {
    /// The root: a parameter, `self`, or an `rc` type name.
    pub root: Ident,
    /// The steps after the root.
    pub steps: Vec<PlaceStep>,
    /// The location.
    pub span: Span,
}

/// One step in a written place.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PlaceStep {
    /// `.name`: a field, a variant (capitalized) or a tuple index (`.0`).
    Field(Ident),
    /// `[]`: any element.
    Elem,
    /// `[..k]`: the low segment of a split at `k`.
    SegLo(Ident),
    /// `[k..]`: the high segment of a split at `k`.
    SegHi(Ident),
    /// `..`: anywhere inside. Only valid as the last step.
    Wildcard,
}

/// An effect row after `/`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EffectRow {
    /// The items, in source order.
    pub items: Vec<EffectItem>,
    /// The location.
    pub span: Span,
}

/// One item of an effect row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EffectItem {
    /// `mut(p, q, ...)`.
    Mut(Vec<PlaceExpr>),
    /// A named effect: `io`, `Log`, `net`, `par`, or a path such as `a.Note`.
    Named(EffectPath),
}

/// A written effect name: `Log`, or a path through modules such as `a.Note` or
/// `util.Note`. It resolves like a type path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EffectPath {
    /// The segments. The last one is the effect name. There is at least one.
    pub segments: Vec<Ident>,
    /// The location of the whole path.
    pub span: Span,
}

impl EffectPath {
    /// Makes a path of one name.
    pub fn single(id: Ident) -> Self {
        let span = id.span;
        Self {
            segments: vec![id],
            span,
        }
    }

    /// Returns the names of the segments.
    pub fn names(&self) -> Vec<&str> {
        self.segments.iter().map(|s| s.name.as_str()).collect()
    }

    /// Returns the path as the source writes it: `a.Note`.
    pub fn text(&self) -> String {
        self.names().join(".")
    }
}

/// A struct declaration.
#[derive(Clone, Debug, PartialEq)]
pub struct StructDecl {
    /// The struct name.
    pub name: Ident,
    /// Type parameters.
    pub generics: Vec<Ident>,
    /// The fields.
    pub fields: Vec<FieldDecl>,
    /// True for `linear struct`.
    pub is_linear: bool,
    /// True for `struct Name: !Move`.
    pub is_immovable: bool,
    /// The function after `on abort =`.
    pub on_abort: Option<Ident>,
}

/// A struct field.
#[derive(Clone, Debug, PartialEq)]
pub struct FieldDecl {
    /// The field name.
    pub name: Ident,
    /// The field type.
    pub ty: TypeExpr,
    /// The location.
    pub span: Span,
}

/// An enum declaration.
#[derive(Clone, Debug, PartialEq)]
pub struct EnumDecl {
    /// The enum name.
    pub name: Ident,
    /// Type parameters.
    pub generics: Vec<Ident>,
    /// The variants.
    pub variants: Vec<VariantDecl>,
}

/// One enum variant with a positional payload: `Died(u32)`, `None`.
#[derive(Clone, Debug, PartialEq)]
pub struct VariantDecl {
    /// The variant name.
    pub name: Ident,
    /// The payload types.
    pub fields: Vec<TypeExpr>,
    /// The location.
    pub span: Span,
}

/// An effect declaration.
#[derive(Clone, Debug, PartialEq)]
pub struct EffectDecl {
    /// The effect name.
    pub name: Ident,
    /// The operations.
    pub ops: Vec<OpDecl>,
}

/// An effect operation: `fn log(msg: String)` or `multi fn choose() -> bool`.
#[derive(Clone, Debug, PartialEq)]
pub struct OpDecl {
    /// The operation name.
    pub name: Ident,
    /// The parameters.
    pub params: Vec<Param>,
    /// The return type. `None` means unit.
    pub ret: Option<TypeExpr>,
    /// True for `multi fn`.
    pub is_multi: bool,
    /// The location.
    pub span: Span,
}

/// An `impl` block.
#[derive(Clone, Debug, PartialEq)]
pub struct ImplBlock {
    /// Type parameters: `impl<T> Vec<T>`.
    pub generics: Vec<Ident>,
    /// The type that gets the methods.
    pub self_ty: TypeExpr,
    /// The methods (function items).
    pub items: Vec<Item>,
}

/// A module: a namespace for items.
#[derive(Clone, Debug, PartialEq)]
pub struct ModDecl {
    /// The module name.
    pub name: Ident,
    /// The items.
    pub items: Vec<Item>,
}

/// A test block.
#[derive(Clone, Debug, PartialEq)]
pub struct TestDecl {
    /// The test name in quotes.
    pub name: String,
    /// The body.
    pub body: Block,
}

/// An extern type with declared properties: `extern type Vec<T> { elem: unstable }`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExternTypeDecl {
    /// The type name.
    pub name: Ident,
    /// Type parameters.
    pub generics: Vec<Ident>,
    /// The properties, such as `elem: unstable`, `deref: stable`, `nonportable`, `linear`.
    pub props: Vec<TypeProp>,
}

/// One extern type property: `key` or `key: value`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeProp {
    /// The key.
    pub key: Ident,
    /// The value, if any.
    pub value: Option<Ident>,
}

/// A block: `{ stmt* }`. The value is the last statement if it is an expression.
#[derive(Clone, Debug, PartialEq)]
pub struct Block {
    /// The statements.
    pub stmts: Vec<Stmt>,
    /// The location, braces included.
    pub span: Span,
}

/// A statement.
#[derive(Clone, Debug, PartialEq)]
pub struct Stmt {
    /// The kind of statement.
    pub kind: StmtKind,
    /// The location.
    pub span: Span,
}

/// Compound assignment operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AssignOp {
    /// `=`
    Assign,
    /// `+=`
    Add,
    /// `-=`
    Sub,
    /// `*=`
    Mul,
}

/// The kinds of statement.
#[derive(Clone, Debug, PartialEq)]
pub enum StmtKind {
    /// `let pat (: ty)? (= init)?`.
    Let {
        /// The pattern.
        pat: Pattern,
        /// The declared type.
        ty: Option<TypeExpr>,
        /// The initializer.
        init: Option<Expr>,
    },
    /// An expression statement.
    Expr(Expr),
    /// `target op value`.
    Assign {
        /// The place that gets the value.
        target: Expr,
        /// The operator.
        op: AssignOp,
        /// The value.
        value: Expr,
    },
    /// `return` or `return e`.
    Return(Option<Expr>),
    /// `break`.
    Break,
    /// `continue`.
    Continue,
    /// `while cond { body }`.
    While {
        /// The condition.
        cond: Expr,
        /// The body.
        body: Block,
    },
    /// `for pat in iter { body }`.
    For {
        /// The loop pattern.
        pat: Pattern,
        /// The iterated expression: `xs[]` or a range `a..b`.
        iter: Expr,
        /// The body.
        body: Block,
    },
    /// `loop { body }`.
    Loop(Block),
    /// `assert e`.
    Assert(Expr),
}

/// A pattern.
#[derive(Clone, Debug, PartialEq)]
pub enum Pattern {
    /// A binding: `x`.
    Bind(Ident),
    /// `_`.
    Wild(Span),
    /// `(a, b)`.
    Tuple(Vec<Self>, Span),
    /// `Some(x)`, `Died(id)`, `None`, `Event.Died(id)`.
    Variant {
        /// The variant path: one or two segments.
        path: Vec<Ident>,
        /// The payload patterns.
        fields: Vec<Self>,
        /// The location.
        span: Span,
    },
    /// A literal pattern.
    Lit(Lit, Span),
}

impl Pattern {
    /// Returns the location of the pattern.
    pub const fn span(&self) -> Span {
        match self {
            Self::Bind(id) => id.span,
            Self::Wild(s) | Self::Tuple(_, s) | Self::Lit(_, s) => *s,
            Self::Variant { span, .. } => *span,
        }
    }
}

/// A literal.
#[derive(Clone, Debug, PartialEq)]
pub enum Lit {
    /// An integer.
    Int(u64),
    /// `true` or `false`.
    Bool(bool),
    /// A string, with interpolated parts.
    Str(Vec<StrPart>),
    /// `()`.
    Unit,
}

/// A part of a string literal.
#[derive(Clone, Debug, PartialEq)]
pub enum StrPart {
    /// Plain text, escapes already decoded.
    Text(String),
    /// `{expr}`.
    Interp(Expr),
}

/// An expression.
#[derive(Clone, Debug, PartialEq)]
pub struct Expr {
    /// The kind of expression.
    pub kind: ExprKind,
    /// The location.
    pub span: Span,
}

/// Unary operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    /// `-e`
    Neg,
    /// `!e`
    Not,
    /// `&e`
    Ref,
}

/// Binary operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    /// `+`
    Add,
    /// `-`
    Sub,
    /// `*`
    Mul,
    /// `/`
    Div,
    /// `%`
    Rem,
    /// `==`
    Eq,
    /// `!=`
    Ne,
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `>`
    Gt,
    /// `>=`
    Ge,
    /// `&&`
    And,
    /// `||`
    Or,
}

/// A call argument, optionally named: `seed: 42`.
#[derive(Clone, Debug, PartialEq)]
pub struct Arg {
    /// The name before `:`.
    pub name: Option<Ident>,
    /// The value.
    pub value: Expr,
}

/// A `match` arm.
#[derive(Clone, Debug, PartialEq)]
pub struct Arm {
    /// The pattern.
    pub pat: Pattern,
    /// The body.
    pub body: Expr,
    /// The location.
    pub span: Span,
}

/// A handler clause: `fn op(params) { body }`.
#[derive(Clone, Debug, PartialEq)]
pub struct HandlerClause {
    /// The operation name.
    pub op: Ident,
    /// The parameters (types come from the effect declaration).
    pub params: Vec<Param>,
    /// The body. `resume` is in scope here.
    pub body: Block,
    /// The location.
    pub span: Span,
}

/// The kinds of expression.
#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    /// A literal.
    Lit(Lit),
    /// A name: a local, a function, a type, a module or an effect.
    Name(Ident),
    /// `base.name`. Also a tuple index (`t.0`) and `2.s`.
    Field {
        /// The base expression.
        base: Box<Expr>,
        /// The field name.
        name: Ident,
    },
    /// `base[index]`, or `base[]` when `index` is `None`.
    Index {
        /// The base expression.
        base: Box<Expr>,
        /// The index.
        index: Option<Box<Expr>>,
    },
    /// `callee(args) { trailing }`.
    Call {
        /// The callee.
        callee: Box<Expr>,
        /// The arguments.
        args: Vec<Arg>,
        /// A trailing block. The parser makes it a closure with no parameters.
        trailing: Option<Box<Expr>>,
    },
    /// `receiver.method(args) { trailing }`.
    MethodCall {
        /// The receiver: a value, a type, a module or an effect.
        receiver: Box<Expr>,
        /// The method name.
        method: Ident,
        /// The arguments.
        args: Vec<Arg>,
        /// A trailing block, as a closure with no parameters.
        trailing: Option<Box<Expr>>,
    },
    /// A unary operation.
    Unary {
        /// The operator.
        op: UnOp,
        /// The operand.
        expr: Box<Expr>,
    },
    /// A binary operation.
    Binary {
        /// The operator.
        op: BinOp,
        /// The left operand.
        lhs: Box<Expr>,
        /// The right operand.
        rhs: Box<Expr>,
    },
    /// `lo..hi`.
    Range {
        /// The start.
        lo: Box<Expr>,
        /// The end (excluded).
        hi: Box<Expr>,
    },
    /// `(a, b)`.
    Tuple(Vec<Expr>),
    /// `[a, b]`.
    Array(Vec<Expr>),
    /// `Name { field: value, ... }`.
    StructLit {
        /// The struct name segments.
        path: Vec<Ident>,
        /// The field values.
        fields: Vec<(Ident, Expr)>,
    },
    /// `|params| body`.
    Closure {
        /// The parameters.
        params: Vec<Param>,
        /// The body.
        body: Box<Expr>,
    },
    /// `{ stmts }`.
    Block(Block),
    /// `if cond { then } else { ... }`.
    If {
        /// The condition.
        cond: Box<Expr>,
        /// The then block.
        then: Block,
        /// The else branch: a block or another `if`.
        else_: Option<Box<Expr>>,
    },
    /// `match scrutinee { arms }`.
    Match {
        /// The value to match.
        scrutinee: Box<Expr>,
        /// The arms.
        arms: Vec<Arm>,
    },
    /// `handle Effect { clauses } in body`.
    Handle {
        /// The effect name or path.
        effect: EffectPath,
        /// The operation clauses.
        clauses: Vec<HandlerClause>,
        /// The handled computation.
        body: Box<Expr>,
    },
    /// `scope { s => body }`.
    Scope {
        /// The scope capability name.
        binder: Ident,
        /// The body.
        body: Block,
    },
}
