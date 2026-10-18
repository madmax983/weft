//! Recursive-descent parser. See `docs/grammar.md`.
//!
//! [`parse_file`] parses a full file and [`parse_expr`] parses one expression.
//! The parser stops at the first error. It does not panic on any input: a
//! nesting budget limits the recursion depth and the depth of the tree.
//!
//! The functions on the recursive path are small on purpose. Debug builds give
//! each local its own stack slot, so large functions use much stack per level.

use crate::ast::{
    Arg, Arm, AssignOp, BinOp, Block, EffectDecl, EffectItem, EffectRow, EnumDecl, Expr, ExprKind,
    ExternTypeDecl, FieldDecl, File, FnDecl, HandlerClause, Ident, ImplBlock, Item, ItemKind, Lit,
    ModDecl, Mode, OpDecl, Param, Pattern, PlaceExpr, PlaceStep, Span, Stmt, StmtKind, StrPart,
    StructDecl, TestDecl, TypeExpr, TypeExprKind, TypeProp, UnOp, VariantDecl,
};
use crate::lexer::{lex_at, StrPiece, Token, TokenKind as T};

/// A syntax error.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("{message}")]
pub struct ParseError {
    /// What is wrong.
    pub message: String,
    /// Where it is.
    pub span: Span,
}

impl ParseError {
    /// Makes an error.
    pub fn new(message: impl Into<String>, span: Span) -> Self {
        Self {
            message: message.into(),
            span,
        }
    }
}

/// The nesting budget. A nested construct costs [`NEST_COST`]. One step of an
/// operator chain costs [`CHAIN_COST`]. The budget limits the parser stack and
/// the depth of the tree, so that code that walks the tree has enough stack too.
const MAX_DEPTH: u32 = 768;

/// The budget cost of one nested expression, block, type, pattern or item.
const NEST_COST: u32 = 8;

/// The budget cost of one operator, postfix step or `else if` in a chain.
const CHAIN_COST: u32 = 2;

/// The text that lists the item keywords.
const ITEM_START: &str =
    "an item (`fn`, `struct`, `enum`, `effect`, `impl`, `mod`, `extern` or `test`)";

/// The mode words, for error messages.
const MODES: &str = "uniq, aliased, portable, nonportable, uncontended, shared, once, many";

/// The precedence of the comparison operators, which do not chain.
const CMP_PREC: u8 = 2;

/// The token that the parser sees after the end of the token list.
static EOF: Token = Token {
    kind: T::Eof,
    span: Span { lo: 0, hi: 0 },
    starts_line: false,
};

type PResult<T> = Result<T, ParseError>;

/// Parses one source file.
pub fn parse_file(src: &str) -> Result<File, ParseError> {
    Parser::new(lex_at(src, 0)?, 0).file()
}

/// Parses one expression. Statement ends before and after it are allowed.
pub fn parse_expr(src: &str) -> Result<Expr, ParseError> {
    let mut p = Parser::new(lex_at(src, 0)?, 0);
    p.skip_ends();
    let e = p.expr()?;
    p.skip_ends();
    if !p.at(&T::Eof) {
        return Err(p.expected("end of input after the expression"));
    }
    Ok(e)
}

struct Parser {
    toks: Vec<Token>,
    pos: usize,
    /// True in an `if`, `while`, `for` or `match` head: no struct literal and
    /// no trailing block at the top level.
    no_struct: bool,
    /// The used part of the nesting budget.
    depth: u32,
    /// The end of the last token that is not a `Newline`.
    last_hi: u32,
}

// ------------------------------------------------------------------ helpers

impl Parser {
    fn new(toks: Vec<Token>, depth: u32) -> Self {
        let last_hi = toks.first().map_or(0, |t| t.span.lo);
        Self {
            toks,
            pos: 0,
            no_struct: false,
            depth,
            last_hi,
        }
    }

    fn tok(&self, n: usize) -> &Token {
        self.toks
            .get(self.pos + n)
            .or_else(|| self.toks.last())
            .unwrap_or(&EOF)
    }

    fn peek(&self) -> &Token {
        self.tok(0)
    }

    fn kind(&self) -> &T {
        &self.tok(0).kind
    }

    fn kind_at(&self, n: usize) -> &T {
        &self.tok(n).kind
    }

    fn lo(&self) -> u32 {
        self.peek().span.lo
    }

    fn at(&self, k: &T) -> bool {
        self.kind() == k
    }

    fn at_name(&self, s: &str) -> bool {
        matches!(self.kind(), T::Name(n) if n == s)
    }

    fn at_any_name(&self) -> bool {
        matches!(self.kind(), T::Name(_))
    }

    /// Consumes the current token and returns its span.
    fn bump(&mut self) -> Span {
        let t = self.peek();
        let span = t.span;
        if t.kind != T::Newline {
            self.last_hi = span.hi;
        }
        if self.pos < self.toks.len() {
            self.pos += 1;
        }
        span
    }

    fn eat(&mut self, k: &T) -> bool {
        let found = self.at(k);
        if found {
            self.bump();
        }
        found
    }

    fn expect(&mut self, k: &T, what: &str) -> PResult<Span> {
        if self.at(k) {
            Ok(self.bump())
        } else {
            Err(self.expected(what))
        }
    }

    /// Makes the error "expected {what}, found {current token}".
    fn expected(&self, what: &str) -> ParseError {
        let t = self.peek();
        ParseError::new(
            format!("expected {what}, found {}", t.kind.describe()),
            t.span,
        )
    }

    /// Consumes a name, or fails with "expected {what}".
    fn name(&mut self, what: &str) -> PResult<Ident> {
        if self.at_any_name() {
            Ok(self.ident())
        } else {
            Err(self.expected(what))
        }
    }

    /// Consumes the current token as a name. The caller checks the kind.
    fn ident(&mut self) -> Ident {
        let text = match self.kind() {
            T::Name(n) => n.clone(),
            other => other.to_string(),
        };
        Ident::new(text, self.bump())
    }

    fn skip_newlines(&mut self) {
        while self.at(&T::Newline) {
            self.bump();
        }
    }

    fn skip_ends(&mut self) {
        while matches!(self.kind(), T::Newline | T::Semi) {
            self.bump();
        }
    }

    /// Skips statement ends if the next other token matches `pred`.
    fn skip_ends_before(&mut self, pred: impl Fn(&T) -> bool) -> bool {
        let mut n = 0;
        while matches!(self.kind_at(n), T::Newline | T::Semi) {
            n += 1;
        }
        let found = pred(self.kind_at(n));
        if found {
            for _ in 0..n {
                self.bump();
            }
        }
        found
    }

    /// True at a line break after a `>` or `..` that ends a type or a place.
    /// The lexer inserts no `Newline` there, because both are also operators.
    fn soft_break(&self) -> bool {
        self.peek().starts_line
            && self
                .pos
                .checked_sub(1)
                .and_then(|i| self.toks.get(i))
                .is_some_and(|t| matches!(t.kind, T::Gt | T::DotDot))
    }

    fn at_line_break(&self) -> bool {
        self.at(&T::Newline) || self.soft_break()
    }

    fn at_stmt_end(&self) -> bool {
        matches!(self.kind(), T::Newline | T::Semi | T::RBrace | T::Eof) || self.soft_break()
    }

    fn too_deep(&self) -> ParseError {
        ParseError::new("the code is nested too deeply", self.peek().span)
    }

    fn too_long(&self) -> ParseError {
        ParseError::new(
            "the expression is too long or nested too deeply; split it",
            self.peek().span,
        )
    }

    /// Goes one nesting level deeper. The caller calls [`Self::leave`] after.
    fn enter(&mut self) -> PResult<()> {
        self.depth += NEST_COST;
        if self.depth > MAX_DEPTH {
            return Err(self.too_deep());
        }
        Ok(())
    }

    const fn leave(&mut self) {
        self.depth -= NEST_COST;
    }

    /// Uses one unit of the budget for one step of an operator chain.
    /// The caller restores `depth` at the end of the chain.
    fn chain_step(&mut self) -> PResult<()> {
        self.depth += CHAIN_COST;
        if self.depth > MAX_DEPTH {
            return Err(self.too_long());
        }
        Ok(())
    }

    /// Sets the `no_struct` flag and returns the old value.
    const fn set_ns(&mut self, ns: bool) -> bool {
        std::mem::replace(&mut self.no_struct, ns)
    }

    /// Parses `item ( "," item )* ","? close`. The open token is consumed.
    /// Returns the items and true if a trailing comma is present.
    fn comma_list<R>(
        &mut self,
        close: &T,
        what: &str,
        mut f: impl FnMut(&mut Self) -> PResult<R>,
    ) -> PResult<(Vec<R>, bool)> {
        let mut items = Vec::new();
        let mut trailing = false;
        while !self.eat(close) {
            items.push(f(self)?);
            trailing = self.eat(&T::Comma);
            if !trailing && !self.at(close) {
                return Err(self.expected(what));
            }
        }
        Ok((items, trailing))
    }

    /// Parses `( item sep )* "}"` where `sep` is `,` or a line break.
    /// The `{` is consumed.
    fn brace_list<R>(
        &mut self,
        what: &str,
        mut f: impl FnMut(&mut Self) -> PResult<R>,
    ) -> PResult<Vec<R>> {
        let mut items = Vec::new();
        loop {
            self.skip_newlines();
            if self.eat(&T::RBrace) {
                return Ok(items);
            }
            if self.at(&T::Eof) {
                return Err(self.expected("`}`"));
            }
            items.push(f(self)?);
            if self.eat(&T::Comma) || self.at_line_break() || self.at(&T::RBrace) {
                continue;
            }
            if self.at(&T::Eof) {
                return Err(self.expected("`}`"));
            }
            return Err(self.expected(what));
        }
    }

    /// Consumes a `>`. A `>=` becomes `=` after it, as in `Vec<T>= x`.
    fn eat_gt(&mut self) -> bool {
        match self.kind() {
            T::Gt => {
                self.bump();
                true
            }
            T::Ge => {
                let span = self.peek().span;
                let mid = span.lo.saturating_add(1);
                if let Some(t) = self.toks.get_mut(self.pos) {
                    t.kind = T::Eq;
                    t.span = Span::new(mid, span.hi);
                    t.starts_line = false;
                }
                self.last_hi = mid;
                true
            }
            _ => false,
        }
    }

    fn at_gt(&self) -> bool {
        matches!(self.kind(), T::Gt | T::Ge)
    }
}

// ------------------------------------------------------------------ items

impl Parser {
    fn file(&mut self) -> PResult<File> {
        let mut items = Vec::new();
        loop {
            self.skip_ends();
            if self.at(&T::Eof) {
                return Ok(File { items });
            }
            items.push(self.item()?);
        }
    }

    fn item(&mut self) -> PResult<Item> {
        let lo = self.lo();
        let is_pub = self.eat(&T::Pub);
        let kind = self.item_kind()?;
        Ok(Item {
            kind,
            is_pub,
            span: Span::new(lo, self.last_hi),
        })
    }

    fn item_kind(&mut self) -> PResult<ItemKind> {
        match self.kind() {
            T::Fn => self.fn_decl(false, false).map(ItemKind::Fn),
            T::Extern => self.extern_item(),
            T::Struct => self.struct_decl(false).map(ItemKind::Struct),
            T::Enum => self.enum_decl().map(ItemKind::Enum),
            T::Effect => self.effect_decl().map(ItemKind::Effect),
            T::Impl => self.impl_block().map(ItemKind::Impl),
            T::Mod => self.mod_decl().map(ItemKind::Mod),
            T::Name(n) if n == "fip" && self.kind_at(1) == &T::Fn => {
                self.bump();
                self.fn_decl(true, false).map(ItemKind::Fn)
            }
            T::Name(n) if n == "linear" && self.kind_at(1) == &T::Struct => {
                self.bump();
                self.struct_decl(true).map(ItemKind::Struct)
            }
            T::Name(n) if n == "test" && matches!(self.kind_at(1), T::Str(_)) => {
                self.test_decl().map(ItemKind::Test)
            }
            _ => Err(self.expected(ITEM_START)),
        }
    }

    /// Parses `extern fn` or `extern type`. The current token is `extern`.
    fn extern_item(&mut self) -> PResult<ItemKind> {
        self.bump();
        if self.at(&T::Fn) {
            return self.fn_decl(false, true).map(ItemKind::Fn);
        }
        if self.at_name("type") {
            self.bump();
            return self.extern_type().map(ItemKind::ExternType);
        }
        Err(self.expected("`fn` or `type` after `extern`"))
    }

    /// Parses `"{" item* "}"` for `impl` and `mod`.
    fn items_in_braces(&mut self, what: &str) -> PResult<Vec<Item>> {
        self.expect(&T::LBrace, what)?;
        self.enter()?;
        let mut items = Vec::new();
        loop {
            self.skip_ends();
            if self.eat(&T::RBrace) {
                break;
            }
            if self.at(&T::Eof) {
                return Err(self.expected("`}` at the end of the item list"));
            }
            items.push(self.item()?);
        }
        self.leave();
        Ok(items)
    }

    /// Parses a function. The current token is `fn`.
    fn fn_decl(&mut self, is_fip: bool, is_extern: bool) -> PResult<FnDecl> {
        self.bump();
        let name = self.name("the function name")?;
        let generics = self.generics()?;
        self.expect(&T::LParen, "`(` after the function name")?;
        let params = self.params(&T::RParen, "`,` or `)` after a parameter")?;
        let ret = if self.eat(&T::Arrow) {
            Some(self.ty()?)
        } else {
            None
        };
        let effects = if self.eat(&T::Slash) {
            Some(self.row()?)
        } else {
            None
        };
        let body = if is_extern {
            if self.at(&T::LBrace) {
                return Err(ParseError::new(
                    "an `extern fn` cannot have a body",
                    self.peek().span,
                ));
            }
            None
        } else {
            Some(self.block("`{` to start the function body")?)
        };
        Ok(FnDecl {
            name,
            generics,
            params,
            ret,
            effects,
            body,
            is_extern,
            is_fip,
        })
    }

    fn generics(&mut self) -> PResult<Vec<Ident>> {
        let mut names = Vec::new();
        if !self.eat(&T::Lt) {
            return Ok(names);
        }
        while !self.eat_gt() {
            names.push(self.name("a type parameter name")?);
            if !self.eat(&T::Comma) && !self.at_gt() {
                return Err(self.expected("`,` or `>` after a type parameter"));
            }
        }
        Ok(names)
    }

    fn params(&mut self, close: &T, what: &str) -> PResult<Vec<Param>> {
        Ok(self.comma_list(close, what, Self::param)?.0)
    }

    fn param(&mut self) -> PResult<Param> {
        let name = if self.at(&T::SelfValue) {
            Ident::new("self", self.bump())
        } else {
            self.name("a parameter name")?
        };
        let ty = if self.eat(&T::Colon) {
            Some(self.ty()?)
        } else {
            None
        };
        Ok(Param {
            span: Span::new(name.span.lo, self.last_hi),
            name,
            ty,
        })
    }

    /// Parses a struct. The current token is `struct`.
    fn struct_decl(&mut self, is_linear: bool) -> PResult<StructDecl> {
        self.bump();
        let name = self.name("the struct name")?;
        let generics = self.generics()?;
        let is_immovable = self.eat(&T::Colon);
        if is_immovable {
            self.expect(&T::Bang, "`!` after `:` in a struct header")?;
            if !self.at_name("Move") {
                return Err(self.expected("`Move` after `!`"));
            }
            self.bump();
        }
        self.expect(&T::LBrace, "`{` to start the struct fields")?;
        let fields = self.brace_list("`,`, a line break or `}` after the field", Self::field)?;
        let on_abort = self.on_abort()?;
        Ok(StructDecl {
            name,
            generics,
            fields,
            is_linear,
            is_immovable,
            on_abort,
        })
    }

    /// Parses an optional `on abort = f`, maybe on the next line.
    fn on_abort(&mut self) -> PResult<Option<Ident>> {
        if !self.skip_ends_before(|k| matches!(k, T::Name(n) if n == "on")) {
            return Ok(None);
        }
        self.bump();
        if !self.at_name("abort") {
            return Err(self.expected("`abort` after `on`"));
        }
        self.bump();
        self.expect(&T::Eq, "`=` after `on abort`")?;
        Ok(Some(self.name("the abort function name")?))
    }

    fn field(&mut self) -> PResult<FieldDecl> {
        let name = self.name("the field name")?;
        self.expect(&T::Colon, "`:` after the field name")?;
        let ty = self.ty()?;
        Ok(FieldDecl {
            span: Span::new(name.span.lo, self.last_hi),
            name,
            ty,
        })
    }

    /// Parses an enum. The current token is `enum`.
    fn enum_decl(&mut self) -> PResult<EnumDecl> {
        self.bump();
        let name = self.name("the enum name")?;
        let generics = self.generics()?;
        self.expect(&T::LBrace, "`{` to start the variants")?;
        let variants = self.brace_list("`,`, a line break or `}` after the variant", |p| {
            let name = p.name("the variant name")?;
            let fields = if p.eat(&T::LParen) {
                p.comma_list(&T::RParen, "`,` or `)` after a type", Self::ty)?
                    .0
            } else {
                Vec::new()
            };
            Ok(VariantDecl {
                span: Span::new(name.span.lo, p.last_hi),
                name,
                fields,
            })
        })?;
        Ok(EnumDecl {
            name,
            generics,
            variants,
        })
    }

    /// Parses an effect. The current token is `effect`.
    fn effect_decl(&mut self) -> PResult<EffectDecl> {
        self.bump();
        let name = self.name("the effect name")?;
        self.expect(&T::LBrace, "`{` to start the effect operations")?;
        let ops = self.brace_list(
            "`,`, a line break or `}` after the operation",
            Self::op_decl,
        )?;
        Ok(EffectDecl { name, ops })
    }

    fn op_decl(&mut self) -> PResult<OpDecl> {
        let lo = self.lo();
        let is_multi = self.at_name("multi") && self.kind_at(1) == &T::Fn;
        if is_multi {
            self.bump();
        }
        self.expect(&T::Fn, "`fn` to start an effect operation")?;
        let name = self.name("the operation name")?;
        self.expect(&T::LParen, "`(` after the operation name")?;
        let params = self.params(&T::RParen, "`,` or `)` after a parameter")?;
        let ret = if self.eat(&T::Arrow) {
            Some(self.ty()?)
        } else {
            None
        };
        Ok(OpDecl {
            name,
            params,
            ret,
            is_multi,
            span: Span::new(lo, self.last_hi),
        })
    }

    /// Parses an impl block. The current token is `impl`.
    fn impl_block(&mut self) -> PResult<ImplBlock> {
        self.bump();
        let generics = self.generics()?;
        let self_ty = self.ty()?;
        let items = self.items_in_braces("`{` to start the impl body")?;
        Ok(ImplBlock {
            generics,
            self_ty,
            items,
        })
    }

    /// Parses a module. The current token is `mod`.
    fn mod_decl(&mut self) -> PResult<ModDecl> {
        self.bump();
        let name = self.name("the module name")?;
        let items = self.items_in_braces("`{` to start the module body")?;
        Ok(ModDecl { name, items })
    }

    /// Parses a test. The current token is `test` and a string follows.
    fn test_decl(&mut self) -> PResult<TestDecl> {
        self.bump();
        let span = self.peek().span;
        let pieces = match self.kind() {
            T::Str(p) => p.clone(),
            _ => Vec::new(),
        };
        self.bump();
        let mut name = String::new();
        for piece in pieces {
            match piece {
                StrPiece::Text(t) => name.push_str(&t),
                StrPiece::Interp { .. } => {
                    return Err(ParseError::new(
                        "a test name cannot contain interpolation",
                        span,
                    ));
                }
            }
        }
        let body = self.block("`{` to start the test body")?;
        Ok(TestDecl { name, body })
    }

    /// Parses an extern type after `extern type`.
    fn extern_type(&mut self) -> PResult<ExternTypeDecl> {
        let name = self.name("the type name")?;
        let generics = self.generics()?;
        let props = if self.eat(&T::LBrace) {
            self.brace_list("`,`, a line break or `}` after the property", |p| {
                let key = p.name("a property name")?;
                let value = if p.eat(&T::Colon) {
                    Some(p.name("a property value")?)
                } else {
                    None
                };
                Ok(TypeProp { key, value })
            })?
        } else {
            Vec::new()
        };
        Ok(ExternTypeDecl {
            name,
            generics,
            props,
        })
    }
}

// ------------------------------------------------------------------ types, places, rows

impl Parser {
    fn ty(&mut self) -> PResult<TypeExpr> {
        self.enter()?;
        let r = self.ty_inner();
        self.leave();
        r
    }

    fn ty_inner(&mut self) -> PResult<TypeExpr> {
        let mut ty = self.ty_atom()?;
        if self.eat(&T::At) {
            self.modes(&mut ty)?;
        }
        Ok(ty)
    }

    /// Parses `MODE+` after `@` into `ty`.
    fn modes(&mut self, ty: &mut TypeExpr) -> PResult<()> {
        let before = ty.modes.len();
        while let T::Name(n) = self.kind() {
            let Some(mode) = Mode::from_name(n) else {
                break;
            };
            self.bump();
            ty.modes.push(mode);
        }
        if ty.modes.len() == before {
            return Err(match self.kind() {
                T::Name(n) => ParseError::new(
                    format!("unknown mode `{n}`; expected one of {MODES}"),
                    self.peek().span,
                ),
                _ => self.expected("a mode after `@`"),
            });
        }
        ty.span = Span::new(ty.span.lo, self.last_hi);
        Ok(())
    }

    fn ty_atom(&mut self) -> PResult<TypeExpr> {
        let lo = self.lo();
        let kind = match self.kind() {
            T::Amp => {
                self.bump();
                self.ref_ty()?
            }
            T::AndAnd => {
                self.bump();
                self.double_ref_ty(lo)?
            }
            T::LParen => return self.paren_ty(),
            T::LBracket => {
                self.bump();
                self.array_ty()?
            }
            T::Fn => self.fn_ty()?,
            T::SelfType => {
                self.bump();
                TypeExprKind::SelfType
            }
            T::Name(_) => self.path_ty()?,
            _ => return Err(self.expected("a type")),
        };
        Ok(TypeExpr {
            kind,
            modes: Vec::new(),
            span: Span::new(lo, self.last_hi),
        })
    }

    /// Parses the rest of `&T` or `&T in place` after the `&`.
    fn ref_ty(&mut self) -> PResult<TypeExprKind> {
        self.enter()?;
        let inner = self.ty_atom();
        self.leave();
        let inner = Box::new(inner?);
        let place = if self.eat(&T::In) {
            Some(self.place()?)
        } else {
            None
        };
        Ok(TypeExprKind::Ref { inner, place })
    }

    /// Parses the rest of `&&T` after the `&&`. The inner `&T` takes the first `in`.
    fn double_ref_ty(&mut self, lo: u32) -> PResult<TypeExprKind> {
        let kind = self.ref_ty()?;
        let span = Span::new(lo.saturating_add(1), self.last_hi);
        let inner = Box::new(TypeExpr {
            kind,
            modes: Vec::new(),
            span,
        });
        let place = if self.eat(&T::In) {
            Some(self.place()?)
        } else {
            None
        };
        Ok(TypeExprKind::Ref { inner, place })
    }

    /// Parses `()`, `(T)` or a tuple type. The current token is `(`.
    fn paren_ty(&mut self) -> PResult<TypeExpr> {
        let lo = self.bump().lo;
        let (mut items, trailing) =
            self.comma_list(&T::RParen, "`,` or `)` after a type", Self::ty)?;
        let span = Span::new(lo, self.last_hi);
        if items.len() == 1 && !trailing {
            if let Some(mut t) = items.pop() {
                t.span = span;
                return Ok(t);
            }
        }
        Ok(TypeExpr {
            kind: TypeExprKind::Tuple(items),
            modes: Vec::new(),
            span,
        })
    }

    /// Parses the rest of `[T]` or `[T; N]` after the `[`.
    fn array_ty(&mut self) -> PResult<TypeExprKind> {
        let elem = Box::new(self.ty()?);
        if !self.eat(&T::Semi) {
            self.expect(&T::RBracket, "`]` after the element type")?;
            return Ok(TypeExprKind::Slice(elem));
        }
        let &T::Int(len) = self.kind() else {
            return Err(self.expected("an integer array length after `;`"));
        };
        self.bump();
        self.expect(&T::RBracket, "`]` after the array length")?;
        Ok(TypeExprKind::Array { elem, len })
    }

    /// Parses `fn(A, B) -> R / row`. The current token is `fn`.
    fn fn_ty(&mut self) -> PResult<TypeExprKind> {
        self.bump();
        self.expect(&T::LParen, "`(` after `fn` in a function type")?;
        let params = self
            .comma_list(&T::RParen, "`,` or `)` after a type", Self::ty)?
            .0;
        let ret = if self.eat(&T::Arrow) {
            Some(Box::new(self.ty()?))
        } else {
            None
        };
        let effects = if self.eat(&T::Slash) {
            Some(self.fn_row()?)
        } else {
            None
        };
        Ok(TypeExprKind::Fn {
            params,
            ret,
            effects,
        })
    }

    fn path_ty(&mut self) -> PResult<TypeExprKind> {
        let mut segments = vec![self.ident()];
        while self.at(&T::Dot) && matches!(self.kind_at(1), T::Name(_)) {
            self.bump();
            segments.push(self.ident());
        }
        let mut args = Vec::new();
        if self.eat(&T::Lt) {
            while !self.eat_gt() {
                args.push(self.ty()?);
                if !self.eat(&T::Comma) && !self.at_gt() {
                    return Err(self.expected("`,` or `>` after a type argument"));
                }
            }
        }
        Ok(TypeExprKind::Path { segments, args })
    }

    fn place(&mut self) -> PResult<PlaceExpr> {
        let lo = self.lo();
        let root = match self.kind() {
            T::Name(_) => self.ident(),
            T::SelfValue => Ident::new("self", self.bump()),
            _ => return Err(self.expected("a place")),
        };
        let mut steps = Vec::new();
        loop {
            match self.kind() {
                T::Dot => {
                    self.bump();
                    steps.push(PlaceStep::Field(self.place_field()?));
                }
                T::LBracket => {
                    self.bump();
                    steps.push(self.bracket_step()?);
                }
                T::DotDot => {
                    self.bump();
                    steps.push(PlaceStep::Wildcard);
                    if matches!(self.kind(), T::Dot | T::LBracket | T::DotDot) {
                        return Err(ParseError::new(
                            "the wildcard step `..` must be the last step",
                            self.peek().span,
                        ));
                    }
                    break;
                }
                _ => break,
            }
        }
        Ok(PlaceExpr {
            root,
            steps,
            span: Span::new(lo, self.last_hi),
        })
    }

    /// Parses the name or index after a `.` in a place.
    fn place_field(&mut self) -> PResult<Ident> {
        match self.kind() {
            T::Name(_) => Ok(self.ident()),
            T::Int(v) => {
                let text = v.to_string();
                Ok(Ident::new(text, self.bump()))
            }
            _ => Err(self.expected("a field name after `.` in a place")),
        }
    }

    /// Parses `]`, `..k]` or `k..]` after a `[` in a place.
    fn bracket_step(&mut self) -> PResult<PlaceStep> {
        if self.eat(&T::RBracket) {
            return Ok(PlaceStep::Elem);
        }
        if self.eat(&T::DotDot) {
            let k = self.name("a split index name after `[..`")?;
            self.expect(&T::RBracket, "`]` after the segment")?;
            return Ok(PlaceStep::SegLo(k));
        }
        if self.at_any_name() && self.kind_at(1) == &T::DotDot {
            let k = self.ident();
            self.bump();
            self.expect(&T::RBracket, "`]` after the segment")?;
            return Ok(PlaceStep::SegHi(k));
        }
        Err(self.expected("`]`, `..name]` or `name..]` in a place"))
    }

    /// Parses a function row: `row_item ( "," row_item )*`.
    fn row(&mut self) -> PResult<EffectRow> {
        let lo = self.lo();
        let mut items = vec![self.row_item()?];
        while self.eat(&T::Comma) {
            items.push(self.row_item()?);
        }
        Ok(EffectRow {
            items,
            span: Span::new(lo, self.last_hi),
        })
    }

    /// Parses a function type row: `row_item` or `"(" row ")"`.
    fn fn_row(&mut self) -> PResult<EffectRow> {
        let lo = self.lo();
        if !self.eat(&T::LParen) {
            let item = self.row_item()?;
            return Ok(EffectRow {
                items: vec![item],
                span: Span::new(lo, self.last_hi),
            });
        }
        let (items, _) =
            self.comma_list(&T::RParen, "`,` or `)` after an effect", Self::row_item)?;
        let span = Span::new(lo, self.last_hi);
        if items.is_empty() {
            return Err(ParseError::new(
                "an effect row needs at least one effect",
                span,
            ));
        }
        Ok(EffectRow { items, span })
    }

    fn row_item(&mut self) -> PResult<EffectItem> {
        if self.at_name("mut") && self.kind_at(1) == &T::LParen {
            let lo = self.lo();
            self.bump();
            self.bump();
            let (places, _) =
                self.comma_list(&T::RParen, "`,` or `)` after a place", Self::place)?;
            if places.is_empty() {
                return Err(ParseError::new(
                    "`mut(...)` needs at least one place",
                    Span::new(lo, self.last_hi),
                ));
            }
            return Ok(EffectItem::Mut(places));
        }
        if self.at_any_name() {
            return Ok(EffectItem::Named(self.ident()));
        }
        Err(self.expected("an effect name or `mut(...)`"))
    }
}

// ------------------------------------------------------------------ statements and patterns

impl Parser {
    fn block(&mut self, what: &str) -> PResult<Block> {
        let lo = self.lo();
        self.expect(&T::LBrace, what)?;
        self.block_rest(lo)
    }

    /// Parses the statements of a block after its `{`, up to and with the `}`.
    fn block_rest(&mut self, lo: u32) -> PResult<Block> {
        self.enter()?;
        let old = self.set_ns(false);
        let r = self.stmts(lo);
        self.no_struct = old;
        self.leave();
        r
    }

    fn stmts(&mut self, lo: u32) -> PResult<Block> {
        let mut stmts = Vec::new();
        loop {
            self.skip_ends();
            if self.eat(&T::RBrace) {
                return Ok(Block {
                    stmts,
                    span: Span::new(lo, self.last_hi),
                });
            }
            if self.at(&T::Eof) {
                return Err(self.expected("`}` at the end of the block"));
            }
            stmts.push(self.stmt()?);
            if !self.at_stmt_end() {
                return Err(self.expected("a line break or `;` after the statement"));
            }
        }
    }

    fn stmt(&mut self) -> PResult<Stmt> {
        let lo = self.lo();
        let kind = self.stmt_kind()?;
        Ok(Stmt {
            kind,
            span: Span::new(lo, self.last_hi),
        })
    }

    fn stmt_kind(&mut self) -> PResult<StmtKind> {
        match self.kind() {
            T::Let => self.let_stmt(),
            T::Return => self.return_stmt(),
            T::Break => {
                self.bump();
                Ok(StmtKind::Break)
            }
            T::Continue => {
                self.bump();
                Ok(StmtKind::Continue)
            }
            T::While => self.while_stmt(),
            T::For => self.for_stmt(),
            T::Loop => {
                self.bump();
                self.block("`{` after `loop`").map(StmtKind::Loop)
            }
            T::Name(n) if n == "assert" && can_start_expr(self.kind_at(1)) => {
                self.bump();
                self.expr().map(StmtKind::Assert)
            }
            _ => self.expr_stmt(),
        }
    }

    fn let_stmt(&mut self) -> PResult<StmtKind> {
        self.bump();
        let pat = self.pattern()?;
        let ty = if self.eat(&T::Colon) {
            Some(self.ty()?)
        } else {
            None
        };
        let init = if self.eat(&T::Eq) {
            Some(self.expr()?)
        } else {
            None
        };
        Ok(StmtKind::Let { pat, ty, init })
    }

    fn return_stmt(&mut self) -> PResult<StmtKind> {
        self.bump();
        if self.at_stmt_end() {
            return Ok(StmtKind::Return(None));
        }
        self.expr().map(|e| StmtKind::Return(Some(e)))
    }

    fn while_stmt(&mut self) -> PResult<StmtKind> {
        self.bump();
        let cond = self.head_expr()?;
        let body = self.block("`{` after the `while` condition")?;
        Ok(StmtKind::While { cond, body })
    }

    fn for_stmt(&mut self) -> PResult<StmtKind> {
        self.bump();
        let pat = self.pattern()?;
        self.expect(&T::In, "`in` after the `for` pattern")?;
        let iter = self.head_expr()?;
        let body = self.block("`{` after the `for` value")?;
        Ok(StmtKind::For { pat, iter, body })
    }

    fn expr_stmt(&mut self) -> PResult<StmtKind> {
        let target = self.expr()?;
        let Some(op) = assign_op(self.kind()) else {
            return Ok(StmtKind::Expr(target));
        };
        self.bump();
        let value = self.expr()?;
        Ok(StmtKind::Assign { target, op, value })
    }

    fn pattern(&mut self) -> PResult<Pattern> {
        self.enter()?;
        let r = self.pattern_inner();
        self.leave();
        r
    }

    fn pattern_inner(&mut self) -> PResult<Pattern> {
        let lo = self.lo();
        match self.kind() {
            T::Name(n) if n == "_" => Ok(Pattern::Wild(self.bump())),
            T::Name(n) if is_upper(n) => self.variant_pattern(),
            T::Name(_) => Ok(Pattern::Bind(self.ident())),
            T::Int(v) => {
                let lit = Lit::Int(*v);
                Ok(Pattern::Lit(lit, self.bump()))
            }
            T::True => Ok(Pattern::Lit(Lit::Bool(true), self.bump())),
            T::False => Ok(Pattern::Lit(Lit::Bool(false), self.bump())),
            T::Str(_) => {
                let lit = self.str_lit()?;
                Ok(Pattern::Lit(lit, Span::new(lo, self.last_hi)))
            }
            T::LParen => self.paren_pattern(),
            _ => Err(self.expected("a pattern")),
        }
    }

    fn variant_pattern(&mut self) -> PResult<Pattern> {
        let lo = self.lo();
        let mut path = vec![self.ident()];
        if self.at(&T::Dot) && matches!(self.kind_at(1), T::Name(m) if is_upper(m)) {
            self.bump();
            path.push(self.ident());
        }
        let fields = if self.eat(&T::LParen) {
            self.comma_list(&T::RParen, "`,` or `)` after a pattern", Self::pattern)?
                .0
        } else {
            Vec::new()
        };
        Ok(Pattern::Variant {
            path,
            fields,
            span: Span::new(lo, self.last_hi),
        })
    }

    /// Parses `()`, `(p)` or a tuple pattern. The current token is `(`.
    fn paren_pattern(&mut self) -> PResult<Pattern> {
        let lo = self.bump().lo;
        let (mut items, trailing) =
            self.comma_list(&T::RParen, "`,` or `)` after a pattern", Self::pattern)?;
        let span = Span::new(lo, self.last_hi);
        if items.is_empty() {
            return Ok(Pattern::Lit(Lit::Unit, span));
        }
        if items.len() == 1 && !trailing {
            if let Some(only) = items.pop() {
                return Ok(only);
            }
        }
        Ok(Pattern::Tuple(items, span))
    }
}

// ------------------------------------------------------------------ expressions

impl Parser {
    fn expr(&mut self) -> PResult<Expr> {
        self.enter()?;
        let r = self.range();
        self.leave();
        r
    }

    /// Parses an expression with no struct literal and no trailing block at its
    /// top level: the head of `if`, `while`, `for` and `match`.
    fn head_expr(&mut self) -> PResult<Expr> {
        let old = self.set_ns(true);
        let r = self.expr();
        self.no_struct = old;
        r
    }

    /// Parses an expression inside brackets, where struct literals are allowed.
    fn inner_expr(&mut self) -> PResult<Expr> {
        let old = self.set_ns(false);
        let r = self.expr();
        self.no_struct = old;
        r
    }

    fn range(&mut self) -> PResult<Expr> {
        let lo = self.binary(0)?;
        if !self.eat(&T::DotDot) {
            return Ok(lo);
        }
        let hi = self.binary(0)?;
        if self.at(&T::DotDot) {
            return Err(ParseError::new(
                "range operators cannot be chained; add parentheses",
                self.peek().span,
            ));
        }
        let span = lo.span.to(hi.span);
        Ok(Expr {
            span,
            kind: ExprKind::Range {
                lo: Box::new(lo),
                hi: Box::new(hi),
            },
        })
    }

    /// Parses binary operators of precedence `min` and higher (precedence climbing).
    fn binary(&mut self, min: u8) -> PResult<Expr> {
        let saved = self.depth;
        let mut lhs = self.unary()?;
        let mut after_cmp = false;
        while let Some((op, prec)) = bin_op(self.kind()) {
            if prec < min {
                break;
            }
            if prec == CMP_PREC && after_cmp {
                return Err(ParseError::new(
                    "comparison operators cannot be chained; use `&&`",
                    self.peek().span,
                ));
            }
            after_cmp = prec == CMP_PREC;
            self.chain_step()?;
            self.bump();
            let rhs = self.binary(prec + 1)?;
            lhs = binary(op, lhs, rhs);
        }
        self.depth = saved;
        Ok(lhs)
    }

    fn unary(&mut self) -> PResult<Expr> {
        let saved = self.depth;
        let mut ops = Vec::new();
        loop {
            let lo = self.lo();
            match self.kind() {
                T::Minus => ops.push((UnOp::Neg, lo)),
                T::Bang => ops.push((UnOp::Not, lo)),
                T::Amp => ops.push((UnOp::Ref, lo)),
                T::AndAnd => {
                    self.chain_step()?;
                    ops.push((UnOp::Ref, lo));
                    ops.push((UnOp::Ref, lo.saturating_add(1)));
                }
                _ => break,
            }
            self.chain_step()?;
            self.bump();
        }
        let mut e = self.postfix()?;
        for (op, lo) in ops.into_iter().rev() {
            let span = Span::new(lo, e.span.hi);
            e = Expr {
                span,
                kind: ExprKind::Unary {
                    op,
                    expr: Box::new(e),
                },
            };
        }
        self.depth = saved;
        Ok(e)
    }

    fn postfix(&mut self) -> PResult<Expr> {
        let saved = self.depth;
        let mut e = self.primary()?;
        while matches!(self.kind(), T::Dot | T::LParen | T::LBracket) {
            self.chain_step()?;
            e = self.postfix_op(e)?;
        }
        self.depth = saved;
        Ok(e)
    }

    fn postfix_op(&mut self, e: Expr) -> PResult<Expr> {
        match self.kind() {
            T::Dot => self.dot(e),
            T::LParen => self.call(e),
            _ => self.index(e),
        }
    }

    /// Parses `.name`, `.0` or `.method(args)` after `e`.
    fn dot(&mut self, e: Expr) -> PResult<Expr> {
        self.bump();
        let name = match self.kind() {
            T::Name(_) => self.ident(),
            T::Int(v) => {
                let text = v.to_string();
                Ident::new(text, self.bump())
            }
            _ => return Err(self.expected("a field or method name after `.`")),
        };
        let lo = e.span.lo;
        if !self.at(&T::LParen) {
            let span = Span::new(lo, name.span.hi);
            return Ok(Expr {
                kind: ExprKind::Field {
                    base: Box::new(e),
                    name,
                },
                span,
            });
        }
        let args = self.args()?;
        let trailing = self.trailing()?;
        let kind = ExprKind::MethodCall {
            receiver: Box::new(e),
            method: name,
            args,
            trailing,
        };
        Ok(Expr {
            kind,
            span: Span::new(lo, self.last_hi),
        })
    }

    /// Parses `(args) trailing?` after `e`.
    fn call(&mut self, e: Expr) -> PResult<Expr> {
        let lo = e.span.lo;
        let args = self.args()?;
        let trailing = self.trailing()?;
        let kind = ExprKind::Call {
            callee: Box::new(e),
            args,
            trailing,
        };
        Ok(Expr {
            kind,
            span: Span::new(lo, self.last_hi),
        })
    }

    /// Parses `[index]` or `[]` after `e`.
    fn index(&mut self, e: Expr) -> PResult<Expr> {
        let lo = e.span.lo;
        self.bump();
        let index = if self.eat(&T::RBracket) {
            None
        } else {
            let i = self.inner_expr()?;
            self.expect(&T::RBracket, "`]` after the index")?;
            Some(Box::new(i))
        };
        Ok(Expr {
            kind: ExprKind::Index {
                base: Box::new(e),
                index,
            },
            span: Span::new(lo, self.last_hi),
        })
    }

    /// Parses `"(" args? ")"`. The current token is `(`.
    fn args(&mut self) -> PResult<Vec<Arg>> {
        self.bump();
        let old = self.set_ns(false);
        let r = self.comma_list(&T::RParen, "`)` after arguments", Self::arg);
        self.no_struct = old;
        Ok(r?.0)
    }

    fn arg(&mut self) -> PResult<Arg> {
        let name = if self.at_any_name() && self.kind_at(1) == &T::Colon {
            let n = self.ident();
            self.bump();
            Some(n)
        } else {
            None
        };
        Ok(Arg {
            name,
            value: self.expr()?,
        })
    }

    /// Parses a trailing block after `)`. It must start on the same line.
    /// The block becomes a closure with no parameters.
    fn trailing(&mut self) -> PResult<Option<Box<Expr>>> {
        if self.no_struct || !self.at(&T::LBrace) || self.peek().starts_line {
            return Ok(None);
        }
        let block = self.block("`{`")?;
        let span = block.span;
        let body = Box::new(Expr {
            kind: ExprKind::Block(block),
            span,
        });
        Ok(Some(Box::new(Expr {
            kind: ExprKind::Closure {
                params: Vec::new(),
                body,
            },
            span,
        })))
    }

    fn primary(&mut self) -> PResult<Expr> {
        match self.kind() {
            T::Name(_) => self.name_expr(),
            T::LParen => self.paren(),
            T::LBracket => self.array(),
            T::LBrace => {
                let b = self.block("`{`")?;
                Ok(Expr {
                    span: b.span,
                    kind: ExprKind::Block(b),
                })
            }
            T::Pipe | T::OrOr => self.closure(),
            T::If => self.if_expr(),
            T::Match => self.match_expr(),
            T::Str(_) => {
                let lo = self.lo();
                let lit = self.str_lit()?;
                Ok(Expr {
                    kind: ExprKind::Lit(lit),
                    span: Span::new(lo, self.last_hi),
                })
            }
            _ => self.atom(),
        }
    }

    /// Parses a literal, `self` or `Self`.
    fn atom(&mut self) -> PResult<Expr> {
        let kind = match self.kind() {
            T::Int(v) => ExprKind::Lit(Lit::Int(*v)),
            T::True => ExprKind::Lit(Lit::Bool(true)),
            T::False => ExprKind::Lit(Lit::Bool(false)),
            T::SelfValue => ExprKind::Name(Ident::new("self", self.peek().span)),
            T::SelfType => ExprKind::Name(Ident::new("Self", self.peek().span)),
            _ => return Err(self.expected("an expression")),
        };
        Ok(Expr {
            kind,
            span: self.bump(),
        })
    }

    /// Parses a name, or a `handle`, `scope` or struct literal that starts with a name.
    fn name_expr(&mut self) -> PResult<Expr> {
        let (is_handle, is_scope, is_struct) = match self.kind() {
            T::Name(n) => (
                n == "handle"
                    && matches!(self.kind_at(1), T::Name(_))
                    && self.kind_at(2) == &T::LBrace,
                n == "scope" && self.kind_at(1) == &T::LBrace,
                is_upper(n) && !self.no_struct && self.struct_lit_ahead(),
            ),
            _ => (false, false, false),
        };
        if is_handle {
            return self.handle_expr();
        }
        if is_scope {
            return self.scope_expr();
        }
        if is_struct {
            return self.struct_lit();
        }
        let id = self.ident();
        Ok(Expr {
            span: id.span,
            kind: ExprKind::Name(id),
        })
    }

    /// True if a struct literal starts here: `Name {` or `A.B {`, then `NAME :` or `}`.
    fn struct_lit_ahead(&self) -> bool {
        let at =
            if self.kind_at(1) == &T::Dot && matches!(self.kind_at(2), T::Name(m) if is_upper(m)) {
                3
            } else {
                1
            };
        self.kind_at(at) == &T::LBrace
            && (self.kind_at(at + 1) == &T::RBrace
                || (matches!(self.kind_at(at + 1), T::Name(_))
                    && self.kind_at(at + 2) == &T::Colon))
    }

    fn struct_lit(&mut self) -> PResult<Expr> {
        let lo = self.lo();
        let mut path = vec![self.ident()];
        if self.eat(&T::Dot) {
            path.push(self.ident());
        }
        self.bump();
        let old = self.set_ns(false);
        let r = self.brace_list("`,`, a line break or `}` after the field", Self::field_init);
        self.no_struct = old;
        let fields = r?;
        Ok(Expr {
            kind: ExprKind::StructLit { path, fields },
            span: Span::new(lo, self.last_hi),
        })
    }

    fn field_init(&mut self) -> PResult<(Ident, Expr)> {
        let name = self.name("a field name")?;
        self.expect(&T::Colon, "`:` after the field name")?;
        Ok((name, self.expr()?))
    }

    /// Parses `"(" ( expr "," ... )? ")"` or `"[" ... "]"` items.
    fn expr_list(&mut self, close: &T, what: &str) -> PResult<(Vec<Expr>, bool)> {
        let old = self.set_ns(false);
        let r = self.comma_list(close, what, Self::expr);
        self.no_struct = old;
        r
    }

    /// Parses `()`, `(e)` or a tuple. The current token is `(`.
    fn paren(&mut self) -> PResult<Expr> {
        let lo = self.bump().lo;
        let (mut items, trailing) = self.expr_list(&T::RParen, "`,` or `)`")?;
        let span = Span::new(lo, self.last_hi);
        if items.is_empty() {
            return Ok(Expr {
                kind: ExprKind::Lit(Lit::Unit),
                span,
            });
        }
        if items.len() == 1 && !trailing {
            if let Some(mut only) = items.pop() {
                only.span = span;
                return Ok(only);
            }
        }
        Ok(Expr {
            kind: ExprKind::Tuple(items),
            span,
        })
    }

    /// Parses `[a, b]`. The current token is `[`.
    fn array(&mut self) -> PResult<Expr> {
        let lo = self.bump().lo;
        let (items, _) = self.expr_list(&T::RBracket, "`,` or `]`")?;
        Ok(Expr {
            kind: ExprKind::Array(items),
            span: Span::new(lo, self.last_hi),
        })
    }

    /// Parses `|params| body` or `|| body`.
    fn closure(&mut self) -> PResult<Expr> {
        let lo = self.lo();
        let params = if self.eat(&T::OrOr) {
            Vec::new()
        } else {
            self.bump();
            self.params(&T::Pipe, "`,` or `|` after a closure parameter")?
        };
        let body = self.closure_body()?;
        let span = Span::new(lo, body.span.hi);
        Ok(Expr {
            span,
            kind: ExprKind::Closure {
                params,
                body: Box::new(body),
            },
        })
    }

    /// Parses a closure body. An assignment body, as in `|| x += 1`, becomes a
    /// block with one statement.
    fn closure_body(&mut self) -> PResult<Expr> {
        let target = self.expr()?;
        let Some(op) = assign_op(self.kind()) else {
            return Ok(target);
        };
        self.bump();
        let value = self.expr()?;
        let span = target.span.to(value.span);
        let stmt = Stmt {
            kind: StmtKind::Assign { target, op, value },
            span,
        };
        Ok(Expr {
            kind: ExprKind::Block(Block {
                stmts: vec![stmt],
                span,
            }),
            span,
        })
    }

    /// Parses an `if` chain. It loops over `else if`, so a long chain does not recurse.
    fn if_expr(&mut self) -> PResult<Expr> {
        let saved = self.depth;
        let mut links = Vec::new();
        let mut last_else = None;
        loop {
            let lo = self.bump().lo;
            let cond = self.head_expr()?;
            let then = self.block("`{` after the `if` condition")?;
            links.push((lo, cond, then));
            if !self.skip_ends_before(|k| k == &T::Else) {
                break;
            }
            self.bump();
            if self.at(&T::If) {
                self.chain_step()?;
                continue;
            }
            if !self.at(&T::LBrace) {
                return Err(self.expected("`{` or `if` after `else`"));
            }
            let b = self.block("`{`")?;
            last_else = Some(Box::new(Expr {
                span: b.span,
                kind: ExprKind::Block(b),
            }));
            break;
        }
        self.depth = saved;
        let hi = self.last_hi;
        let mut result: Option<Expr> = None;
        for (lo, cond, then) in links.into_iter().rev() {
            let else_ = result.take().map(Box::new).or_else(|| last_else.take());
            let kind = ExprKind::If {
                cond: Box::new(cond),
                then,
                else_,
            };
            result = Some(Expr {
                kind,
                span: Span::new(lo, hi),
            });
        }
        result.ok_or_else(|| self.expected("`if`"))
    }

    /// Parses a `match`. The current token is `match`.
    fn match_expr(&mut self) -> PResult<Expr> {
        let lo = self.bump().lo;
        let scrutinee = self.head_expr()?;
        self.expect(&T::LBrace, "`{` after the `match` value")?;
        let old = self.set_ns(false);
        let r = self.brace_list("`,`, a line break or `}` after the match arm", Self::arm);
        self.no_struct = old;
        let kind = ExprKind::Match {
            scrutinee: Box::new(scrutinee),
            arms: r?,
        };
        Ok(Expr {
            kind,
            span: Span::new(lo, self.last_hi),
        })
    }

    fn arm(&mut self) -> PResult<Arm> {
        let pat = self.pattern()?;
        self.expect(&T::FatArrow, "`=>` after the pattern")?;
        let body = self.expr()?;
        Ok(Arm {
            span: pat.span().to(body.span),
            pat,
            body,
        })
    }

    /// Parses `handle E { clauses } in expr`. The current tokens are `handle E {`.
    fn handle_expr(&mut self) -> PResult<Expr> {
        let lo = self.bump().lo;
        let effect = self.ident();
        self.bump();
        let mut clauses = Vec::new();
        loop {
            self.skip_newlines();
            if self.eat(&T::RBrace) {
                break;
            }
            if self.at(&T::Eof) {
                return Err(self.expected("`}`"));
            }
            clauses.push(self.handler_clause()?);
        }
        if !self.skip_ends_before(|k| k == &T::In) {
            return Err(self.expected("`in` after the handler"));
        }
        self.bump();
        let body = self.expr()?;
        let span = Span::new(lo, body.span.hi);
        Ok(Expr {
            kind: ExprKind::Handle {
                effect,
                clauses,
                body: Box::new(body),
            },
            span,
        })
    }

    fn handler_clause(&mut self) -> PResult<HandlerClause> {
        let lo = self.expect(&T::Fn, "`fn` to start a handler clause")?.lo;
        let op = self.name("the operation name")?;
        self.expect(&T::LParen, "`(` after the operation name")?;
        let params = self.params(&T::RParen, "`,` or `)` after a parameter")?;
        let body = self.block("`{` to start the handler clause body")?;
        Ok(HandlerClause {
            op,
            params,
            body,
            span: Span::new(lo, self.last_hi),
        })
    }

    /// Parses `scope { s => stmts }`. The current tokens are `scope {`.
    fn scope_expr(&mut self) -> PResult<Expr> {
        let lo = self.bump().lo;
        let brace = self.bump().lo;
        self.skip_newlines();
        let binder = self.name("the scope name after `scope {`")?;
        self.expect(&T::FatArrow, "`=>` after the scope name")?;
        let body = self.block_rest(brace)?;
        Ok(Expr {
            kind: ExprKind::Scope { binder, body },
            span: Span::new(lo, self.last_hi),
        })
    }

    /// Parses a string token. Each interpolation is parsed as an expression.
    fn str_lit(&mut self) -> PResult<Lit> {
        let pieces = match self.kind() {
            T::Str(p) => p.clone(),
            _ => Vec::new(),
        };
        self.bump();
        let mut parts = Vec::with_capacity(pieces.len());
        for piece in pieces {
            parts.push(match piece {
                StrPiece::Text(t) => StrPart::Text(t),
                StrPiece::Interp { src, offset } => StrPart::Interp(self.interp(&src, offset)?),
            });
        }
        Ok(Lit::Str(parts))
    }

    /// Parses the source of one interpolation. Spans stay absolute.
    fn interp(&self, src: &str, offset: u32) -> PResult<Expr> {
        if src.trim().is_empty() {
            let len = u32::try_from(src.len()).unwrap_or(u32::MAX);
            let hi = offset.saturating_add(len).saturating_add(1);
            return Err(ParseError::new(
                "empty interpolation `{}` in a string; write `\\{` for a literal brace",
                Span::new(offset.saturating_sub(1), hi),
            ));
        }
        let mut sub = Self::new(lex_at(src, offset)?, self.depth);
        let e = sub.expr()?;
        if !sub.at(&T::Eof) {
            return Err(sub.expected("`}` to end the interpolation"));
        }
        Ok(e)
    }
}

fn is_upper(s: &str) -> bool {
    s.bytes().next().is_some_and(|b| b.is_ascii_uppercase())
}

/// True if the token can start an expression. `assert` uses this.
const fn can_start_expr(k: &T) -> bool {
    matches!(
        k,
        T::Name(_)
            | T::Int(_)
            | T::Str(_)
            | T::True
            | T::False
            | T::SelfValue
            | T::SelfType
            | T::LParen
            | T::LBracket
            | T::LBrace
            | T::Pipe
            | T::OrOr
            | T::Minus
            | T::Bang
            | T::Amp
            | T::AndAnd
            | T::If
            | T::Match
    )
}

const fn assign_op(k: &T) -> Option<AssignOp> {
    match k {
        T::Eq => Some(AssignOp::Assign),
        T::PlusEq => Some(AssignOp::Add),
        T::MinusEq => Some(AssignOp::Sub),
        T::StarEq => Some(AssignOp::Mul),
        _ => None,
    }
}

/// Returns the binary operator and its precedence. A higher number binds tighter.
const fn bin_op(k: &T) -> Option<(BinOp, u8)> {
    Some(match k {
        T::OrOr => (BinOp::Or, 0),
        T::AndAnd => (BinOp::And, 1),
        T::EqEq => (BinOp::Eq, CMP_PREC),
        T::Ne => (BinOp::Ne, CMP_PREC),
        T::Lt => (BinOp::Lt, CMP_PREC),
        T::Le => (BinOp::Le, CMP_PREC),
        T::Gt => (BinOp::Gt, CMP_PREC),
        T::Ge => (BinOp::Ge, CMP_PREC),
        T::Plus => (BinOp::Add, 3),
        T::Minus => (BinOp::Sub, 3),
        T::Star => (BinOp::Mul, 4),
        T::Slash => (BinOp::Div, 4),
        T::Percent => (BinOp::Rem, 4),
        _ => return None,
    })
}

fn binary(op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
    let span = lhs.span.to(rhs.span);
    Expr {
        span,
        kind: ExprKind::Binary {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        },
    }
}
