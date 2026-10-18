//! Recursive-descent parser. See `docs/grammar.md`.
//!
//! [`parse_file`] parses a full file and [`parse_expr`] parses one expression.
//! The parser stops at the first error. It does not panic on any input: a
//! nesting budget limits the recursion depth and the depth of the tree.

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
        Self { message: message.into(), span }
    }
}

/// The nesting budget. A nested construct costs [`NEST_COST`]. One step of an
/// operator chain costs 1. The budget limits the parser stack and the tree depth.
const MAX_DEPTH: u32 = 1024;

/// The budget cost of one nested expression, block, type or pattern.
const NEST_COST: u32 = 8;

/// The text that lists the item keywords.
const ITEM_START: &str =
    "an item (`fn`, `struct`, `enum`, `effect`, `impl`, `mod`, `extern` or `test`)";

/// The mode words, for error messages.
const MODES: &str = "uniq, aliased, portable, nonportable, uncontended, shared, once, many";

/// The token that the parser sees after the end of the token list.
static EOF: Token = Token { kind: T::Eof, span: Span { lo: 0, hi: 0 }, starts_line: false };

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
        Self { toks, pos: 0, no_struct: false, depth, last_hi }
    }

    fn tok(&self, n: usize) -> &Token {
        self.toks.get(self.pos + n).or_else(|| self.toks.last()).unwrap_or(&EOF)
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
        ParseError::new(format!("expected {what}, found {}", t.kind.describe()), t.span)
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

    /// Runs `f` one nesting level deeper.
    fn nested<R>(&mut self, f: impl FnOnce(&mut Self) -> PResult<R>) -> PResult<R> {
        self.depth += NEST_COST;
        if self.depth > MAX_DEPTH {
            return Err(self.too_deep());
        }
        let r = f(self);
        self.depth -= NEST_COST;
        r
    }

    /// Uses one unit of the budget for one step of an operator chain.
    /// The caller restores `depth` at the end of the chain.
    fn chain_step(&mut self) -> PResult<()> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(self.too_deep());
        }
        Ok(())
    }

    /// Runs `f` with the `no_struct` flag set to `ns`.
    fn with_ns<R>(&mut self, ns: bool, f: impl FnOnce(&mut Self) -> PResult<R>) -> PResult<R> {
        let old = std::mem::replace(&mut self.no_struct, ns);
        let r = f(self);
        self.no_struct = old;
        r
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
        let kind = if self.at(&T::Fn) {
            ItemKind::Fn(self.fn_decl(false, false)?)
        } else if self.at_name("fip") && self.kind_at(1) == &T::Fn {
            self.bump();
            ItemKind::Fn(self.fn_decl(true, false)?)
        } else if self.eat(&T::Extern) {
            if self.at(&T::Fn) {
                ItemKind::Fn(self.fn_decl(false, true)?)
            } else if self.at_name("type") {
                self.bump();
                ItemKind::ExternType(self.extern_type()?)
            } else {
                return Err(self.expected("`fn` or `type` after `extern`"));
            }
        } else if self.at_name("linear") && self.kind_at(1) == &T::Struct {
            self.bump();
            ItemKind::Struct(self.struct_decl(true)?)
        } else if self.at(&T::Struct) {
            ItemKind::Struct(self.struct_decl(false)?)
        } else if self.at(&T::Enum) {
            ItemKind::Enum(self.enum_decl()?)
        } else if self.at(&T::Effect) {
            ItemKind::Effect(self.effect_decl()?)
        } else if self.at(&T::Impl) {
            ItemKind::Impl(self.impl_block()?)
        } else if self.at(&T::Mod) {
            ItemKind::Mod(self.mod_decl()?)
        } else if self.at_name("test") && matches!(self.kind_at(1), T::Str(_)) {
            ItemKind::Test(self.test_decl()?)
        } else {
            return Err(self.expected(ITEM_START));
        };
        Ok(Item { kind, is_pub, span: Span::new(lo, self.last_hi) })
    }

    /// Parses `"{" item* "}"` for `impl` and `mod`.
    fn items_in_braces(&mut self, what: &str) -> PResult<Vec<Item>> {
        self.expect(&T::LBrace, what)?;
        let mut items = Vec::new();
        loop {
            self.skip_ends();
            if self.eat(&T::RBrace) {
                return Ok(items);
            }
            if self.at(&T::Eof) {
                return Err(self.expected("`}` at the end of the item list"));
            }
            items.push(self.nested(Self::item)?);
        }
    }

    /// Parses a function. The current token is `fn`.
    fn fn_decl(&mut self, is_fip: bool, is_extern: bool) -> PResult<FnDecl> {
        self.bump();
        let name = self.name("the function name")?;
        let generics = self.generics()?;
        self.expect(&T::LParen, "`(` after the function name")?;
        let params = self.params(&T::RParen, "`,` or `)` after a parameter")?;
        let ret = if self.eat(&T::Arrow) { Some(self.ty()?) } else { None };
        let effects = if self.eat(&T::Slash) { Some(self.row()?) } else { None };
        let body = if is_extern {
            if self.at(&T::LBrace) {
                return Err(ParseError::new("an `extern fn` cannot have a body", self.peek().span));
            }
            None
        } else {
            Some(self.block("`{` to start the function body")?)
        };
        Ok(FnDecl { name, generics, params, ret, effects, body, is_extern, is_fip })
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
        let ty = if self.eat(&T::Colon) { Some(self.ty()?) } else { None };
        Ok(Param { span: Span::new(name.span.lo, self.last_hi), name, ty })
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
        let on_abort = if self.skip_ends_before(|k| matches!(k, T::Name(n) if n == "on")) {
            self.bump();
            if !self.at_name("abort") {
                return Err(self.expected("`abort` after `on`"));
            }
            self.bump();
            self.expect(&T::Eq, "`=` after `on abort`")?;
            Some(self.name("the abort function name")?)
        } else {
            None
        };
        Ok(StructDecl { name, generics, fields, is_linear, is_immovable, on_abort })
    }

    fn field(&mut self) -> PResult<FieldDecl> {
        let name = self.name("the field name")?;
        self.expect(&T::Colon, "`:` after the field name")?;
        let ty = self.ty()?;
        Ok(FieldDecl { span: Span::new(name.span.lo, self.last_hi), name, ty })
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
                p.comma_list(&T::RParen, "`,` or `)` after a type", Self::ty)?.0
            } else {
                Vec::new()
            };
            Ok(VariantDecl { span: Span::new(name.span.lo, p.last_hi), name, fields })
        })?;
        Ok(EnumDecl { name, generics, variants })
    }

    /// Parses an effect. The current token is `effect`.
    fn effect_decl(&mut self) -> PResult<EffectDecl> {
        self.bump();
        let name = self.name("the effect name")?;
        self.expect(&T::LBrace, "`{` to start the effect operations")?;
        let ops = self.brace_list("`,`, a line break or `}` after the operation", Self::op_decl)?;
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
        let ret = if self.eat(&T::Arrow) { Some(self.ty()?) } else { None };
        Ok(OpDecl { name, params, ret, is_multi, span: Span::new(lo, self.last_hi) })
    }

    /// Parses an impl block. The current token is `impl`.
    fn impl_block(&mut self) -> PResult<ImplBlock> {
        self.bump();
        let generics = self.generics()?;
        let self_ty = self.ty()?;
        let items = self.items_in_braces("`{` to start the impl body")?;
        Ok(ImplBlock { generics, self_ty, items })
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
                    return Err(ParseError::new("a test name cannot contain interpolation", span));
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
                let value = if p.eat(&T::Colon) { Some(p.name("a property value")?) } else { None };
                Ok(TypeProp { key, value })
            })?
        } else {
            Vec::new()
        };
        Ok(ExternTypeDecl { name, generics, props })
    }
}

// ------------------------------------------------------------------ types, places, rows

impl Parser {
    fn ty(&mut self) -> PResult<TypeExpr> {
        self.nested(|p| {
            let mut ty = p.ty_atom()?;
            if p.eat(&T::At) {
                let before = ty.modes.len();
                while let T::Name(n) = p.kind() {
                    let Some(mode) = Mode::from_name(n) else { break };
                    p.bump();
                    ty.modes.push(mode);
                }
                if ty.modes.len() == before {
                    return Err(match p.kind() {
                        T::Name(n) => ParseError::new(
                            format!("unknown mode `{n}`; expected one of {MODES}"),
                            p.peek().span,
                        ),
                        _ => p.expected("a mode after `@`"),
                    });
                }
                ty.span = Span::new(ty.span.lo, p.last_hi);
            }
            Ok(ty)
        })
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
                let inner = self.ref_ty()?;
                let inner = TypeExpr {
                    kind: inner,
                    modes: Vec::new(),
                    span: Span::new(lo.saturating_add(1), self.last_hi),
                };
                let place = if self.eat(&T::In) { Some(self.place()?) } else { None };
                TypeExprKind::Ref { inner: Box::new(inner), place }
            }
            T::LParen => {
                self.bump();
                let (mut items, trailing) =
                    self.comma_list(&T::RParen, "`,` or `)` after a type", Self::ty)?;
                if items.len() == 1 && !trailing {
                    if let Some(mut t) = items.pop() {
                        t.span = Span::new(lo, self.last_hi);
                        return Ok(t);
                    }
                }
                TypeExprKind::Tuple(items)
            }
            T::LBracket => {
                self.bump();
                self.array_ty()?
            }
            T::Fn => {
                self.bump();
                self.expect(&T::LParen, "`(` after `fn` in a function type")?;
                let params = self.comma_list(&T::RParen, "`,` or `)` after a type", Self::ty)?.0;
                let ret = if self.eat(&T::Arrow) { Some(Box::new(self.ty()?)) } else { None };
                let effects = if self.eat(&T::Slash) { Some(self.fn_row()?) } else { None };
                TypeExprKind::Fn { params, ret, effects }
            }
            T::SelfType => {
                self.bump();
                TypeExprKind::SelfType
            }
            T::Name(_) => self.path_ty()?,
            _ => return Err(self.expected("a type")),
        };
        Ok(TypeExpr { kind, modes: Vec::new(), span: Span::new(lo, self.last_hi) })
    }

    /// Parses the rest of `&T` or `&T in place` after the `&`.
    fn ref_ty(&mut self) -> PResult<TypeExprKind> {
        let inner = Box::new(self.nested(Self::ty_atom)?);
        let place = if self.eat(&T::In) { Some(self.place()?) } else { None };
        Ok(TypeExprKind::Ref { inner, place })
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
                    let name = match self.kind() {
                        T::Name(_) => self.ident(),
                        T::Int(v) => {
                            let text = v.to_string();
                            Ident::new(text, self.bump())
                        }
                        _ => return Err(self.expected("a field name after `.` in a place")),
                    };
                    steps.push(PlaceStep::Field(name));
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
        Ok(PlaceExpr { root, steps, span: Span::new(lo, self.last_hi) })
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
        Ok(EffectRow { items, span: Span::new(lo, self.last_hi) })
    }

    /// Parses a function type row: `row_item` or `"(" row ")"`.
    fn fn_row(&mut self) -> PResult<EffectRow> {
        let lo = self.lo();
        if !self.eat(&T::LParen) {
            let item = self.row_item()?;
            return Ok(EffectRow { items: vec![item], span: Span::new(lo, self.last_hi) });
        }
        let (items, _) = self.comma_list(&T::RParen, "`,` or `)` after an effect", Self::row_item)?;
        let span = Span::new(lo, self.last_hi);
        if items.is_empty() {
            return Err(ParseError::new("an effect row needs at least one effect", span));
        }
        Ok(EffectRow { items, span })
    }

    fn row_item(&mut self) -> PResult<EffectItem> {
        if self.at_name("mut") && self.kind_at(1) == &T::LParen {
            let lo = self.lo();
            self.bump();
            self.bump();
            let (places, _) = self.comma_list(&T::RParen, "`,` or `)` after a place", Self::place)?;
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
        self.nested(|p| {
            p.with_ns(false, |p| {
                let mut stmts = Vec::new();
                loop {
                    p.skip_ends();
                    if p.eat(&T::RBrace) {
                        break;
                    }
                    if p.at(&T::Eof) {
                        return Err(p.expected("`}` at the end of the block"));
                    }
                    stmts.push(p.stmt()?);
                    if !p.at_stmt_end() {
                        return Err(p.expected("a line break or `;` after the statement"));
                    }
                }
                Ok(Block { stmts, span: Span::new(lo, p.last_hi) })
            })
        })
    }

    fn stmt(&mut self) -> PResult<Stmt> {
        let lo = self.lo();
        let kind = match self.kind() {
            T::Let => {
                self.bump();
                let pat = self.pattern()?;
                let ty = if self.eat(&T::Colon) { Some(self.ty()?) } else { None };
                let init = if self.eat(&T::Eq) { Some(self.expr()?) } else { None };
                StmtKind::Let { pat, ty, init }
            }
            T::Return => {
                self.bump();
                StmtKind::Return(if self.at_stmt_end() { None } else { Some(self.expr()?) })
            }
            T::Break => {
                self.bump();
                StmtKind::Break
            }
            T::Continue => {
                self.bump();
                StmtKind::Continue
            }
            T::While => {
                self.bump();
                let cond = self.with_ns(true, Self::expr)?;
                let body = self.block("`{` after the `while` condition")?;
                StmtKind::While { cond, body }
            }
            T::For => {
                self.bump();
                let pat = self.pattern()?;
                self.expect(&T::In, "`in` after the `for` pattern")?;
                let iter = self.with_ns(true, Self::expr)?;
                let body = self.block("`{` after the `for` value")?;
                StmtKind::For { pat, iter, body }
            }
            T::Loop => {
                self.bump();
                StmtKind::Loop(self.block("`{` after `loop`")?)
            }
            _ if self.at_name("assert") && can_start_expr(self.kind_at(1)) => {
                self.bump();
                StmtKind::Assert(self.expr()?)
            }
            _ => {
                let target = self.expr()?;
                match assign_op(self.kind()) {
                    Some(op) => {
                        self.bump();
                        let value = self.expr()?;
                        StmtKind::Assign { target, op, value }
                    }
                    None => StmtKind::Expr(target),
                }
            }
        };
        Ok(Stmt { kind, span: Span::new(lo, self.last_hi) })
    }

    fn pattern(&mut self) -> PResult<Pattern> {
        self.nested(|p| {
            let lo = p.lo();
            match p.kind() {
                T::Name(n) if n == "_" => Ok(Pattern::Wild(p.bump())),
                T::Name(n) if is_upper(n) => {
                    let mut path = vec![p.ident()];
                    if p.at(&T::Dot) && matches!(p.kind_at(1), T::Name(m) if is_upper(m)) {
                        p.bump();
                        path.push(p.ident());
                    }
                    let fields = if p.eat(&T::LParen) {
                        p.comma_list(&T::RParen, "`,` or `)` after a pattern", Self::pattern)?.0
                    } else {
                        Vec::new()
                    };
                    Ok(Pattern::Variant { path, fields, span: Span::new(lo, p.last_hi) })
                }
                T::Name(_) => Ok(Pattern::Bind(p.ident())),
                T::Int(v) => {
                    let lit = Lit::Int(*v);
                    Ok(Pattern::Lit(lit, p.bump()))
                }
                T::True => Ok(Pattern::Lit(Lit::Bool(true), p.bump())),
                T::False => Ok(Pattern::Lit(Lit::Bool(false), p.bump())),
                T::Str(_) => {
                    let lit = p.str_lit()?;
                    Ok(Pattern::Lit(lit, Span::new(lo, p.last_hi)))
                }
                T::LParen => {
                    p.bump();
                    let (mut items, trailing) =
                        p.comma_list(&T::RParen, "`,` or `)` after a pattern", Self::pattern)?;
                    let span = Span::new(lo, p.last_hi);
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
                _ => Err(p.expected("a pattern")),
            }
        })
    }
}

// ------------------------------------------------------------------ expressions

impl Parser {
    fn expr(&mut self) -> PResult<Expr> {
        self.nested(Self::range)
    }

    fn range(&mut self) -> PResult<Expr> {
        let lo = self.or()?;
        if !self.eat(&T::DotDot) {
            return Ok(lo);
        }
        let hi = self.or()?;
        if self.at(&T::DotDot) {
            return Err(ParseError::new(
                "range operators cannot be chained; add parentheses",
                self.peek().span,
            ));
        }
        Ok(Expr { span: lo.span.to(hi.span), kind: ExprKind::Range { lo: Box::new(lo), hi: Box::new(hi) } })
    }

    /// Parses a left-associative chain of binary operators.
    fn binary_left(
        &mut self,
        next: fn(&mut Self) -> PResult<Expr>,
        op_of: fn(&T) -> Option<BinOp>,
    ) -> PResult<Expr> {
        let saved = self.depth;
        let mut lhs = next(self)?;
        while let Some(op) = op_of(self.kind()) {
            self.chain_step()?;
            self.bump();
            let rhs = next(self)?;
            lhs = binary(op, lhs, rhs);
        }
        self.depth = saved;
        Ok(lhs)
    }

    fn or(&mut self) -> PResult<Expr> {
        self.binary_left(Self::and, |k| (k == &T::OrOr).then_some(BinOp::Or))
    }

    fn and(&mut self) -> PResult<Expr> {
        self.binary_left(Self::cmp, |k| (k == &T::AndAnd).then_some(BinOp::And))
    }

    fn cmp(&mut self) -> PResult<Expr> {
        let lhs = self.add()?;
        let Some(op) = cmp_op(self.kind()) else { return Ok(lhs) };
        self.bump();
        let rhs = self.add()?;
        if cmp_op(self.kind()).is_some() {
            return Err(ParseError::new(
                "comparison operators cannot be chained; use `&&`",
                self.peek().span,
            ));
        }
        Ok(binary(op, lhs, rhs))
    }

    fn add(&mut self) -> PResult<Expr> {
        self.binary_left(Self::mul, |k| match k {
            T::Plus => Some(BinOp::Add),
            T::Minus => Some(BinOp::Sub),
            _ => None,
        })
    }

    fn mul(&mut self) -> PResult<Expr> {
        self.binary_left(Self::unary, |k| match k {
            T::Star => Some(BinOp::Mul),
            T::Slash => Some(BinOp::Div),
            T::Percent => Some(BinOp::Rem),
            _ => None,
        })
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
            e = Expr { span: Span::new(lo, e.span.hi), kind: ExprKind::Unary { op, expr: Box::new(e) } };
        }
        self.depth = saved;
        Ok(e)
    }

    fn postfix(&mut self) -> PResult<Expr> {
        let saved = self.depth;
        let mut e = self.primary()?;
        loop {
            let lo = e.span.lo;
            e = match self.kind() {
                T::Dot => {
                    self.chain_step()?;
                    self.bump();
                    let name = match self.kind() {
                        T::Name(_) => self.ident(),
                        T::Int(v) => {
                            let text = v.to_string();
                            Ident::new(text, self.bump())
                        }
                        _ => return Err(self.expected("a field or method name after `.`")),
                    };
                    if self.at(&T::LParen) {
                        let (args, trailing) = self.call_suffix()?;
                        let kind = ExprKind::MethodCall { receiver: Box::new(e), method: name, args, trailing };
                        Expr { kind, span: Span::new(lo, self.last_hi) }
                    } else {
                        let span = Span::new(lo, name.span.hi);
                        Expr { kind: ExprKind::Field { base: Box::new(e), name }, span }
                    }
                }
                T::LParen => {
                    self.chain_step()?;
                    let (args, trailing) = self.call_suffix()?;
                    let kind = ExprKind::Call { callee: Box::new(e), args, trailing };
                    Expr { kind, span: Span::new(lo, self.last_hi) }
                }
                T::LBracket => {
                    self.chain_step()?;
                    self.bump();
                    let index = if self.eat(&T::RBracket) {
                        None
                    } else {
                        let i = self.with_ns(false, Self::expr)?;
                        self.expect(&T::RBracket, "`]` after the index")?;
                        Some(Box::new(i))
                    };
                    Expr { kind: ExprKind::Index { base: Box::new(e), index }, span: Span::new(lo, self.last_hi) }
                }
                _ => break,
            };
        }
        self.depth = saved;
        Ok(e)
    }

    /// Parses `"(" args? ")" trailing?`. The current token is `(`.
    fn call_suffix(&mut self) -> PResult<(Vec<Arg>, Option<Box<Expr>>)> {
        self.bump();
        let (args, _) =
            self.with_ns(false, |p| p.comma_list(&T::RParen, "`)` after arguments", Self::arg))?;
        let trailing = if !self.no_struct && self.at(&T::LBrace) && !self.peek().starts_line {
            let block = self.block("`{`")?;
            let span = block.span;
            let body = Box::new(Expr { kind: ExprKind::Block(block), span });
            Some(Box::new(Expr { kind: ExprKind::Closure { params: Vec::new(), body }, span }))
        } else {
            None
        };
        Ok((args, trailing))
    }

    fn arg(&mut self) -> PResult<Arg> {
        let name = if self.at_any_name() && self.kind_at(1) == &T::Colon {
            let n = self.ident();
            self.bump();
            Some(n)
        } else {
            None
        };
        Ok(Arg { name, value: self.expr()? })
    }

    fn primary(&mut self) -> PResult<Expr> {
        let lo = self.lo();
        let kind = match self.kind() {
            T::Int(v) => {
                let lit = Lit::Int(*v);
                self.bump();
                ExprKind::Lit(lit)
            }
            T::Str(_) => ExprKind::Lit(self.str_lit()?),
            T::True => {
                self.bump();
                ExprKind::Lit(Lit::Bool(true))
            }
            T::False => {
                self.bump();
                ExprKind::Lit(Lit::Bool(false))
            }
            T::SelfValue => ExprKind::Name(Ident::new("self", self.bump())),
            T::SelfType => ExprKind::Name(Ident::new("Self", self.bump())),
            T::Name(n) => {
                let is_handle = n == "handle"
                    && matches!(self.kind_at(1), T::Name(_))
                    && self.kind_at(2) == &T::LBrace;
                let is_scope = n == "scope" && self.kind_at(1) == &T::LBrace;
                let is_struct = is_upper(n) && !self.no_struct && self.struct_lit_ahead();
                if is_handle {
                    return self.handle_expr();
                }
                if is_scope {
                    return self.scope_expr();
                }
                if is_struct {
                    return self.struct_lit();
                }
                ExprKind::Name(self.ident())
            }
            T::LParen => return self.paren(),
            T::LBracket => {
                self.bump();
                let (items, _) =
                    self.with_ns(false, |p| p.comma_list(&T::RBracket, "`,` or `]`", Self::expr))?;
                ExprKind::Array(items)
            }
            T::LBrace => ExprKind::Block(self.block("`{`")?),
            T::Pipe | T::OrOr => return self.closure(),
            T::If => return self.if_expr(),
            T::Match => return self.match_expr(),
            _ => return Err(self.expected("an expression")),
        };
        Ok(Expr { kind, span: Span::new(lo, self.last_hi) })
    }

    /// True if a struct literal starts here: `Name {` or `A.B {`, then `NAME :` or `}`.
    fn struct_lit_ahead(&self) -> bool {
        let at = if self.kind_at(1) == &T::Dot && matches!(self.kind_at(2), T::Name(m) if is_upper(m)) {
            3
        } else {
            1
        };
        self.kind_at(at) == &T::LBrace
            && (self.kind_at(at + 1) == &T::RBrace
                || (matches!(self.kind_at(at + 1), T::Name(_)) && self.kind_at(at + 2) == &T::Colon))
    }

    fn struct_lit(&mut self) -> PResult<Expr> {
        let lo = self.lo();
        let mut path = vec![self.ident()];
        if self.eat(&T::Dot) {
            path.push(self.ident());
        }
        self.bump();
        let fields = self.with_ns(false, |p| {
            p.brace_list("`,`, a line break or `}` after the field", |p| {
                let name = p.name("a field name")?;
                p.expect(&T::Colon, "`:` after the field name")?;
                Ok((name, p.expr()?))
            })
        })?;
        Ok(Expr { kind: ExprKind::StructLit { path, fields }, span: Span::new(lo, self.last_hi) })
    }

    /// Parses `()`, `(e)` or a tuple. The current token is `(`.
    fn paren(&mut self) -> PResult<Expr> {
        let lo = self.lo();
        self.bump();
        let (mut items, trailing) =
            self.with_ns(false, |p| p.comma_list(&T::RParen, "`,` or `)`", Self::expr))?;
        let span = Span::new(lo, self.last_hi);
        if items.is_empty() {
            return Ok(Expr { kind: ExprKind::Lit(Lit::Unit), span });
        }
        if items.len() == 1 && !trailing {
            if let Some(mut only) = items.pop() {
                only.span = span;
                return Ok(only);
            }
        }
        Ok(Expr { kind: ExprKind::Tuple(items), span })
    }

    /// Parses `|params| body` or `|| body`.
    ///
    /// An assignment body, as in `|| x += 1`, becomes a block with one statement.
    fn closure(&mut self) -> PResult<Expr> {
        let lo = self.lo();
        let params = if self.eat(&T::OrOr) {
            Vec::new()
        } else {
            self.bump();
            self.params(&T::Pipe, "`,` or `|` after a closure parameter")?
        };
        let mut body = self.expr()?;
        if let Some(op) = assign_op(self.kind()) {
            self.bump();
            let value = self.expr()?;
            let span = body.span.to(value.span);
            let stmt = Stmt { kind: StmtKind::Assign { target: body, op, value }, span };
            body = Expr { kind: ExprKind::Block(Block { stmts: vec![stmt], span }), span };
        }
        Ok(Expr { span: Span::new(lo, body.span.hi), kind: ExprKind::Closure { params, body: Box::new(body) } })
    }

    /// Parses an `if` chain. It loops over `else if`, so a long chain does not recurse.
    fn if_expr(&mut self) -> PResult<Expr> {
        let saved = self.depth;
        let mut links = Vec::new();
        let mut last_else = None;
        loop {
            let lo = self.bump().lo;
            let cond = self.with_ns(true, Self::expr)?;
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
            last_else = Some(Box::new(Expr { span: b.span, kind: ExprKind::Block(b) }));
            break;
        }
        self.depth = saved;
        let hi = self.last_hi;
        let mut result: Option<Expr> = None;
        for (lo, cond, then) in links.into_iter().rev() {
            let else_ = result.take().map(Box::new).or_else(|| last_else.take());
            let kind = ExprKind::If { cond: Box::new(cond), then, else_ };
            result = Some(Expr { kind, span: Span::new(lo, hi) });
        }
        result.ok_or_else(|| self.expected("`if`"))
    }

    /// Parses a `match`. The current token is `match`.
    fn match_expr(&mut self) -> PResult<Expr> {
        let lo = self.lo();
        self.bump();
        let scrutinee = self.with_ns(true, Self::expr)?;
        self.expect(&T::LBrace, "`{` after the `match` value")?;
        let arms = self.with_ns(false, |p| {
            p.brace_list("`,`, a line break or `}` after the match arm", |p| {
                let pat = p.pattern()?;
                p.expect(&T::FatArrow, "`=>` after the pattern")?;
                let body = p.expr()?;
                Ok(Arm { span: pat.span().to(body.span), pat, body })
            })
        })?;
        let kind = ExprKind::Match { scrutinee: Box::new(scrutinee), arms };
        Ok(Expr { kind, span: Span::new(lo, self.last_hi) })
    }

    /// Parses `handle E { clauses } in expr`. The current tokens are `handle E {`.
    fn handle_expr(&mut self) -> PResult<Expr> {
        let lo = self.lo();
        self.bump();
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
            if !self.at(&T::Fn) {
                return Err(self.expected("`fn` to start a handler clause"));
            }
            let clause_lo = self.bump().lo;
            let op = self.name("the operation name")?;
            self.expect(&T::LParen, "`(` after the operation name")?;
            let params = self.params(&T::RParen, "`,` or `)` after a parameter")?;
            let body = self.block("`{` to start the handler clause body")?;
            clauses.push(HandlerClause { op, params, body, span: Span::new(clause_lo, self.last_hi) });
        }
        if !self.skip_ends_before(|k| k == &T::In) {
            return Err(self.expected("`in` after the handler"));
        }
        self.bump();
        let body = self.expr()?;
        let span = Span::new(lo, body.span.hi);
        Ok(Expr { kind: ExprKind::Handle { effect, clauses, body: Box::new(body) }, span })
    }

    /// Parses `scope { s => stmts }`. The current tokens are `scope {`.
    fn scope_expr(&mut self) -> PResult<Expr> {
        let lo = self.lo();
        self.bump();
        let brace = self.bump().lo;
        self.skip_newlines();
        let binder = self.name("the scope name after `scope {`")?;
        self.expect(&T::FatArrow, "`=>` after the scope name")?;
        let body = self.block_rest(brace)?;
        Ok(Expr { kind: ExprKind::Scope { binder, body }, span: Span::new(lo, self.last_hi) })
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

    fn interp(&self, src: &str, offset: u32) -> PResult<Expr> {
        if src.trim().is_empty() {
            let len = u32::try_from(src.len()).unwrap_or(u32::MAX);
            let span = Span::new(offset.saturating_sub(1), offset.saturating_add(len).saturating_add(1));
            return Err(ParseError::new(
                "empty interpolation `{}` in a string; write `\\{` for a literal brace",
                span,
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

const fn cmp_op(k: &T) -> Option<BinOp> {
    match k {
        T::EqEq => Some(BinOp::Eq),
        T::Ne => Some(BinOp::Ne),
        T::Lt => Some(BinOp::Lt),
        T::Le => Some(BinOp::Le),
        T::Gt => Some(BinOp::Gt),
        T::Ge => Some(BinOp::Ge),
        _ => None,
    }
}

fn binary(op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
    Expr { span: lhs.span.to(rhs.span), kind: ExprKind::Binary { op, lhs: Box::new(lhs), rhs: Box::new(rhs) } }
}
