//! Lexer with automatic statement ends. See `docs/grammar.md`.
//!
//! [`lex`] turns source text into [`Token`]s. It inserts [`TokenKind::Newline`]
//! tokens by the automatic statement-end rules. A string literal keeps the raw
//! source of each `{expr}` interpolation, so that the parser can parse it.

use std::fmt;

use crate::ast::Span;
use crate::parser::ParseError;

/// One part of a string literal token.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StrPiece {
    /// Plain text. The escapes are decoded.
    Text(String),
    /// The raw source of an `{expr}` interpolation.
    Interp {
        /// The text between the braces.
        src: String,
        /// The byte offset of `src` in the full source.
        offset: u32,
    },
}

/// The kinds of token.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    /// A name. Contextual keywords such as `handle` are names too.
    Name(String),
    /// An integer literal.
    Int(u64),
    /// A string literal.
    Str(Vec<StrPiece>),
    /// `fn`
    Fn,
    /// `let`
    Let,
    /// `if`
    If,
    /// `else`
    Else,
    /// `while`
    While,
    /// `for`
    For,
    /// `in`
    In,
    /// `loop`
    Loop,
    /// `break`
    Break,
    /// `continue`
    Continue,
    /// `return`
    Return,
    /// `match`
    Match,
    /// `struct`
    Struct,
    /// `enum`
    Enum,
    /// `effect`
    Effect,
    /// `impl`
    Impl,
    /// `mod`
    Mod,
    /// `pub`
    Pub,
    /// `extern`
    Extern,
    /// `true`
    True,
    /// `false`
    False,
    /// `self`
    SelfValue,
    /// `Self`
    SelfType,
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `[`
    LBracket,
    /// `]`
    RBracket,
    /// `{`
    LBrace,
    /// `}`
    RBrace,
    /// `,`
    Comma,
    /// `;`
    Semi,
    /// `:`
    Colon,
    /// `.`
    Dot,
    /// `..`
    DotDot,
    /// `->`
    Arrow,
    /// `=>`
    FatArrow,
    /// `=`
    Eq,
    /// `==`
    EqEq,
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
    /// `+`
    Plus,
    /// `-`
    Minus,
    /// `*`
    Star,
    /// `/`
    Slash,
    /// `%`
    Percent,
    /// `!`
    Bang,
    /// `&`
    Amp,
    /// `&&`
    AndAnd,
    /// `|`
    Pipe,
    /// `||`
    OrOr,
    /// `+=`
    PlusEq,
    /// `-=`
    MinusEq,
    /// `*=`
    StarEq,
    /// `@`
    At,
    /// An automatic statement end at a line break.
    Newline,
    /// The end of the input.
    Eof,
}

impl TokenKind {
    /// Returns the fixed text of a keyword or punctuation token.
    /// Returns `None` for names, literals, `Newline` and `Eof`.
    pub const fn fixed_text(&self) -> Option<&'static str> {
        Some(match self {
            Self::Fn => "fn",
            Self::Let => "let",
            Self::If => "if",
            Self::Else => "else",
            Self::While => "while",
            Self::For => "for",
            Self::In => "in",
            Self::Loop => "loop",
            Self::Break => "break",
            Self::Continue => "continue",
            Self::Return => "return",
            Self::Match => "match",
            Self::Struct => "struct",
            Self::Enum => "enum",
            Self::Effect => "effect",
            Self::Impl => "impl",
            Self::Mod => "mod",
            Self::Pub => "pub",
            Self::Extern => "extern",
            Self::True => "true",
            Self::False => "false",
            Self::SelfValue => "self",
            Self::SelfType => "Self",
            Self::LParen => "(",
            Self::RParen => ")",
            Self::LBracket => "[",
            Self::RBracket => "]",
            Self::LBrace => "{",
            Self::RBrace => "}",
            Self::Comma => ",",
            Self::Semi => ";",
            Self::Colon => ":",
            Self::Dot => ".",
            Self::DotDot => "..",
            Self::Arrow => "->",
            Self::FatArrow => "=>",
            Self::Eq => "=",
            Self::EqEq => "==",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Star => "*",
            Self::Slash => "/",
            Self::Percent => "%",
            Self::Bang => "!",
            Self::Amp => "&",
            Self::AndAnd => "&&",
            Self::Pipe => "|",
            Self::OrOr => "||",
            Self::PlusEq => "+=",
            Self::MinusEq => "-=",
            Self::StarEq => "*=",
            Self::At => "@",
            Self::Name(_) | Self::Int(_) | Self::Str(_) | Self::Newline | Self::Eof => return None,
        })
    }

    /// Describes the token for an error message, for example `` `{` `` or "end of line".
    pub fn describe(&self) -> String {
        match self {
            Self::Name(n) => format!("`{n}`"),
            Self::Int(v) => format!("`{v}`"),
            Self::Str(_) => "a string".into(),
            Self::Newline => "end of line".into(),
            Self::Eof => "end of file".into(),
            other => format!("`{other}`"),
        }
    }

    /// Returns true if a line break after this token can end a statement (rule 1).
    pub const fn can_end_statement(&self) -> bool {
        matches!(
            self,
            Self::Name(_)
                | Self::Int(_)
                | Self::Str(_)
                | Self::RParen
                | Self::RBracket
                | Self::RBrace
                | Self::Return
                | Self::Break
                | Self::Continue
                | Self::True
                | Self::False
                | Self::SelfValue
                | Self::SelfType
        )
    }
}

impl fmt::Display for TokenKind {
    /// Writes the token in source form. `Newline` is `NL` and `Eof` is `EOF`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Name(n) => f.write_str(n),
            Self::Int(v) => write!(f, "{v}"),
            Self::Str(pieces) => {
                f.write_str("\"")?;
                for p in pieces {
                    match p {
                        StrPiece::Text(t) => f.write_str(&escape_text(t))?,
                        StrPiece::Interp { src, .. } => write!(f, "{{{src}}}")?,
                    }
                }
                f.write_str("\"")
            }
            Self::Newline => f.write_str("NL"),
            Self::Eof => f.write_str("EOF"),
            other => f.write_str(other.fixed_text().unwrap_or("?")),
        }
    }
}

/// Escapes text for a string literal: `\n`, `\t`, `\\`, `\"`, `\{` and `\}`.
pub fn escape_text(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '{' => out.push_str("\\{"),
            '}' => out.push_str("\\}"),
            c => out.push(c),
        }
    }
    out
}

/// A token with its location.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    /// The kind of token.
    pub kind: TokenKind,
    /// The location in the source.
    pub span: Span,
    /// True if a line break comes between the previous token and this one.
    pub starts_line: bool,
}

/// Lexes a full source file. The last token is [`TokenKind::Eof`].
pub fn lex(src: &str) -> Result<Vec<Token>, ParseError> {
    lex_at(src, 0)
}

/// Lexes `src` as if it starts at byte offset `base` of a larger source.
///
/// The parser uses this for string interpolations, so that spans stay absolute.
pub fn lex_at(src: &str, base: u32) -> Result<Vec<Token>, ParseError> {
    let fits = u32::try_from(src.len()).ok().and_then(|n| base.checked_add(n)).is_some();
    if !fits {
        return Err(ParseError::new("the source text is too large", Span::new(base, base)));
    }
    let mut lx = Lexer { src, bytes: src.as_bytes(), pos: 0, base, toks: Vec::new() };
    lx.run()?;
    Ok(insert_newlines(src, base, lx.toks))
}

/// The modes of the scanner that finds the end of an interpolation.
enum Nest {
    /// Inside `{ ... }`, with the count of open inner braces.
    Interp(u32),
    /// Inside a nested string literal.
    Str,
}

struct Lexer<'a> {
    src: &'a str,
    bytes: &'a [u8],
    pos: usize,
    base: u32,
    toks: Vec<Token>,
}

impl Lexer<'_> {
    fn span(&self, lo: usize, hi: usize) -> Span {
        let at = |i: usize| self.base.saturating_add(u32::try_from(i).unwrap_or(u32::MAX));
        Span::new(at(lo), at(hi))
    }

    fn byte(&self, i: usize) -> Option<u8> {
        self.bytes.get(i).copied()
    }

    fn char_at(&self, i: usize) -> Option<char> {
        self.src.get(i..).and_then(|s| s.chars().next())
    }

    fn run(&mut self) -> Result<(), ParseError> {
        loop {
            let starts_line = self.skip_trivia();
            let lo = self.pos;
            let Some(b) = self.byte(lo) else {
                let span = self.span(lo, lo);
                self.toks.push(Token { kind: TokenKind::Eof, span, starts_line });
                return Ok(());
            };
            let kind = match b {
                b'a'..=b'z' | b'A'..=b'Z' | b'_' => self.word(),
                b'0'..=b'9' => self.int()?,
                b'"' => self.string()?,
                _ => self.punct()?,
            };
            let span = self.span(lo, self.pos);
            self.toks.push(Token { kind, span, starts_line });
        }
    }

    /// Skips spaces and comments. Returns true if it skips a line break.
    fn skip_trivia(&mut self) -> bool {
        let mut saw_newline = false;
        loop {
            match self.byte(self.pos) {
                Some(b'\n') => {
                    saw_newline = true;
                    self.pos += 1;
                }
                Some(b' ' | b'\t' | b'\r') => self.pos += 1,
                Some(b'/') if self.byte(self.pos + 1) == Some(b'/') => {
                    while self.byte(self.pos).is_some_and(|b| b != b'\n') {
                        self.pos += 1;
                    }
                }
                _ => return saw_newline,
            }
        }
    }

    fn word(&mut self) -> TokenKind {
        let lo = self.pos;
        while self.byte(self.pos).is_some_and(|b| b.is_ascii_alphanumeric() || b == b'_') {
            self.pos += 1;
        }
        let text = self.src.get(lo..self.pos).unwrap_or_default();
        keyword(text).unwrap_or_else(|| TokenKind::Name(text.to_owned()))
    }

    fn int(&mut self) -> Result<TokenKind, ParseError> {
        let lo = self.pos;
        let mut value: Option<u64> = Some(0);
        while let Some(b) = self.byte(self.pos) {
            match b {
                b'0'..=b'9' => {
                    value = value
                        .and_then(|v| v.checked_mul(10))
                        .and_then(|v| v.checked_add(u64::from(b - b'0')));
                }
                b'_' => {}
                _ => break,
            }
            self.pos += 1;
        }
        value.map(TokenKind::Int).ok_or_else(|| {
            ParseError::new("the integer literal is too large", self.span(lo, self.pos))
        })
    }

    fn punct(&mut self) -> Result<TokenKind, ParseError> {
        use TokenKind as T;
        let lo = self.pos;
        let next = self.byte(lo + 1);
        let (kind, len) = match (self.byte(lo).unwrap_or_default(), next) {
            (b'(', _) => (T::LParen, 1),
            (b')', _) => (T::RParen, 1),
            (b'[', _) => (T::LBracket, 1),
            (b']', _) => (T::RBracket, 1),
            (b'{', _) => (T::LBrace, 1),
            (b'}', _) => (T::RBrace, 1),
            (b',', _) => (T::Comma, 1),
            (b';', _) => (T::Semi, 1),
            (b':', _) => (T::Colon, 1),
            (b'@', _) => (T::At, 1),
            (b'%', _) => (T::Percent, 1),
            (b'/', _) => (T::Slash, 1),
            (b'.', Some(b'.')) => (T::DotDot, 2),
            (b'.', _) => (T::Dot, 1),
            (b'-', Some(b'>')) => (T::Arrow, 2),
            (b'-', Some(b'=')) => (T::MinusEq, 2),
            (b'-', _) => (T::Minus, 1),
            (b'=', Some(b'=')) => (T::EqEq, 2),
            (b'=', Some(b'>')) => (T::FatArrow, 2),
            (b'=', _) => (T::Eq, 1),
            (b'!', Some(b'=')) => (T::Ne, 2),
            (b'!', _) => (T::Bang, 1),
            (b'<', Some(b'=')) => (T::Le, 2),
            (b'<', _) => (T::Lt, 1),
            (b'>', Some(b'=')) => (T::Ge, 2),
            (b'>', _) => (T::Gt, 1),
            (b'+', Some(b'=')) => (T::PlusEq, 2),
            (b'+', _) => (T::Plus, 1),
            (b'*', Some(b'=')) => (T::StarEq, 2),
            (b'*', _) => (T::Star, 1),
            (b'&', Some(b'&')) => (T::AndAnd, 2),
            (b'&', _) => (T::Amp, 1),
            (b'|', Some(b'|')) => (T::OrOr, 2),
            (b'|', _) => (T::Pipe, 1),
            _ => {
                let c = self.char_at(lo).unwrap_or('\u{fffd}');
                let span = self.span(lo, lo + c.len_utf8());
                return Err(ParseError::new(
                    format!("unexpected character `{}`", c.escape_debug()),
                    span,
                ));
            }
        };
        self.pos += len;
        Ok(kind)
    }

    /// Lexes a string literal. The current byte is the opening quote.
    fn string(&mut self) -> Result<TokenKind, ParseError> {
        let lo = self.pos;
        self.pos += 1;
        let mut pieces = Vec::new();
        let mut text = String::new();
        loop {
            match self.byte(self.pos) {
                None | Some(b'\n') => {
                    return Err(ParseError::new(
                        "the string literal is not closed",
                        self.span(lo, self.pos),
                    ));
                }
                Some(b'"') => {
                    self.pos += 1;
                    break;
                }
                Some(b'\\') => {
                    let decoded = match self.byte(self.pos + 1) {
                        None | Some(b'\n') => {
                            return Err(ParseError::new(
                                "the string literal is not closed",
                                self.span(lo, self.pos + 1),
                            ));
                        }
                        Some(b'n') => '\n',
                        Some(b't') => '\t',
                        Some(b'\\') => '\\',
                        Some(b'"') => '"',
                        Some(b'{') => '{',
                        Some(b'}') => '}',
                        Some(_) => {
                            let c = self.char_at(self.pos + 1).unwrap_or('\u{fffd}');
                            let span = self.span(self.pos, self.pos + 1 + c.len_utf8());
                            return Err(ParseError::new(
                                format!(
                                    "unknown escape `\\{}`; use \\n, \\t, \\\\, \\\", \\{{ or \\}}",
                                    c.escape_debug()
                                ),
                                span,
                            ));
                        }
                    };
                    text.push(decoded);
                    self.pos += 2;
                }
                Some(b'{') => {
                    if !text.is_empty() {
                        pieces.push(StrPiece::Text(std::mem::take(&mut text)));
                    }
                    let start = self.pos + 1;
                    let end = self.interp_end(start)?;
                    let src = self.src.get(start..end).unwrap_or_default().to_owned();
                    pieces.push(StrPiece::Interp { src, offset: self.span(start, start).lo });
                    self.pos = end + 1;
                }
                Some(_) => {
                    let c = self.char_at(self.pos).unwrap_or('\u{fffd}');
                    text.push(c);
                    self.pos += c.len_utf8().max(1);
                }
            }
        }
        if !text.is_empty() {
            pieces.push(StrPiece::Text(text));
        }
        Ok(TokenKind::Str(pieces))
    }

    /// Finds the `}` that closes an interpolation that starts at `start`.
    ///
    /// It skips nested braces and nested string literals. It does not recurse.
    fn interp_end(&self, start: usize) -> Result<usize, ParseError> {
        let mut stack = vec![Nest::Interp(0)];
        let mut i = start;
        loop {
            let Some(b) = self.byte(i).filter(|&b| b != b'\n') else {
                return Err(ParseError::new(
                    "the interpolation in this string is not closed; add `}`",
                    self.span(start.saturating_sub(1), i),
                ));
            };
            if let Some(Nest::Interp(depth)) = stack.last_mut() {
                match b {
                    b'"' => stack.push(Nest::Str),
                    b'{' => *depth += 1,
                    b'}' if *depth == 0 => {
                        stack.pop();
                        if stack.is_empty() {
                            return Ok(i);
                        }
                    }
                    b'}' => *depth -= 1,
                    _ => {}
                }
            } else {
                match b {
                    b'\\' if self.byte(i + 1) != Some(b'\n') => i += 1,
                    b'"' => {
                        stack.pop();
                    }
                    b'{' => stack.push(Nest::Interp(0)),
                    _ => {}
                }
            }
            i += 1;
        }
    }
}

fn keyword(s: &str) -> Option<TokenKind> {
    use TokenKind as T;
    Some(match s {
        "fn" => T::Fn,
        "let" => T::Let,
        "if" => T::If,
        "else" => T::Else,
        "while" => T::While,
        "for" => T::For,
        "in" => T::In,
        "loop" => T::Loop,
        "break" => T::Break,
        "continue" => T::Continue,
        "return" => T::Return,
        "match" => T::Match,
        "struct" => T::Struct,
        "enum" => T::Enum,
        "effect" => T::Effect,
        "impl" => T::Impl,
        "mod" => T::Mod,
        "pub" => T::Pub,
        "extern" => T::Extern,
        "true" => T::True,
        "false" => T::False,
        "self" => T::SelfValue,
        "Self" => T::SelfType,
        _ => return None,
    })
}

/// Inserts `Newline` tokens by the automatic statement-end rules.
///
/// A line break before token `t` gives a `Newline` when:
/// 1. the previous token can end a statement,
/// 2. the innermost open bracket is not `(` or `[`, and
/// 3. `t` is not a `.` that a name on the same line follows.
fn insert_newlines(src: &str, base: u32, raw: Vec<Token>) -> Vec<Token> {
    let mut out: Vec<Token> = Vec::with_capacity(raw.len() + raw.len() / 4);
    let mut open: Vec<u8> = Vec::new();
    let mut it = raw.into_iter().peekable();
    while let Some(tok) = it.next() {
        if tok.starts_line {
            let chain = tok.kind == TokenKind::Dot
                && it
                    .peek()
                    .is_some_and(|n| matches!(n.kind, TokenKind::Name(_)) && !n.starts_line);
            let in_parens = matches!(open.last(), Some(b'(' | b'['));
            if let Some(prev) = out.last() {
                if prev.kind.can_end_statement() && !in_parens && !chain {
                    let span = newline_span(src, base, prev.span.hi);
                    out.push(Token { kind: TokenKind::Newline, span, starts_line: false });
                }
            }
        }
        match tok.kind {
            TokenKind::LParen => open.push(b'('),
            TokenKind::LBracket => open.push(b'['),
            TokenKind::LBrace => open.push(b'{'),
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                open.pop();
            }
            _ => {}
        }
        out.push(tok);
    }
    out
}

/// Returns the span of the first line break at or after absolute offset `from`.
fn newline_span(src: &str, base: u32, from: u32) -> Span {
    let start = from.saturating_sub(base) as usize;
    let found = src.as_bytes().get(start..).and_then(|rest| rest.iter().position(|&b| b == b'\n'));
    found.map_or(Span::new(from, from), |i| {
        let lo = from.saturating_add(u32::try_from(i).unwrap_or(u32::MAX));
        Span::new(lo, lo.saturating_add(1))
    })
}
