//! The lexer and the parser.
//!
//! Grammar:
//!
//! ```text
//! program := clause*
//! clause  := atom "." | atom ":-" literal ("," literal)* "."
//! literal := atom | "!" atom | term ("=" | "!=") term
//! atom    := name | name "(" [term ("," term)*] ")"
//! term    := Variable | "_" | integer | string | name
//! ```
//!
//! A line comment starts with `//`.

use std::sync::Arc;

use crate::ast::{Atom, CmpOp, Const, Fact, Literal, Program, Rule, Term};
use crate::error::{Error, Location};

/// Parses a program and checks it.
///
/// The checks are arity, range restriction and stratification. Error
/// locations have line numbers.
///
/// # Examples
///
/// ```
/// let program = weft_datalog::parse_program("path(X, Y) :- edge(X, Y).")?;
/// assert_eq!(program.rules().len(), 1);
/// # Ok::<(), weft_datalog::Error>(())
/// ```
pub fn parse_program(src: &str) -> Result<Program, Error> {
    parse_program_named("", src)
}

/// Parses a program and checks it. Error locations name `origin`, for
/// example a file name.
pub fn parse_program_named(origin: &str, src: &str) -> Result<Program, Error> {
    let program = parse_unchecked(origin, src)?;
    program.check()?;
    Ok(program)
}

/// Parses a program. It does not do the checks.
pub fn parse_unchecked(origin: &str, src: &str) -> Result<Program, Error> {
    let origin: Arc<str> = Arc::from(origin);
    let tokens = lex(src, &origin)?;
    Parser {
        tokens,
        pos: 0,
        origin,
    }
    .program()
}

/// Parses a list of facts. A rule is an error.
pub fn parse_facts(src: &str) -> Result<Vec<Fact>, Error> {
    let program = parse_unchecked("", src)?;
    if let Some(rule) = program.rules.first() {
        return Err(Error::Syntax {
            loc: rule.loc.clone(),
            column: 1,
            message: "input facts cannot contain rules".to_string(),
        });
    }
    Ok(program.facts)
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Var(String),
    Wildcard,
    Int(i64),
    Str(String),
    LParen,
    RParen,
    Comma,
    Dot,
    If,
    Bang,
    Eq,
    Ne,
    Eof,
}

impl Tok {
    fn describe(&self) -> String {
        match self {
            Self::Ident(s) | Self::Var(s) => format!("`{s}`"),
            Self::Wildcard => "`_`".to_string(),
            Self::Int(i) => format!("`{i}`"),
            Self::Str(_) => "a string".to_string(),
            Self::LParen => "`(`".to_string(),
            Self::RParen => "`)`".to_string(),
            Self::Comma => "`,`".to_string(),
            Self::Dot => "`.`".to_string(),
            Self::If => "`:-`".to_string(),
            Self::Bang => "`!`".to_string(),
            Self::Eq => "`=`".to_string(),
            Self::Ne => "`!=`".to_string(),
            Self::Eof => "end of input".to_string(),
        }
    }
}

#[derive(Clone, Debug)]
struct Token {
    tok: Tok,
    line: usize,
    column: usize,
}

/// Splits `src` into tokens. The last token is [`Tok::Eof`].
fn lex(src: &str, origin: &Arc<str>) -> Result<Vec<Token>, Error> {
    let chars: Vec<char> = src.chars().collect();
    let mut lexer = Lexer {
        chars: &chars,
        i: 0,
        line: 1,
        column: 1,
        origin,
    };
    let mut tokens = Vec::new();
    loop {
        lexer.skip_blank();
        let (line, column) = (lexer.line, lexer.column);
        let Some(c) = lexer.peek(0) else {
            tokens.push(Token {
                tok: Tok::Eof,
                line,
                column,
            });
            return Ok(tokens);
        };
        let tok = match c {
            '(' => lexer.single(Tok::LParen),
            ')' => lexer.single(Tok::RParen),
            ',' => lexer.single(Tok::Comma),
            '.' => lexer.single(Tok::Dot),
            '=' => lexer.single(Tok::Eq),
            '!' if lexer.peek(1) == Some('=') => lexer.double(Tok::Ne),
            '!' => lexer.single(Tok::Bang),
            ':' if lexer.peek(1) == Some('-') => lexer.double(Tok::If),
            ':' => return Err(lexer.error(line, column, "expected `:-`".to_string())),
            '-' | '0'..='9' => lexer.number()?,
            '"' => lexer.string()?,
            c if c.is_ascii_alphabetic() || c == '_' => lexer.word(),
            c => {
                return Err(lexer.error(line, column, format!("unexpected character `{c}`")));
            }
        };
        tokens.push(Token { tok, line, column });
    }
}

struct Lexer<'a> {
    chars: &'a [char],
    i: usize,
    line: usize,
    column: usize,
    origin: &'a Arc<str>,
}

impl Lexer<'_> {
    fn peek(&self, ahead: usize) -> Option<char> {
        self.chars.get(self.i + ahead).copied()
    }

    fn advance(&mut self) -> Option<char> {
        let c = self.peek(0)?;
        self.i += 1;
        if c == '\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }
        Some(c)
    }

    fn error(&self, line: usize, column: usize, message: String) -> Error {
        Error::Syntax {
            loc: Location {
                origin: Arc::clone(self.origin),
                line,
            },
            column,
            message,
        }
    }

    fn skip_blank(&mut self) {
        while let Some(c) = self.peek(0) {
            if c.is_whitespace() {
                self.advance();
            } else if c == '/' && self.peek(1) == Some('/') {
                while self.peek(0).is_some_and(|c| c != '\n') {
                    self.advance();
                }
            } else {
                break;
            }
        }
    }

    fn single(&mut self, tok: Tok) -> Tok {
        self.advance();
        tok
    }

    fn double(&mut self, tok: Tok) -> Tok {
        self.advance();
        self.advance();
        tok
    }

    fn number(&mut self) -> Result<Tok, Error> {
        let (line, column) = (self.line, self.column);
        let mut text = String::new();
        if self.peek(0) == Some('-') {
            text.push('-');
            self.advance();
            if !self.peek(0).is_some_and(|c| c.is_ascii_digit()) {
                return Err(self.error(line, column, "expected a digit after `-`".to_string()));
            }
        }
        while let Some(c) = self.peek(0).filter(char::is_ascii_digit) {
            text.push(c);
            self.advance();
        }
        text.parse().map(Tok::Int).map_err(|_| {
            self.error(
                line,
                column,
                format!("integer `{text}` is out of the 64-bit range"),
            )
        })
    }

    fn string(&mut self) -> Result<Tok, Error> {
        let (line, column) = (self.line, self.column);
        let unterminated =
            |lexer: &Self| lexer.error(line, column, "unterminated string".to_string());
        self.advance();
        let mut text = String::new();
        loop {
            match self.peek(0) {
                None | Some('\n') => return Err(unterminated(self)),
                Some('"') => {
                    self.advance();
                    return Ok(Tok::Str(text));
                }
                Some('\\') => {
                    let (esc_line, esc_column) = (self.line, self.column);
                    self.advance();
                    let c = match self.advance() {
                        None => return Err(unterminated(self)),
                        Some('n') => '\n',
                        Some('t') => '\t',
                        Some('r') => '\r',
                        Some(c @ ('"' | '\\')) => c,
                        Some(c) => {
                            return Err(self.error(
                                esc_line,
                                esc_column,
                                format!("unknown escape `\\{c}` in string"),
                            ));
                        }
                    };
                    text.push(c);
                }
                Some(c) => {
                    text.push(c);
                    self.advance();
                }
            }
        }
    }

    fn word(&mut self) -> Tok {
        let mut text = String::new();
        while let Some(c) = self
            .peek(0)
            .filter(|c| c.is_ascii_alphanumeric() || *c == '_')
        {
            text.push(c);
            self.advance();
        }
        if text == "_" {
            Tok::Wildcard
        } else if text.starts_with(|c: char| c.is_ascii_lowercase()) {
            Tok::Ident(text)
        } else {
            Tok::Var(text)
        }
    }
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    origin: Arc<str>,
}

impl Parser {
    fn peek(&self) -> &Token {
        &self.tokens[self.pos.min(self.tokens.len() - 1)]
    }

    fn peek_second(&self) -> &Tok {
        &self.tokens[(self.pos + 1).min(self.tokens.len() - 1)].tok
    }

    fn bump(&mut self) {
        if self.pos + 1 < self.tokens.len() {
            self.pos += 1;
        }
    }

    fn loc(&self, line: usize) -> Location {
        Location {
            origin: Arc::clone(&self.origin),
            line,
        }
    }

    fn expected(&self, what: &str) -> Error {
        let t = self.peek();
        Error::Syntax {
            loc: self.loc(t.line),
            column: t.column,
            message: format!("expected {what}, found {}", t.tok.describe()),
        }
    }

    fn program(mut self) -> Result<Program, Error> {
        let mut program = Program::default();
        while self.peek().tok != Tok::Eof {
            self.clause(&mut program)?;
        }
        Ok(program)
    }

    fn clause(&mut self, program: &mut Program) -> Result<(), Error> {
        let loc = self.loc(self.peek().line);
        let head = self.atom()?;
        match self.peek().tok {
            Tok::Dot => {
                self.bump();
                program.facts.push(into_fact(head, loc)?);
                Ok(())
            }
            Tok::If => {
                self.bump();
                let mut body = Vec::new();
                loop {
                    body.push(self.literal()?);
                    match self.peek().tok {
                        Tok::Comma => self.bump(),
                        Tok::Dot => {
                            self.bump();
                            break;
                        }
                        _ => return Err(self.expected("`,` or `.`")),
                    }
                }
                program.rules.push(Rule { head, body, loc });
                Ok(())
            }
            _ => Err(self.expected("`.` or `:-`")),
        }
    }

    fn atom(&mut self) -> Result<Atom, Error> {
        let Tok::Ident(name) = &self.peek().tok else {
            return Err(self.expected("a relation name"));
        };
        let relation = name.clone();
        self.bump();
        let mut terms = Vec::new();
        if self.peek().tok == Tok::LParen {
            self.bump();
            if self.peek().tok == Tok::RParen {
                self.bump();
            } else {
                loop {
                    terms.push(self.term()?);
                    match self.peek().tok {
                        Tok::Comma => self.bump(),
                        Tok::RParen => {
                            self.bump();
                            break;
                        }
                        _ => return Err(self.expected("`,` or `)`")),
                    }
                }
            }
        }
        Ok(Atom { relation, terms })
    }

    fn term(&mut self) -> Result<Term, Error> {
        let term = match &self.peek().tok {
            Tok::Var(v) => Term::Var(v.clone()),
            Tok::Wildcard => Term::Wildcard,
            Tok::Int(i) => Term::Const(Const::Int(*i)),
            Tok::Str(s) | Tok::Ident(s) => Term::Const(Const::Sym(s.clone())),
            _ => return Err(self.expected("a term")),
        };
        self.bump();
        Ok(term)
    }

    fn literal(&mut self) -> Result<Literal, Error> {
        match &self.peek().tok {
            Tok::Bang => {
                self.bump();
                Ok(Literal::Neg(self.atom()?))
            }
            Tok::Ident(_) if !matches!(self.peek_second(), Tok::Eq | Tok::Ne) => {
                Ok(Literal::Pos(self.atom()?))
            }
            _ => {
                let left = self.term()?;
                let op = match self.peek().tok {
                    Tok::Eq => CmpOp::Eq,
                    Tok::Ne => CmpOp::Ne,
                    _ => return Err(self.expected("`=` or `!=`")),
                };
                self.bump();
                let right = self.term()?;
                Ok(Literal::Cmp { op, left, right })
            }
        }
    }
}

/// Converts the head of a clause without a body into a fact.
fn into_fact(head: Atom, loc: Location) -> Result<Fact, Error> {
    let mut values = Vec::with_capacity(head.terms.len());
    for term in head.terms {
        match term {
            Term::Const(c) => values.push(c),
            Term::Var(v) => return Err(Error::NotGround { loc, variable: v }),
            Term::Wildcard => {
                return Err(Error::NotGround {
                    loc,
                    variable: "_".to_string(),
                })
            }
        }
    }
    Ok(Fact {
        relation: head.relation,
        values,
        loc,
    })
}
