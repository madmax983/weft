//! Lexer, parser and AST for the Weft language.
//!
//! Entry point: [`parse_file`]. The grammar is in `docs/grammar.md`.

pub mod ast;
pub mod diag;
pub mod lexer;
pub mod parser;
pub mod pretty;
pub mod source;

pub use parser::{parse_expr, parse_file, ParseError};
pub use pretty::pretty;
pub use source::SourceFile;
