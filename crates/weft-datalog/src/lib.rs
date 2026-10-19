//! A small Datalog engine with stratified negation and provenance.
//!
//! The Weft language specification is a Datalog program. This crate parses
//! the program, checks it and evaluates it over input facts. It records the
//! first derivation of each tuple, so it can explain each derived fact.
//!
//! # Language
//!
//! ```text
//! // A line comment.
//! edge(1, 2).                               // A fact.
//! path(X, Y) :- edge(X, Y).                 // A rule.
//! path(X, Z) :- path(X, Y), edge(Y, Z).     // A recursive rule.
//! reach(X) :- start(X), !blocked(X).        // Stratified negation.
//! diff(X, Y) :- node(X), node(Y), X != Y.   // Comparisons: `=` and `!=`.
//! named(X) :- sym(X, "a string"), kind(X, atom_constant).
//! clean() :- library(), !error(_).          // Nullary atoms and a wildcard.
//! ```
//!
//! - A variable starts with an uppercase letter or `_`. The wildcard `_`
//!   alone is an anonymous variable. Each `_` is a different variable.
//! - A constant is an integer (`i64`, negative values are permitted), a
//!   string in double quotes, or a lowercase identifier. Strings and
//!   identifiers are the same symbol type: `foo` and `"foo"` are equal.
//!   Strings can contain the escapes `\"`, `\\`, `\n`, `\t` and `\r`.
//! - A nullary atom is `name()` or `name`.
//! - A relation can have program facts, input facts and rules together.
//!
//! # Checks
//!
//! [`parse_program`] and [`evaluate`] do these checks. Each error has a line
//! number.
//!
//! - Arity: all atoms of a relation have the same number of arguments. Input
//!   tuples must also agree with the program.
//! - Range restriction: a variable in the head, in a negated atom or in a
//!   comparison must also be in a positive body atom. A wildcard is not
//!   permitted in the head or in a comparison. A wildcard in
//!   a negated atom means "any value".
//! - Stratification: a rule must not negate a relation in its own recursive
//!   cycle.
//!
//! # Evaluation
//!
//! The engine finds the strongly connected components of the dependency
//! graph and evaluates them in dependency order. Inside a component, it uses
//! semi-naive evaluation with hash indexes on the bound columns of each body
//! atom. See [`evaluate`].
//!
//! # Provenance
//!
//! With [`EvalOptions::provenance`] on (the default), each derived tuple
//! records its first derivation. The record has the rule index and the rows
//! that matched the positive body atoms. [`Output::explain`] uses this record to build a
//! [`Derivation`] tree. The tree also shows the negated atoms and the
//! comparisons that held, with the values of the derivation. Input facts and
//! program facts are leaves. The tree is finite, because each premise row is
//! older than the row that it supports.
//!
//! # Example
//!
//! ```
//! use weft_datalog::{evaluate, parse_program, Database, EvalOptions};
//!
//! let mut spec = parse_program(
//!     "error(R, P) :- uses(R, P), invalid(R, P).\n\
//!      invalid(R, P) :- uses(R, P), !declared(R, P).",
//! )?;
//! // User lint rules come after the specification.
//! spec.extend(parse_program("unused(R) :- declared(R, _), !uses(R, _).")?);
//!
//! let mut db = Database::new();
//! let (v1, v2, n4) = (db.sym("v1"), db.sym("v2"), db.sym("n4"));
//! db.insert("uses", [v1, n4]);
//! db.insert("declared", [v2, n4]);
//!
//! let out = evaluate(&spec, db, EvalOptions::default())?;
//! assert_eq!(out.tuples("error"), [vec![v1, n4]]);
//! assert!(out.contains("unused", &[v2]));
//! let proof = out.explain("error", &[v1, n4]).expect("derived");
//! assert_eq!(
//!     proof.to_string(),
//!     "error(v1, n4)  by  error(R, P) :- uses(R, P), invalid(R, P).\n  \
//!        uses(v1, n4)  [input]\n  \
//!        invalid(v1, n4)  by  invalid(R, P) :- uses(R, P), !declared(R, P).\n    \
//!          uses(v1, n4)  [input]\n    \
//!          not declared(v1, n4)"
//! );
//! # Ok::<(), weft_datalog::Error>(())
//! ```
//!
//! # Limits
//!
//! - `=` does not bind a variable. Both sides must be bound by positive
//!   atoms or be constants.
//! - The only built-ins are `=` and `!=`. There is no arithmetic, no order
//!   comparison and no aggregation.
//! - An explanation shows the first derivation only, not all derivations.
//! - A relation can have fewer than `u32::MAX` rows.

mod ast;
mod check;
mod error;
mod eval;
mod parser;
mod provenance;
mod relation;
mod value;

pub use ast::{Atom, CmpOp, Const, Fact, Literal, Program, Rule, Term};
pub use error::{Error, Location, Place};
pub use eval::{evaluate, Database, EvalOptions, Output};
pub use parser::{parse_program, parse_program_named};
pub use provenance::{Derivation, GroundAtom, Premise, Reason};
pub use value::{Interner, Symbol, Value};
