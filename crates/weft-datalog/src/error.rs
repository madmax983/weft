//! Errors and source locations.

use std::fmt;
use std::sync::Arc;

/// A place in a program source.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Location {
    /// The name of the source, for example a file name. It can be empty.
    pub origin: Arc<str>,
    /// The line number. The first line is 1.
    pub line: usize,
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.origin.is_empty() {
            write!(f, "line {}", self.line)
        } else {
            write!(f, "{}:{}", self.origin, self.line)
        }
    }
}

/// The part of a rule that contains an unbound variable or a wildcard.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Place {
    /// The head of the rule.
    Head,
    /// A negated body atom.
    Negation,
    /// A comparison (`=` or `!=`).
    Comparison,
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Head => "the head",
            Self::Negation => "a negated atom",
            Self::Comparison => "a comparison",
        })
    }
}

/// An error from parsing, checking or evaluation.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// The source text is not valid syntax.
    #[error("{loc}, column {column}: syntax error: {message}")]
    Syntax {
        /// The location of the error.
        loc: Location,
        /// The column number. The first column is 1.
        column: usize,
        /// A description of the error.
        message: String,
    },
    /// A fact contains a variable or a wildcard.
    #[error("{loc}: a fact must be ground, but it contains `{variable}`")]
    NotGround {
        /// The location of the fact.
        loc: Location,
        /// The variable or the wildcard.
        variable: String,
    },
    /// Two atoms of the same relation have different numbers of arguments.
    #[error(
        "{loc}: relation `{relation}` has {found} arguments here, \
         but it has {expected} arguments at {first}"
    )]
    Arity {
        /// The location of the second atom.
        loc: Location,
        /// The relation name.
        relation: String,
        /// The arity at the first atom.
        expected: usize,
        /// The arity at the second atom.
        found: usize,
        /// The location of the first atom.
        first: Location,
    },
    /// A program atom does not have the arity of the input relation.
    #[error(
        "{loc}: relation `{relation}` has {found} arguments here, \
         but the input database has tuples with {expected} values"
    )]
    InputArity {
        /// The location of the atom.
        loc: Location,
        /// The relation name.
        relation: String,
        /// The arity in the input database.
        expected: usize,
        /// The arity in the program.
        found: usize,
    },
    /// The input database has tuples of different arity in one relation.
    #[error(
        "input database: relation `{relation}` has tuples with {expected} values \
         and tuples with {found} values"
    )]
    DatabaseArity {
        /// The relation name.
        relation: String,
        /// The arity of the first tuple.
        expected: usize,
        /// The arity of a later tuple.
        found: usize,
    },
    /// A variable does not occur in a positive body atom (range restriction).
    #[error("{loc}: variable `{variable}` in {place} does not occur in a positive body atom")]
    Unbound {
        /// The location of the rule.
        loc: Location,
        /// The variable name.
        variable: String,
        /// The part of the rule that contains the variable.
        place: Place,
    },
    /// A wildcard `_` occurs where a value is necessary.
    #[error("{loc}: the wildcard `_` is not permitted in {place}")]
    Wildcard {
        /// The location of the rule.
        loc: Location,
        /// The part of the rule that contains the wildcard.
        place: Place,
    },
    /// A rule negates a relation that depends on the head of the rule.
    #[error("{loc}: rule for `{relation}` uses negation inside a recursive cycle: {cycle}")]
    Stratification {
        /// The location of the rule.
        loc: Location,
        /// The head relation of the rule.
        relation: String,
        /// The cycle, for example `a -> !b -> a`.
        cycle: String,
    },
}

impl Error {
    /// Returns the location of the error, if the error has one.
    pub const fn location(&self) -> Option<&Location> {
        match self {
            Self::Syntax { loc, .. }
            | Self::NotGround { loc, .. }
            | Self::Arity { loc, .. }
            | Self::InputArity { loc, .. }
            | Self::Unbound { loc, .. }
            | Self::Wildcard { loc, .. }
            | Self::Stratification { loc, .. } => Some(loc),
            Self::DatabaseArity { .. } => None,
        }
    }

    /// Returns the line number of the error, if the error has one.
    pub fn line(&self) -> Option<usize> {
        self.location().map(|loc| loc.line)
    }
}
