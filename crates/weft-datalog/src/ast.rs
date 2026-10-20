//! The syntax tree of a Datalog program.

use std::collections::BTreeSet;
use std::fmt;

use crate::error::{Error, Location};
use crate::value::{display_symbol, Value};

/// A constant in a program: an integer or a symbol.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Const {
    /// A 64-bit signed integer.
    Int(i64),
    /// A symbol. A string and a lowercase identifier with the same text are
    /// the same symbol.
    Sym(String),
}

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(i) => write!(f, "{i}"),
            Self::Sym(s) => f.write_str(&display_symbol(s)),
        }
    }
}

/// A term in an atom or a comparison.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    /// A named variable, for example `X` or `_Tmp`.
    Var(String),
    /// The wildcard `_`. Each wildcard is a different anonymous variable.
    Wildcard,
    /// A constant.
    Const(Const),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var(v) => f.write_str(v),
            Self::Wildcard => f.write_str("_"),
            Self::Const(c) => c.fmt(f),
        }
    }
}

/// An atom: a relation name and a list of terms.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Atom {
    /// The relation name.
    pub relation: String,
    /// The arguments. The list is empty for a nullary atom.
    pub terms: Vec<Term>,
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.relation)?;
        for (i, t) in self.terms.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            t.fmt(f)?;
        }
        f.write_str(")")
    }
}

/// A built-in comparison operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CmpOp {
    /// `=`: the two values are equal.
    Eq,
    /// `!=`: the two values are different.
    Ne,
}

impl CmpOp {
    /// Returns `true` if the comparison holds for `left` and `right`.
    pub fn holds(self, left: Value, right: Value) -> bool {
        match self {
            Self::Eq => left == right,
            Self::Ne => left != right,
        }
    }
}

impl fmt::Display for CmpOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Eq => "=",
            Self::Ne => "!=",
        })
    }
}

/// A body literal.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Literal {
    /// A positive atom. It must match a tuple.
    Pos(Atom),
    /// A negated atom, written `!atom`. No tuple may match it.
    Neg(Atom),
    /// A comparison of two terms.
    Cmp {
        /// The operator.
        op: CmpOp,
        /// The left operand.
        left: Term,
        /// The right operand.
        right: Term,
    },
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Pos(a) => a.fmt(f),
            Self::Neg(a) => write!(f, "!{a}"),
            Self::Cmp { op, left, right } => write!(f, "{left} {op} {right}"),
        }
    }
}

/// A rule `head :- body.` with a non-empty body.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Rule {
    /// The head atom.
    pub head: Atom,
    /// The body literals in source order.
    pub body: Vec<Literal>,
    /// The location of the rule.
    pub loc: Location,
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} :- ", self.head)?;
        for (i, lit) in self.body.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            lit.fmt(f)?;
        }
        f.write_str(".")
    }
}

/// A ground fact in a program, for example `edge(1, 2).`
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Fact {
    /// The relation name.
    pub relation: String,
    /// The values.
    pub values: Vec<Const>,
    /// The location of the fact.
    pub loc: Location,
}

impl fmt::Display for Fact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.relation)?;
        for (i, v) in self.values.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            v.fmt(f)?;
        }
        f.write_str(").")
    }
}

/// A Datalog program: facts and rules.
///
/// Rules have indices in the order of [`Program::rules`]. Provenance uses
/// these indices.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Program {
    pub(crate) facts: Vec<Fact>,
    pub(crate) rules: Vec<Rule>,
}

impl Program {
    /// Makes an empty program.
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the facts in source order.
    pub fn facts(&self) -> &[Fact] {
        &self.facts
    }

    /// Returns the rules in source order. The position of a rule is its index.
    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }

    /// Returns the relations that have a rule head or a fact in the program.
    pub fn relations_defined(&self) -> BTreeSet<&str> {
        self.facts
            .iter()
            .map(|f| f.relation.as_str())
            .chain(self.rules.iter().map(|r| r.head.relation.as_str()))
            .collect()
    }

    /// Returns the relations that occur in rule bodies.
    pub fn relations_used(&self) -> BTreeSet<&str> {
        self.rules
            .iter()
            .flat_map(|r| &r.body)
            .filter_map(|lit| match lit {
                Literal::Pos(a) | Literal::Neg(a) => Some(a.relation.as_str()),
                Literal::Cmp { .. } => None,
            })
            .collect()
    }

    /// Appends the facts and rules of `other`. The rules of `other` get the
    /// indices after the rules of `self`.
    ///
    /// This function does not check the result. [`crate::evaluate`] checks it.
    /// Call [`Program::check`] to check it earlier.
    pub fn extend(&mut self, other: Self) {
        self.facts.extend(other.facts);
        self.rules.extend(other.rules);
    }

    /// Checks arity, range restriction and stratification.
    pub fn check(&self) -> Result<(), Error> {
        crate::check::analyze(self).map(|_| ())
    }

    /// Checks the program and returns the strongly connected components of
    /// its dependency graph, in evaluation order. Two relations are in one
    /// component when each depends on the other.
    pub fn components(&self) -> Result<Vec<Vec<String>>, Error> {
        crate::check::analyze(self).map(|a| a.components)
    }
}

impl fmt::Display for Program {
    /// Writes the facts, then the rules, one clause on each line.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for fact in &self.facts {
            writeln!(f, "{fact}")?;
        }
        for rule in &self.rules {
            writeln!(f, "{rule}")?;
        }
        Ok(())
    }
}
