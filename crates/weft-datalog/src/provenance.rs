//! Derivation trees.

use std::fmt::{self, Write as _};

use crate::ast::CmpOp;
use crate::error::Location;
use crate::value::{json_string, Interner, Value};

/// A ground fact: a relation and values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GroundAtom {
    /// The relation name.
    pub relation: String,
    /// The values.
    pub values: Vec<Value>,
    /// The fact in Datalog syntax, for example `edge(a, 1)`.
    pub text: String,
}

impl fmt::Display for GroundAtom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.text)
    }
}

/// The reason that a fact is true.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reason {
    /// The fact is in the input database.
    Input,
    /// The fact is written in the program.
    Fact {
        /// The location of the fact.
        loc: Location,
    },
    /// A rule derived the fact.
    Rule {
        /// The index of the rule in [`crate::Program::rules`].
        index: usize,
        /// The rule in Datalog syntax.
        text: String,
        /// The premises in the order of the rule body.
        premises: Vec<Premise>,
    },
}

/// A premise of a rule application.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Premise {
    /// A positive body atom matched this fact.
    Derived(Derivation),
    /// A negated body atom held: no tuple matched it.
    Absent {
        /// The relation name.
        relation: String,
        /// The values. `None` is a wildcard.
        args: Vec<Option<Value>>,
        /// The atom in Datalog syntax, for example `blocked(a, _)`.
        text: String,
    },
    /// A comparison held.
    Holds {
        /// The operator.
        op: CmpOp,
        /// The left value.
        left: Value,
        /// The right value.
        right: Value,
        /// The comparison in Datalog syntax, for example `a != b`.
        text: String,
    },
}

/// A derivation tree. Each node is a ground fact and the reason for it.
///
/// Leaves are input facts, program facts, negated atoms and comparisons.
/// [`Output::explain`](crate::Output::explain) makes the tree. The
/// [`Display`](fmt::Display) output, [`Derivation::to_json`] and `drop` do
/// not use recursion, so a deep tree does not overflow the stack. The
/// derived `Clone`, `Debug` and `PartialEq` use recursion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Derivation {
    /// The fact.
    pub fact: GroundAtom,
    /// The reason for the fact.
    pub reason: Reason,
}

impl Derivation {
    /// Returns the premises. The list is empty for a leaf.
    pub fn premises(&self) -> &[Premise] {
        match &self.reason {
            Reason::Rule { premises, .. } => premises,
            Reason::Input | Reason::Fact { .. } => &[],
        }
    }

    /// Returns the index of the rule that derived the fact, if a rule did.
    pub const fn rule_index(&self) -> Option<usize> {
        match &self.reason {
            Reason::Rule { index, .. } => Some(*index),
            Reason::Input | Reason::Fact { .. } => None,
        }
    }

    /// Writes the tree as one line of JSON.
    ///
    /// A fact node has the keys `fact`, `relation`, `args` and `source`.
    /// The source is `"input"`, `"fact"` (with `line`) or `"rule"` (with
    /// `rule`, `text` and `premises`). A negated premise is
    /// `{"not": ..., "relation": ..., "args": [...]}`, where `null` is a
    /// wildcard. A comparison is `{"holds": ...}`. Integers are JSON numbers
    /// and symbols are JSON strings.
    pub fn to_json(&self, interner: &Interner) -> String {
        enum Task<'a> {
            Node(&'a Derivation),
            Premise(&'a Premise),
            Raw(&'static str),
        }
        let mut out = String::new();
        let mut stack = vec![Task::Node(self)];
        while let Some(task) = stack.pop() {
            match task {
                Task::Raw(s) => out.push_str(s),
                Task::Node(d) | Task::Premise(Premise::Derived(d)) => {
                    out.push_str("{\"fact\":");
                    json_string(&mut out, &d.fact.text);
                    out.push_str(",\"relation\":");
                    json_string(&mut out, &d.fact.relation);
                    out.push_str(",\"args\":");
                    json_args(&mut out, d.fact.values.iter().map(|&v| Some(v)), interner);
                    match &d.reason {
                        Reason::Input => out.push_str(",\"source\":\"input\"}"),
                        Reason::Fact { loc } => {
                            let _ = write!(out, ",\"source\":\"fact\",\"line\":{}}}", loc.line);
                        }
                        Reason::Rule {
                            index,
                            text,
                            premises,
                        } => {
                            let _ = write!(out, ",\"source\":\"rule\",\"rule\":{index},\"text\":");
                            json_string(&mut out, text);
                            out.push_str(",\"premises\":[");
                            stack.push(Task::Raw("]}"));
                            for (i, p) in premises.iter().enumerate().rev() {
                                stack.push(Task::Premise(p));
                                if i > 0 {
                                    stack.push(Task::Raw(","));
                                }
                            }
                        }
                    }
                }
                Task::Premise(Premise::Absent {
                    relation,
                    args,
                    text,
                }) => {
                    out.push_str("{\"not\":");
                    json_string(&mut out, text);
                    out.push_str(",\"relation\":");
                    json_string(&mut out, relation);
                    out.push_str(",\"args\":");
                    json_args(&mut out, args.iter().copied(), interner);
                    out.push('}');
                }
                Task::Premise(Premise::Holds { text, .. }) => {
                    out.push_str("{\"holds\":");
                    json_string(&mut out, text);
                    out.push('}');
                }
            }
        }
        out
    }
}

/// Drops the tree without recursion, so that deep trees do not overflow
/// the stack.
impl Drop for Derivation {
    fn drop(&mut self) {
        let Reason::Rule { premises, .. } = &mut self.reason else {
            return;
        };
        let mut stack = vec![std::mem::take(premises)];
        while let Some(premises) = stack.pop() {
            for premise in premises {
                if let Premise::Derived(mut child) = premise {
                    if let Reason::Rule { premises, .. } = &mut child.reason {
                        stack.push(std::mem::take(premises));
                    }
                }
            }
        }
    }
}

/// Writes values as a JSON array. `None` is `null`.
fn json_args(out: &mut String, args: impl Iterator<Item = Option<Value>>, interner: &Interner) {
    out.push('[');
    for (i, arg) in args.enumerate() {
        if i > 0 {
            out.push(',');
        }
        match arg {
            None => out.push_str("null"),
            Some(Value::Int(n)) => {
                let _ = write!(out, "{n}");
            }
            Some(v @ Value::Sym(s)) => match interner.resolve(s) {
                Some(text) => json_string(out, text),
                None => json_string(out, &interner.display(v)),
            },
        }
    }
    out.push(']');
}

/// Writes an indented tree. Each line is one node. A child is two spaces
/// deeper than its parent. A rule node shows `fact  by  rule`. A leaf shows
/// `fact  [input]`, `fact  [fact]`, `not atom` or a comparison.
impl fmt::Display for Derivation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut stack: Vec<(&Self, Option<&Premise>, usize)> = vec![(self, None, 0)];
        let mut first = true;
        while let Some((node, premise, depth)) = stack.pop() {
            if !first {
                f.write_str("\n")?;
            }
            first = false;
            write!(f, "{:width$}", "", width = 2 * depth)?;
            match premise {
                Some(Premise::Absent { text, .. }) => write!(f, "not {text}")?,
                Some(Premise::Holds { text, .. }) => f.write_str(text)?,
                Some(Premise::Derived(_)) | None => {
                    f.write_str(&node.fact.text)?;
                    match &node.reason {
                        Reason::Input => f.write_str("  [input]")?,
                        Reason::Fact { .. } => f.write_str("  [fact]")?,
                        Reason::Rule { text, premises, .. } => {
                            write!(f, "  by  {text}")?;
                            for p in premises.iter().rev() {
                                match p {
                                    Premise::Derived(child) => stack.push((child, None, depth + 1)),
                                    other => stack.push((node, Some(other), depth + 1)),
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }
}
