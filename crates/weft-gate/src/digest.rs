//! The fact digest and the violations of one program (plan §2.3, items 2 and 3).
//!
//! The ids of the facts (`n3`, `v1`, `p2`) depend on the fact generator. The
//! digest replaces them with names that the two pipelines can share:
//!
//! - a node `n3` becomes `@LINE:LABEL`, its line and its label;
//! - a variable `v1` becomes its name;
//! - a place `p2` becomes its display text, for example `world.entities[]`.
//!
//! The other values stay as they are (tasks `t0`, handlers `h0`, capabilities,
//! effects and integers). In a violation, a node is only `@LINE`: the label of a
//! node is not part of the result of the checker.
//!
//! The canonical digest is one line for each tuple: a JSON array of the file,
//! the function, the relation and the arguments. The lines are in sorted order.
//! Two tuples can have the same line (two nodes with the same line and label);
//! the digest keeps both, so it is a multiset.

use std::collections::BTreeMap;
use std::path::Path;

use sha2::{Digest as _, Sha256};
use weft_check::bridge::{self, Arg};
use weft_check::Checked;
use weft_cli::package::Package;
use weft_facts::{FnFacts, Violations};
use weft_syntax::SourceFile;

use crate::snapshot::Violation;

/// The digest of the input facts of one program.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FactDigest {
    /// The number of tuples of each input relation. A relation with no tuple is
    /// not in the map.
    pub counts: BTreeMap<String, usize>,
    /// The canonical lines, in sorted order.
    pub lines: Vec<String>,
}

impl FactDigest {
    /// The canonical text: each line, and a line feed after each line.
    pub fn text(&self) -> String {
        let mut out = String::with_capacity(self.lines.iter().map(|l| l.len() + 1).sum());
        for l in &self.lines {
            out.push_str(l);
            out.push('\n');
        }
        out
    }
}

/// Returns the SHA-256 of `text` in lower-case hex.
pub fn sha256(text: &str) -> String {
    crate::manifest::hex(&Sha256::digest(text.as_bytes()))
}

/// How the names of one body show a node.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NodeForm {
    /// `@LINE:LABEL`, for the digest.
    LineLabel,
    /// `@LINE`, for the violations.
    Line,
}

/// The names of the ids of one body.
struct Names<'a> {
    facts: &'a FnFacts,
    file: Option<&'a SourceFile>,
    form: NodeForm,
}

impl Names<'_> {
    /// Returns the name of the value with the text `raw`.
    fn name(&self, raw: &str) -> String {
        let mut chars = raw.chars();
        let head = chars.next();
        let digits = chars.as_str();
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return raw.to_string();
        }
        let Ok(i) = digits.parse::<usize>() else {
            return raw.to_string();
        };
        let f = self.facts;
        match head {
            Some('v') => f
                .vars
                .get(i)
                .map_or_else(|| raw.to_string(), |v| v.name.clone()),
            Some('p') => f
                .places
                .get(i)
                .map_or_else(|| raw.to_string(), |p| p.display.clone()),
            Some('n') => f.nodes.get(i).map_or_else(
                || raw.to_string(),
                |n| {
                    let line = self.file.map_or(0, |s| s.line_col(n.span.lo).0);
                    match self.form {
                        NodeForm::LineLabel => format!("@{line}:{}", n.label),
                        NodeForm::Line => format!("@{line}"),
                    }
                },
            ),
            _ => raw.to_string(),
        }
    }

    fn arg(&self, a: &Arg) -> String {
        match a {
            Arg::Sym(t) => self.name(t),
            Arg::Int(i) => i.to_string(),
        }
    }
}

/// Returns the name of the file `name` relative to `base`, with `/`. A name
/// outside `base` (the prelude) stays as it is.
pub fn relative_name(base: &Path, name: &str) -> String {
    Path::new(name).strip_prefix(base).map_or_else(
        |_| name.to_string(),
        |rel| {
            rel.components()
                .map(|c| c.as_os_str().to_string_lossy())
                .collect::<Vec<_>>()
                .join("/")
        },
    )
}

/// One line of the canonical digest: a JSON array of strings.
fn line(parts: &[&str], args: &[String]) -> String {
    let all: Vec<&str> = parts
        .iter()
        .copied()
        .chain(args.iter().map(String::as_str))
        .collect();
    serde_json::to_string(&all).unwrap_or_default()
}

/// Computes the digest of the input facts of each body of `checked`. The file
/// names are relative to `base`.
pub fn fact_digest(base: &Path, pkg: &Package, checked: &Checked) -> FactDigest {
    let mut d = FactDigest::default();
    for b in &checked.analysis.bodies {
        let file = pkg.files.get(b.unit);
        let file_name = file.map_or_else(String::new, |f| relative_name(base, &f.name));
        let names = Names {
            facts: &b.facts,
            file,
            form: NodeForm::LineLabel,
        };
        bridge::each_fact(&b.facts, &mut |rel, args| {
            *d.counts.entry(rel.to_string()).or_default() += 1;
            let args: Vec<String> = args.iter().map(|a| names.arg(a)).collect();
            d.lines.push(line(
                &[file_name.as_str(), b.facts.name.as_str(), rel],
                &args,
            ));
        });
    }
    d.lines.sort_unstable();
    d
}

/// Returns the violations of the checker for each body of `checked`, with
/// names. The file names are relative to `base`. The list is in sorted order.
pub fn violations(base: &Path, pkg: &Package, checked: &Checked) -> Vec<Violation> {
    let mut out = Vec::new();
    for (b, report) in checked.analysis.bodies.iter().zip(&checked.reports) {
        let file = pkg.files.get(b.unit);
        let file_name = file.map_or_else(String::new, |f| relative_name(base, &f.name));
        let names = Names {
            facts: &b.facts,
            file,
            form: NodeForm::Line,
        };
        for (rel, args) in violation_tuples(&report.violations) {
            out.push(Violation {
                file: file_name.clone(),
                function: b.facts.name.clone(),
                relation: rel.to_string(),
                args: args.iter().map(|a| names.arg(a)).collect(),
            });
        }
    }
    out.sort();
    out
}

/// Returns the tuples of each violation relation (`bridge::VIOLATION_RELATIONS`)
/// with raw ids. The relation `stealable` is information for the scheduler, not
/// a violation, so it is not in the list.
pub fn violation_tuples(v: &Violations) -> Vec<(&'static str, Vec<Arg>)> {
    // The pattern names each field, so a new sink relation does not compile
    // until it is in this list.
    let Violations {
        error,
        use_after_move,
        use_before_set,
        moved_immovable,
        unconsumed,
        overwritten,
        abort_unhandled,
        live_across_multi,
        unauthorized_mut,
        unauthorized_effect,
        shared_mutation,
        alias_conflict,
        task_conflict,
        nonportable_capture,
        shared_mut_capture,
        root_handler_in_lib,
        arg_outside,
        ref_outside,
        not_uniq,
        arg_effect_outside,
        sim_in_lib,
        unhandled_effect,
        embedded_effect,
        stealable: _,
    } = v;
    let s = |x: &dyn std::fmt::Display| Arg::Sym(x.to_string());
    let int = |i: &u32| Arg::Int(i64::from(*i));
    let mut out: Vec<(&'static str, Vec<Arg>)> = Vec::new();
    for (rel, set) in [
        ("error", error),
        ("use_after_move", use_after_move),
        ("use_before_set", use_before_set),
        ("moved_immovable", moved_immovable),
        ("unconsumed", unconsumed),
        ("overwritten", overwritten),
        ("abort_unhandled", abort_unhandled),
        ("live_across_multi", live_across_multi),
    ] {
        out.extend(set.iter().map(|(a, b)| (rel, vec![s(a), s(b)])));
    }
    for (rel, set) in [
        ("unauthorized_mut", unauthorized_mut),
        ("shared_mutation", shared_mutation),
        ("ref_outside", ref_outside),
    ] {
        out.extend(set.iter().map(|(a, b)| (rel, vec![s(a), s(b)])));
    }
    for (rel, set) in [
        ("unauthorized_effect", unauthorized_effect),
        ("unhandled_effect", unhandled_effect),
        ("embedded_effect", embedded_effect),
    ] {
        out.extend(set.iter().map(|(a, e)| (rel, vec![s(a), s(e)])));
    }
    out.extend(
        alias_conflict
            .iter()
            .map(|(a, m, p)| ("alias_conflict", vec![s(a), s(m), s(p)])),
    );
    out.extend(
        task_conflict
            .iter()
            .map(|(t, a)| ("task_conflict", vec![s(t), s(a)])),
    );
    for (rel, set) in [
        ("nonportable_capture", nonportable_capture),
        ("shared_mut_capture", shared_mut_capture),
    ] {
        out.extend(set.iter().map(|(t, x)| (rel, vec![s(t), s(x)])));
    }
    out.extend(
        root_handler_in_lib
            .iter()
            .map(|h| ("root_handler_in_lib", vec![s(h)])),
    );
    out.extend(
        arg_outside
            .iter()
            .map(|(a, i, p)| ("arg_outside", vec![s(a), int(i), s(p)])),
    );
    out.extend(
        not_uniq
            .iter()
            .map(|(a, i)| ("not_uniq", vec![s(a), int(i)])),
    );
    out.extend(
        arg_effect_outside
            .iter()
            .map(|(a, i, e)| ("arg_effect_outside", vec![s(a), int(i), s(e)])),
    );
    out.extend(sim_in_lib.iter().map(|a| ("sim_in_lib", vec![s(a)])));
    out
}

/// The names of the relations that [`violation_tuples`] gives, in its order.
pub fn violation_relations() -> Vec<&'static str> {
    vec![
        "error",
        "use_after_move",
        "use_before_set",
        "moved_immovable",
        "unconsumed",
        "overwritten",
        "abort_unhandled",
        "live_across_multi",
        "unauthorized_mut",
        "shared_mutation",
        "ref_outside",
        "unauthorized_effect",
        "unhandled_effect",
        "embedded_effect",
        "alias_conflict",
        "task_conflict",
        "nonportable_capture",
        "shared_mut_capture",
        "root_handler_in_lib",
        "arg_outside",
        "not_uniq",
        "arg_effect_outside",
        "sim_in_lib",
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use weft_facts::{HandlerId, NodeId, PlaceId, TaskId, VarId};

    /// Violations with one tuple in each relation.
    fn one_of_each() -> Violations {
        let (v, n, p, t) = (VarId(0), NodeId(1), PlaceId(2), TaskId(3));
        let e = "Log".to_string();
        Violations {
            error: [(v, n)].into(),
            use_after_move: [(v, n)].into(),
            use_before_set: [(v, n)].into(),
            moved_immovable: [(v, n)].into(),
            unconsumed: [(v, n)].into(),
            overwritten: [(v, n)].into(),
            abort_unhandled: [(v, n)].into(),
            live_across_multi: [(v, n)].into(),
            unauthorized_mut: [(n, p)].into(),
            unauthorized_effect: [(n, e.clone())].into(),
            shared_mutation: [(n, p)].into(),
            alias_conflict: [(n, p, p)].into(),
            task_conflict: [(t, n)].into(),
            nonportable_capture: [(t, v)].into(),
            shared_mut_capture: [(t, v)].into(),
            root_handler_in_lib: [HandlerId(4)].into(),
            arg_outside: [(n, 5, p)].into(),
            ref_outside: [(n, p)].into(),
            not_uniq: [(n, 5)].into(),
            arg_effect_outside: [(n, 5, e.clone())].into(),
            sim_in_lib: [n].into(),
            unhandled_effect: [(n, e.clone())].into(),
            embedded_effect: [(n, e)].into(),
            stealable: [t].into(),
        }
    }

    #[test]
    fn each_violation_relation_gives_its_tuples() {
        let tuples = violation_tuples(&one_of_each());
        let names: Vec<&str> = tuples.iter().map(|(r, _)| *r).collect();
        assert_eq!(names, violation_relations());
        let error = tuples.iter().find(|(r, _)| *r == "error").map(|(_, a)| a);
        assert_eq!(
            error,
            Some(&vec![Arg::Sym("v0".into()), Arg::Sym("n1".into())])
        );
        let not_uniq = tuples
            .iter()
            .find(|(r, _)| *r == "not_uniq")
            .map(|(_, a)| a);
        assert_eq!(not_uniq, Some(&vec![Arg::Sym("n1".into()), Arg::Int(5)]));
    }

    #[test]
    fn a_name_outside_the_tables_stays_raw() {
        let facts = FnFacts::default();
        let names = Names {
            facts: &facts,
            file: None,
            form: NodeForm::LineLabel,
        };
        for raw in ["v0", "n7", "p3", "t0", "Log", "v", "v+1", "main.a.Note"] {
            assert_eq!(names.name(raw), raw);
        }
    }
}
