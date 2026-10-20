//! Compares the evidence of the checker with the derivations of the spec.
//!
//! The diagnostics of W0301 and W0405 come from the evidence of the checker
//! ([`Report::invalidations`], [`Report::conflicts`]), not only from the
//! violation sets. So the agreement test checks the evidence too:
//!
//! - Each `error(R, P)` has one piece of evidence, and each `task_conflict(T,
//!   P)` has one conflict. Each piece of evidence has its violation.
//! - Each piece of evidence is a derivation of the spec. [`program`] adds a
//!   probe rule for each rule of the spec that derives `invalidated_at`,
//!   `task_conflict` or `frees_at`. A probe rule has the body of its rule, and
//!   its head names the places of the derivation (the witness). The evidence
//!   must be such a witness.
//!
//! The probes come from the rules of the spec, so a new rule of these
//! relations gets a probe with no edit here. A new rule of another shape is
//! an error of [`program`], and a test finds it.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::sync::OnceLock;

use weft_datalog::{
    evaluate, parse_program_named, Atom, EvalOptions, Literal, Output, Program, Term, Value,
};
use weft_facts::{FnFacts, NodeId, VarId};

use crate::bridge::{database, spec, SpecError};
use crate::rules::{Cause, Conflict, Invalidation, Report};

/// The relations of the changes that invalidate a reference.
const CHANGES: [&str; 3] = ["mutates_at", "lends_mut", "frees_at"];

/// The relations of the accesses of a node that can conflict with a task.
const ACCESSES: [&str; 4] = ["accesses", "mutates_at", "frees_at", "lends_mut"];

/// The relations of the footprint of a task.
const TASK_ACCESSES: [&str; 3] = ["task_writes", "task_reads", "task_accesses"];

/// Returns the first positive atom of `body` with a relation of `relations`
/// whose argument at position `at` is `term`.
fn atom_with<'a>(
    body: &'a [Literal],
    relations: &[&str],
    at: usize,
    term: &Term,
) -> Option<&'a Atom> {
    body.iter().find_map(|l| match l {
        Literal::Pos(a)
            if relations.contains(&a.relation.as_str()) && a.terms.get(at) == Some(term) =>
        {
            Some(a)
        }
        _ => None,
    })
}

/// Returns the text of a probe rule: `head(args) :- body.`
fn probe(head: &str, args: &[String], body: &[Literal]) -> String {
    let body: Vec<String> = body.iter().map(ToString::to_string).collect();
    format!("{head}({}) :- {}.\n", args.join(", "), body.join(", "))
}

/// Returns the probe rules of the spec, as Datalog text.
///
/// - `inv_witness(R, P, Path, M, Kind)`: a rule of `invalidated_at(R, P)`
///   holds with `points_into(R, Path)` and the change `Kind(P, M)`.
/// - `free_witness(P, M, Kind, X)`: a rule of `frees_at(P, M)` holds with the
///   fact `Kind` that names `P`, and `X` is the owner variable of the rule, or
///   `M` if it has none.
/// - `conflict_witness(T, P, A, M, Kind)`: a rule of `task_conflict(T, P)`
///   holds with a task access of `A` and the access `Kind(P, M)`.
///
/// # Errors
///
/// Returns the rule that does not have the shape of its relation.
pub fn probes(spec: &Program) -> Result<String, String> {
    let mut out = String::new();
    for rule in spec.rules() {
        let head = &rule.head;
        let shape = || format!("{}: no probe for `{rule}`", rule.loc);
        let (Some(first), Some(second)) = (head.terms.first(), head.terms.get(1)) else {
            continue;
        };
        match head.relation.as_str() {
            "invalidated_at" => {
                let path = atom_with(&rule.body, &["points_into"], 0, first)
                    .and_then(|a| a.terms.get(1))
                    .ok_or_else(shape)?;
                let change = atom_with(&rule.body, &CHANGES, 0, second).ok_or_else(shape)?;
                let m = change.terms.get(1).ok_or_else(shape)?;
                let args = [first, second, path, m].map(ToString::to_string);
                let mut args = args.to_vec();
                args.push(change.relation.clone());
                out.push_str(&probe("inv_witness", &args, &rule.body));
            }
            "frees_at" => {
                let kind = rule
                    .body
                    .iter()
                    .find_map(|l| match l {
                        Literal::Pos(a) if a.relation != "owner" && a.terms.contains(first) => {
                            Some(a)
                        }
                        _ => None,
                    })
                    .ok_or_else(shape)?;
                let owner = rule.body.iter().find_map(|l| match l {
                    Literal::Pos(a) if a.relation == "owner" => a.terms.get(1),
                    _ => None,
                });
                let x = owner.unwrap_or(second);
                let args = vec![
                    first.to_string(),
                    second.to_string(),
                    kind.relation.clone(),
                    x.to_string(),
                ];
                out.push_str(&probe("free_witness", &args, &rule.body));
            }
            "task_conflict" => {
                let task = atom_with(&rule.body, &TASK_ACCESSES, 0, first)
                    .and_then(|a| a.terms.get(1))
                    .ok_or_else(shape)?;
                let access = atom_with(&rule.body, &ACCESSES, 0, second).ok_or_else(shape)?;
                let m = access.terms.get(1).ok_or_else(shape)?;
                let mut args = [first, second, task, m].map(ToString::to_string).to_vec();
                args.push(access.relation.clone());
                out.push_str(&probe("conflict_witness", &args, &rule.body));
            }
            _ => {}
        }
    }
    Ok(out)
}

/// Returns the spec with the probe rules of [`probes`].
///
/// # Errors
///
/// Returns why the probes cannot be made: a rule that does not have the shape
/// of its relation, or probe text that does not parse.
pub fn program() -> Result<&'static Program, SpecError> {
    static PROGRAM: OnceLock<Result<Program, String>> = OnceLock::new();
    PROGRAM
        .get_or_init(|| {
            let text = probes(spec())?;
            let extra = parse_program_named("evidence probes", &text).map_err(|e| e.to_string())?;
            let mut p = spec().clone();
            p.extend(extra);
            p.check().map_err(|e| e.to_string())?;
            Ok(p)
        })
        .as_ref()
        .map_err(|e| SpecError::Probes(e.clone()))
}

/// Evaluates the spec with the probe rules on the facts of one function. The
/// output has the violations of the spec too.
///
/// # Errors
///
/// Returns why the probes cannot be made, or the error of the engine.
pub fn evaluate_probes(f: &FnFacts) -> Result<Output, SpecError> {
    let p = program()?;
    Ok(evaluate(p, database(f), EvalOptions { provenance: false })?)
}

/// Returns true if `out` has the tuple of `relation` with these arguments. An
/// argument whose text is a number is an integer; each other argument is a
/// symbol.
fn holds(out: &Output, relation: &str, args: &[&dyn std::fmt::Display]) -> bool {
    let mut tuple = Vec::new();
    for a in args {
        let text = a.to_string();
        let v = match text.parse::<i64>() {
            Ok(i) => Value::Int(i),
            Err(_) => match out.symbol(&text) {
                Some(v) => v,
                None => return false,
            },
        };
        tuple.push(v);
    }
    out.contains(relation, &tuple)
}

/// Returns the fact and its owner for a free of [`Cause`]: the relation of the
/// fact that names the node, and the owner variable or the place.
fn free_kind(cause: Cause) -> Option<(&'static str, String)> {
    match cause {
        Cause::Move(o) => Some(("moved_at", o.to_string())),
        Cause::ScopeEnd(o) => Some(("scope_end", o.to_string())),
        Cause::Unwound(o) => Some(("unwound_at", o.to_string())),
        Cause::MovePart(m) => Some(("moved_part", m.to_string())),
        Cause::Release(m) => Some(("releases_at", m.to_string())),
        Cause::Mutation(_) | Cause::Lend(_) => None,
    }
}

/// Returns true if the spec frees a place at `at` for `cause`, and the freed
/// place `m` makes the witness of `relation`, such as `inv_witness(R, P, Path,
/// M, frees_at)`.
fn free_witness(out: &Output, at: NodeId, cause: Cause, m: &dyn Fn(&str) -> bool) -> bool {
    let Some((kind, x)) = free_kind(cause) else {
        return false;
    };
    out.tuples("free_witness").iter().any(|t| {
        let text: Vec<String> = t.iter().map(|&v| out.display_value(v)).collect();
        text.first() == Some(&at.to_string())
            && text.get(2).map(String::as_str) == Some(kind)
            && text.get(3) == Some(&x)
            && text.get(1).is_some_and(|place| m(place))
    })
}

/// Checks one piece of W0301 evidence against the witnesses of the spec.
fn invalidation_ok(out: &Output, inv: &Invalidation) -> bool {
    let (r, at, path) = (inv.var, inv.at, inv.path);
    match inv.cause {
        Cause::Mutation(m) => holds(out, "inv_witness", &[&r, &at, &path, &m, &"mutates_at"]),
        Cause::Lend(m) => holds(out, "inv_witness", &[&r, &at, &path, &m, &"lends_mut"]),
        cause => free_witness(out, at, cause, &|m| {
            holds(out, "inv_witness", &[&r, &at, &path, &m, &"frees_at"])
        }),
    }
}

/// Checks one W0405 conflict against the witnesses of the spec.
fn conflict_ok(f: &FnFacts, out: &Output, c: &Conflict) -> bool {
    let (t, at, a, m) = (c.task, c.at, c.task_place, c.node_place);
    let task_side = if c.task_writes {
        f.task_writes.contains(&(t, a))
    } else {
        f.task_reads.contains(&(t, a))
    };
    let kind = match (c.lends, c.free, c.task_writes) {
        (true, _, _) => "lends_mut",
        (false, Some(_), _) => "frees_at",
        (false, None, true) => "accesses",
        (false, None, false) => "mutates_at",
    };
    let node_side = holds(out, "conflict_witness", &[&t, &at, &a, &m, &kind]);
    let cause = c
        .free
        .is_none_or(|cause| free_witness(out, at, cause, &|freed| freed == m.to_string()));
    task_side && node_side && cause
}

/// Returns each difference between the evidence of the checker and the spec
/// for one function. `out` is the result of [`evaluate_probes`].
pub fn differences(f: &FnFacts, r: &Report, out: &Output) -> Vec<String> {
    let mut bad = Vec::new();
    let v = &r.violations;
    // Each violation has one piece of evidence, and each piece of evidence
    // has its violation.
    let uses: Vec<(VarId, NodeId)> = r.invalidations.iter().map(|i| (i.var, i.used_at)).collect();
    let once: BTreeSet<&(VarId, NodeId)> = uses.iter().collect();
    if once.len() != uses.len() {
        bad.push("an error(R, P) has two pieces of evidence".to_string());
    }
    for e in &v.error {
        if !once.contains(e) {
            bad.push(format!("error({}, {}) has no evidence", e.0, e.1));
        }
    }
    for (var, used) in &uses {
        if !v.error.contains(&(*var, *used)) {
            bad.push(format!(
                "evidence for error({var}, {used}), which is no violation"
            ));
        }
    }
    let conflicts: Vec<_> = r.conflicts.iter().map(|c| (c.task, c.at)).collect();
    let once: BTreeSet<_> = conflicts.iter().collect();
    if once.len() != conflicts.len() {
        bad.push("a task_conflict(T, P) has two conflicts".to_string());
    }
    for c in &v.task_conflict {
        if !once.contains(c) {
            bad.push(format!("task_conflict({}, {}) has no conflict", c.0, c.1));
        }
    }
    for (t, at) in &conflicts {
        if !v.task_conflict.contains(&(*t, *at)) {
            bad.push(format!(
                "a conflict for task_conflict({t}, {at}), which is no violation"
            ));
        }
    }
    // Each piece of evidence is a derivation of the spec.
    for inv in &r.invalidations {
        if !invalidation_ok(out, inv) {
            let mut text = String::new();
            let _ = write!(text, "the spec has no derivation for the evidence {inv:?}");
            bad.push(text);
        }
    }
    for c in &r.conflicts {
        if !conflict_ok(f, out, c) {
            bad.push(format!("the spec has no derivation for the conflict {c:?}"));
        }
    }
    bad
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check_source;
    use weft_sema::Options;

    /// Each rule of `invalidated_at`, `frees_at` and `task_conflict` gets one
    /// probe rule, and a rule of another shape is an error.
    #[test]
    fn each_rule_of_the_evidence_gets_a_probe() {
        let text = probes(spec()).expect("the spec has the shapes of the probes");
        let count = |head: &str| {
            spec()
                .rules()
                .iter()
                .filter(|r| r.head.relation == head)
                .count()
        };
        let lines = |head: &str| text.lines().filter(|l| l.starts_with(head)).count();
        assert_eq!(lines("inv_witness("), count("invalidated_at"));
        assert_eq!(lines("free_witness("), count("frees_at"));
        assert_eq!(lines("conflict_witness("), count("task_conflict"));
        assert!(program().is_ok());
        let odd = parse_program_named("odd.dl", "invalidated_at(R, P) :- uses(R, P).")
            .expect("the rule parses");
        let Err(e) = probes(&odd) else {
            panic!("a rule with no change has a probe");
        };
        assert!(
            e.contains("no probe for `invalidated_at(R, P) :- uses(R, P).`"),
            "{e}"
        );
    }

    /// Checks a program, and returns the facts and the report of `name`.
    fn body(src: &str, name: &str) -> (FnFacts, Report) {
        let c = check_source("t.wf", src, Options::default());
        let i = c
            .analysis
            .bodies
            .iter()
            .position(|b| b.facts.name == name)
            .expect("the body exists");
        (c.analysis.bodies[i].facts.clone(), c.reports[i].clone())
    }

    const BAD: &str = "struct E { hp: u64 }\nstruct W { es: Vec<E>, other: Vec<E> }\nfn bad(w: &W) / mut(w..) {\n    let first = &w.es[0]\n    w.es.push(E { hp: 1 })\n    print(first.hp)\n}\n";

    #[test]
    fn wrong_or_missing_evidence_of_w0301_is_a_difference() {
        let (f, r) = body(BAD, "bad");
        let out = evaluate_probes(&f).expect("the spec runs");
        assert_eq!(differences(&f, &r, &out), Vec::<String>::new());
        assert_eq!(r.invalidations.len(), 1);
        // A place that the reference does not point into.
        let mut wrong = r.clone();
        let other = f
            .places
            .iter()
            .position(|p| p.display == "w.es")
            .map(|i| weft_facts::PlaceId(u32::try_from(i).unwrap_or(0)))
            .expect("the place exists");
        wrong.invalidations[0].path = other;
        assert_eq!(differences(&f, &wrong, &out).len(), 1);
        // A cause that the node does not have.
        let mut wrong = r.clone();
        wrong.invalidations[0].cause = Cause::Lend(other);
        assert_eq!(differences(&f, &wrong, &out).len(), 1);
        // No evidence for the error.
        let mut wrong = r;
        wrong.invalidations.clear();
        let d = differences(&f, &wrong, &out);
        assert_eq!(d.len(), 1, "{d:?}");
        assert!(d[0].ends_with("has no evidence"), "{d:?}");
    }

    const TASK: &str = "struct S { n: u64 }\nfn t(s: &S) / async, mut(s..) {\n    scope { sc =>\n        sc.spawn(|| { s.n += 1 })\n        print(s.n)\n    }\n}\n";

    #[test]
    fn wrong_or_missing_evidence_of_w0405_is_a_difference() {
        let (f, r) = body(TASK, "t");
        let out = evaluate_probes(&f).expect("the spec runs");
        assert!(!r.conflicts.is_empty(), "{:?}", r.violations);
        assert_eq!(differences(&f, &r, &out), Vec::<String>::new());
        // The task reads, not writes, its place.
        let mut wrong = r.clone();
        wrong.conflicts[0].task_writes = !wrong.conflicts[0].task_writes;
        assert!(!differences(&f, &wrong, &out).is_empty());
        // A free that the node does not do.
        let mut wrong = r.clone();
        wrong.conflicts[0].free = Some(Cause::Move(VarId(0)));
        assert!(!differences(&f, &wrong, &out).is_empty());
        // No conflict for the violation.
        let mut wrong = r;
        wrong.conflicts.clear();
        assert!(!differences(&f, &wrong, &out).is_empty());
    }
}
