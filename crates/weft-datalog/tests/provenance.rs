//! Tests for provenance: `explain`, the derivation tree and its output formats.

use std::fmt::Write as _;

use weft_datalog::{
    evaluate, parse_program, Database, Derivation, EvalOptions, Output, Premise, Reason, Value,
};

const CHECKER: &str = "\
// The checker rules.
error(R, P) :- uses(R, P), invalid(R, P).
invalid(R, P) :- uses(R, P), !declared(R, P), R != P.
kind(atom).
tagged(R) :- uses(R, _), kind(K), K = atom, !silenced(R, _).
";

/// Evaluates the checker over a small input database.
fn checker() -> (Output, Value, Value) {
    let program = parse_program(CHECKER).expect("valid program");
    let mut db = Database::new();
    let v1 = db.sym("v1");
    let n4 = db.sym("n4");
    let n5 = db.sym("n5");
    db.insert("uses", [v1, n4]);
    db.insert("uses", [v1, n5]);
    db.insert("declared", [v1, n5]);
    let out = evaluate(&program, db, EvalOptions::default()).expect("evaluation succeeds");
    (out, v1, n4)
}

/// Checks that `d` is a valid proof in `out` and returns its node count.
fn validate(out: &Output, d: &Derivation) -> usize {
    assert!(out.contains(&d.fact.relation, &d.fact.values), "{d}");
    match &d.reason {
        Reason::Input | Reason::Fact { .. } => {
            assert!(d.premises().is_empty());
            1
        }
        Reason::Rule { premises, .. } => {
            let mut size = 1;
            for premise in premises {
                match premise {
                    Premise::Derived(child) => size += validate(out, child),
                    Premise::Absent { relation, args, .. } => {
                        assert!(!out.tuples(relation).iter().any(|t| {
                            t.iter().zip(args).all(|(v, a)| a.is_none_or(|a| a == *v))
                        }));
                        size += 1;
                    }
                    Premise::Holds {
                        op, left, right, ..
                    } => {
                        assert!(op.holds(*left, *right));
                        size += 1;
                    }
                }
            }
            size
        }
    }
}

#[test]
fn explains_a_derived_fact() {
    let (out, v1, n4) = checker();
    let d = out
        .explain("error", &[v1, n4])
        .expect("error(v1, n4) is derived");
    assert_eq!(d.fact.relation, "error");
    assert_eq!(d.fact.values, vec![v1, n4]);
    assert_eq!(d.fact.to_string(), "error(v1, n4)");
    assert_eq!(d.rule_index(), Some(0));
    match &d.reason {
        Reason::Rule {
            index,
            text,
            premises,
        } => {
            assert_eq!(*index, 0);
            assert_eq!(text, "error(R, P) :- uses(R, P), invalid(R, P).");
            assert_eq!(premises.len(), 2);
        }
        other => panic!("expected a rule, got {other:?}"),
    }
    assert_eq!(validate(&out, &d), 6);
}

#[test]
fn display_shows_an_indented_tree() {
    let (out, v1, n4) = checker();
    let d = out.explain("error", &[v1, n4]).expect("derived");
    assert_eq!(
        d.to_string(),
        "\
error(v1, n4)  by  error(R, P) :- uses(R, P), invalid(R, P).
  uses(v1, n4)  [input]
  invalid(v1, n4)  by  invalid(R, P) :- uses(R, P), !declared(R, P), R != P.
    uses(v1, n4)  [input]
    not declared(v1, n4)
    v1 != n4"
    );
}

#[test]
fn display_shows_program_facts_and_wildcards() {
    let (out, v1, _) = checker();
    let d = out.explain("tagged", &[v1]).expect("derived");
    assert_eq!(
        d.to_string(),
        "\
tagged(v1)  by  tagged(R) :- uses(R, _), kind(K), K = atom, !silenced(R, _).
  uses(v1, n4)  [input]
  kind(atom)  [fact]
  atom = atom
  not silenced(v1, _)"
    );
    assert_eq!(validate(&out, &d), 5);
}

#[test]
fn explains_input_and_program_facts_as_leaves() {
    let (out, v1, n4) = checker();
    let d = out.explain("uses", &[v1, n4]).expect("input fact");
    assert!(matches!(d.reason, Reason::Input));
    assert_eq!(d.rule_index(), None);
    let atom = out.symbol("atom").expect("interned");
    let d = out.explain("kind", &[atom]).expect("program fact");
    assert!(matches!(&d.reason, Reason::Fact { loc } if loc.line == 4));
    assert_eq!(d.to_string(), "kind(atom)  [fact]");
}

#[test]
fn does_not_explain_missing_facts() {
    let (out, v1, _) = checker();
    let n5 = out.symbol("n5").expect("interned");
    assert!(out.explain("error", &[v1, n5]).is_none());
    assert!(out.explain("error", &[v1]).is_none());
}

#[test]
fn every_derived_fact_has_a_finite_valid_proof() {
    let src = "\
        edge(1, 2). edge(2, 3). edge(3, 1). edge(3, 4). blocked(4).\n\
        path(X, Y) :- edge(X, Y).\n\
        path(X, Z) :- path(X, Y), path(Y, Z).\n\
        free(X, Y) :- path(X, Y), !blocked(Y), X != Y.\n";
    let program = parse_program(src).expect("valid");
    let out = evaluate(&program, Database::new(), EvalOptions::default()).expect("ok");
    for rel in ["edge", "path", "free"] {
        for t in out.tuples(rel) {
            let d = out.explain(rel, &t).expect("every tuple has a proof");
            assert!(validate(&out, &d) >= 1);
        }
    }
}

#[test]
fn explains_long_chains_without_overflow() {
    let n: i64 = 400;
    let mut src =
        String::from("path(X, Y) :- edge(X, Y).\npath(X, Z) :- path(X, Y), edge(Y, Z).\n");
    for i in 1..n {
        writeln!(src, "edge({i}, {}).", i + 1).expect("write to a string");
    }
    let program = parse_program(&src).expect("valid");
    let out = evaluate(&program, Database::new(), EvalOptions::default()).expect("ok");
    let d = out
        .explain("path", &[Value::Int(1), Value::Int(n)])
        .expect("derived");
    // One path node and one edge leaf for each of the n - 1 steps.
    let nodes = 2 * usize::try_from(n - 1).expect("small");
    assert_eq!(validate(&out, &d), nodes);
    assert_eq!(d.to_string().lines().count(), nodes);
}

#[test]
fn explains_very_deep_derivations() {
    let n: i64 = 20_000;
    let program =
        parse_program("reach(X) :- start(X).\nreach(Y) :- reach(X), edge(X, Y).").expect("valid");
    let mut db = Database::new();
    db.insert("start", [Value::Int(0)]);
    for i in 0..n {
        db.insert("edge", [Value::Int(i), Value::Int(i + 1)]);
    }
    let out = evaluate(&program, db, EvalOptions::default()).expect("ok");
    let d = out.explain("reach", &[Value::Int(n)]).expect("derived");
    assert_eq!(d.premises().len(), 2);
    let json = d.to_json(out.interner());
    assert!(
        json.starts_with(r#"{"fact":"reach(20000)","#),
        "{}",
        &json[..80]
    );
    assert!(json.ends_with(r#""args":[19999,20000],"source":"input"}]}"#));
    assert_eq!(json.matches(r#""source":"rule""#).count(), 20_001);
    // The text has quadratic size (indentation), so check a smaller tree.
    let small = out.explain("reach", &[Value::Int(2000)]).expect("derived");
    let text = small.to_string();
    assert_eq!(text.lines().count(), 2 * 2001);
    let deepest = format!("{:width$}start(0)  [input]", "", width = 2 * 2001);
    assert!(text.lines().any(|line| line == deepest));
    assert!(text.ends_with("\n  edge(1999, 2000)  [input]"));
    // Dropping a deep tree must not overflow the stack.
    drop(d);
}

#[test]
fn renders_json() {
    let (out, v1, n4) = checker();
    let d = out.explain("error", &[v1, n4]).expect("derived");
    assert_eq!(
        d.to_json(out.interner()),
        concat!(
            r#"{"fact":"error(v1, n4)","relation":"error","args":["v1","n4"],"source":"rule","rule":0,"#,
            r#""text":"error(R, P) :- uses(R, P), invalid(R, P).","premises":["#,
            r#"{"fact":"uses(v1, n4)","relation":"uses","args":["v1","n4"],"source":"input"},"#,
            r#"{"fact":"invalid(v1, n4)","relation":"invalid","args":["v1","n4"],"source":"rule","rule":1,"#,
            r#""text":"invalid(R, P) :- uses(R, P), !declared(R, P), R != P.","premises":["#,
            r#"{"fact":"uses(v1, n4)","relation":"uses","args":["v1","n4"],"source":"input"},"#,
            r#"{"not":"declared(v1, n4)","relation":"declared","args":["v1","n4"]},"#,
            r#"{"holds":"v1 != n4"}]}]}"#
        )
    );
    let d = out.explain("tagged", &[v1]).expect("derived");
    let json = d.to_json(out.interner());
    assert!(
        json.contains(
            r#"{"fact":"kind(atom)","relation":"kind","args":["atom"],"source":"fact","line":4}"#
        ),
        "{json}"
    );
    assert!(
        json.contains(r#"{"not":"silenced(v1, _)","relation":"silenced","args":["v1",null]}"#),
        "{json}"
    );
}

#[test]
fn renders_json_escapes_and_integers() {
    let program = parse_program("p(-3, \"a \\\"q\\\"\\n\\\\\").").expect("valid");
    let out = evaluate(&program, Database::new(), EvalOptions::default()).expect("ok");
    let t = out.tuples("p").pop().expect("one tuple");
    let json = out.explain("p", &t).expect("fact").to_json(out.interner());
    assert_eq!(
        json,
        r#"{"fact":"p(-3, \"a \\\"q\\\"\\n\\\\\")","relation":"p","args":[-3,"a \"q\"\n\\"],"source":"fact","line":1}"#
    );
}
