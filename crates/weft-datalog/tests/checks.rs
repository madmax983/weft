//! Tests for the static checks: arity, range restriction and stratification.

use weft_datalog::{
    evaluate, parse_program, parse_program_named, Database, Error, EvalOptions, Place,
};

#[test]
fn rejects_arity_mismatch_between_fact_and_rule() {
    match parse_program("edge(1, 2).\np(X) :- edge(X).") {
        Err(Error::Arity {
            loc,
            relation,
            found,
            expected,
            first,
        }) => {
            assert_eq!(relation, "edge");
            assert_eq!((loc.line, found), (2, 1));
            assert_eq!((first.line, expected), (1, 2));
        }
        other => panic!("expected an arity error, got {other:?}"),
    }
}

#[test]
fn rejects_arity_mismatch_in_heads_and_negations() {
    let err = parse_program("p(X) :- q(X).\np(X, Y) :- q(X), q(Y).").expect_err("arity");
    assert!(matches!(&err, Error::Arity { relation, .. } if relation == "p"));
    assert_eq!(err.line(), Some(2));
    let err = parse_program("p(X) :- q(X), !r(X).\ns(X) :- q(X), !r(X, X).").expect_err("arity");
    assert!(matches!(&err, Error::Arity { relation, .. } if relation == "r"));
    let err = parse_program("lib().\nok() :- lib(1).").expect_err("arity");
    assert!(err.to_string().contains("`lib`"), "{err}");
}

#[test]
fn rejects_unbound_head_variable() {
    match parse_program("q(1).\np(X, Y) :- q(X).") {
        Err(Error::Unbound {
            loc,
            variable,
            place,
        }) => {
            assert_eq!(loc.line, 2);
            assert_eq!(variable, "Y");
            assert_eq!(place, Place::Head);
        }
        other => panic!("expected an unbound variable error, got {other:?}"),
    }
}

#[test]
fn rejects_variable_bound_only_by_negation() {
    let err = parse_program("p(X) :- !q(X).").expect_err("unbound");
    assert!(matches!(
        err,
        Error::Unbound {
            place: Place::Head,
            ..
        }
    ));
    let err = parse_program("p(X) :- q(X), !r(Y).").expect_err("unbound");
    assert!(
        matches!(&err, Error::Unbound { variable, place: Place::Negation, .. } if variable == "Y")
    );
    assert!(err.to_string().contains("negated atom"), "{err}");
}

#[test]
fn rejects_unbound_comparison_variable() {
    let err = parse_program("p(X) :- q(X), X != Y.").expect_err("unbound");
    assert!(
        matches!(&err, Error::Unbound { variable, place: Place::Comparison, .. } if variable == "Y")
    );
    let err = parse_program("p(X) :- q(X), Y = X.").expect_err("unbound");
    assert!(matches!(
        err,
        Error::Unbound {
            place: Place::Comparison,
            ..
        }
    ));
}

#[test]
fn rejects_wildcards_in_heads_and_comparisons() {
    let err = parse_program("p(_) :- q(1).").expect_err("wildcard");
    assert!(matches!(
        err,
        Error::Wildcard {
            place: Place::Head,
            ..
        }
    ));
    let err = parse_program("p(X) :- q(X), X != _.").expect_err("wildcard");
    assert!(matches!(
        err,
        Error::Wildcard {
            place: Place::Comparison,
            ..
        }
    ));
    assert!(err.to_string().contains("comparison"), "{err}");
}

#[test]
fn accepts_wildcards_in_negated_atoms() {
    assert!(parse_program("p(X) :- q(X), !r(X, _).").is_ok());
}

#[test]
fn rejects_negation_on_itself() {
    match parse_program("q(1).\np(X) :- q(X), !p(X).") {
        Err(Error::Stratification {
            loc,
            relation,
            cycle,
        }) => {
            assert_eq!(loc.line, 2);
            assert_eq!(relation, "p");
            assert_eq!(cycle, "p -> !p");
        }
        other => panic!("expected a stratification error, got {other:?}"),
    }
}

#[test]
fn rejects_negation_inside_a_longer_cycle() {
    let src = "n(1).\na(X) :- n(X), !b(X).\nb(X) :- c(X).\nc(X) :- n(X), a(X).";
    let err = parse_program(src).expect_err("not stratified");
    assert_eq!(err.line(), Some(2));
    assert!(matches!(&err, Error::Stratification { cycle, .. } if cycle == "a -> !b -> c -> a"));
    assert!(err.to_string().contains("recursive cycle"), "{err}");
}

#[test]
fn accepts_negation_on_a_lower_stratum() {
    let src = "n(1).\nb(X) :- n(X), b(X).\na(X) :- n(X), !b(X).\nc(X) :- a(X), !b(X), c(X).";
    assert!(parse_program(src).is_ok());
}

#[test]
fn extend_is_checked_at_evaluate_time() {
    let mut spec = parse_program("edge(1, 2).\npath(X, Y) :- edge(X, Y).").expect("valid");
    let lint = parse_program_named("lint.dl", "bad(X) :- path(X).").expect("valid alone");
    spec.extend(lint);
    let err = evaluate(&spec, Database::new(), EvalOptions::default()).expect_err("arity");
    assert!(err.to_string().starts_with("lint.dl:1: "), "{err}");

    let mut spec = parse_program("n(1).\np(X) :- n(X), !q(X).").expect("valid");
    let lint = parse_program("q(X) :- p(X).").expect("valid alone");
    spec.extend(lint);
    let err = spec.check().expect_err("not stratified");
    assert!(matches!(err, Error::Stratification { .. }));
}

#[test]
fn rejects_input_with_wrong_arity() {
    let program = parse_program("path(X, Y) :- edge(X, Y).").expect("valid");
    let mut db = Database::new();
    let a = db.sym("a");
    db.insert("edge", vec![a]);
    match evaluate(&program, db, EvalOptions::default()) {
        Err(Error::InputArity {
            loc,
            relation,
            expected,
            found,
        }) => {
            assert_eq!(relation, "edge");
            assert_eq!(loc.line, 1);
            assert_eq!((expected, found), (1, 2));
        }
        other => panic!("expected an input arity error, got {other:?}"),
    }
}

#[test]
fn rejects_database_with_mixed_arity() {
    let program = parse_program("").expect("valid");
    let mut db = Database::new();
    let a = db.sym("a");
    db.insert("edge", [a, a]);
    db.insert("edge", [a]);
    db.insert("edge", [a, a, a]);
    match evaluate(&program, db, EvalOptions::default()) {
        Err(Error::DatabaseArity {
            relation,
            expected,
            found,
        }) => {
            assert_eq!(relation, "edge");
            assert_eq!((expected, found), (2, 1));
        }
        other => panic!("expected a database arity error, got {other:?}"),
    }
}

#[test]
fn error_line_is_none_for_database_errors() {
    let err = Error::DatabaseArity {
        relation: "r".into(),
        expected: 1,
        found: 2,
    };
    assert_eq!(err.line(), None);
    assert!(err.to_string().contains("input database"), "{err}");
}

#[test]
fn components_group_relations_that_depend_on_each_other() {
    let p = parse_program(
        "edge(1, 2).\n\
         live_in(X) :- edge(X, _).\n\
         live_in(X) :- live_out(X).\n\
         live_out(X) :- edge(X, Y), live_in(Y).\n\
         path(X, Y) :- edge(X, Y).\n\
         path(X, Z) :- path(X, Y), edge(Y, Z).\n\
         top(X) :- path(X, _), live_in(X).",
    )
    .expect("parses");
    let comps = p.components().expect("checks");
    let find = |r: &str| comps.iter().position(|c| c.iter().any(|x| x == r));
    assert_eq!(find("live_in"), find("live_out"));
    assert_ne!(find("live_in"), find("path"));
    assert_ne!(find("edge"), find("path"));
    // A component comes after the components that it depends on.
    assert!(find("edge") < find("path") && find("path") < find("top"));
    assert!(find("live_out") < find("top"));
    assert_eq!(comps.iter().map(Vec::len).sum::<usize>(), 5);
}
