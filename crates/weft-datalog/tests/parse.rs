//! Tests for the parser.

use weft_datalog::{parse_program, parse_program_named, CmpOp, Const, Error, Literal, Term};

/// Parses `src` and returns the line and column of the syntax error.
fn syntax_error(src: &str) -> (usize, usize, String) {
    match parse_program(src) {
        Err(Error::Syntax {
            loc,
            column,
            message,
        }) => (loc.line, column, message),
        other => panic!("expected a syntax error, got {other:?}"),
    }
}

#[test]
fn parses_facts_rules_and_comments() {
    let src = "// a comment\n\
               edge(1, 2). // a trailing comment\n\
               path(X, Y) :- edge(X, Y).\n\
               path(X, Z) :- path(X, Y), edge(Y, Z).\n";
    let p = parse_program(src).expect("valid program");
    assert_eq!(p.facts().len(), 1);
    let fact = &p.facts()[0];
    assert_eq!(fact.relation, "edge");
    assert_eq!(fact.values, vec![Const::Int(1), Const::Int(2)]);
    assert_eq!(fact.loc.line, 2);
    assert_eq!(p.rules().len(), 2);
    assert_eq!(p.rules()[0].to_string(), "path(X, Y) :- edge(X, Y).");
    assert_eq!(
        p.rules()[1].to_string(),
        "path(X, Z) :- path(X, Y), edge(Y, Z)."
    );
    assert_eq!(p.rules()[1].loc.line, 4);
}

#[test]
fn parses_empty_and_comment_only_programs() {
    let p = parse_program("").expect("valid program");
    assert!(p.rules().is_empty() && p.facts().is_empty());
    let p = parse_program("// only a comment").expect("valid program");
    assert!(p.rules().is_empty() && p.facts().is_empty());
}

#[test]
fn parses_strings_symbols_and_negative_integers() {
    let p = parse_program(r#"sym(-42, "a string", foo, "foo", "q\"x\\y\n\t\r")."#)
        .expect("valid program");
    assert_eq!(
        p.facts()[0].values,
        vec![
            Const::Int(-42),
            Const::Sym("a string".into()),
            Const::Sym("foo".into()),
            Const::Sym("foo".into()),
            Const::Sym("q\"x\\y\n\t\r".into()),
        ]
    );
    assert_eq!(
        p.facts()[0].to_string(),
        r#"sym(-42, "a string", foo, foo, "q\"x\\y\n\t\r")."#
    );
}

#[test]
fn parses_extreme_integers() {
    let p = parse_program("n(-9223372036854775808, 9223372036854775807).").expect("valid");
    assert_eq!(
        p.facts()[0].values,
        vec![Const::Int(i64::MIN), Const::Int(i64::MAX)]
    );
}

#[test]
fn parses_nullary_atoms() {
    let p = parse_program("library().\nlint.\nok() :- library(), lint.\nbare :- ok.")
        .expect("valid program");
    assert_eq!(p.facts().len(), 2);
    assert!(p.facts().iter().all(|f| f.values.is_empty()));
    assert_eq!(p.rules()[0].to_string(), "ok() :- library(), lint().");
    assert_eq!(p.rules()[1].to_string(), "bare() :- ok().");
}

#[test]
fn parses_negation_comparisons_and_wildcards() {
    let p =
        parse_program("r(X) :- s(X, _), !b(X, _), X != 3, foo = X, X = Y, t(Y), _V = X, s(_V, _).")
            .expect("valid program");
    let body = &p.rules()[0].body;
    assert!(matches!(&body[0], Literal::Pos(a) if a.terms[1] == Term::Wildcard));
    assert!(matches!(&body[1], Literal::Neg(a) if a.relation == "b"));
    assert!(matches!(&body[2], Literal::Cmp { op: CmpOp::Ne, .. }));
    assert!(matches!(
        &body[3],
        Literal::Cmp { op: CmpOp::Eq, left: Term::Const(Const::Sym(s)), .. } if s == "foo"
    ));
    assert!(matches!(&body[6], Literal::Cmp { left: Term::Var(v), .. } if v == "_V"));
    assert_eq!(
        p.rules()[0].to_string(),
        "r(X) :- s(X, _), !b(X, _), X != 3, foo = X, X = Y, t(Y), _V = X, s(_V, _)."
    );
}

#[test]
fn parses_comparisons_with_literal_left_operands() {
    let p = parse_program("r(X) :- s(X), 1 != X, \"s\" = X, -2 != X.").expect("valid program");
    assert_eq!(
        p.rules()[0].to_string(),
        "r(X) :- s(X), 1 != X, s = X, -2 != X."
    );
}

#[test]
fn display_round_trips() {
    let src = "a(1, \"two words\", sym).\nb() :- a(_, _, _), !c(\"x y\"), 1 != 2.\n";
    let p = parse_program(src).expect("valid program");
    let printed = p.to_string();
    let q = parse_program(&printed).expect("printed program is valid");
    assert_eq!(q.to_string(), printed);
    assert_eq!(
        printed,
        "a(1, \"two words\", sym).\nb() :- a(_, _, _), !c(\"x y\"), 1 != 2.\n"
    );
}

#[test]
fn reports_missing_dot_with_line_and_column() {
    let (line, column, message) = syntax_error("a(1).\nb(2)\nc(3).");
    assert_eq!((line, column), (3, 1));
    assert!(message.contains("expected"), "{message}");
}

#[test]
fn reports_unterminated_string() {
    assert_eq!(syntax_error("a(1).\na(\"abc").0, 2);
    assert_eq!(syntax_error("a(\"abc\ndef\").").0, 1);
}

#[test]
fn reports_bad_escape() {
    let (_, _, message) = syntax_error(r#"a("\q")."#);
    assert!(message.contains("escape"), "{message}");
}

#[test]
fn reports_unexpected_character() {
    let (line, column, _) = syntax_error("a(1) @");
    assert_eq!((line, column), (1, 6));
}

#[test]
fn reports_lone_colon_and_minus() {
    assert_eq!(syntax_error("a :").0, 1);
    assert_eq!(syntax_error("a(-x).").0, 1);
}

#[test]
fn reports_integer_overflow() {
    let (_, _, message) = syntax_error("a(99999999999999999999).");
    assert!(message.contains("integer"), "{message}");
}

#[test]
fn reports_unexpected_end_of_input() {
    let (line, _, message) = syntax_error("a(X) :-\n  b(X)");
    assert_eq!(line, 2);
    assert!(message.contains("end of input"), "{message}");
}

#[test]
fn reports_missing_relation_name() {
    assert_eq!(syntax_error("(1).").1, 1);
    assert_eq!(syntax_error("X :- a(X).").1, 1);
    assert_eq!(syntax_error("a(X) :- !X.").1, 10);
}

#[test]
fn reports_bad_terms_and_literals() {
    assert_eq!(syntax_error("a(,).").1, 3);
    assert_eq!(syntax_error("a(1 2).").1, 5);
    assert_eq!(syntax_error("a(X) :- X b(X).").1, 11);
    assert_eq!(syntax_error("a(X) :- b(X), X != .").1, 20);
}

#[test]
fn rejects_facts_with_variables() {
    match parse_program("a(1).\nb(X, 2).") {
        Err(Error::NotGround { loc, variable }) => {
            assert_eq!(loc.line, 2);
            assert_eq!(variable, "X");
        }
        other => panic!("expected NotGround, got {other:?}"),
    }
    assert!(matches!(
        parse_program("b(_)."),
        Err(Error::NotGround { variable, .. }) if variable == "_"
    ));
}

#[test]
fn error_messages_name_the_line() {
    let err = parse_program("a(1).\nb(2)").expect_err("missing dot");
    assert!(err.to_string().starts_with("line 2, column 5: "), "{err}");
    assert_eq!(err.line(), Some(2));
    let err = parse_program_named("lint.dl", "a(1)").expect_err("missing dot");
    assert!(
        err.to_string().starts_with("lint.dl:1, column 5: "),
        "{err}"
    );
}

#[test]
fn lists_defined_and_used_relations() {
    let p = parse_program(
        "edge(1, 2).\npath(X, Y) :- edge(X, Y).\nreach(X) :- path(X, _), !blocked(X).",
    )
    .expect("valid program");
    let defined: Vec<&str> = p.relations_defined().into_iter().collect();
    assert_eq!(defined, ["edge", "path", "reach"]);
    let used: Vec<&str> = p.relations_used().into_iter().collect();
    assert_eq!(used, ["blocked", "edge", "path"]);
}

#[test]
fn extend_appends_facts_and_rules() {
    let mut spec = parse_program("a(1).\nb(X) :- a(X).").expect("valid program");
    let lint = parse_program_named("lint.dl", "c(X) :- b(X).\na(2).").expect("valid program");
    spec.extend(lint);
    assert_eq!(spec.rules().len(), 2);
    assert_eq!(spec.facts().len(), 2);
    assert_eq!(&*spec.rules()[1].loc.origin, "lint.dl");
    assert!(spec.check().is_ok());
}
