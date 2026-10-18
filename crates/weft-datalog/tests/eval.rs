//! Tests for evaluation results.

use weft_datalog::{evaluate, parse_program, Database, EvalOptions, Output, Value};

/// Evaluates `src` over `db`.
fn run_with(src: &str, db: Database) -> Output {
    let program = parse_program(src).expect("valid program");
    evaluate(&program, db, EvalOptions::default()).expect("evaluation succeeds")
}

/// Evaluates `src` over an empty database.
fn run(src: &str) -> Output {
    run_with(src, Database::new())
}

/// Returns the tuples of `rel` as sorted text.
fn show(out: &Output, rel: &str) -> Vec<String> {
    out.tuples(rel)
        .iter()
        .map(|t| out.display_tuple(rel, t))
        .collect()
}

const TC: &str = "path(X, Y) :- edge(X, Y).\npath(X, Z) :- path(X, Y), edge(Y, Z).\n";

#[test]
fn computes_transitive_closure() {
    let out = run(&format!("edge(1, 2).\nedge(2, 3).\nedge(3, 4).\n{TC}"));
    assert_eq!(
        show(&out, "path"),
        [
            "path(1, 2)",
            "path(1, 3)",
            "path(1, 4)",
            "path(2, 3)",
            "path(2, 4)",
            "path(3, 4)"
        ]
    );
    assert_eq!(out.len("path"), 6);
}

#[test]
fn computes_transitive_closure_with_a_cycle() {
    let out = run(&format!("edge(a, b).\nedge(b, a).\nedge(b, c).\n{TC}"));
    assert_eq!(
        show(&out, "path"),
        [
            "path(a, a)",
            "path(a, b)",
            "path(a, c)",
            "path(b, a)",
            "path(b, b)",
            "path(b, c)"
        ]
    );
}

#[test]
fn recursion_shape_does_not_change_the_result() {
    let facts = "edge(1, 2).\nedge(2, 3).\nedge(3, 1).\nedge(3, 4).\nedge(5, 5).\n";
    let left = run(&format!("{facts}{TC}"));
    let right = run(&format!(
        "{facts}path(X, Y) :- edge(X, Y).\npath(X, Z) :- edge(X, Y), path(Y, Z).\n"
    ));
    let double = run(&format!(
        "{facts}path(X, Y) :- edge(X, Y).\npath(X, Z) :- path(X, Y), path(Y, Z).\n"
    ));
    assert_eq!(left.tuples("path"), right.tuples("path"));
    assert_eq!(show(&left, "path"), show(&double, "path"));
    assert_eq!(left.len("path"), 4 * 3 + 1);
}

#[test]
fn computes_same_generation() {
    let src = "\
        parent(b, a). parent(c, a). parent(d, b). parent(e, c). parent(f, c).\n\
        person(X) :- parent(X, _).\n\
        person(X) :- parent(_, X).\n\
        sg(X, X) :- person(X).\n\
        sg(X, Y) :- parent(X, XP), sg(XP, YP), parent(Y, YP), X != Y.\n";
    let out = run(src);
    assert_eq!(
        show(&out, "sg")
            .into_iter()
            .filter(|s| !s.starts_with("sg(a") && s.as_bytes()[3] != s.as_bytes()[6])
            .collect::<Vec<_>>(),
        [
            "sg(b, c)", "sg(c, b)", "sg(d, e)", "sg(d, f)", "sg(e, d)", "sg(e, f)", "sg(f, d)",
            "sg(f, e)"
        ]
    );
    assert_eq!(out.len("sg"), 6 + 8);
}

#[test]
fn computes_mutual_recursion() {
    let src = "\
        num(0). num(1). num(2). num(3). num(4). num(5).\n\
        succ(0, 1). succ(1, 2). succ(2, 3). succ(3, 4). succ(4, 5).\n\
        even(0).\n\
        odd(Y) :- even(X), succ(X, Y).\n\
        even(Y) :- odd(X), succ(X, Y).\n";
    let out = run(src);
    assert_eq!(show(&out, "even"), ["even(0)", "even(2)", "even(4)"]);
    assert_eq!(show(&out, "odd"), ["odd(1)", "odd(3)", "odd(5)"]);
}

#[test]
fn applies_stratified_negation() {
    let src = "\
        edge(1, 2). edge(2, 3). edge(3, 4). edge(1, 5).\n\
        start(1). blocked(3).\n\
        reach(X) :- start(X), !blocked(X).\n\
        reach(Y) :- reach(X), edge(X, Y), !blocked(Y).\n\
        node(X) :- edge(X, _).\n\
        node(X) :- edge(_, X).\n\
        unreached(X) :- node(X), !reach(X).\n";
    let out = run(src);
    assert_eq!(show(&out, "reach"), ["reach(1)", "reach(2)", "reach(5)"]);
    assert_eq!(show(&out, "unreached"), ["unreached(3)", "unreached(4)"]);
}

#[test]
fn applies_negation_with_wildcards() {
    let src = "\
        handles(h1, e1). handles(h2, e2). forwards(h1, x).\n\
        silent(H) :- handles(H, _), !forwards(H, _).\n\
        none() :- !missing(_, _).\n";
    let out = run(src);
    assert_eq!(show(&out, "silent"), ["silent(h2)"]);
    assert_eq!(show(&out, "none"), ["none()"]);
    assert_eq!(out.len("missing"), 0);
}

#[test]
fn applies_comparisons() {
    let src = "\
        node(1). node(2). node(3).\n\
        diff(X, Y) :- node(X), node(Y), X != Y.\n\
        same(X, Y) :- node(X), node(Y), X = Y.\n\
        notone(X) :- node(X), X != 1, 1 != X.\n\
        isone(X) :- node(X), 1 = X.\n\
        never(X) :- node(X), 1 = 2.\n\
        always(X) :- node(X), 1 != 2.\n";
    let out = run(src);
    assert_eq!(out.len("diff"), 6);
    assert_eq!(
        show(&out, "same"),
        ["same(1, 1)", "same(2, 2)", "same(3, 3)"]
    );
    assert_eq!(show(&out, "notone"), ["notone(2)", "notone(3)"]);
    assert_eq!(show(&out, "isone"), ["isone(1)"]);
    assert_eq!(out.len("never"), 0);
    assert_eq!(out.len("always"), 3);
}

#[test]
fn compares_integers_and_symbols_as_different() {
    let out = run("v(1). v(\"1\"). d(X, Y) :- v(X), v(Y), X != Y.");
    assert_eq!(show(&out, "d"), ["d(1, \"1\")", "d(\"1\", 1)"]);
}

#[test]
fn derives_nullary_facts_and_rules() {
    let src = "\
        library().\n\
        handles(h1, io). handles(h2, net). handles(h3, io).\n\
        std_effect(io).\n\
        forwards(h3, io).\n\
        lib_error(H) :- library(), handles(H, E), std_effect(E), !forwards(H, E).\n\
        has_errors :- lib_error(_).\n\
        clean() :- !has_errors().\n\
        app_error(H) :- !library(), handles(H, _).\n";
    let out = run(src);
    assert_eq!(show(&out, "lib_error"), ["lib_error(h1)"]);
    assert_eq!(show(&out, "has_errors"), ["has_errors()"]);
    assert!(out.contains("has_errors", &[]));
    assert_eq!(out.len("clean"), 0);
    assert_eq!(out.len("app_error"), 0);
}

#[test]
fn derives_rules_without_positive_atoms() {
    let out = run("p(1) :- !q(1).\nr(a) :- 1 != 2.\ns(X) :- p(X), !q(X).\nq(2).");
    assert_eq!(show(&out, "p"), ["p(1)"]);
    assert_eq!(show(&out, "r"), ["r(a)"]);
    assert_eq!(show(&out, "s"), ["s(1)"]);
}

#[test]
fn joins_on_constants_and_repeated_variables() {
    let src = "\
        sym(x1, \"a string\"). sym(x2, \"a string\"). sym(x3, other).\n\
        kind(x1, atom_constant). kind(x2, \"other\"). kind(x3, atom_constant).\n\
        named(X) :- sym(X, \"a string\"), kind(X, atom_constant).\n\
        e(1, 1). e(1, 2). e(2, 2).\n\
        loop(X) :- e(X, X).\n\
        tag(X, fixed, 7) :- loop(X).\n";
    let out = run(src);
    assert_eq!(show(&out, "named"), ["named(x1)"]);
    assert_eq!(show(&out, "loop"), ["loop(1)", "loop(2)"]);
    assert_eq!(show(&out, "tag"), ["tag(1, fixed, 7)", "tag(2, fixed, 7)"]);
}

#[test]
fn mixes_program_facts_input_facts_and_rules() {
    let mut db = Database::new();
    let a = db.sym("a");
    let b = db.sym("b");
    let c = db.sym("c");
    db.insert("edge", vec![a, b]);
    db.insert("path", vec![c, a]);
    db.insert("edge", vec![a, b]);
    let out = run_with(&format!("edge(b, c).\npath(z, a).\n{TC}"), db);
    assert!(out.contains("path", &[c, c]));
    assert_eq!(
        show(&out, "path"),
        [
            "path(a, b)",
            "path(a, c)",
            "path(b, c)",
            "path(c, a)",
            "path(c, b)",
            "path(c, c)",
            "path(z, a)",
            "path(z, b)",
            "path(z, c)"
        ]
    );
    assert_eq!(show(&out, "edge"), ["edge(a, b)", "edge(b, c)"]);
}

#[test]
fn symbols_and_strings_from_input_and_program_are_equal() {
    let mut db = Database::new();
    let x = db.sym("x1");
    let kind = db.sym("atom_constant");
    let text = db.sym("a string");
    db.insert("kind", [x, kind]);
    db.insert("sym", [x, text]);
    let out = run_with(
        "named(X) :- sym(X, \"a string\"), kind(X, \"atom_constant\").",
        db,
    );
    assert!(out.contains("named", &[x]));
    assert_eq!(out.symbol("atom_constant"), Some(kind));
    assert_eq!(out.symbol("never interned"), None);
}

#[test]
fn keeps_input_relations_that_the_program_does_not_use() {
    let mut db = Database::new();
    db.insert("extra", [Value::Int(3), Value::Int(-1)]);
    assert_eq!(db.len("extra"), 1);
    assert_eq!(db.len("missing"), 0);
    let out = run_with("p(1).", db);
    assert_eq!(show(&out, "extra"), ["extra(3, -1)"]);
    let names: Vec<&str> = out.relations().collect();
    assert_eq!(names, ["extra", "p"]);
}

#[test]
fn unknown_relations_are_empty() {
    let out = run("p(X) :- q(X).");
    assert!(out.tuples("nothing").is_empty());
    assert!(!out.contains("nothing", &[Value::Int(1)]));
    assert!(!out.contains("p", &[Value::Int(1), Value::Int(2)]));
    assert!(out.explain("nothing", &[]).is_none());
    assert_eq!(out.len("nothing"), 0);
    assert_eq!(out.len("q"), 0);
}

#[test]
fn sorts_tuples_by_value() {
    let out = run("v(b). v(10). v(\"B\"). v(-3). v(a). v(2). v(\"a b\").");
    assert_eq!(
        show(&out, "v"),
        [
            "v(-3)",
            "v(2)",
            "v(10)",
            "v(\"B\")",
            "v(a)",
            "v(\"a b\")",
            "v(b)"
        ]
    );
}

#[test]
fn displays_values_in_datalog_syntax() {
    let mut db = Database::new();
    let plain = db.sym("n12");
    let spaced = db.sym("a \"quoted\" word");
    let upper = db.sym("Upper");
    let empty = db.sym("");
    assert_eq!(db.display(plain), "n12");
    assert_eq!(db.display(spaced), "\"a \\\"quoted\\\" word\"");
    assert_eq!(db.display(upper), "\"Upper\"");
    assert_eq!(db.display(empty), "\"\"");
    assert_eq!(db.display(Value::Int(-7)), "-7");
    assert_eq!(db.sym("n12"), plain);
    assert_eq!(
        db.interner().resolve(upper.as_sym().expect("symbol")),
        Some("Upper")
    );
    assert_eq!(upper.as_int(), None);
    assert_eq!(Value::Int(4).as_int(), Some(4));
    assert_eq!(Value::from(4), Value::Int(4));
    let out = run_with("", db);
    assert_eq!(out.display_value(plain), "n12");
    assert_eq!(out.interner().get("n12").map(Value::Sym), Some(plain));
}

#[test]
fn loads_input_facts_from_text() {
    let mut db = Database::new();
    let n = db
        .load_facts("edge(a, b).\nedge(b, c). // comment\nedge(a, b).")
        .expect("valid facts");
    assert_eq!(n, 3);
    assert_eq!(db.len("edge"), 2);
    let out = run_with(TC, db);
    assert_eq!(out.len("path"), 3);
    let a = out.symbol("a").expect("interned");
    let derivation = out.explain("edge", &[a, out.symbol("b").expect("interned")]);
    assert!(derivation
        .expect("input fact")
        .to_string()
        .ends_with("[input]"));
}

#[test]
fn load_facts_rejects_rules_and_bad_syntax() {
    let mut db = Database::new();
    assert!(db.load_facts("p(X) :- q(X).").is_err());
    assert!(db.load_facts("p(1)").is_err());
}

#[test]
fn provenance_off_gives_the_same_tuples() {
    let src = format!("edge(1, 2). edge(2, 3). edge(3, 1).\n{TC}");
    let program = parse_program(&src).expect("valid");
    let with = evaluate(&program, Database::new(), EvalOptions::default()).expect("ok");
    let without =
        evaluate(&program, Database::new(), EvalOptions { provenance: false }).expect("ok");
    assert_eq!(with.tuples("path"), without.tuples("path"));
    let t = [Value::Int(1), Value::Int(1)];
    assert!(with.explain("path", &t).is_some());
    assert!(without.explain("path", &t).is_none());
}

#[test]
fn evaluates_extended_programs() {
    let mut spec = parse_program(&format!("edge(1, 2). edge(2, 3).\n{TC}")).expect("valid");
    let lint = parse_program("long(X, Y) :- path(X, Y), !edge(X, Y).").expect("valid");
    spec.extend(lint);
    let out = evaluate(&spec, Database::new(), EvalOptions::default()).expect("ok");
    assert_eq!(show(&out, "long"), ["long(1, 3)"]);
    let d = out
        .explain("long", &[Value::Int(1), Value::Int(3)])
        .expect("derived");
    assert_eq!(d.rule_index(), Some(2));
}

#[test]
fn evaluates_many_strata() {
    let src = "\
        n(1). n(2). n(3). n(4).\n\
        a(X) :- n(X), X != 1.\n\
        b(X) :- n(X), !a(X).\n\
        c(X) :- n(X), !b(X), X != 2.\n\
        d(X) :- n(X), !c(X).\n\
        e(X) :- d(X), !b(X).\n";
    let out = run(src);
    assert_eq!(show(&out, "b"), ["b(1)"]);
    assert_eq!(show(&out, "c"), ["c(3)", "c(4)"]);
    assert_eq!(show(&out, "d"), ["d(1)", "d(2)"]);
    assert_eq!(show(&out, "e"), ["e(2)"]);
}

#[test]
fn output_is_reusable_after_clone() {
    let mut db = Database::new();
    db.insert("edge", [Value::Int(1), Value::Int(2)]);
    let copy = db.clone();
    let program = parse_program(TC).expect("valid");
    let first = evaluate(&program, db, EvalOptions::default()).expect("ok");
    let second = evaluate(&program, copy, EvalOptions::default()).expect("ok");
    assert_eq!(first.tuples("path"), second.tuples("path"));
}
