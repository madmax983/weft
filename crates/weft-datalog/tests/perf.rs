//! Performance checks.
//!
//! Run the large cases in release mode:
//! `cargo test -p weft-datalog --release --test perf -- --ignored --nocapture`.

use std::time::Instant;

use weft_datalog::{evaluate, parse_program, Database, EvalOptions, Output, Value};

const TC: &str = "path(X, Y) :- edge(X, Y).\npath(X, Z) :- path(X, Y), edge(Y, Z).\n";

fn int(n: usize) -> Value {
    Value::Int(i64::try_from(n).expect("small"))
}

/// Computes the transitive closure of a chain with `n` nodes.
fn chain(n: usize, provenance: bool) -> Output {
    let program = parse_program(TC).expect("valid");
    let mut db = Database::new();
    for i in 1..n {
        db.insert("edge", [int(i), int(i + 1)]);
    }
    evaluate(&program, db, EvalOptions { provenance }).expect("ok")
}

#[test]
fn chain_closure_small() {
    let n = 300;
    let out = chain(n, true);
    assert_eq!(out.len("path"), n * (n - 1) / 2);
    let d = out.explain("path", &[int(1), int(n)]).expect("derived");
    assert_eq!(d.to_string().lines().count(), 2 * (n - 1));
}

#[test]
#[ignore = "performance target; run in release mode"]
fn chain_closure_2000() {
    let n = 2000;
    for provenance in [false, true] {
        let start = Instant::now();
        let out = chain(n, provenance);
        let elapsed = start.elapsed();
        assert_eq!(out.len("path"), n * (n - 1) / 2);
        println!(
            "chain {n}: {} tuples in {elapsed:?} (provenance {provenance})",
            out.len("path")
        );
        if provenance {
            let start = Instant::now();
            let d = out.explain("path", &[int(1), int(n)]).expect("derived");
            let lines = d.to_string().lines().count();
            println!(
                "explain path(1, {n}): {lines} lines in {:?}",
                start.elapsed()
            );
            assert_eq!(lines, 2 * (n - 1));
        }
    }
}

/// Builds a program and input that look like a compiler check: about 50,000
/// input tuples, joins, recursion and negation.
fn compiler_like(scale: usize) -> (weft_datalog::Program, Database) {
    let src = "\
        // Flow and reachability.
        flows(A, B) :- assign(A, B).
        flows(A, C) :- flows(A, B), assign(B, C).
        // A use is invalid when its variable was moved and not reassigned.
        moved_at(V, P) :- move(V, P).
        invalid(U, V) :- use(U, V, P), moved_at(V, Q), before(Q, P), !reinit(V, P).
        error(U, V) :- invalid(U, V), !allowed(V).
        // Effects.
        handled(F, E) :- calls(F, G), performs(G, E), handler(F, E).
        leaks(F, E) :- calls(F, G), performs(G, E), !handler(F, E), std_effect(E).
        lib_error(F) :- library(), leaks(F, _).
        library().
        std_effect(io).
    ";
    let program = parse_program(src).expect("valid");
    let mut db = Database::new();
    let io = db.sym("io");
    let net = db.sym("net");
    for i in 0..scale {
        let v = int(i);
        if i % 10 != 9 {
            db.insert("assign", [v, int(i + 1)]);
        }
        db.insert("move", [v, int(i % 100)]);
        db.insert("use", [int(i), v, int(i % 100 + 1)]);
        db.insert("before", [int(i % 100), int(i % 100 + 1)]);
        if i % 3 == 0 {
            db.insert("reinit", [v, int(i % 100 + 1)]);
        }
        if i % 5 == 0 {
            db.insert("allowed", [v]);
        }
        db.insert("calls", [v, int((i + 1) % scale)]);
        db.insert("performs", [v, if i % 2 == 0 { io } else { net }]);
        if i % 4 == 0 {
            db.insert("handler", [v, io]);
        }
    }
    (program, db)
}

#[test]
fn compiler_like_small() {
    let (program, db) = compiler_like(500);
    let out = evaluate(&program, db, EvalOptions::default()).expect("ok");
    assert!(out.len("error") > 0);
    assert!(out.len("lib_error") > 0);
    let t = out.tuples("lib_error").remove(0);
    assert!(out.explain("lib_error", &t).is_some());
}

#[test]
#[ignore = "performance target; run in release mode"]
fn compiler_like_50k() {
    let scale = 6000;
    let (program, db) = compiler_like(scale);
    let start = Instant::now();
    let out = evaluate(&program, db, EvalOptions::default()).expect("ok");
    let elapsed = start.elapsed();
    let total: usize = out.relations().map(|r| out.len(r)).sum();
    println!("compiler-like program: {total} tuples in {elapsed:?}");
}
