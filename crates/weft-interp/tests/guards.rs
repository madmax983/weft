//! Run-time guards. The checker rejects these programs; the interpreter runs the
//! unchecked analysis and must stop with a clear error.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

use weft_interp::{run_analysis_main, run_analysis_tests, ErrorKind, RunOptions, RunOutcome};
use weft_sema::Options;

fn opts() -> RunOptions {
    RunOptions {
        max_steps: Some(100_000),
        ..RunOptions::default()
    }
}

fn run(src: &str) -> Result<RunOutcome, weft_interp::RuntimeError> {
    let a = weft_sema::analyze_source(src, Options::default()).unwrap();
    run_analysis_main(&a, &opts())
}

fn fault(src: &str, want: &str) {
    match run(src) {
        Ok(o) => panic!("expected `{want}`, but the program ran: {}", o.stdout),
        Err(e) => assert!(
            e.message.contains(want),
            "expected `{want}`, found `{}`",
            e.message
        ),
    }
}

#[test]
fn guards_on_values() {
    fault(
        "fn main() { let v = Vec.new()\n let w = v\n print(v.len()) }",
        "used after it was moved",
    );
    fault("fn main() { let n = 5\n n(1) }", "cannot be called");
    fault(
        "struct P { x: u64 }\nfn main() { let p = P { x: 1 }\n print(p.y) }",
        "no field `y`",
    );
    fault("fn main() { let n = 5\n n.foo() }", "no method `foo`");
    fault("fn main() { let n = 5\n print(n[0]) }", "has no elements");
    fault("fn main() { print(1 + true) }", "cannot apply");
    fault("fn main() { if 1 { print(1) } }", "a boolean is needed");
    fault("fn main() { print(-true) }", "`-` needs an integer");
    fault("fn main() { print(!5) }", "a boolean is needed");
    fault("fn main() { let v = [1]\n print(v[-1]) }", "out of bounds");
    fault("fn main() { print(1.s - 2.s) }", "duration underflow");
    fault(
        "fn main() { print(18446744073709551615) }",
        "integer literal is too large",
    );
    fault("fn main() { for x in 5 { print(x) } }", "has no elements");
    fault(
        "fn main() { let (a, b) = (1, 2, 3) }",
        "not a tuple of that size",
    );
    fault(
        "struct S { x: u64 }\nfn main() { let S(a) = 5 }",
        "not a struct of that size",
    );
    fault(
        "fn main() { let x = 9223372036854775807\n print(x * 2) }",
        "integer overflow",
    );
    fault("fn main() { let z = 0\n print(5 % z) }", "division by zero");
    fault(
        "fn main() { print(2 - 3 + -9223372036854775807 - 9) }",
        "overflow",
    );
}

#[test]
fn guards_on_names_and_calls() {
    fault("fn main() { print(nope) }", "unknown name");
    fault("fn main() { nope(1) }", "unknown function");
    fault("fn main() { break }", "outside a loop");
    fault("fn main() { let r = 1..2 }", "only valid in `for`");
    fault(
        "fn add(a: u64) -> u64 { a }\nfn main() { add(1) = 3 }",
        "must be a place",
    );
    fault(
        "enum E { A, B }\nfn main() { let e = B\n match e { A => print(1) } }",
        "no `match` arm",
    );
    fault(
        "enum E { A(u64) }\nfn main() { let A(x) = A(1) }",
        "needs `match`",
    );
    fault("fn main() { let s = Q { x: 1 } }", "unknown struct");
    fault("fn f(a: u64) {}\nfn main() { f() }", "misses an argument");
    fault(
        "fn main() { let f = |x: u64| x\n f() }",
        "takes 1 arguments",
    );
    fault("fn main() { handle Nope { } in 1 }", "unknown effect");
    fault("fn main() { print(Log.info) }", "needs a call");
    fault(
        "mod m { pub struct S { x: u64 } }\nfn main() { print(m.S) }",
        "no value `S` in this module",
    );
    fault(
        "enum E { A }\nfn main() { print(E.Z) }",
        "no value `Z` here",
    );
    fault(
        "struct S { x: u64 }\nfn main() { S.nope() }",
        "has no function",
    );
    fault("fn main() { Log.nope() }", "no operation");
    fault("mod m {}\nfn main() { m.nope() }", "no function `nope`");
    fault("enum E { A }\nfn main() { E(1) }", "has no constructor");
    fault("enum E { A }\nfn main() { let e = E { } }", "not a struct");
    fault(
        "struct S { x: u64 }\nfn main() { let s = S { y: 1 } }",
        "no field `y`",
    );
    fault(
        "fn main() / io { scope { s => s.spawn(5) } }",
        "a task needs a closure",
    );
    fault("fn main() / par { fork(1, 2) }", "a task needs a closure");
    fault("extern fn ffi()\nfn main() { (5)(1) }", "cannot be called");
}

#[test]
fn guards_allow_valid_unusual_forms() {
    let o = run(
        "mod m { pub struct S { x: u64 }\n pub fn f() -> u64 { 7 } }\nenum E { A(u64), B }\n\
         fn main(env: Env) / io {\n print(m.S(1), E.A(2), E.B, m.f)\n let g = m.f\n print(g())\n\
         print(env.fs, env.stdout, env.net.listen(\":1\"))\n\
         scope { s =>\n let t = s.spawn(|| 1)\n print(t, s)\n t.join()\n }\n\
         handle Log { fn info(m) { print(resume)\n resume(()) } } in log.info(\"x\")\n\
         let x = 0\n let x = x + 1\n print(x)\n let y\n y = 4\n print(y)\n}",
    )
    .unwrap();
    assert_eq!(
        o.stdout,
        "S { x: 1 } A(2) B <fn m.f>\n7\n<FsCap> <Stdout> <Listener>\n<task 1> <scope>\n<continuation>\n1\n4\n"
    );
}

#[test]
fn unwinding_finds_nested_linear_values_innermost_first() {
    // Values in a frame unwind from the newest local to the oldest; values inside
    // a Vec, a Box, a tuple or a struct field are found too.
    let src = "linear struct Tx { id: u64 }\n on abort = undo\n\
        linear struct Bare { id: u64 }\n\
        struct Holder { tx: Tx, n: u64 }\n\
        fn undo(t: Tx) { let Tx(id) = t\n print(\"undo {id}\") }\n\
        fn work() / fail {\n let txs = Vec.new()\n txs.push(Tx { id: 1 })\n txs.push(Tx { id: 2 })\n\
         let h = Holder { tx: Tx { id: 3 }, n: 0 }\n let b = Box.new(Tx { id: 4 })\n\
         let pair = (Tx { id: 5 }, 1)\n let bare = Bare { id: 6 }\n let e = Some(Tx { id: 7 })\n fail(\"stop\")\n }\n\
        fn main() { handle Fail { fn fail(m) { print(\"caught {m}\") } } in work() }";
    let o = run(src).unwrap();
    assert_eq!(
        o.stdout,
        "caught stop\nundo 7\nundo 5\nundo 4\nundo 3\nundo 1\nundo 2\n"
    );
}

#[test]
fn deadlock_is_detected() {
    // A task that waits for itself can never wake.
    let src =
        "fn main() / io {\n scope { s =>\n let t = s.spawn(|| 1)\n let u = t\n t.join()\n }\n}";
    let e = run(src).unwrap_err();
    assert!(
        e.message.contains("moved") || e.kind == ErrorKind::Deadlock,
        "{e}"
    );
}

#[test]
fn unchecked_tests_run() {
    let a = weft_sema::analyze_source(
        "test \"t\" { print(nope) }\ntest \"u\" { print(1) }",
        Options::default(),
    )
    .unwrap();
    let ts = run_analysis_tests(&a, &opts());
    assert!(!ts[0].passed);
    assert!(ts[1].passed);
}
