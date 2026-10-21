//! Size limits of the whole pipeline.
//!
//! For each deep or long construct, the test finds the largest program that the
//! parser accepts. That program must go through every stage on a 2 MiB thread,
//! the stack of a test thread: parse, print, analyze, check, the spec, the
//! builder of the IR, the interpreter and drop. The library moves its stages to
//! a thread with a large stack (`weft_sema::on_large_stack`), so the test keeps
//! them on the 2 MiB thread with `weft_sema::on_current_stack`. A larger program
//! gets a parser error, never a stack overflow. A flat chain of binary
//! operators has no limit.
//!
//! The derivation printer of `check --explain` does not recurse. It folds a
//! long chain of relations that depend on each other, so a long path in a
//! body gives a short text.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use weft_interp::RunOptions;
use weft_sema::Options;

/// The stack of a test thread.
const STACK: usize = 2 * 1024 * 1024;

/// Runs every stage on `src` on a small stack. Returns the output of `main`
/// if the checker accepts the program.
fn pipeline(src: String) -> Option<String> {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            weft_sema::on_current_stack(|| {
                let file = weft_syntax::parse_file(&src).expect("the program parses");
                let text = weft_syntax::pretty::pretty(&file);
                if let Err(e) = weft_syntax::parse_file(&text) {
                    panic!("the printed program does not parse: {e}\n{text}");
                }
                assert!(!format!("{file:?}").is_empty());
                drop(file);
                let checked = weft_check::check_source("limit.wf", &src, Options::default());
                assert!(weft_check::agreement(&checked).is_ok());
                let ir = weft_sema::irbuild::build(&checked.analysis);
                assert!(ir.broken.is_empty(), "the IR breaks rules: {:?}", ir.broken);
                // The builder is total: each body is built or has a reason for
                // no IR (a type error of the program).
                for e in &ir.entries {
                    assert!(
                        !matches!(e.outcome, weft_sema::irbuild::Outcome::Unsupported(_)),
                        "{}: {:?}",
                        e.name,
                        e.outcome
                    );
                }
                if !checked.ok() {
                    return None;
                }
                let opts = RunOptions {
                    max_steps: Some(10_000_000),
                    ..RunOptions::default()
                };
                let out = weft_interp::run_main(&checked, &opts).expect("main runs");
                Some(out.stdout)
            })
        })
        .expect("the thread starts")
        .join()
        .expect("no stage panics")
}

/// Finds the largest `n` up to `max` for which `make(n)` parses. Parsing is
/// monotone in `n`.
fn largest(make: &dyn Fn(usize) -> String, max: usize) -> usize {
    let (mut lo, mut hi) = (0, max);
    assert!(weft_syntax::parse_file(&make(1)).is_ok(), "{}", make(1));
    lo += 1;
    while lo < hi {
        let mid = (lo + hi).div_ceil(2);
        if weft_syntax::parse_file(&make(mid)).is_ok() {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    lo
}

/// The lines `1` to `n`.
fn numbers(n: usize) -> String {
    use std::fmt::Write as _;
    let mut s = String::new();
    for i in 1..=n {
        let _ = writeln!(s, "{i}");
    }
    s
}

fn rep(s: &str, n: usize) -> String {
    s.repeat(n)
}

/// A program whose `main` prints `f()`.
fn main_prints(f: &str) -> String {
    format!("{f}\nfn main() {{ print(f()) }}\n")
}

/// The nesting around a chain in the mixed constructs: half the nesting limit.
const HALF: usize = 46;

/// Each construct, its documented limit, and the output of `main` at the limit.
#[allow(clippy::type_complexity)]
fn constructs() -> Vec<(&'static str, Box<dyn Fn(usize) -> String>, usize)> {
    vec![
        (
            "blocks",
            Box::new(|n| {
                main_prints(&format!(
                    "fn f() -> u64 {{ {}1{} }}",
                    rep("{ ", n),
                    rep(" }", n)
                ))
            }),
            94,
        ),
        (
            "parentheses",
            Box::new(|n| {
                main_prints(&format!(
                    "fn f() -> u64 {{ {}1{} }}",
                    rep("(", n),
                    rep(")", n)
                ))
            }),
            94,
        ),
        (
            "closures",
            Box::new(|n| {
                main_prints(&format!(
                    "fn f() -> u64 {{ let g = {}1\n 1 }}",
                    rep("|| ", n)
                ))
            }),
            94,
        ),
        (
            "handles",
            Box::new(|n| {
                format!(
                    "effect E {{ fn op(x: u64) -> u64 }}\nfn f() -> u64 {{ let a = 1\n {}op(a){} }}\nfn main() {{ print(f()) }}\n",
                    rep("handle E { fn op(x) { resume(x + a) } } in { ", n),
                    rep(" }", n)
                )
            }),
            46,
        ),
        (
            "scopes",
            Box::new(|n| {
                format!(
                    "fn f() -> u64 / async {{ let a = 1\n {}s.spawn(|| a).join(){} }}\nfn main() / async {{ print(f()) }}\n",
                    rep("scope { s => ", n),
                    rep(" }", n)
                )
            }),
            91,
        ),
        (
            "if",
            Box::new(|n| {
                main_prints(&format!(
                    "fn f() -> u64 {{ let a = true\n {}1{} }}",
                    rep("if a { ", n),
                    rep(" } else { 0 }", n)
                ))
            }),
            90,
        ),
        (
            "match",
            Box::new(|n| {
                main_prints(&format!(
                    "fn f() -> u64 {{ let a = 1\n {}1{} }}",
                    rep("match a { _ => ", n),
                    rep(" }", n)
                ))
            }),
            90,
        ),
        (
            "else if",
            Box::new(|n| {
                main_prints(&format!(
                    "fn f() -> u64 {{ let a = false\n if a {{ 0 }}{} else {{ 1 }} }}",
                    rep(" else if a { 0 }", n)
                ))
            }),
            140,
        ),
        (
            "prefix minus",
            Box::new(|n| main_prints(&format!("fn f() -> i64 {{ {}1 }}", rep("- ", n)))),
            140,
        ),
        (
            "prefix not",
            Box::new(|n| main_prints(&format!("fn f() -> bool {{ {}true }}", rep("!", n)))),
            140,
        ),
        (
            "method calls",
            Box::new(|n| {
                main_prints(&format!(
                    "fn f() -> u64 {{ let v = Vec.new()\n v.push(1)\n v{}.len() }}",
                    rep(".clone()", n)
                ))
            }),
            140,
        ),
        (
            "borrows",
            Box::new(|n| {
                main_prints(&format!(
                    "fn f() -> u64 {{ let x = 1\n let r = {}x\n 1 }}",
                    rep("&", n)
                ))
            }),
            140,
        ),
        (
            "method calls in blocks",
            Box::new(|n| {
                main_prints(&format!(
                    "fn f() -> u64 {{ let v = Vec.new()\n v.push(1)\n {}v{}.len(){} }}",
                    rep("{ ", HALF),
                    rep(".clone()", n),
                    rep(" }", HALF)
                ))
            }),
            70,
        ),
        (
            "else if in blocks",
            Box::new(|n| {
                main_prints(&format!(
                    "fn f() -> u64 {{ let a = false\n {}if a {{ 0 }}{} else {{ 1 }}{} }}",
                    rep("{ ", HALF),
                    rep(" else if a { 0 }", n),
                    rep(" }", HALF)
                ))
            }),
            70,
        ),
        (
            "borrows in blocks",
            Box::new(|n| {
                main_prints(&format!(
                    "fn f() -> u64 {{ let x = 1\n {}let r = {}x\n 1{} }}",
                    rep("{ ", HALF),
                    rep("&", n),
                    rep(" }", HALF)
                ))
            }),
            70,
        ),
        (
            "indexes",
            Box::new(|n| {
                main_prints(&format!(
                    "fn f() -> u64 {{ let v = [1]\n v{} }}",
                    rep("[0]", n)
                ))
            }),
            140,
        ),
        (
            "interpolations",
            Box::new(|n| {
                main_prints(&format!(
                    "fn f() -> String {{ {}1{} }}",
                    rep("\"{", n),
                    rep("}\"", n)
                ))
            }),
            40,
        ),
        (
            "reference types",
            Box::new(|n| {
                main_prints(&format!(
                    "fn g(x: {}u64) {{}}\nfn f() -> u64 {{ 1 }}",
                    rep("&", n)
                ))
            }),
            90,
        ),
        (
            "generic types",
            Box::new(|n| {
                main_prints(&format!(
                    "fn g(x: {}u64{}) {{}}\nfn f() -> u64 {{ 1 }}",
                    rep("Vec<", n),
                    rep(">", n)
                ))
            }),
            90,
        ),
        (
            "patterns",
            Box::new(|n| {
                main_prints(&format!(
                    "fn f() -> u64 {{ let {}x{} = 1\n x }}",
                    rep("(", n),
                    rep(")", n)
                ))
            }),
            90,
        ),
        (
            "modules",
            Box::new(|n| {
                main_prints(&format!(
                    "{}fn h() {{}}{}\nfn f() -> u64 {{ 1 }}",
                    rep("mod m { ", n),
                    rep(" }", n)
                ))
            }),
            90,
        ),
    ]
}

#[test]
fn every_accepted_program_fits_in_a_test_stack() {
    for (name, make, documented) in constructs() {
        let n = largest(&*make, 20_000);
        assert!(n >= documented, "{name}: only {n} levels parse");
        assert!(n < 20_000, "{name}: no limit");
        let err = weft_syntax::parse_file(&make(n + 1)).unwrap_err();
        assert!(
            err.message.contains("deep") || err.message.contains("long"),
            "{name}: {err}"
        );
        pipeline(make(n));
    }
}

#[test]
fn long_flat_chains_have_no_limit() {
    let n = 20_000;
    let sum = main_prints(&format!("fn f() -> u64 {{ 1{} }}", rep(" + 1", n)));
    assert_eq!(pipeline(sum), Some(format!("{}\n", n + 1)));
    let mixed = main_prints(&format!("fn f() -> u64 {{ 1{} }}", rep(" + 2 * 3 - 1", n)));
    assert_eq!(pipeline(mixed), Some(format!("{}\n", 1 + 5 * n)));
    let all = main_prints(&format!(
        "fn f() -> bool {{ let t = true\n t{} }}",
        rep(" && t || t", n)
    ));
    assert_eq!(pipeline(all), Some("true\n".to_string()));
    // The operands run in source order, and `&&` stops at the first `false`.
    let terms: Vec<String> = (1..=100).map(|i| format!("t({i})")).collect();
    let order = format!(
        "fn t(n: u64) -> u64 {{ print(n)\n n }}\nfn f() -> u64 {{ {} }}\nfn main() {{ print(f()) }}\n",
        terms.join(" + ")
    );
    let want = numbers(100);
    assert_eq!(pipeline(order), Some(format!("{want}5050\n")));
    let stops = format!(
        "fn b(n: u64) -> bool {{ print(n)\n n < 50 }}\nfn main() {{ print({}) }}\n",
        (1..=100)
            .map(|i| format!("b({i})"))
            .collect::<Vec<_>>()
            .join(" && ")
    );
    let want = numbers(50);
    assert_eq!(pipeline(stops), Some(format!("{want}false\n")));
}

/// A body with one reference, one mutation, `n` statements and one use. The
/// derivation of the error has a chain of about `n` steps of `invalid`.
fn long_path(n: usize) -> String {
    let mut s = String::from("fn big(v: &Vec<u32>) / mut(v) {\n    let r = &v[0]\n    v.push(1)\n");
    s.push_str(&"    print(1)\n".repeat(n));
    s.push_str("    print(r)\n}\n");
    s
}

/// A body with a linear value that is live across a `multi` operation, then
/// `n` statements and one use. The derivation of W0503 has a chain of about
/// `2 n` steps that alternate between `live_out` and `live_in`.
fn long_multi(n: usize) -> String {
    let mut s = String::from(
        "effect Choice { multi fn choose() -> bool }\n\
         linear struct Token { id: u64 }\n    on abort = spend\n\
         fn spend(t: Token) { let Token(i) = t }\n\
         fn mint() -> Token { Token { id: 1 } }\n\
         fn big() -> bool / Choice {\n    let t = mint()\n    let b = choose()\n",
    );
    s.push_str(&"    print(1)\n".repeat(n));
    s.push_str("    spend(t)\n    b\n}\n");
    s
}

/// Checks `src` and renders the derivation of each violation on a 2 MiB
/// thread. The library calls run on this thread, so the renderer must not
/// recurse.
fn explain_on_small_stack(src: String) -> String {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let checked = weft_check::check_source("long.wf", &src, Options::default());
            let file = weft_syntax::SourceFile::new("long.wf", src.as_str());
            let line_of = |o: u32| file.line_col(o).0;
            let mut text = String::new();
            for b in &checked.analysis.bodies {
                for e in weft_check::bridge::explain(&b.facts, &line_of).expect("the spec runs") {
                    text.push_str(&e.tree);
                }
            }
            text
        })
        .expect("the thread starts")
        .join()
        .expect("explain does not overflow the stack")
}

/// Asserts that a rendered derivation is short and has a small indent.
fn assert_short(text: &str) {
    assert!(text.len() < 64 * 1024, "{} bytes", text.len());
    let widest = text.lines().map(|l| l.len() - l.trim_start().len()).max();
    assert!(widest.is_some_and(|w| w <= 64), "indent {widest:?}");
}

/// The long derivations of [`explain_folds_a_long_derivation`].
fn long_derivations() -> [(String, &'static str, &'static str); 2] {
    [
        (long_path(10_000), "error(", "more `invalid` steps ..."),
        (
            long_multi(10_000),
            "live_across_multi(",
            "more `live_in`, `live_out` steps ...",
        ),
    ]
}

#[test]
fn explain_folds_a_long_derivation() {
    for (src, relation, fold) in long_derivations() {
        let text = explain_on_small_stack(src);
        assert!(text.starts_with(relation), "{text}");
        assert!(text.contains(fold), "{text}");
        assert_short(&text);
    }
}

/// A clock is not stable on a loaded machine, so this bound runs only in a
/// release build (`cargo test --release -p weft-cli --test limits`).
#[test]
#[cfg_attr(debug_assertions, ignore = "a time bound needs a release build")]
fn explain_folds_a_long_derivation_in_time() {
    for (src, _, _) in long_derivations() {
        let start = std::time::Instant::now();
        let text = explain_on_small_stack(src);
        let time = start.elapsed();
        assert_short(&text);
        assert!(time.as_secs() < 20, "{time:?}");
    }
}

/// The printer does not recurse, also on a deep derivation that it cannot
/// fold. `ping` and `pong` are not relations of the spec, so the printer
/// does not fold their chain.
#[test]
fn the_printer_does_not_recurse() {
    use weft_datalog::{evaluate, parse_program, Database, EvalOptions, Value};
    let n: i64 = 20_000;
    let text = std::thread::Builder::new()
        .stack_size(STACK / 4)
        .spawn(move || {
            let program = parse_program(
                "ping(X) :- start(X).\n\
                 pong(Y) :- ping(X), edge(X, Y).\n\
                 ping(Y) :- pong(X), edge(X, Y).",
            )
            .expect("parses");
            let mut db = Database::new();
            db.insert("start", [Value::Int(0)]);
            for i in 0..n {
                db.insert("edge", [Value::Int(i), Value::Int(i + 1)]);
            }
            let out = evaluate(&program, db, EvalOptions::default()).expect("evaluates");
            let d = out.explain("ping", &[Value::Int(n)]).expect("derived");
            let facts = weft_facts::FnFacts::default();
            weft_check::bridge::render_derivation(&d, &facts, &|_| 0)
        })
        .expect("the thread starts")
        .join()
        .expect("the printer does not overflow the stack");
    // One line for each rule node and each `edge` leaf, and one `start` leaf.
    let lines = usize::try_from(2 * n + 2).unwrap();
    assert_eq!(text.lines().count(), lines);
    assert!(!text.contains("more"), "the chain is not folded");
    let widest = text.lines().map(|l| l.len() - l.trim_start().len()).max();
    assert_eq!(widest, Some(2 * weft_check::bridge::MAX_INDENT));
}

#[test]
fn check_explain_prints_a_folded_derivation() {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("limits");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("long_multi.wf");
    std::fs::write(&path, long_multi(10_000)).unwrap();
    let args = vec![
        "check".to_string(),
        "--explain".to_string(),
        path.display().to_string(),
    ];
    let out = weft_cli::run(&args).expect("the command runs");
    assert_eq!(out.code, 1, "{}", out.text);
    assert!(out.text.contains("error[W0503]"), "{}", out.text);
    assert!(
        out.text.contains("derivation of live_across_multi("),
        "{}",
        out.text
    );
    assert_short(&out.text);
}

/// `weft_cli::run` runs the command on its own large stack, so a caller on a
/// small stack can check the deepest program.
#[test]
fn run_has_its_own_stack() {
    let (_, make, _) = constructs().swap_remove(0);
    let n = largest(&*make, 20_000);
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("limits");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("deep_blocks.wf");
    std::fs::write(&path, make(n)).unwrap();
    let args = vec!["run".to_string(), path.display().to_string()];
    let out = std::thread::Builder::new()
        .stack_size(STACK / 8)
        .spawn(move || weft_cli::run(&args).expect("the command runs"))
        .expect("the thread starts")
        .join()
        .expect("the command does not overflow the stack");
    assert_eq!(out.code, 0, "{}", out.stderr);
    assert_eq!(out.text, "1\n");
}

/// A small stack for a caller of the library: 256 KiB.
const SMALL: usize = 256 * 1024;

/// The library entry points run on their own large stack
/// (`weft_sema::on_large_stack`). So a caller on a 256 KiB thread can analyze,
/// check and run the deepest program that the parser accepts.
#[test]
fn the_library_has_its_own_stack() {
    for (name, make, _) in constructs() {
        let n = largest(&*make, 20_000);
        let src = make(n);
        let out = std::thread::Builder::new()
            .stack_size(SMALL)
            .spawn(move || {
                let a = weft_sema::analyze_source(&src, Options::default());
                assert!(a.is_ok(), "{name}: analysis");
                let checked = weft_check::check_source("deep.wf", &src, Options::default());
                let tests = weft_interp::run_tests(&checked, &RunOptions::default());
                assert!(tests.is_empty(), "{name}: tests");
                if !checked.ok() {
                    return Ok(String::new());
                }
                let opts = RunOptions {
                    max_steps: Some(10_000_000),
                    ..RunOptions::default()
                };
                weft_interp::run_main(&checked, &opts).map(|o| o.stdout)
            })
            .expect("the thread starts")
            .join()
            .expect("the library does not overflow the stack of its caller");
        assert!(out.is_ok(), "{name}: {out:?}");
    }
}
