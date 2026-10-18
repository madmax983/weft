//! Size limits of the whole pipeline.
//!
//! For each deep or long construct, the test finds the largest program that the
//! parser accepts. That program must go through every stage on a 2 MiB thread,
//! the stack of a test thread: parse, print, analyze, check, the spec, the
//! interpreter and drop. A larger program gets a parser error, never a stack
//! overflow. A flat chain of binary operators has no limit.
//!
//! The derivation printer of `check --explain` does not recurse. It folds a
//! long chain of one relation, so a long path in a body gives a short text.

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
            let file = weft_syntax::parse_file(&src).expect("the program parses");
            let text = weft_syntax::pretty::pretty(&file);
            if let Err(e) = weft_syntax::parse_file(&text) {
                panic!("the printed program does not parse: {e}\n{text}");
            }
            assert!(!format!("{file:?}").is_empty());
            drop(file);
            let checked = weft_check::check_source("limit.wf", &src, Options::default());
            assert!(weft_check::agreement(&checked).is_ok());
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

#[test]
fn explain_folds_a_long_derivation() {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("limits");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("long_path.wf");
    std::fs::write(&path, long_path(10_000)).unwrap();
    let args = vec![
        "check".to_string(),
        "--explain".to_string(),
        path.display().to_string(),
    ];
    let start = std::time::Instant::now();
    let out = std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || weft_cli::run(&args).expect("the command runs"))
        .expect("the thread starts")
        .join()
        .expect("explain does not overflow the stack");
    let time = start.elapsed();
    assert_eq!(out.code, 1, "{}", out.text);
    assert!(out.text.contains("error[W0301]"), "{}", out.text);
    assert!(
        out.text.contains("more `invalid` steps ..."),
        "{}",
        out.text
    );
    assert!(out.text.len() < 64 * 1024, "{} bytes", out.text.len());
    let widest = out
        .text
        .lines()
        .map(|l| l.len() - l.trim_start().len())
        .max();
    assert!(widest.is_some_and(|w| w <= 64), "indent {widest:?}");
    assert!(time.as_secs() < 60, "{time:?}");
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
