//! The cost of the builder and the verifier of the IR on large programs
//! (`docs/ir.md` 5.1.9). Each test builds one large program and checks the
//! time against a large bound: a quadratic pass takes far more time, also in a
//! release build.

use std::fmt::Write as _;
use std::time::{Duration, Instant};

use weft_sema::irbuild;
use weft_sema::{analyze_source, Options};

/// The time bound of each test, for the build and the verifier together.
const BOUND: Duration = Duration::from_secs(30);

/// The time bound of the verifier alone.
const VERIFY_BOUND: Duration = Duration::from_secs(10);

/// The time bound of a `match` with many arms.
const ARMS_BOUND: Duration = Duration::from_secs(5);

/// The time bound of the verifier on a body with many closures.
const CLOSURES_BOUND: Duration = Duration::from_secs(5);

/// Builds the IR of `src`, checks that it is valid, and returns the time of the
/// build (the verifier runs inside it) and the time of one more run of the
/// verifier alone.
fn build_time(src: &str) -> (Duration, Duration) {
    let a = analyze_source(src, Options::from_markers(src))
        .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
    let start = Instant::now();
    let b = irbuild::build(&a);
    let time = start.elapsed();
    assert!(
        b.broken.is_empty(),
        "{:?}",
        &b.broken[..b.broken.len().min(5)]
    );
    let (built, _, _) = b.counts();
    assert_eq!(built, b.entries.len());
    let start = Instant::now();
    let broken = weft_ir::verify::verify_program(&b.program, &b.tys);
    let verify = start.elapsed();
    assert!(broken.is_empty());
    (time, verify)
}

/// `depth` nested `if`s; each one has `per` pairs of locals that get the
/// result of a call. Each call has a cleanup chain, and each `if` statement
/// has a temporary that lives across the `if`s inside it.
fn nested_ifs(depth: usize, per: usize) -> String {
    let mut s =
        String::from("fn g(i: u64) -> u64 { i }\nfn mk() -> Vec<u64> { Vec.new() }\nfn main() {\n");
    for d in 0..depth {
        let ind = "    ".repeat(d + 1);
        let _ = writeln!(s, "{ind}if true {{");
        for k in 0..per {
            let _ = writeln!(s, "{ind}    let a{d}_{k} = g({k})");
            let _ = writeln!(s, "{ind}    let v{d}_{k} = mk()");
        }
    }
    for d in (0..depth).rev() {
        let _ = writeln!(s, "{}}}", "    ".repeat(d + 1));
    }
    s.push_str("}\n");
    s
}

#[test]
fn deep_nested_ifs_with_calls_build_in_time() {
    let (time, verify) = build_time(&nested_ifs(80, 50));
    eprintln!("80 nested ifs: build {time:?}, verifier {verify:?}");
    assert!(time < BOUND, "80 nested ifs: {time:?}");
    assert!(
        verify < VERIFY_BOUND,
        "80 nested ifs: the verifier takes {verify:?}"
    );
}

/// A `match` with `n` arms of unit variants: each arm tests the discriminant.
#[test]
fn a_match_with_many_arms_builds_in_time() {
    let n = 6000;
    let vs: Vec<String> = (0..n).map(|i| format!("V{i}")).collect();
    let arms: Vec<String> = (0..n).map(|i| format!("V{i} => {i},")).collect();
    let src = format!(
        "enum E {{ {} }}\nfn f(e: E) -> u64 {{ match e {{ {} }} }}\n",
        vs.join(", "),
        arms.join(" ")
    );
    let (time, verify) = build_time(&src);
    eprintln!("{n} arms: build {time:?}, verifier {verify:?}");
    assert!(time < ARMS_BOUND, "{n} arms: {time:?}");
}

/// A body that makes `n` closures: the verifier checks each closure against
/// the aggregate that makes it.
#[test]
fn many_closures_verify_in_time() {
    let n = 4000;
    let body: Vec<String> = (0..n)
        .map(|i| format!("    let c{i} = || v.push({i})\n    c{i}()"))
        .collect();
    let src = format!("fn f(v: &Vec<u64>) / mut(v) {{\n{}\n}}\n", body.join("\n"));
    let (time, verify) = build_time(&src);
    eprintln!("{n} closures: build {time:?}, verifier {verify:?}");
    assert!(time < BOUND, "{n} closures: {time:?}");
    assert!(
        verify < CLOSURES_BOUND,
        "{n} closures: the verifier takes {verify:?}"
    );
}
