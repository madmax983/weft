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

/// The time bound of the `ir` pipeline (facts and summaries) on a long
/// chain of calls and on a long chain of `let`s with a cleanup chain.
const FACTS_BOUND: Duration = Duration::from_secs(30);

/// Analyzes `src` with the facts of the `ir` pipeline (group A) and returns
/// the time. The program must be in scope.
fn ir_facts_time(src: &str) -> Duration {
    let opts = Options {
        facts: weft_sema::FactGen::Ir,
        ..Options::from_markers(src)
    };
    let start = Instant::now();
    let a = analyze_source(src, opts)
        .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
    let time = start.elapsed();
    assert!(
        a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope),
        "{:?}",
        a.ir_scope.as_ref().and_then(|s| s.fallback.clone())
    );
    time
}

#[test]
fn the_facts_of_long_chains_of_blocks_take_linear_space() {
    // Stage F8 (tier 2 ran out of memory): each call is a block, and the
    // cleanup chain of a call has a block for each live local. The analysis
    // kept a state of each block with each local (blocks times locals).
    // 2000 linear locals, then 2000 calls that consume them.
    let mut s = String::from(
        "linear struct Tok { id: u64 }\nfn spend(t: Tok) { let Tok(i) = t }\nfn f() {\n",
    );
    for i in 0..2000 {
        let _ = writeln!(s, "    let t{i} = Tok {{ id: {i} }}");
    }
    for i in 0..2000 {
        let _ = writeln!(s, "    spend(t{i})");
    }
    s.push_str("}\n");
    let calls = ir_facts_time(&s);
    // 6000 `let`s before a call: the call has a cleanup chain of 6000
    // blocks.
    let mut s = String::from("fn g() -> u64 { 1 }\nfn f() {\n");
    for _ in 0..6000 {
        s.push_str("    let i = 1\n");
    }
    s.push_str("    print(g())\n}\n");
    let lets = ir_facts_time(&s);
    assert!(
        calls < FACTS_BOUND && lets < FACTS_BOUND,
        "calls {calls:?}, lets {lets:?}"
    );
}

#[test]
fn a_ring_of_calls_reaches_its_fixpoint_in_a_few_passes() {
    // Stage F8 (tier 2: r2/quality/gen/ring_400.wf timed out): `f(i)` calls
    // `f(i + 1)` and performs `E(i)`, and the last calls the first. Each
    // row gets each effect. A round over each function of the ring moved
    // one effect one step: rounds times functions runs of the fact
    // generator.
    let n = 200;
    let mut s = String::new();
    for i in 0..n {
        let _ = writeln!(s, "effect E{i} {{ fn op() }}");
    }
    for i in 0..n {
        let next = (i + 1) % n;
        let _ = writeln!(
            s,
            "fn f{i}(k: u64) {{ if k > 0 {{ f{next}(k - 1) }}\n    E{i}.op() }}"
        );
    }
    let time = ir_facts_time(&s);
    assert!(time < FACTS_BOUND, "{time:?}");
}

/// The time of the fact generator of the `ir` pipeline in the last analysis
/// of [`emit_time`], in nanoseconds.
static EMIT_NS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// The fact generator of the `ir` pipeline, with its time in [`EMIT_NS`].
fn timed_emit(
    input: &weft_sema::factgen::Input<'_>,
    facts: &mut [weft_facts::FnFacts],
) -> Result<(), weft_sema::factgen::Unsupported> {
    let start = Instant::now();
    let out = weft_sema::factgen::emit(input, facts);
    let ns = u64::try_from(start.elapsed().as_nanos()).unwrap_or(u64::MAX);
    EMIT_NS.store(ns, std::sync::atomic::Ordering::SeqCst);
    out
}

/// Analyzes `src` with the `ir` pipeline and the groups A, B and C, and
/// returns the time of its fact generator (not of the old lowering, which
/// runs too). The program must be in scope.
fn emit_time(src: &str) -> Duration {
    let prelude =
        weft_sema::prelude_unit().unwrap_or_else(|e| panic!("the prelude: {}", e.message));
    let file = weft_syntax::parse_file(src).unwrap_or_else(|e| panic!("the source: {}", e.message));
    let units = vec![
        prelude,
        weft_sema::Unit {
            name: String::new(),
            file,
            is_std: false,
        },
    ];
    let opts = Options {
        facts: weft_sema::FactGen::Ir,
        ir_groups: weft_sema::Groups::parse("ABC").unwrap_or(weft_sema::Groups::NONE),
        ..Options::from_markers(src)
    };
    let a = weft_sema::analyze_with_emit(&units, opts, timed_emit);
    assert!(
        a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope),
        "{:?}",
        a.ir_scope.as_ref().and_then(|s| s.fallback.clone())
    );
    Duration::from_nanos(EMIT_NS.load(std::sync::atomic::Ordering::SeqCst))
}

#[test]
fn a_dag_of_closures_that_run_each_other_gets_its_facts_in_time() {
    // Q3-2 (`tests/gate/probes/r3/quality/repro/Q3_closure_dag_18.wf`):
    // closure `c(k)` runs `c(k - 1)` and `c(k - 2)`. A run node applies
    // each closure that it reaches one time, so the cost is linear (before
    // stage F12 the program was out of scope, and the old lowering takes
    // exponential time on it). The old lowering runs in this test too, so
    // the size is small.
    let n = 12;
    let mut s = String::from(
        "struct W { v: Vec<u64> }\nfn f(w: &W) / mut(w.v) {\n    let c0 = || w.v.push(1)\n    let c1 = || w.v.push(2)\n",
    );
    for k in 2..n {
        let _ = writeln!(s, "    let c{k} = || {{ c{}(); c{}() }}", k - 1, k - 2);
    }
    let _ = writeln!(s, "    c{}()\n}}", n - 1);
    let time = emit_time(&s);
    assert!(time < CLOSURES_BOUND, "{time:?}");
}
