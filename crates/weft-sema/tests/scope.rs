//! Tests of the switch between the fact pipelines (plan stage F1): the
//! construct groups of each body (`weft_sema::irbuild::scope`, plan §2.6), the
//! scope of a program, the fallback to the old pipeline, `--facts=both`, and
//! what the `ir` mode keeps of the old lowering (`docs/ir.md` 2.4).

use std::collections::BTreeSet;

use weft_facts::FnFacts;
use weft_sema::factgen::{Input, Unsupported};
use weft_sema::{analyze_with_emit, prelude_unit, Analysis, FactGen, Group, Groups, Options, Unit};
use weft_syntax::diag::Code;
use weft_syntax::parse_file;

/// The units of a program with the root `src`.
fn units(src: &str) -> Vec<Unit> {
    let prelude = prelude_unit().unwrap_or_else(|e| panic!("the prelude: {}", e.message));
    let file = parse_file(src).unwrap_or_else(|e| panic!("the source: {}", e.message));
    vec![
        prelude,
        Unit {
            name: String::new(),
            file,
            is_std: false,
        },
    ]
}

/// Options with the pipeline `facts` and the groups `on`.
fn opts(facts: FactGen, on: Groups) -> Options {
    Options {
        facts,
        ir_groups: on,
        ..Options::default()
    }
}

/// Analyzes `src` with the stub fact generator.
fn analyze(src: &str, o: Options) -> Analysis {
    weft_sema::analyze(&units(src), o)
}

/// An `emit` that writes no fact: the hook that puts each program in scope.
/// Its type is `weft_sema::factgen::Emit`, so it returns a `Result`.
#[allow(clippy::unnecessary_wraps)]
const fn empty(_: &Input<'_>, _: &mut [FnFacts]) -> Result<(), Unsupported> {
    Ok(())
}

/// Analyzes `src` with the hook [`empty`] and every group on.
fn analyze_empty(src: &str, facts: FactGen) -> Analysis {
    analyze_with_emit(&units(src), opts(facts, Groups::ALL), empty)
}

/// The groups of each body of `src`, by name, as text.
fn groups_of(src: &str) -> Vec<(String, String)> {
    let a = analyze(src, opts(FactGen::Ir, Groups::ALL));
    let scope = a.ir_scope.as_ref().expect("the ir pipeline gives a scope");
    a.bodies
        .iter()
        .zip(&scope.bodies)
        .map(|(b, g)| (b.facts.name.clone(), g.to_string()))
        .collect()
}

/// The groups of body `name` of `src`.
fn body_groups(src: &str, name: &str) -> String {
    let found = groups_of(src).into_iter().find(|(n, _)| n == name);
    let Some((_, g)) = found else {
        panic!("no body `{name}`");
    };
    g
}

#[test]
fn group_sets_parse_and_print() {
    assert_eq!(
        Groups::parse("ACF").map(|g| g.to_string()),
        Ok("ACF".into())
    );
    assert!(Groups::parse("CA").is_err());
    assert!(Groups::parse("AA").is_err());
    assert!(Groups::parse("G").is_err());
    assert!(Groups::parse("").is_err());
    assert_eq!(Groups::ALL.to_string(), "ABCDEF");
    assert_eq!(Groups::NONE.to_string(), "");
    let ab = Groups::of(Group::A).with(Group::B);
    assert!(ab.contains(Groups::of(Group::B)));
    assert!(!ab.contains(Groups::of(Group::C)));
    assert_eq!(ab.minus(Groups::of(Group::A)).to_string(), "B");
    assert_eq!(ab.first(), Some(Group::A));
    assert_eq!(Groups::NONE.first(), None);
}

#[test]
fn straight_line_code_is_group_a() {
    let src = "struct P { x: u64 }
        fn f(p: &P, n: u64) -> u64 {
            let y = p.x + n
            let b = Box.new(y)
            if y > 2 && n < 9 { print(y) }
            match n { 0 => 1, _ => y }
        }";
    assert_eq!(body_groups(src, "f"), "A");
}

#[test]
fn a_loop_is_group_b() {
    let src = "fn w(n: u64) -> u64 { let i = 0; while i < n { i += 1 }; i }
        fn l() { loop { break } }
        fn r(v: &Vec<u64>) -> u64 { let s = 0; for x in v[] { s += x }; s }
        fn g(n: u64) -> u64 { let i = 0; loop { i += 1; if i > n { break } }; i }";
    assert_eq!(body_groups(src, "w"), "AB");
    assert_eq!(body_groups(src, "r"), "AB");
    assert_eq!(body_groups(src, "g"), "AB");
    // A loop that never goes back is straight-line code in the IR.
    assert_eq!(body_groups(src, "l"), "A");
}

#[test]
fn closures_and_function_values_are_group_c() {
    let src = "fn inc(x: u64) -> u64 { x + 1 }
        fn clo() -> u64 { let g = |x: u64| x + 1; g(2) }
        fn item() -> u64 { let g = inc; g(2) }
        fn param(f: fn(u64) -> u64) -> u64 { f(1) }
        struct Cb { f: fn() }
        fn stored(c: &Cb) { let k = 1 }";
    assert_eq!(body_groups(src, "clo"), "AC");
    assert_eq!(body_groups(src, "item"), "AC");
    assert_eq!(body_groups(src, "param"), "AC");
    assert_eq!(body_groups(src, "stored"), "AC");
    assert_eq!(body_groups(src, "inc"), "A");
}

#[test]
fn handlers_are_group_d_and_a_perform_through_the_row_is_group_a() {
    let src = "effect Log { fn log(m: u64) }
        fn row() / Log { log(1) }
        fn handled() { handle Log { fn log(m) { resume(()) } } in log(2) }";
    assert_eq!(body_groups(src, "row"), "A");
    assert_eq!(body_groups(src, "handled"), "AD");
}

#[test]
fn tasks_are_group_e() {
    let src = "fn joined() -> u64 / async {
            scope { s => let t = s.spawn(|| 40); t.join() + 2 }
        }
        fn simulated() {
            sim.run(seed: 42) { print(1) }
        }";
    // The task closure is group C too.
    assert_eq!(body_groups(src, "joined"), "ACE");
    assert_eq!(body_groups(src, "simulated"), "ACE");
}

#[test]
fn a_type_parameter_is_group_f() {
    let src = "fn first<T>(p: (T, T)) -> T { p.0 }
        fn user() -> u64 { first((1, 2)) }";
    assert_eq!(body_groups(src, "first"), "AF");
    assert_eq!(body_groups(src, "user"), "A");
}

#[test]
fn the_scope_of_a_program_is_the_union_of_its_bodies() {
    let src = "fn a() -> u64 { let i = 0; while i < 3 { i += 1 }; i }
        fn b() -> u64 { let g = || 1; g() }
        test \"t\" { print(a() + b()) }";
    let a = analyze(src, opts(FactGen::Ir, Groups::ALL));
    let scope = a.ir_scope.expect("a scope");
    assert_eq!(scope.used.to_string(), "ABC");
    let names: Vec<String> = scope.bodies.iter().map(ToString::to_string).collect();
    assert_eq!(names, ["AB", "AC", "A"]);
}

#[test]
fn a_body_with_no_ir_uses_no_group() {
    // `f` has a type error: it has no IR, so its groups are empty.
    let src = "fn f() -> u64 { let g = || 1; true }
        fn h() -> u64 { 1 }";
    assert_eq!(body_groups(src, "f"), "");
    assert_eq!(body_groups(src, "h"), "A");
}

/// The text of each diagnostic: the code and the start of the span.
fn diags(a: &Analysis) -> Vec<String> {
    let mut v: Vec<String> = a
        .diags
        .iter()
        .map(|d| format!("{} {}", d.code.as_str(), d.span.lo))
        .collect();
    v.sort();
    v
}

/// The names and the fact counts of the bodies.
fn shape(bodies: &[weft_sema::BodyFacts]) -> Vec<(String, usize, usize)> {
    bodies
        .iter()
        .map(|b| {
            (
                b.facts.name.clone(),
                b.facts.nodes.len(),
                b.facts.cfg_edge.len(),
            )
        })
        .collect()
}

const ESCAPE: &str = "effect Log { fn log(msg: String) }
fn as_result() {
    let f = handle Log { fn log(m) { resume(()) } } in || log(\"late\")
}
fn typo() -> u64 { nope }
fn plain(n: u64) -> u64 { n + 1 }
";

#[test]
fn the_old_pipeline_checks_a_program_out_of_scope_and_says_why() {
    let old = analyze(ESCAPE, Options::default());
    assert!(old.ir_scope.is_none(), "the old pipeline computes no scope");
    assert!(old.ir_facts.is_none());
    // No group is on.
    let ir = analyze(ESCAPE, opts(FactGen::Ir, Groups::NONE));
    let scope = ir.ir_scope.as_ref().expect("a scope");
    let why = scope.fallback.as_deref().expect("out of scope");
    assert!(why.contains("group A"), "{why}");
    assert!(!scope.in_scope());
    assert_eq!(shape(&ir.bodies), shape(&old.bodies));
    assert_eq!(diags(&ir), diags(&old));
    // Every group is on, but the stub fact generator supports none.
    let ir = analyze(ESCAPE, opts(FactGen::Ir, Groups::ALL));
    let why = ir
        .ir_scope
        .as_ref()
        .and_then(|s| s.fallback.clone())
        .expect("out of scope");
    assert!(why.contains("fact generator"), "{why}");
    assert_eq!(shape(&ir.bodies), shape(&old.bodies));
    assert_eq!(diags(&ir), diags(&old));
}

#[test]
fn a_group_that_is_off_keeps_the_program_out_of_scope_with_the_hook() {
    let src = "fn f() -> u64 { let g = || 1; g() }";
    let a = analyze_with_emit(&units(src), opts(FactGen::Ir, Groups::of(Group::A)), empty);
    let why = a
        .ir_scope
        .as_ref()
        .and_then(|s| s.fallback.clone())
        .expect("out of scope");
    assert!(why.contains("group C"), "{why}");
}

#[test]
fn the_ir_mode_keeps_only_the_typeck_diagnostics_of_the_old_lowering() {
    let old = analyze(ESCAPE, Options::default());
    let codes = |a: &Analysis| -> BTreeSet<Code> { a.diags.iter().map(|d| d.code).collect() };
    assert!(codes(&old).contains(&Code::W0313), "{:?}", codes(&old));
    assert!(codes(&old).contains(&Code::W0101), "{:?}", codes(&old));
    let ir = analyze_empty(ESCAPE, FactGen::Ir);
    assert!(ir.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope));
    // W0313 of the old lowering goes away; W0101 of typeck stays.
    assert!(!codes(&ir).contains(&Code::W0313), "{:?}", codes(&ir));
    assert!(codes(&ir).contains(&Code::W0101), "{:?}", codes(&ir));
    // The facts are the facts of the emit: here none, with the names.
    let names: Vec<&str> = ir.bodies.iter().map(|b| b.facts.name.as_str()).collect();
    assert_eq!(names, ["as_result", "typo", "plain"]);
    assert!(ir.bodies.iter().all(|b| b.facts.nodes.is_empty()));
    assert!(ir.ir_facts.is_none(), "the ir mode gives one fact set");
}

#[test]
fn the_both_mode_gives_both_fact_sets() {
    let old = analyze(ESCAPE, Options::default());
    let both = analyze_empty(ESCAPE, FactGen::Both);
    assert_eq!(shape(&both.bodies), shape(&old.bodies));
    assert_eq!(diags(&both), diags(&old));
    let ir = both.ir_facts.as_ref().expect("the ir facts");
    assert!(ir.bodies.iter().all(|b| b.facts.nodes.is_empty()));
    assert!(!ir.diags.iter().any(|d| d.code == Code::W0313));
    assert!(ir.diags.iter().any(|d| d.code == Code::W0101));
    // With the stub fact generator, the ir side is the old side.
    let stub = analyze(ESCAPE, opts(FactGen::Both, Groups::ALL));
    assert!(stub.ir_facts.is_none());
    assert!(stub.ir_scope.and_then(|s| s.fallback).is_some());
    // The ir view of the both mode is the analysis of the ir mode.
    let view = both.clone().ir_view();
    let ir_mode = analyze_empty(ESCAPE, FactGen::Ir);
    assert_eq!(shape(&view.bodies), shape(&ir_mode.bodies));
    assert_eq!(diags(&view), diags(&ir_mode));
}

#[test]
fn the_ir_mode_gives_the_w0315_of_the_builder() {
    let src = "effect E { fn op() }
        fn f() {
            loop {
                handle E { fn op() { resume(()) } } in { break }
            }
        }";
    let old = analyze(src, Options::default());
    assert!(old.diags.iter().any(|d| d.code == Code::W0315));
    let ir = analyze_empty(src, FactGen::Ir);
    let n = ir.diags.iter().filter(|d| d.code == Code::W0315).count();
    assert_eq!(n, 1, "{:?}", diags(&ir));
}

/// The exports of the bodies: the captures by value (closure span and
/// variable name), the argument orders and the integer types.
type Exports = (
    BTreeSet<(u32, u32, String)>,
    BTreeSet<(u32, u32, Vec<Option<u32>>)>,
    BTreeSet<(u32, u32, String)>,
);

fn exports(bodies: &[weft_sema::BodyFacts]) -> Exports {
    let mut out = Exports::default();
    for b in bodies {
        for (s, v) in &b.facts.by_value {
            out.0.insert((s.lo, s.hi, b.facts.var(*v).name.clone()));
        }
        for (s, o) in &b.facts.arg_order {
            out.1.insert((s.lo, s.hi, o.clone()));
        }
        for (s, t) in &b.facts.int_ops {
            out.2.insert((s.lo, s.hi, t.clone()));
        }
    }
    out
}

#[test]
fn the_ir_pipeline_fills_the_exports_of_the_interpreter() {
    let src = "struct Entity { hp: i32 }
        impl Entity {
            fn diff(self, a: i32, b: i32) -> i32 { a - b }
        }
        fn diff(a: i32, b: i32) -> i32 { a - b }
        fn take(v: Vec<u64>) -> usize { v.len() }
        fn calls() -> i32 {
            let x = Entity { hp: 1 }
            let g = diff
            x.diff(b: 1, a: 2) + g(b: 3, a: 4) + diff(b: 5, a: 6)
        }
        fn moves() {
            let v = Vec.new()
            v.push(1)
            let f = || print(take(v))
            f()
        }
        fn ops(a: u8, b: u8) -> u8 {
            let c = a + b
            c *= 2
            c
        }
        fn neg(a: i32) -> i32 { -a }";
    let old = analyze(src, Options::default());
    let want = exports(&old.bodies);
    assert!(!want.0.is_empty() && !want.1.is_empty() && !want.2.is_empty());
    let ir = analyze_empty(src, FactGen::Ir);
    assert_eq!(exports(&ir.bodies), want);
}

/// The programs of the corpus with a capture of class `closure-copy`
/// (`crates/weft-sema/tests/exports_parity.rs`): a closure body that copies a
/// function value out of a capture. The old lowering moves the capture; the
/// IR copies the function value.
const CLOSURE_COPY: [&str; 1] = ["143_arg_roots.wf"];

/// Each program of the corpus: the exports of the `ir` pipeline (with the hook)
/// are the exports of the old lowering. The captures of function values that
/// a closure body copies are the one expected difference (`closure-copy`,
/// `crates/weft-sema/tests/exports_parity.rs`).
#[test]
fn the_exports_of_the_corpus_are_the_exports_of_the_old_lowering() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs");
    let mut files: Vec<_> = std::fs::read_dir(&dir)
        .expect("the corpus")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "wf"))
        .collect();
    files.sort();
    let mut bad = Vec::new();
    for f in &files {
        let src = std::fs::read_to_string(f).expect("read");
        let Ok(file) = parse_file(&src) else {
            continue;
        };
        let us = vec![
            prelude_unit().expect("the prelude"),
            Unit {
                name: String::new(),
                file,
                is_std: false,
            },
        ];
        let a = analyze_with_emit(&us, opts(FactGen::Both, Groups::ALL), empty);
        let Some(ir) = &a.ir_facts else {
            bad.push(format!("{}: not in scope", f.display()));
            continue;
        };
        let (old, new) = (exports(&a.bodies), exports(&ir.bodies));
        if old.1 != new.1 || old.2 != new.2 {
            bad.push(format!("{}: argument orders or integer types", f.display()));
        }
        // A capture that only one side moves. In a program of
        // [`CLOSURE_COPY`] the old lowering moves more captures.
        let copies = f
            .file_name()
            .is_some_and(|n| CLOSURE_COPY.contains(&n.to_string_lossy().as_ref()));
        let diff: Vec<_> = if copies {
            new.0.difference(&old.0).collect()
        } else {
            old.0.symmetric_difference(&new.0).collect()
        };
        if !diff.is_empty() {
            bad.push(format!("{}: captures {diff:?}", f.display()));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

#[test]
fn with_no_group_on_no_program_is_in_scope() {
    // Each body has a type error: the bodies have no IR and use no group.
    let src = "fn f() -> u64 { true }\nfn g() -> u64 { nope }\n";
    let a = analyze(src, opts(FactGen::Ir, Groups::NONE));
    let scope = a.ir_scope.as_ref().expect("a scope");
    assert!(scope.used.is_empty());
    let why = scope.fallback.as_deref().expect("out of scope");
    assert!(why.contains("no construct group is on"), "{why}");
    // With a group on, the program is in scope: its diagnostics are those
    // of `typeck`.
    let a = analyze(src, opts(FactGen::Ir, Groups::of(Group::A)));
    assert!(a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope));
}

#[test]
fn group_a_is_on_by_default() {
    // Stage F8 turns group A on (plan §2.6): the default options put a
    // program of group A in scope, and keep a program with a loop out.
    assert_eq!(Options::default().ir_groups, Groups::of(Group::A));
    let o = Options {
        facts: FactGen::Ir,
        ..Options::default()
    };
    let a = analyze("fn main() { let x = 1; print(x) }\n", o);
    assert!(a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope));
    let a = analyze("fn main() { let i = 0; while i < 3 { i += 1 } }\n", o);
    assert!(!a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope));
}
