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

/// The default options with the old pipeline: a test that compares with
/// the old pipeline names it, because the default is the `ir` pipeline from
/// plan stage C3.
fn old_options() -> Options {
    Options {
        facts: FactGen::Old,
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

/// A program that the fact generator does not support with each group on:
/// a `resume` of a captured continuation (follow-up F16.1). Stage F17 put
/// the W0313 escape of `ESCAPE` in scope.
// A program that the fact generator does not support: a clause gives the
// callee a function value that can race (stage R0g put the `resume` in a
// closure, the form of this program before, in scope for a program that the
// `ir` pipeline rejects; stage R0h put a value that cannot race in scope).
const KONT: &str = "effect Get { fn get() -> fn() }
fn run_it() / Get { let g = get(); g() }
fn kont() { let v = Vec.new(); v.push(1); handle Get { fn get() { resume(|| v.clear()) } } in { run_it() } }
fn typo() -> u64 { nope }
fn plain(n: u64) -> u64 { n + 1 }
";

#[test]
fn the_old_pipeline_checks_a_program_out_of_scope_and_says_why() {
    let old = analyze(ESCAPE, old_options());
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
    // Every group is on, but the fact generator does not support the
    // program.
    let old = analyze(KONT, old_options());
    let ir = analyze(KONT, opts(FactGen::Ir, Groups::ALL));
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
    let old = analyze(ESCAPE, old_options());
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
    let old = analyze(ESCAPE, old_options());
    let both = analyze_empty(ESCAPE, FactGen::Both);
    assert_eq!(shape(&both.bodies), shape(&old.bodies));
    assert_eq!(diags(&both), diags(&old));
    let ir = both.ir_facts.as_ref().expect("the ir facts");
    assert!(ir.bodies.iter().all(|b| b.facts.nodes.is_empty()));
    assert!(!ir.diags.iter().any(|d| d.code == Code::W0313));
    assert!(ir.diags.iter().any(|d| d.code == Code::W0101));
    // With a program that the fact generator does not support, the ir side
    // is the old side.
    let stub = analyze(KONT, opts(FactGen::Both, Groups::ALL));
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
    let old = analyze(src, old_options());
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
    let old = analyze(src, old_options());
    let want = exports(&old.bodies);
    assert!(!want.0.is_empty() && !want.1.is_empty() && !want.2.is_empty());
    let ir = analyze_empty(src, FactGen::Ir);
    assert_eq!(exports(&ir.bodies), want);
}

/// The programs of the corpus with a capture of class `closure-copy`
/// (`crates/weft-sema/tests/exports_parity.rs`): a closure body that copies a
/// function value out of a capture. The old lowering moves the capture; the
/// IR copies the function value.
const CLOSURE_COPY: [&str; 2] = ["143_arg_roots.wf", "177_o3_5_field_closure_tasks.wf"];

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

/// Plan stage C3: the `ir` pipeline is the default, with each construct
/// group on. `--facts=old` stays behind its flag until plan stage R3.
#[test]
fn the_ir_pipeline_is_the_default() {
    assert_eq!(Options::default().facts, FactGen::Ir);
    assert_eq!(FactGen::default(), FactGen::Ir);
    let a = analyze(ESCAPE, Options::default());
    assert!(a.ir_scope.is_some(), "the ir pipeline computes a scope");
    let old = analyze(ESCAPE, old_options());
    assert!(old.ir_scope.is_none(), "the old pipeline computes no scope");
}

#[test]
fn each_group_is_on_by_default() {
    // Stage F8 turns group A on, stage F10 turns group B (loops) on, stage
    // F13 turns group C (closures and function values) on, stage F17 turns
    // group D (handlers) on, stage F19 turns group E (tasks) on, and stage
    // F20 turns group F (type parameters) on (plan §2.6): the default
    // options put a program of each group in scope.
    assert_eq!(Options::default().ir_groups, Groups::ALL);
    let o = Options {
        facts: FactGen::Ir,
        ..Options::default()
    };
    let a = analyze("fn main() { let x = 1; print(x) }\n", o);
    assert!(a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope));
    let a = analyze("fn main() { let i = 0; while i < 3 { i += 1 } }\n", o);
    assert!(a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope));
    let a = analyze("fn main() { let g = || 1; print(g()) }\n", o);
    assert!(a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope));
    let src = "effect Log { fn log(msg: String) }\nfn main() {\n    handle Log { fn log(msg) { resume(()) } } in log(\"a\")\n}\n";
    let a = analyze(src, o);
    assert!(a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope));
    let src = "fn main() {\n    scope { s =>\n        s.spawn(|| print(1))\n    }\n}\n";
    let a = analyze(src, o);
    assert!(a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope));
    let src = "fn id<T>(x: T) -> T { x }\nfn main() { print(id(1)) }\n";
    let a = analyze(src, o);
    assert!(a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope));
}

/// The fallback note of `src` with the `ir` pipeline, group A and the fact
/// generator of the pipeline.
fn fallback_a(src: &str) -> Option<String> {
    let a = analyze(src, opts(FactGen::Ir, Groups::of(Group::A)));
    a.ir_scope.and_then(|s| s.fallback)
}

#[test]
fn a_variant_payload_of_no_field_or_of_more_fields_is_w0121() {
    // Stage F10.1, hole H-B (review of stage F10): such a body had no IR and
    // no error for it, so the old pipeline checked the program. From plan
    // stage R0b `typeck` rejects the payload (W0121): the body has no IR for
    // an error of the program, and the program stays in scope.
    let cases = [
        // A variant payload with two fields.
        "enum E { A(u64, u64), B }
            fn main() {
                let e = E.A(1, 2)
                let v = Vec.new()
                v.push(1)
                let r = &v[0]
                v.push(2)
                print(r)
                print(e.A)
            }",
        // The same in a callee, next to an error of another body.
        "enum E { A(u64, u64), B }
            fn show(e: &E) { print(e.A) }
            fn bad(v: &Vec<u64>) / mut(v) {
                let r = &v[0]
                v.push(2)
                print(r)
            }
            fn main() { let v = Vec.new(); v.push(1); bad(&v); show(&E.A(1, 2)) }",
        // A variant with no field.
        "enum E { A(u64, u64), B }
            fn main() { let e = E.B; print(e.B) }",
    ];
    for src in cases {
        assert_eq!(fallback_a(src), None, "{src}");
        let a = analyze(src, opts(FactGen::Ir, Groups::of(Group::A)));
        assert!(
            a.diags.iter().any(|d| d.code == Code::W0121),
            "{src}: {:?}",
            diags(&a)
        );
    }
}

/// The fallback note of `src` with the default options (each group on).
fn fallback(src: &str) -> Option<String> {
    let a = analyze(src, Options::default());
    a.ir_scope.and_then(|s| s.fallback)
}

#[test]
fn a_callee_with_no_ir_gets_the_worst_case_of_its_declaration() {
    // Plan stage R0b. Each callee has a type error, so it has no IR. Its
    // summary comes from its declaration (the worst case), not from the old
    // inference, whose parts a summary cannot carry: the program stays in
    // scope, and the type error rejects it.
    let cases = [
        // The callee keeps a function value (the old part `ret`).
        "fn keep(f: fn()) -> fn() { let x: u64 = true; f }
        fn main() { let v = Vec.new(); let g = keep(|| v.push(1)); g() }",
        // The callee starts a task (the old parts `tasks` and `task_runs`).
        "fn start(f: fn()) {
            let x: u64 = true
            scope { s =>
                let t = s.spawn(f)
                t.join()
            }
        }
        fn main() { start(|| print(1)) }",
        // The callee runs a closure that changes a place: the worst case
        // runs it as a task that the facts follow.
        "fn run(f: fn()) { let x: u64 = true; f() }
        fn main() { let v = Vec.new(); run(|| v.push(1)); print(v.len()) }",
        // A callee with a stated row.
        "effect Log { fn log(n: u64) }
        fn logs(f: fn()) / Log { let x: u64 = true; f(); log(1) }
        fn main() { handle Log { fn log(n) { resume(()) } } in logs(|| print(2)) }",
    ];
    for src in cases {
        assert_eq!(fallback(src), None, "{src}");
        let a = analyze(src, Options::default());
        assert!(
            a.diags.iter().any(|d| d.code == Code::W0102),
            "{src}: {:?}",
            diags(&a)
        );
    }
}

#[test]
fn a_handler_with_no_clause_for_an_operation_passes_it_on() {
    // Plan stage R0b: the builder gives such an operation to the capability
    // of the handler outside (an upvar of the site) or of the row, as the
    // interpreter does. The program stays in scope.
    let cases = [
        "effect Log2 { fn l(m: String) }
        fn f() { handle Log2 {} in l(\"x\") }",
        "fn main() / io {
            handle Log { fn info(m) { print(\"caught {m}\"); resume(()) } } in {
                log.info(\"a\")
                log.warn(\"b\")
            }
        }",
        "effect Note { fn note(n: u64), fn flush() }
        fn f() {
            handle Note { fn note(n) { resume(()) } fn flush() { resume(()) } } in {
                handle Note {} in note(3)
            }
        }",
    ];
    for src in cases {
        assert_eq!(fallback(src), None, "{src}");
        let a = analyze(src, Options::default());
        assert!(a.diags.is_empty(), "{src}: {:?}", diags(&a));
    }
}

#[test]
fn the_note_of_a_fallback_names_the_body_that_the_fact_generator_does_not_support() {
    // Plan stage R0b: the callers of a body that the fact generator does not
    // support get the worst case of its declaration, so the note gives the
    // reason of that body, not "a call of a function with ...".
    let src = "effect Get { fn get() -> fn() }
        fn run_it() / Get { let g = get(); g() }
        fn first() { kont() }
        fn kont() { let v = Vec.new(); v.push(1); handle Get { fn get() { resume(|| v.clear()) } } in { run_it() } }";
    let why = fallback(src).expect("out of scope");
    assert!(why.contains("gives a function value"), "{why}");
}

#[test]
fn a_body_with_no_ir_for_an_error_of_the_program_keeps_the_program_in_scope() {
    // A W01xx diagnostic of `typeck` in the body.
    let typo = "fn typo() -> u64 { nope }
        fn plain(n: u64) -> u64 { n + 1 }";
    // W0303 in the body.
    let w0303 = "struct Holder { name: String }
        fn take(s: String) { print(s) }
        fn steal(h: &Holder) { take(h.name) }";
    for src in [typo, w0303] {
        assert_eq!(fallback_a(src), None, "{src}");
    }
}

#[test]
fn a_reference_through_a_copy_of_an_rc_handle_stays_in_scope() {
    // Plan stage R0c (reason A1 of the scope report): the store check
    // decides if a copy of a handle (`let d = c.clone()`) is a handle of the
    // object that gets the reference, and the program stays in scope. A copy
    // of the handle parameter of the store that gets no other value is a
    // handle of the same object: no W0204.
    let copy = "struct Cache { refs: Vec<&u64>, data: Vec<u64> }
        fn fill(c: Rc<Cache>) / mut(Cache) {
            let d = c.clone()
            d.data.push(1)
            c.refs.push(&d.data[0])
        }";
    assert_eq!(fallback(copy), None);
    let a = analyze(copy, Options::default());
    assert!(
        !a.diags.iter().any(|d| d.code == Code::W0204),
        "{:?}",
        diags(&a)
    );
    // Else the facts cannot tell, and the check reports W0204: a store
    // handle in an `rc` object, and a local that can get another value.
    let cases = [
        "struct Cache { refs: Vec<&u64>, data: Vec<u64> }
        fn newc() -> Rc<Cache> { Rc.new(Cache { refs: Vec.new(), data: Vec.new() }) }
        fn fill(c: Rc<Rc<Cache>>) / mut(Cache) {
            let d = newc()
            d.data.push(1)
            c.refs.push(&d.data[0])
        }",
        "struct Cache { refs: Vec<&u64>, data: Vec<u64> }
        fn newc() -> Rc<Cache> { Rc.new(Cache { refs: Vec.new(), data: Vec.new() }) }
        fn fill(c: Rc<Cache>, b: bool) / mut(Cache) {
            let d = c.clone()
            if b { d = newc() }
            d.data.push(1)
            c.refs.push(&d.data[0])
        }",
    ];
    for src in cases {
        assert_eq!(fallback(src), None, "{src}");
        let a = analyze(src, Options::default());
        assert!(
            a.diags.iter().any(|d| d.code == Code::W0204),
            "{src}: {:?}",
            diags(&a)
        );
    }
}

#[test]
fn a_task_that_performs_through_a_handler_of_this_task_is_w0314_in_scope() {
    // Plan stage R0c (reason A2 of the scope report): the clause would run
    // on another task, so the continuation of its `resume` has no node of
    // the handled body. The part `tasks` reports W0314, and the program
    // stays in scope.
    let cases = [
        "effect Tick { fn tick() }
        fn worker() / Tick, async { tick() }
        fn main() / async {
            let n = 0
            handle Tick { fn tick() { n += 1; resume(()) } } in {
                scope { s => s.spawn(|| worker()) }
            }
            print(n)
        }",
        "effect Tick { fn tick() }
        fn main() / par {
            let n = 0
            handle Tick { fn tick() { n += 1; resume(()) } } in fork(|| tick(), || print(2))
            print(n)
        }",
    ];
    for src in cases {
        assert_eq!(fallback(src), None, "{src}");
        let a = analyze(src, Options::default());
        assert!(
            a.diags.iter().any(|d| d.code == Code::W0314),
            "{src}: {:?}",
            diags(&a)
        );
    }
}

#[test]
fn a_loop_that_builds_a_recursive_value_ends() {
    // Plan stage R0c (reason B1 of the scope report): rule 5 of the
    // widening limits the depth of the values at a loop head, so the
    // analysis of the loop ends and the program stays in scope.
    let clean = "enum List { Cons(u64, List), Nil }
        fn main() {
            let l = Nil
            let i = 0
            while i < 10 {
                l = Cons(i, l)
                i += 1
            }
        }";
    assert_eq!(fallback(clean), None);
    assert!(analyze(clean, Options::default()).diags.is_empty());
    let deep = "enum Refs { More(&u64, Refs), End }
        fn first(l: &Refs) -> u64 {
            match l {
                More(r, _) => r + 0,
                End => 0,
            }
        }
        fn main() {
            let v = Vec.new()
            v.push(1)
            let w: u64 = 3
            let l = More(&v[0], End)
            let i = 0
            while i < 20 {
                l = More(&w, l)
                i += 1
            }
            v.push(2)
            print(first(&l))
        }";
    // The checker reports W0301 for `deep` (corpus
    // `186_recursive_list_loop.wf`).
    assert_eq!(fallback(deep), None);
}

#[test]
fn a_construct_with_no_full_facts_keeps_both_views_for_the_check() {
    // Stage R0g: a `resume` in a closure has no full facts. The program is
    // pending: the scope names the reason, and the analysis keeps the facts
    // of the old lowering and those of the `ir` pipeline, also in the `ir`
    // mode. `weft_check::check_analysis` decides.
    let src = "effect Ask { fn ask() -> u64 }
        fn kont() -> u64 { handle Ask { fn ask() { let k = || resume(1); k() } } in ask() }";
    let a = analyze(src, opts(FactGen::Ir, Groups::ALL));
    let scope = a.ir_scope.as_ref().expect("a scope");
    assert_eq!(scope.fallback, None);
    let p = scope.pending.as_ref().expect("pending");
    assert!(p.reason.contains("captured continuation"), "{}", p.reason);
    assert!(p.ir_view);
    assert!(a.ir_facts.is_some(), "both views");
    let both = analyze(src, opts(FactGen::Both, Groups::ALL));
    let p = both.ir_scope.and_then(|s| s.pending).expect("pending");
    assert!(!p.ir_view);
}

#[test]
fn function_values_and_references_across_operations_are_in_scope() {
    // Plan stage R0h. C2: a function value in an argument of an operation of
    // a handler of a caller. D3: a callee gives a function value to a clause
    // of a local handler, and a clause gives a reference or a function value
    // that cannot race back to the callee.
    let in_scope = [
        "effect Run { fn run(g: fn()) }
        fn f() / Run { let n = 5; run(|| print(n)) }",
        "effect Run { fn run(g: fn()) }
        fn f() / Run { let n = 5; run(|| print(n)) }
        fn main() { handle Run { fn run(g) { g(); resume(()) } } in { f() } }",
        "effect Pick { fn pick() -> &u64 }
        fn user() / Pick { let r = pick(); print(r) }
        fn main() { let v = Vec.new(); v.push(1); handle Pick { fn pick() { resume(&v[0]) } } in user() }",
        "effect Get { fn get() -> fn() }
        fn run_it() / Get { let g = get(); g() }
        fn main() { handle Get { fn get() { resume(|| print(1)) } } in { run_it() } }",
    ];
    for src in in_scope {
        assert_eq!(fallback(src), None, "{src}");
    }
    // A value that the clause can keep with a reference in it, and a value
    // that a clause gives back and that can race, keep the old pipeline.
    let out = [
        "effect Run { fn run(g: fn()) }
        fn f(v: &Vec<u64>) / Run { let r = &v[0]; run(|| print(r)) }",
        "effect Get { fn get() -> fn() }
        fn run_it() / Get { let g = get(); g() }
        fn main() { let v = Vec.new(); v.push(1); handle Get { fn get() { resume(|| v.clear()) } } in { run_it() } }",
    ];
    for src in out {
        assert!(fallback(src).is_some(), "{src}");
    }
}

#[test]
fn the_task_fallbacks_are_pending() {
    // Plan stage R0j: a task run with no full facts is pending (the rule of
    // stage R0g). The scope names the reason, and `weft_check` decides: an
    // error of the `ir` pipeline is final, else the old pipeline checks the
    // program. Each source is the clean twin of a probe.
    let pending = [
        (
            include_str!("../../../tests/gate/probes/fixes/r0j/j01_again_ok.wf"),
            "runs a callback more than once",
        ),
        (
            include_str!("../../../tests/gate/probes/fixes/r0j/j02_late_ok.wf"),
            "function variable that gets a new value",
        ),
        (
            include_str!("../../../tests/gate/probes/fixes/r0j/j03_nested_ok.wf"),
            "a function value of a callee runs as a task",
        ),
        (
            include_str!("../../../tests/gate/probes/fixes/r0j/j04_value_ok.wf"),
            "runs a value of its arguments as a task",
        ),
        (
            include_str!("../../../tests/gate/probes/fixes/r0j/j05_code_old.wf"),
            "runs code of a caller",
        ),
    ];
    for (src, reason) in pending {
        let a = analyze(src, opts(FactGen::Ir, Groups::ALL));
        let scope = a.ir_scope.as_ref().expect("a scope");
        assert_eq!(scope.fallback, None, "{src}");
        let p = scope.pending.as_ref().expect("pending");
        assert!(p.reason.contains(reason), "{}: {src}", p.reason);
    }
    // A spawn on one of two nested scopes has full facts: the task ends at
    // the outer scope (`SiteScope::end`).
    let src = include_str!("../../../tests/gate/probes/fixes/r0j/j06_unowned_ok.wf");
    let a = analyze(src, opts(FactGen::Ir, Groups::ALL));
    let scope = a.ir_scope.as_ref().expect("a scope");
    assert_eq!(
        (scope.fallback.as_deref(), scope.pending.is_some()),
        (None, false)
    );
    // A value that code of a caller runs on a foreign task stays with the
    // old pipeline: the weak facts give W0403 at the call.
    let src = include_str!("../../../tests/gate/probes/fixes/r0j/j07_run_ok.wf");
    let reason = fallback(src).expect("a fallback");
    assert!(reason.contains("can run on another thread"), "{reason}");
}
