//! The conservative rejections of plan stage R0z (Z1, rules A to G) and the
//! list of all the reasons of a fallback (Z0).
//!
//! Each rule rejects a program that the old pipeline rejects too, at a
//! construct that keeps the program out of the scope of the `ir` pipeline
//! (a construct with no full facts, or a body whose analysis stops). The
//! error is final (the pending rule of stage R0g), so the program is in
//! scope. Each test checks the probes of `tests/gate/probes/fixes/r0z/`: the
//! bad twin gets the code of the rule at its line, and the clean twin gets
//! no error.

use std::fs;
use std::path::Path;

use weft_check::check_analysis;
use weft_sema::{analyze_source, FactGen, Options};

/// The line of byte offset `lo` of `src`.
fn line_of(src: &str, lo: u32) -> usize {
    src.get(..lo as usize)
        .map_or(0, |s| s.matches('\n').count() + 1)
}

/// The text of probe `name` of `tests/gate/probes/fixes/r0z/`.
fn probe(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/gate/probes/fixes/r0z")
        .join(name);
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// The codes and lines of the errors of probe `name` with the default
/// options, and the reason of the fallback, if any.
fn codes(name: &str) -> (Vec<(String, usize)>, Option<String>) {
    let src = probe(name);
    let opts = Options {
        facts: FactGen::Ir,
        ..Options::from_markers(&src)
    };
    let a = analyze_source(&src, opts)
        .unwrap_or_else(|d| panic!("{name} does not parse: {}", d.message));
    let c = check_analysis(a, &[]);
    let fallback = c
        .analysis
        .ir_scope
        .as_ref()
        .and_then(|s| s.fallback.clone());
    let mut got: Vec<(String, usize)> = c
        .diags
        .iter()
        .filter(|d| d.severity == weft_syntax::diag::Severity::Error)
        .map(|d| (format!("{:?}", d.code), line_of(&src, d.span.lo)))
        .collect();
    got.sort();
    (got, fallback)
}

/// Checks the bad twin `bad` (the `ir` pipeline gives `want`, and the
/// program is in scope) and the clean twin `ok` (no error; `ok_in_scope`
/// tells if the clean twin is in scope or keeps the fallback).
fn twins(bad: &str, want: &[(&str, usize)], ok: &str, ok_in_scope: bool) {
    let (got, fallback) = codes(bad);
    assert!(fallback.is_none(), "{bad}: {fallback:?}");
    let want: Vec<(String, usize)> = want.iter().map(|&(c, l)| (c.to_string(), l)).collect();
    assert_eq!(got, want, "{bad}");
    let (got, fallback) = codes(ok);
    assert!(got.is_empty(), "{ok}: {got:?}");
    assert_eq!(fallback.is_none(), ok_in_scope, "{ok}: {fallback:?}");
}

/// Rule A: a task that holds a continuation is W0314 at the spawn. The
/// analysis gives it for a body that it supports (`a1`), and the structural
/// form gives it for a body whose analysis stops (`a2`: the capability of a
/// local handler in the spawned closure).
#[test]
fn rule_a_a_task_cannot_hold_a_continuation_or_a_local_capability() {
    twins(
        "a1_task_resume_bad.wf",
        &[("W0314", 7)],
        "a1_task_resume_ok.wf",
        true,
    );
    twins(
        "a2_task_cap_bad.wf",
        &[("W0314", 16)],
        "a2_task_cap_ok.wf",
        true,
    );
}

/// Rule B: a task that runs the value of an operation of a user effect is
/// W0314 at the spawn.
#[test]
fn rule_b_a_task_cannot_run_the_value_of_an_operation() {
    twins(
        "b1_task_op_value_bad.wf",
        &[("W0314", 6)],
        "b1_task_op_value_ok.wf",
        true,
    );
}

/// Rule C: a value that a callee runs as a task of another stack and that
/// holds the capability of a local handler is W0314 at the call. The clean
/// twin keeps the fallback (a value of a callee runs the value as a task).
#[test]
fn rule_c_a_foreign_task_cannot_hold_a_local_capability() {
    twins(
        "c1_sim_param_task_bad.wf",
        &[("W0314", 11)],
        "c1_sim_param_task_ok.wf",
        false,
    );
}

/// Rule D: a closure that performs through a local handler and goes to an
/// operation of that handler (`d1`), or into a local outside the handled
/// body (`d2`: a write in the handled body; `d3`: the clause of another
/// handler writes its parameter there), is W0313 at the `handle`.
#[test]
fn rule_d_a_capability_closure_cannot_leave_its_handler() {
    twins("d1_own_op_bad.wf", &[("W0313", 6)], "d1_own_op_ok.wf", true);
    twins(
        "d2_local_keep_bad.wf",
        &[("W0313", 14)],
        "d2_local_keep_ok.wf",
        true,
    );
    twins(
        "d3_clause_keep_bad.wf",
        &[("W0313", 12)],
        "d3_clause_keep_ok.wf",
        false,
    );
}

/// Rule E: a `once` value that a value of a callee runs as a task more than
/// once is W0502 at the call.
#[test]
fn rule_e_a_nested_task_run_cannot_run_a_once_value_twice() {
    twins(
        "e1_nested_once_bad.wf",
        &[("W0502", 8)],
        "e1_nested_once_ok.wf",
        false,
    );
}

/// Rule F: two `resume`s of a `once` continuation on a path of a scope body
/// of the clause are W0501 at the second one.
#[test]
fn rule_f_a_once_continuation_cannot_resume_twice_in_a_scope_body() {
    twins(
        "f1_scope_resumes_bad.wf",
        &[("W0501", 6)],
        "f1_scope_resumes_ok.wf",
        false,
    );
}

/// Rule G: the error of a body that does not reach the body whose analysis
/// stops is final.
#[test]
fn rule_g_an_error_that_does_not_need_the_failed_body_is_final() {
    twins(
        "g1_other_body_bad.wf",
        &[("W0301", 11)],
        "g1_other_body_ok.wf",
        false,
    );
}

/// Rule G: a body that reaches the body whose analysis stops gets the facts
/// of its declaration only, so the worst case of the failed body gives no
/// error there.
#[test]
fn rule_g_a_body_that_reaches_the_failed_body_gives_no_error() {
    let src = "effect Run { fn run(g: fn()) }
fn mk(h: fn()) -> fn() / Run { || run(h) }
fn uses() / Run {
    let v = Vec.new()
    v.push(1)
    let r = &v[0]
    let c = mk(|| print(1))
    c()
    print(r)
}
fn main() {
    handle Run { fn run(g) { g()
        resume(()) } } in { uses() }
}
";
    let a = analyze_source(src, Options::default()).expect("parses");
    let c = check_analysis(a, &[]);
    assert!(c.ok(), "{:?}", c.codes());
    let fallback = c.analysis.ir_scope.and_then(|s| s.fallback);
    assert!(fallback.is_some_and(|f| f.contains("an operation gives to a handler")));
}

/// Z0: the list of the reasons has each body whose analysis stops, not only
/// the first one, and each construct with no full facts.
#[test]
fn the_reasons_list_each_body_that_stops_and_each_pending_construct() {
    let src = "effect Run { fn run(g: fn()) }
effect Ask { fn ask() -> u64 }
fn mk1(h: fn()) -> fn() / Run { || run(h) }
fn mk2(h: fn()) -> fn() / Run { || run(h) }
fn asks() {
    handle Ask { fn ask() { let f = || resume(1); f() } } in { print(ask()) }
}
fn main() { asks() }
";
    let opts = Options {
        facts: FactGen::Old,
        ..Options::default()
    };
    let a = analyze_source(src, opts).expect("parses");
    let list = weft_sema::factgen::reasons(&a, weft_sema::DEFAULT_GROUPS, false);
    let has = |what: &str| list.iter().any(|r| r.contains(what));
    assert!(
        has("`mk1`: the fact generator does not support"),
        "{list:?}"
    );
    assert!(
        has("`mk2`: the fact generator does not support"),
        "{list:?}"
    );
    assert!(has("pending: the fact generator does not support group D: a `resume` of a captured continuation"), "{list:?}");
    // A program with full facts has no reason.
    let a = analyze_source("fn main() { print(1) }", opts).expect("parses");
    assert!(weft_sema::factgen::reasons(&a, weft_sema::DEFAULT_GROUPS, false).is_empty());
}

/// The probes of the review of Z1 (rounds 1 and 2). A clean twin keeps the verdict
/// of the old pipeline (no error): rule E counts the runs of each value, the
/// structural form of rule A counts a capability of the closure of the task
/// only if its code uses it, and an error of a rule of Z1 (each error of
/// rule G) closes a fallback only if the old pipeline rejects the program
/// too. Each bad twin is rejected.
#[test]
fn the_review_probes_of_z1_keep_the_verdict_of_the_old_pipeline() {
    for name in [
        "rv_e06_two_values_ok.wf",
        "rv_e02_param_other_ok.wf",
        "rv_e09_outer_two_ok.wf",
        "rv_a01_cap_unused_ok.wf",
        "rv_g01_fp_a01_ok.wf",
        "rv_g02_fp_a03_ok.wf",
        "rv_g03_fp_tw_ok.wf",
        "rv2_n06_collide_e_ok.wf",
    ] {
        let (got, _) = codes(name);
        assert!(got.is_empty(), "{name}: {got:?}");
    }
    for name in [
        "rv_e06_two_values_bad.wf",
        "rv_e02_param_other_bad.wf",
        "rv_e09_outer_two_bad.wf",
        "rv_a01_cap_unused_bad.wf",
        "rv_g01_fp_a01_bad.wf",
        "rv_g02_fp_a03_bad.wf",
        "rv2_n07_nocollide_e_bad.wf",
    ] {
        let (got, _) = codes(name);
        assert!(!got.is_empty(), "{name}: no error");
    }
    // Round 2: the true W0502 of the check at the call of `two` stays, also
    // with the W0502 of rule E at the same span with the same text: the
    // program is in scope without Z1, as in main.
    let (got, fallback) = codes("rv2_n06_collide_e_bad.wf");
    assert!(fallback.is_none(), "{fallback:?}");
    assert_eq!(got, vec![("W0502".to_string(), 20)]);
}
