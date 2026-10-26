//! Stored values in the `ir` pipeline (plan stage F13; `docs/ir.md` 6.6 heap
//! slots, 6.7 `stores`, 6.9 the W0204 store forms).
//!
//! A function value or a reference that a body puts behind a reference, in a
//! `Vec`, a `Box`, an `Option` or an `rc` object goes into the heap slot of
//! the place. A later read of the place gets the stored values, a run of a
//! stored function value applies its summary, and code of a caller runs each
//! value that its arguments reach. Each test checks a program of
//! `tests/data/stored/` with `--facts=ir` and the groups A, B and C on. The
//! program must be in scope, and the `//~ CODE` markers are the diagnostics
//! of the `ir` pipeline.

use std::fs;
use std::path::Path;

use weft_check::check_analysis;
use weft_sema::{analyze_source, Options};

/// The options of the `ir` pipeline with the groups A, B and C on.
fn abc(src: &str) -> Options {
    Options {
        facts: weft_sema::FactGen::Ir,
        ir_groups: weft_sema::Groups::parse("ABC").unwrap_or(weft_sema::Groups::NONE),
        ..Options::from_markers(src)
    }
}

/// The line of byte offset `lo` of `src`.
fn line_of(src: &str, lo: u32) -> usize {
    src.get(..lo as usize)
        .map_or(0, |s| s.matches('\n').count() + 1)
}

/// The text of program `name` of `tests/data/stored/`.
fn program(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/data/stored")
        .join(name);
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// The codes and lines of the diagnostics of `src` with the `ir` pipeline
/// and the groups A, B and C on. The program must be in scope.
fn abc_codes(name: &str, src: &str) -> Vec<(String, usize)> {
    let a = analyze_source(src, abc(src))
        .unwrap_or_else(|d| panic!("{name} does not parse: {}", d.message));
    assert!(
        a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope),
        "{name}: {:?}",
        a.ir_scope.as_ref().and_then(|s| s.fallback.clone())
    );
    let mut got: Vec<(String, usize)> = check_analysis(a, &[])
        .diags
        .iter()
        .map(|d| (format!("{:?}", d.code), line_of(src, d.span.lo)))
        .collect();
    got.sort();
    got
}

/// The `//~ CODE` markers of `src` as (code, line), sorted.
fn markers(src: &str) -> Vec<(String, usize)> {
    let mut want: Vec<(String, usize)> = src
        .lines()
        .enumerate()
        .filter_map(|(i, l)| l.split("//~ ").nth(1).map(|c| (c.to_string(), i + 1)))
        .flat_map(|(c, l)| {
            c.split_whitespace()
                .map(|x| (x.to_string(), l))
                .collect::<Vec<_>>()
        })
        .collect();
    want.sort();
    want
}

/// Checks program `name` with the groups A, B and C: its diagnostics are
/// its markers.
fn check(name: &str) {
    let src = program(name);
    assert_eq!(abc_codes(name, &src), markers(&src), "{name}");
}

#[test]
fn a_function_value_behind_a_reference_applies_its_summary_where_it_runs() {
    // A store through a reference, a read back, a loop, a callee that stores
    // its function parameter or a closure of its own (also two levels down),
    // and code of a caller that runs the value of a heap slot. The old
    // pipeline misses `registered_behind` and `registered2`.
    check("behind_ref.wf");
}

#[test]
fn function_values_in_a_vec_a_box_and_an_option_behind_a_reference_apply_their_summaries() {
    // The old pipeline misses `vec_own`, `boxed_callee` and `option_slot`.
    check("containers.wf");
}

#[test]
fn references_and_function_values_in_an_rc_object_stay_after_the_return() {
    // FD3, V108: the W0204 store forms of `tests/programs/116_rc_stores.wf`
    // (with no clause: group D), and closures that an `rc` object holds.
    // The old pipeline misses `hook_own`.
    check("rc.wf");
}

#[test]
fn the_store_check_covers_the_stores_of_closures_and_of_callees() {
    // V087, V037: a closure that puts a reference into its own local behind a
    // captured reference, a closure that captures a local behind a reference
    // parameter, a callee that stores the closure.
    check("stores_w0204.wf");
}

#[test]
fn a_closure_that_leaves_the_body_sees_the_last_value_of_a_kept_variable() {
    // Class K3 of stage F12: the value of a closure keeps the references of
    // a `Kept` variable where the closure is made. A new value into a local
    // of the body after that is W0204 at the return and at the store (as
    // the late stores of the old lowering). Before stage F13 the ir pipeline
    // accepted both, and a run of the closure read the dead local.
    check("kept_late.wf");
}
