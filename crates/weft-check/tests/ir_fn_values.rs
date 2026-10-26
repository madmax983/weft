//! Function values in the `ir` pipeline (plan stage F12, group C part 2;
//! `docs/ir.md` 5.21, 5.22, 5.23, 5.35, 6.6, 6.7).
//!
//! Group C stays off by default until stage F13. Each test checks a program
//! of `tests/data/fn_values/` with `--facts=ir` and the groups A, B and C on.
//! The program must be in scope, and the `//~ CODE` markers are the
//! diagnostics of the `ir` pipeline. A marker can hold more than one code.

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

/// The text of program `name` of `tests/data/fn_values/`.
fn program(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/data/fn_values")
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
fn a_call_through_a_function_item_value_applies_the_summary_of_the_item() {
    // RT6: the item changes `world.entities` (W0301, W0701, W0402 as for a
    // direct call).
    check("rt6_item_values.wf");
}

#[test]
fn an_if_joins_the_summaries_of_two_items() {
    // RT6: each item that the value can be applies its summary.
    check("rt6_if_item.wf");
}

#[test]
fn a_closure_through_a_tuple_an_if_and_a_result_applies_its_summary() {
    // RT7.
    check("rt7_closure_tuple.wf");
}

#[test]
fn the_effects_of_a_closure_reach_the_caller_through_a_return_a_field_and_a_parameter() {
    // RT7: a returned closure, an `if` of items, a closure in a field of an
    // argument, a closure that a function parameter runs.
    check("rt7_effects_hidden.wf");
}

#[test]
fn closures_that_meet_in_a_container_each_apply_their_summary() {
    // RR2: an array, a `Vec`, an element assignment, an `Option`, a field.
    check("rr2_containers.wf");
}

#[test]
fn closures_that_meet_in_a_tuple_type_each_apply_their_summary() {
    // V107.
    check("v107_tuples.wf");
}

#[test]
fn a_callee_that_runs_a_callback_twice_applies_its_summary_twice() {
    // OR3: a direct callee, a loop in the callee, a callee of a callee, and a
    // returned closure that runs the callback twice.
    check("or3_callback.wf");
}

#[test]
fn a_returned_closure_points_into_the_places_of_its_captured_references() {
    // OR1: a move, the end and a change of the argument make the closure
    // invalid.
    check("or1_returned.wf");
}

#[test]
fn the_result_of_a_function_parameter_points_into_the_places_of_the_callers() {
    // Map N2 (`fnres2.wf`): the second run can change what the first result
    // points into.
    check("fnres2.wf");
}

#[test]
fn a_call_of_a_function_parameter_lends_the_places_of_its_arguments() {
    check("fn_param_lends.wf");
}

#[test]
fn the_lost_faults_of_the_preview_are_rejected() {
    // The preview of stage F12 found these classes on tier 1: a `once`
    // closure that a callee runs twice, two runs in each order, a run after
    // a change of the callee, a closure that a closure gives back, a linear
    // closure in a field (W0601 at the end of its scope), the result of a
    // run, and W0705.
    check("preview_fixes.wf");
}

#[test]
fn a_read_of_a_once_closure_in_an_element_a_field_or_a_capture_moves_it() {
    check("copy_once.wf");
}

#[test]
fn more_classes_of_the_preview_are_rejected() {
    // A closure that a returned closure runs keeps the last value of its
    // captured reference; a parameter type with a row performs it; a callee
    // that does not run a linear closure can drop it.
    check("preview_fixes2.wf");
}

#[test]
fn a_closure_that_code_of_a_caller_can_run_on_another_thread_stays_with_the_old_pipeline() {
    let src = program("foreign_task.wf");
    let a = analyze_source(&src, abc(&src)).unwrap_or_else(|d| panic!("{}", d.message));
    let why = a
        .ir_scope
        .as_ref()
        .and_then(|s| s.fallback.clone())
        .unwrap_or_default();
    assert!(why.contains("another thread"), "{why}");
}

#[test]
fn a_reference_into_the_frame_of_a_callee_that_a_closure_keeps_goes_out_of_scope() {
    check("run_frame.wf");
}

#[test]
fn a_run_checks_the_changes_of_the_value_against_the_places_that_the_callee_gives() {
    // The places behind a parameter whose type holds no function value
    // give no function value (`world: &World`): before the fix, the
    // capture `world` made code of a caller run at the call (W0312 on the
    // clean cases).
    check("run_given.wf");
}

#[test]
fn a_closure_that_runs_a_capture_gives_back_what_the_run_gives_back() {
    check("run_results.wf");
}

#[test]
fn a_linear_closure_that_a_function_value_can_drop_is_w0601() {
    check("value_drops.wf");
}

#[test]
fn a_vector_of_function_values_in_another_value_is_linear_only_with_a_linear_closure() {
    // Review of the ABC preview, false positive FP1: a push of a value that
    // is not linear made the vector a linear value in the state, so the
    // vector in another vector, an `Option` or a field was W0601.
    check("vec_of_fns.wf");
}

#[test]
fn a_closure_that_a_maker_gives_back_keeps_its_effects_through_calls_and_values() {
    // Review of the ABC preview, hole H2: a `Made` closure lost its effects
    // in a `Vec` (`fs.push(mk())`), through `id(f)` and `run(mk())`, and a
    // closure that a closure gives back lost them in each value. The value
    // holds the places of the environment with its function values.
    check("made_through_values.wf");
}

#[test]
fn a_linear_closure_that_a_maker_gives_back_is_a_linear_value_of_the_caller() {
    // Review of the ABC preview, hole H3: the result of a call that gives
    // back a linear closure (in a value of a type with a function part) is
    // linear (part `ret`, `Ret::linear`); a caller that drops it is W0601.
    check("returned_linear.wf");
}

#[test]
fn a_linear_closure_that_runs_on_some_paths_only_can_go_away() {
    // Review of the ABC preview, hole H5: a callee or a closure that runs a
    // linear closure on some paths only (part `runs`, `Run::maybe`), and a
    // closure that runs a linear capture on some paths only (its `E`
    // variable is linear), is W0601.
    check("runs_on_some_paths.wf");
}

#[test]
fn a_once_closure_that_a_callee_copies_out_of_a_referent_moves() {
    // Old hole of the review of the ABC preview (`oh/b14`): `first(&fs)`
    // gives back a copy of a `once` closure in `fs`; a second copy ran it
    // again. The call moves the referent (the closure-copy rule).
    check("once_copied_out.wf");
}
