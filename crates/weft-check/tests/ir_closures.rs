//! Closures in the `ir` pipeline (plan stage F11, group C part 1;
//! `docs/ir.md` 5.1.7, 5.22, 6.5, 6.7).
//!
//! Group C stays off by default until stage F13. Each test checks a program
//! of `tests/data/closures/` with `--facts=ir` and the groups A, B and C on.
//! The program must be in scope, and the `//~ CODE` markers are the
//! diagnostics of the `ir` pipeline.

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

/// The text of program `name` of `tests/data/closures/`.
fn program(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/data/closures")
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
        .filter_map(|(i, l)| {
            l.split("//~ ")
                .nth(1)
                .map(|c| (c.trim().to_string(), i + 1))
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
fn a_closure_reads_the_new_value_of_a_captured_reference() {
    // RR7: the closure holds the cell of `r` (a `Kept` capture). A call of
    // the closure uses the value of `r` at the call, so the new value that
    // the change invalidates is W0301. The control gives `r` a valid value
    // after the change, so the call is valid (the old pipeline reports the
    // creation-time place there).
    check("rr7_late_ref.wf");
}

#[test]
fn a_capture_reached_through_an_inner_closure_is_checked_at_the_call() {
    // V103: `f` runs `g`, a capture of `f` (the part `runs` of the summary
    // of `f`). At the call of `f` the summary of the value of `g` there
    // applies, and it uses `r`. A new value of a part of a captured tuple is
    // checked through the variable of the part.
    check("v103_nested.wf");
}

#[test]
fn a_move_and_a_new_value_of_a_captured_variable_keep_the_closure_valid() {
    // O3-11: a `ByRef` capture points into the cell of `v`, not into its
    // value: a move of `v` does not end the cell. The call reads the value
    // of `v` at the call: valid after a new value, W0302 after a move with
    // no new value.
    check("o3_11_refill.wf");
}

#[test]
fn a_returned_closure_that_borrows_a_local_is_w0204_and_a_kept_counter_is_valid() {
    // J5d: `|| print(norm(&p))` captures `p` by reference: the closure
    // points into the cell of `p`, which ends at the return (W0204). The
    // counter closure (`d5_count.wf`) keeps `n` (`Kept`): no reference
    // points into the cell, so the returned closure is valid.
    check("j5d_counter.wf");
}

#[test]
fn a_closure_that_changes_two_aliased_captures_sees_the_alias() {
    // The instantiation of the closure component (`docs/ir.md` 6.5): the
    // captures `a` and `v` name places of the maker, so the change of `v`
    // invalidates the reference into `*a` inside the closure.
    check("aliased_captures.wf");
}

#[test]
fn a_once_closure_called_twice_is_w0502() {
    // The call of a `once` closure moves it. `let g = f` gives `g` the mode
    // `once` from the analysis, but its read stays a copy (B12-fn-once): the
    // facts take the move from the mode (`props.once`), not from `copy`.
    check("once_twice.wf");
}

#[test]
fn a_closure_that_rebinds_a_capture_on_each_path_rebinds_it_at_the_call() {
    // F3-11: the part `rebinds` of the summary gives `r` a new value at the
    // `Ret` node of the call, after the change of the callee. A new value on
    // one path only is a weak definition: the old value stays, and the
    // change invalidates it (W0301).
    check("f3_11_rebind.wf");
}

#[test]
fn a_closure_that_moves_its_captures_owns_them() {
    // R3RT5: a `ByMove` capture moves into the closure when it is made, so
    // the end of the variable does not invalidate the closure (the old
    // pipeline reports W0204 and W0301 here).
    check("r3rt5_by_move.wf");
}

#[test]
fn the_runs_of_captured_closures_move_a_once_value() {
    // RR7 `late_once`, V103 `nested_once`: `j` runs `k`, which runs `c`; at
    // the second call `c` holds a `once` closure that the first call moved
    // (W0502). With one call the program is valid (B12-late-once). A closure
    // that writes a `Kept` counter changes the counter at each call.
    check("nested_once.wf");
}

#[test]
fn a_closure_that_moves_a_linear_capture_on_one_path_drops_it_on_the_other() {
    // Defect of the preview (lost fault, tier 1 g9_closure_branch_lin.wf):
    // the `E` variable of a `ByMove` capture ends at the `Return` of the
    // closure body, so a linear value that a path does not consume is W0601.
    check("move_linear_one_path.wf");
}

#[test]
fn a_change_through_a_parameter_of_a_closure_needs_no_row_of_the_function() {
    // Defect of the preview (new false positive, tier 1 rt24_apply.wf): the
    // parameter roots of a closure are `Arg` roots, not parameters of the
    // function, so W0703 does not check them in the body. The call changes
    // the places of the argument: W0703 there if the row does not state them.
    check("closure_param_change.wf");
}

#[test]
fn a_closure_that_resumes_more_than_once_is_multi_at_its_call() {
    // Defect of the preview (lost W0503, tier 1 u1_uniq.wf): the summary of
    // a closure has the part `multi`.
    check("closure_multi.wf");
}

#[test]
fn a_closure_that_keeps_a_uniq_reference_can_run_twice() {
    // Defect of the preview (W0502 false positive, tier 1 a1.wf): a call
    // moves the closure only if the closure is `once` because it moves a
    // capture, not if its local is `once` because of a `@ uniq` capture.
    check("uniq_capture_twice.wf");
}

#[test]
fn a_closure_that_rebinds_a_linear_capture_drops_the_old_value_once() {
    // Preview of stage F11 (tier 1 ow_closure_run.wf): the body drops the
    // old value (W0601 there); the new value at the call is no second
    // overwrite.
    check("rebind_linear.wf");
}

#[test]
fn a_borrow_for_a_closure_reads_no_place_field() {
    // Preview of stage F11 (tier 1 73_immovable.wf): the borrow of a `ByRef`
    // capture reads no place field; the body of the closure reads its own.
    check("capture_unset_field.wf");
}

#[test]
fn a_linear_closure_that_moves_into_a_place_is_a_linear_value_of_the_place() {
    // A read of a `once` closure moves it (the decision for the class
    // closure-copy): the destination holds the linear value. A local whose
    // type has a function part gets the flag `linear` from the value.
    check("linear_closure_into_vec.wf");
}

#[test]
fn a_move_of_an_immovable_capture_in_the_closure_body_is_w0604() {
    // Preview of stage F11 (tier 1 imm1.wf): the `E` variable of a `ByMove`
    // capture has the flag `immovable` of its type.
    check("immovable_capture.wf");
}

#[test]
fn a_public_function_that_returns_a_closure_states_its_effects() {
    // Preview of stage F11 (tier 1 redteam/pkg): a function with a function
    // value in its signature has no summary until stage F12, so W0701 takes
    // the row of the old inference.
    check("returned_closure_row.wf");
}

#[test]
fn a_closure_program_is_out_of_scope_with_the_default_groups() {
    // Group C stays off by default in stage F11 (plan: F13 turns it on).
    let src = program("rr7_late_ref.wf");
    let opts = Options {
        facts: weft_sema::FactGen::Ir,
        ..Options::from_markers(&src)
    };
    let a = analyze_source(&src, opts).unwrap_or_else(|d| panic!("{}", d.message));
    let fallback = a.ir_scope.as_ref().and_then(|s| s.fallback.clone());
    assert!(
        fallback.as_deref().is_some_and(|f| f.contains("group C")),
        "{fallback:?}"
    );
}
