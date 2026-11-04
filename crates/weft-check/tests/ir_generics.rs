//! Generic bodies in the `ir` pipeline (plan stage F20; `docs/ir.md` 5.20,
//! 5.35, 5.36, 6.7).
//!
//! The fact generator writes the facts of a generic body with each type
//! parameter linear. The parts `drops` and `holds` of its summary are
//! queries over these facts, and a caller checks them with its type
//! arguments. A generic function item as a value gets the checks of a call
//! where it is made (RR9, V081). A `fork` branch of a generic body gives the
//! part `forks` (OL-NR-ptrfork). Follow-up F8.1: a reference in a place
//! field behind a `Box` goes with a move of the `Box`.
//!
//! Each test checks a program of `tests/data/generics/` with `--facts=ir`
//! and all groups on. The program must be in scope, and the `//~ CODE`
//! markers are the diagnostics of the `ir` pipeline.

use std::fs;
use std::path::Path;

use weft_check::check_analysis;
use weft_sema::{analyze_source, Options};

/// The options of the `ir` pipeline with all groups on.
fn all_groups(src: &str) -> Options {
    Options {
        facts: weft_sema::FactGen::Ir,
        ir_groups: weft_sema::Groups::ALL,
        ..Options::from_markers(src)
    }
}

/// The line of byte offset `lo` of `src`.
fn line_of(src: &str, lo: u32) -> usize {
    src.get(..lo as usize)
        .map_or(0, |s| s.matches('\n').count() + 1)
}

/// The text of program `name` of `tests/data/generics/`.
fn program(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/data/generics")
        .join(name);
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// The codes and lines of the diagnostics of `src` with the `ir` pipeline
/// and all groups on. The program must be in scope.
fn codes(name: &str, src: &str) -> Vec<(String, usize)> {
    let a = analyze_source(src, all_groups(src))
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

/// Checks program `name` with all groups: its diagnostics are its markers.
fn check(name: &str) {
    let src = program(name);
    assert_eq!(codes(name, &src), markers(&src), "{name}");
}

/// The part `drops`: a value of a type parameter that a generic body drops
/// is W0601 at a call with a linear type argument (also a linear closure,
/// V056), and no error for a plain one.
#[test]
fn a_generic_body_that_drops_a_linear_type_argument_is_w0601_at_the_call() {
    check("drops.wf");
}

/// The part `holds` (OL-3a, OL-R2c-3): a value of a type parameter live at
/// a node that can abort or resume more than once is W0602 or W0503 at a
/// call with a linear type argument; a `Task<T>` handle counts too. A plain
/// type argument gives no error.
#[test]
fn a_generic_body_that_holds_a_linear_type_argument_is_w0602_at_the_call() {
    check("holds.wf");
}

/// RR9, V081: the checks of a generic item as a value.
#[test]
fn a_generic_item_as_a_value_gets_the_checks_of_a_call() {
    check("item_values.wf");
}

/// `RT3b`, V031, OL-NR-ptrfork, W0604: references, nonportable values and
/// `!Move` values through type parameters.
#[test]
fn values_of_type_parameters_keep_their_modes() {
    check("modes.wf");
}

/// Follow-up F8.1: place fields behind a `Box` go with a move of the `Box`.
#[test]
fn a_place_field_behind_a_box_goes_with_a_move_of_the_box() {
    check("boxed_place_fields.wf");
}

/// The generic bodies themselves have no error: a value of a type
/// parameter is linear only if a caller makes it so.
#[test]
fn a_generic_body_has_no_error_for_a_value_of_its_type_parameter() {
    let src = "fn forget<T>(x: T) { }\n\
               fn hold<T>(x: T) -> T / fail { fail(\"x\")\n x }\n\
               fn swap<T>(x: T, y: T) -> T { let z = x\n z = y\n z }\n";
    assert_eq!(codes("generic bodies", src), Vec::new());
}

/// O3-9: a task handle that a generic identity gives back is the handle of
/// its task: its `join` ends the task.
#[test]
fn a_task_handle_comes_back_from_a_generic_identity() {
    check("task_handles.wf");
}

/// Issue 47 (n03): a linear closure that a generic callee gives back in an
/// `Option`. The arm `None` consumes the local.
#[test]
fn a_linear_closure_in_an_option_from_a_generic_callee_is_consumed_by_the_none_arm() {
    check("option_payload.wf");
}

/// Follow-up F20.2 (F-1, FP-1 of the review of group F): an argument that a
/// generic callee holds moves at `Main`. A closure that reads it during the
/// call is W0301, a `once` closure that the callee holds is moved (W0502).
/// A variable of the type argument stands for the held value (W0602). A
/// part of a tuple argument that the callee does not hold is no error.
#[test]
fn an_argument_that_a_generic_callee_holds_moves_at_the_call() {
    check("held_args.wf");
}

/// Follow-up F20.2 (F-1, m01): a `once` closure that a generic callee holds
/// across a `multi` operation is W0503.
#[test]
fn a_once_closure_that_a_generic_callee_holds_across_a_multi_operation_is_w0503() {
    check("held_multi.wf");
}

/// Follow-up F20.2 (F-2 of the review of group F): a `join` of a result of
/// a type parameter ends a task only if one argument gives one handle. A
/// callee that gives the other handle away does not end its task.
#[test]
fn a_join_of_a_picked_handle_ends_only_a_task_that_one_argument_gives() {
    check("pick_handles.wf");
}
