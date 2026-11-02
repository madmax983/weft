//! Tasks in the `ir` pipeline (plan stage F18; `docs/ir.md` 5.29, 6.4 to
//! 6.6).
//!
//! The scope body of a `scope` is spliced into the component of its site.
//! A spawn runs the task body as a closure run at its node: its changes and
//! reads become the footprint of the task (`task_writes`, `task_reads`). A
//! `join` ends a task only if the handle must hold it, and `ScopeWait` and
//! the cleanup chain of the scope body end each task of the scope.
//!
//! Group E stays off until stage F19. Each test checks a program of
//! `tests/data/tasks/` with `--facts=ir` and the groups A to E on. The
//! program must be in scope, and the `//~ CODE` markers are the diagnostics
//! of the `ir` pipeline.

use std::fs;
use std::path::Path;

use weft_check::check_analysis;
use weft_sema::{analyze_source, Options};

/// The options of the `ir` pipeline with the groups A to E on.
fn abcde(src: &str) -> Options {
    Options {
        facts: weft_sema::FactGen::Ir,
        ir_groups: weft_sema::Groups::parse("ABCDE").unwrap_or(weft_sema::Groups::NONE),
        ..Options::from_markers(src)
    }
}

/// The line of byte offset `lo` of `src`.
fn line_of(src: &str, lo: u32) -> usize {
    src.get(..lo as usize)
        .map_or(0, |s| s.matches('\n').count() + 1)
}

/// The text of program `name` of `tests/data/tasks/`.
fn program(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/data/tasks")
        .join(name);
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// The codes and lines of the diagnostics of `src` with the `ir` pipeline
/// and the groups A to E on. The program must be in scope.
fn abcde_codes(name: &str, src: &str) -> Vec<(String, usize)> {
    let a = analyze_source(src, abcde(src))
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

/// Checks program `name` with the groups A to E: its diagnostics are its
/// markers.
fn check(name: &str) {
    let src = program(name);
    assert_eq!(abcde_codes(name, &src), markers(&src), "{name}");
}

/// O3-4: a spawn statement gives a linear result to its `TaskResult` local;
/// nothing consumes it (W0601 at the spawn).
#[test]
fn a_spawn_statement_that_drops_a_linear_result_is_w0601() {
    check("o34_statement_spawn.wf");
}

/// F3-7: the value of the scope body is live across `ScopeWait`, which can
/// abort (W0602).
#[test]
fn the_value_of_a_scope_body_across_the_scope_wait_is_w0602() {
    check("f37_scope_value.wf");
}

/// O3-6: the parent moves, rebinds or ends an `Rc` handle that a task reads
/// through (W0405).
#[test]
fn a_task_that_reads_through_an_rc_handle_conflicts_with_its_move() {
    check("o36_rc_handle.wf");
}

/// V084: an abort of the scope body cancels and joins the tasks of the
/// scope on its cleanup chain.
#[test]
fn a_scope_abort_cancels_and_joins_its_tasks() {
    check("v084_scope_abort.wf");
}

/// V096: a `join` does not end a task that another handle can hold.
#[test]
fn a_join_ends_only_a_task_that_no_other_handle_can_hold() {
    check("v096_must_set.wf");
}

/// O3-9: a join through a callee, a tuple, an `Option` and a closure ends
/// the task.
#[test]
fn a_join_through_a_callee_a_tuple_an_option_or_a_closure_ends_the_task() {
    check("o39_joins.wf");
}

/// The `detach` control of F3-6 (N1): one W0601, no W0602.
#[test]
fn detach_drops_a_linear_result_with_one_w0601_and_no_w0602() {
    check("f36_detach.wf");
}
