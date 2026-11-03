//! Tasks in the `ir` pipeline (plan stage F18; `docs/ir.md` 5.29, 6.4 to
//! 6.6).
//!
//! The scope body of a `scope` is spliced into the component of its site.
//! A spawn runs the task body as a closure run at its node: its changes and
//! reads become the footprint of the task (`task_writes`, `task_reads`). A
//! `join` ends a task only if the handle must hold it, and `ScopeWait` and
//! the cleanup chain of the scope body end each task of the scope.
//!
//! Stage F19 adds `fork`, `sim.run`, `with_timeout`, a value that a callee
//! runs as a task (part `runs`), a spawn in a closure body or a clause on a
//! scope of the maker (part `tasks`), and W0314. Each test checks a program
//! of `tests/data/tasks/` with `--facts=ir` and the groups A to E on. The
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

/// IP6: a `fork` of units gives a tuple of units.
#[test]
fn a_fork_gives_a_tuple_also_of_units() {
    check("ip6_fork_units.wf");
}

/// The branches of a `fork` run at the same time (W0405) and on other
/// threads (W0403).
#[test]
fn the_branches_of_a_fork_run_at_the_same_time_on_other_threads() {
    check("fork_branches.wf");
}

/// OR7, V126, V127: a callee runs a function parameter as a task or a fork
/// branch; the caller applies the value as a task at the task nodes of the
/// call.
#[test]
fn a_value_that_a_callee_runs_as_a_task_is_a_task_of_the_call() {
    check("or7_params.wf");
}

/// V132 and O3-10: the callee writes while the task of its parameter runs;
/// a spawn is no resume point of this task.
#[test]
fn a_callee_that_writes_while_its_task_runs_conflicts_with_the_value() {
    check("caller_code.wf");
}

/// A spawn in a closure body or a clause on a scope of the maker (part
/// `tasks`), O3-12 and V055 accepted.
#[test]
fn a_spawn_in_a_closure_or_a_clause_starts_at_the_node_that_runs_it() {
    check("nested_spawns.wf");
}

/// `sim.run` and `with_timeout` run their blocks once (5.30, 5.31).
#[test]
fn sim_run_and_with_timeout_run_their_block_once() {
    check("sim_timeout.wf");
}

/// RT17: `sim.run` as a value in a library is W0802.
#[test]
fn sim_run_as_a_value_in_a_library_is_w0802() {
    check("rt17_sim_value.wf");
}

/// W0314 over the tasks of the body and the part `task_effects`.
#[test]
fn a_task_that_performs_through_a_handler_of_this_task_is_w0314() {
    check("w0314_tasks.wf");
}

/// E-1 (follow-up F19.3): a callee or a closure that can abort before its
/// `join` ends the task only on the normal path (part `abort_joins`). A
/// handler of the caller that stops the abort runs the code after it while
/// the task runs.
#[test]
fn a_join_that_an_abort_can_skip_does_not_end_the_task_on_the_abort_path() {
    check("e1_abort_before_join.wf");
}

/// E-2 (follow-up F19.3): a task that a closure starts, where a callee runs
/// the closure, does not conflict with the node that runs it.
#[test]
fn a_task_of_a_closure_that_a_callee_runs_starts_at_the_run() {
    check("e2_late_run_spawn.wf");
}

/// E-3 (follow-up F19.3): a closure that gives back the handle of its task
/// (part `ret.tasks`): a `join` of the result ends the task.
#[test]
fn a_join_of_a_handle_that_a_closure_gives_back_ends_the_task() {
    check("e3_returned_handle.wf");
}

/// The clean twins of the probes of E-1 (`tests/gate/probes/fixes/e1/e*_c.wf`
/// but `e07`, and `tests/data/tasks/e1_twins`): the callee or the closure
/// joins before it can abort, or a handler of the callee stops the abort.
/// The `ir` pipeline accepts each one (the old pipeline rejects each one:
/// W0405).
#[test]
fn a_callee_that_joins_before_it_can_abort_ends_the_task_on_each_path() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let dirs = [
        root.join("tests/data/tasks/e1_twins"),
        root.join("../../tests/gate/probes/fixes/e1"),
    ];
    let mut n = 0;
    for dir in dirs {
        for e in fs::read_dir(&dir).unwrap_or_else(|e| panic!("{}: {e}", dir.display())) {
            let path = e.map(|e| e.path()).unwrap_or_default();
            let file = path
                .file_name()
                .map(|f| f.to_string_lossy().to_string())
                .unwrap_or_default();
            if !file.starts_with('e') || !file.ends_with("_c.wf") || file.starts_with("e07") {
                continue;
            }
            let name = path.display().to_string();
            let src = fs::read_to_string(&path).unwrap_or_else(|e| panic!("{name}: {e}"));
            assert_eq!(abcde_codes(&name, &src), Vec::new(), "{name}");
            n += 1;
        }
    }
    assert!(n >= 12, "{n}");
}

/// R2-1 (follow-up F19.4): a clause of a local handler, or the destination
/// of an abort, runs at a call while a task that the call starts can run:
/// the task starts before the node of the call.
#[test]
fn a_task_of_a_call_conflicts_with_a_clause_that_the_call_runs() {
    check("r2_late_run_clause.wf");
}

/// R2-2 (follow-up F19.4): a clause with no `resume` ends the callee, so a
/// handle that the callee joins only on the normal path is lost there.
#[test]
fn a_clause_that_ends_the_callee_loses_its_task_handle() {
    check("r2_clause_loses_handle.wf");
}

/// R3-1 and R3-2 (follow-up F19.5, issue #50): a task of a callee runs
/// while the callee waits at an operation that a handler of a caller
/// handles (a perform, a `fail`, a timeout, a callee or a closure that
/// performs, a closure that a runner starts before it performs). The
/// clause of the caller runs at the same time as the task (part `waits`).
/// Each bad probe of `tests/gate/probes/fixes/f195/` is W0405; each clean
/// twin (the task ends before the operation, starts after it, or the clause
/// accesses another place) has no diagnostic.
#[test]
fn a_task_of_a_callee_conflicts_with_a_clause_of_a_caller() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/gate/probes/fixes/f195");
    let mut n = 0;
    for e in fs::read_dir(&dir).unwrap_or_else(|e| panic!("{}: {e}", dir.display())) {
        let path = e.map(|e| e.path()).unwrap_or_default();
        let file = path
            .file_name()
            .map(|f| f.to_string_lossy().to_string())
            .unwrap_or_default();
        let name = path.display().to_string();
        let src = fs::read_to_string(&path).unwrap_or_else(|e| panic!("{name}: {e}"));
        let got = abcde_codes(&name, &src);
        if file.ends_with("_b.wf") {
            assert!(
                !got.is_empty() && got.iter().all(|(c, _)| c == "W0405"),
                "{name}: {got:?}"
            );
        } else if file.ends_with("_c.wf") {
            assert_eq!(got, Vec::new(), "{name}");
        } else {
            continue;
        }
        n += 1;
    }
    assert!(n >= 20, "{n}");
}
