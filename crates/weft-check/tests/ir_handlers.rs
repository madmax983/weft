//! Handlers in the `ir` pipeline (plan stage F14; `docs/ir.md` 6.1 to 6.5,
//! 6.7 and 6.10).
//!
//! The handled body of a `handle` is spliced into the component of its site:
//! the nodes of the body run between the `Main` node and the `Exit` node of
//! the `handle`. A perform through the capability of a local handler applies
//! the code of the clause before its first `resume` (the `pre` part). The
//! `Post` node of the `handle` applies the code of each clause after its
//! `resume` (the `post` part). Each clause body is a component of the facts
//! of its function.
//!
//! Group D stays off until stage F17. Each test checks a program of
//! `tests/data/handlers/` with `--facts=ir` and the groups A, B, C and D on.
//! The program must be in scope, and the `//~ CODE` markers are the
//! diagnostics of the `ir` pipeline.

use std::fs;
use std::path::Path;

use weft_check::check_analysis;
use weft_sema::{analyze_source, Options};

/// The options of the `ir` pipeline with the groups A, B, C and D on.
fn abcd(src: &str) -> Options {
    Options {
        facts: weft_sema::FactGen::Ir,
        ir_groups: weft_sema::Groups::parse("ABCD").unwrap_or(weft_sema::Groups::NONE),
        ..Options::from_markers(src)
    }
}

/// The line of byte offset `lo` of `src`.
fn line_of(src: &str, lo: u32) -> usize {
    src.get(..lo as usize)
        .map_or(0, |s| s.matches('\n').count() + 1)
}

/// The text of program `name` of `tests/data/handlers/`.
fn program(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/data/handlers")
        .join(name);
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// The codes and lines of the diagnostics of `src` with the `ir` pipeline
/// and the groups A to D on. The program must be in scope.
fn abcd_codes(name: &str, src: &str) -> Vec<(String, usize)> {
    let a = analyze_source(src, abcd(src))
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

/// Checks program `name` with the groups A to D: its diagnostics are its
/// markers.
fn check(name: &str) {
    let src = program(name);
    assert_eq!(abcd_codes(name, &src), markers(&src), "{name}");
}

/// M1: the clause changes a place after `resume`, and the value of the
/// handled body points into it (`Post` applies the `post` part). The clause
/// reads the resume result after the change too.
#[test]
fn a_change_after_resume_invalidates_the_value_of_the_handled_body() {
    check("m1_post_resume.wf");
    check("postres.wf");
}

/// J1: the handled body keeps a reference in a local of the site, and the
/// clause changes its place after `resume`.
#[test]
fn a_change_after_resume_invalidates_a_reference_that_the_body_keeps() {
    check("j1_post_resume_keep.wf");
}

/// J3: the value of the `handle` is the value of a clause that resumed
/// (`Exit` binds the destination to the values of the clauses too).
#[test]
fn the_value_of_a_resuming_clause_is_the_value_of_the_handle() {
    check("j3_resuming_clause_value.wf");
}

/// O3-2: the value of a handled body points into a temporary of the body,
/// which ends at the end of the body.
#[test]
fn a_reference_into_a_temporary_of_the_handled_body_does_not_leave_it() {
    check("o32_handled_body_temporary.wf");
}

/// A correct program: the clause reads the value of the body after
/// `resume`, and the body reads its own local.
#[test]
fn a_clause_that_reads_the_result_of_resume_is_accepted() {
    check("m6_resume_result_body_local.wf");
}

/// F3 and V035: a perform through a local handler is checked as a call. The
/// parameters of the clause map onto the places of the arguments (`pre`).
#[test]
fn the_parameters_of_a_clause_map_onto_the_arguments_of_the_perform() {
    check("f3_perform_alias.wf");
    check("v1_two_params.wf");
    check("v2_in_loop.wf");
    check("v3_nested.wf");
    check("v4_named.wf");
    check("v6_option.wf");
    check("v7_clause_escape.wf");
    check("v10_tuple.wf");
}

/// V035 v8: a reference into the parameter of a clause across `resume`: the
/// rest of the handled body runs in the `resume` and changes the place.
#[test]
fn a_reference_of_a_clause_across_resume_sees_the_changes_of_the_body() {
    check("v8_across_resume.wf");
}

/// A handler of an effect with a `multi` operation (plan stage F16): the
/// clause resumes twice, and each run of the handled body binds its own
/// locals.
#[test]
fn a_multi_handler_whose_clause_resumes_twice_is_accepted() {
    check("m9_resume_twice_tail.wf");
}

/// O3-14: a `multi` resume runs the rest of the handled body again (the
/// re-entry edge from `Post` to the perform). A tail move of a local of the
/// site moves it once for each run; a local of the handled body is copied.
#[test]
fn a_multi_resume_moves_a_local_of_the_site_again() {
    check("multi_tail_site_move.wf");
    check("multi_tail_body_local.wf");
}

/// J4: the `Copy` node rebinds only the variables whose places are in the
/// copied frames. A reference into a place of the site keeps its state.
#[test]
fn a_multi_resume_keeps_a_reference_into_the_site_invalid() {
    check("multi_j4.wf");
    check("multi_j4_body_local.wf");
}

/// The clause code between two `resume`s runs at `Post`, before the
/// re-entry: a change there invalidates what the first run kept.
#[test]
fn the_clause_code_between_two_resumes_runs_before_the_second_run() {
    check("multi_site_ref_cleared.wf");
    check("multi_site_ref_kept.wf");
}

/// W0503: a linear value of the handled body live across a `multi` perform.
#[test]
fn a_linear_value_across_a_multi_perform_is_w0503() {
    check("multi_linear_across.wf");
    check("multi_linear_after.wf");
}

/// The second `resume` runs the rest of the handled body, which changes the
/// place that the result of the first `resume` points into.
#[test]
fn a_second_resume_invalidates_the_result_of_the_first() {
    check("multi_clause_holds_result.wf");
    check("multi_clause_reads_result.wf");
}

/// A clause that performs the operation of an outer local handler: the
/// code of the outer clause runs at the perform of the inner clause, and
/// both at the perform of the handled body.
#[test]
fn the_clause_of_an_outer_handler_runs_at_the_perform_of_an_inner_clause() {
    check("nested_clause.wf");
}

/// The rest of the handled body runs in `resume`: a change above the place
/// that the parameter of the clause points into (across an unstable step),
/// and the end of the `Rc` handle that the argument depends on, invalidate
/// the parameter.
#[test]
fn the_rest_of_the_handled_body_frees_what_a_parameter_of_the_clause_points_into() {
    check("change_above_param.wf");
    check("rc_param_freed.wf");
}

/// A clause that ends with no `resume`: the value of the `handle` binds at
/// the `AbortValue` node, the handled body unwinds, and the code after the
/// `handle` runs from its `Landing` node.
#[test]
fn an_abort_to_a_local_handler_lands_after_the_handle() {
    check("landing.wf");
}

/// The abort to a local handler does not reach a linear value outside the
/// handled body (`spared_at`): no W0602.
#[test]
fn an_abort_to_a_local_handler_spares_the_values_outside_the_handled_body() {
    check("spared.wf");
}

/// A node of the handled body can resume more than once: the `resume` of a
/// clause is a `multi` point (`body_multi`).
#[test]
fn a_multi_point_of_the_handled_body_makes_the_resume_of_a_clause_multi() {
    check("body_multi.wf");
}

/// A clause gives a linear local of the site a new value: `overwrites` at
/// the node that runs the clause.
#[test]
fn a_new_value_of_a_local_of_the_site_in_a_clause_overwrites_it() {
    check("clause_overwrites.wf");
}

/// The frame of a clause ends at `Post`: a reference into a local of the
/// clause in a local of the site is invalid after the `handle`.
#[test]
fn the_locals_of_a_clause_end_at_post() {
    check("clause_local_leaks.wf");
}

/// The W0204 store check sees the places of the arguments of a clause.
#[test]
fn a_clause_that_stores_its_parameter_into_an_rc_object_is_w0204() {
    check("clause_stores.wf");
}

/// A call in the handled body that performs through the local handler runs
/// the clause, and its effect does not leave the function.
#[test]
fn a_call_that_performs_through_a_local_handler_runs_the_clause() {
    check("call_runs_clause.wf");
}

/// A clause stores the reference of a parameter through another parameter
/// into a local of the site: the local holds the reference after the
/// `handle`.
#[test]
fn a_clause_that_stores_through_a_parameter_changes_a_local_of_the_site() {
    check("clause_stores_through_param.wf");
}

/// A clause that fails past its handler aborts at the node of the handled
/// body that runs it: a linear value of the site is live there.
#[test]
fn a_clause_that_fails_past_its_handler_aborts_where_it_runs() {
    check("clause_fails_past.wf");
}

/// R3RT7: an `in` place on a parameter of an operation works as on a
/// parameter of a function: no W0312 for an argument inside the place, and
/// W0203 for an argument outside it.
#[test]
fn an_in_place_on_a_parameter_of_an_operation_is_checked_as_for_a_function() {
    check("op_in_place.wf");
}

/// A clause or a handled body runs a closure that a closure of the site
/// made: the change through the captures of the maker is a change of the
/// place of the site (the clause runs in the frame of the site).
#[test]
fn a_made_closure_that_a_clause_runs_changes_the_place_of_the_site() {
    check("made_closure_in_clause.wf");
}

/// A clause that resumes on each path never aborts to its handler: a
/// perform of its operation, or a call that runs it, has no abort edge to
/// the handler and no path to the `Landing` of the `handle` (plan stage
/// F15; the D-NEWFP rows `scale400` and `scale_ops` of the F14 preview).
/// A clause that ends with no `resume` on one path keeps the edge.
#[test]
fn a_clause_that_resumes_on_each_path_does_not_abort_to_its_handler() {
    check("resumes_each_path.wf");
}

/// A call that runs a clause whose operation takes a reference (plan stage
/// F15; F3-2, M4): the parameters of the clause point into the frame of
/// the callee and into the places that the arguments of the call reach. The
/// frame of the callee ends at the end of the call, also on the abort path
/// to the handler.
#[test]
fn a_call_gives_a_clause_the_places_of_its_frame_and_of_its_arguments() {
    check("call_clause_refs.wf");
}

/// The lints of `proofs/link/lints/gen_kill.dl` on the facts of each body
/// of `src` with the groups A to D: each node that both invalidates and
/// rebinds a variable.
fn gen_kill(name: &str, src: &str) -> Vec<String> {
    use weft_datalog::{evaluate, parse_program_named, EvalOptions};
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let lint_src = fs::read_to_string(root.join("proofs/link/lints/gen_kill.dl"))
        .unwrap_or_else(|e| panic!("gen_kill.dl: {e}"));
    let mut program = weft_check::bridge::spec().clone();
    program
        .extend(parse_program_named("gen_kill.dl", &lint_src).unwrap_or_else(|e| panic!("{e:?}")));
    let a = analyze_source(src, abcd(src))
        .unwrap_or_else(|d| panic!("{name} does not parse: {}", d.message));
    assert!(
        a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope),
        "{name}: {:?}",
        a.ir_scope.as_ref().and_then(|s| s.fallback.clone())
    );
    let mut out = Vec::new();
    for b in &a.bodies {
        let db = weft_check::bridge::database(&b.facts);
        let ev = evaluate(&program, db, EvalOptions { provenance: false })
            .unwrap_or_else(|e| panic!("{name}: {e:?}"));
        for t in ev.tuples("lint") {
            let shown: Vec<String> = t.iter().map(|v| ev.display_value(*v)).collect();
            out.push(format!(
                "{name}: `{}`: {}",
                b.facts.name,
                shown.join(" at ")
            ));
        }
    }
    out
}

/// No node both binds and invalidates one variable (the hypothesis
/// `no_gen_kill` of the proof link, plan stage F15) on the facts of M3 (the
/// value of a clause with no `resume` binds at `AbortValue`, before the
/// frames unwind) and of F3-2 (a call gives a clause a local of its frame,
/// which ends at `FrameEnd`); the programs keep their W0301.
#[test]
fn the_abort_paths_of_local_handlers_bind_before_they_free() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut lints = Vec::new();
    for rel in [
        "tests/gate/probes/ir/work/machine/m8_abort_value_into_body.wf",
        "tests/gate/probes/ir/work/machine/m10_abort_value_callee_local.wf",
        "tests/gate/probes/r3/fidelity/repro/F3-2_clause_keeps_callee_ref.wf",
        "tests/gate/probes/r3/fidelity/repro/F3-2_clause_keeps_callee_ref_abort.wf",
        "tests/gate/probes/r3/fidelity/repro/F3-2_clause_stores_callee_ref.wf",
    ] {
        let src = fs::read_to_string(root.join(rel)).unwrap_or_else(|e| panic!("{rel}: {e}"));
        lints.extend(gen_kill(rel, &src));
        let codes = abcd_codes(rel, &src);
        assert!(codes.iter().any(|(c, _)| c == "W0301"), "{rel}: {codes:?}");
    }
    for name in ["landing.wf", "call_clause_refs.wf", "resumes_each_path.wf"] {
        lints.extend(gen_kill(name, &program(name)));
    }
    assert!(lints.is_empty(), "{lints:#?}");
}

/// A closure that performs through a captured capability (plan stage
/// F16): the node that runs it (a call of the value, or a call of a callee
/// that runs it) runs the clause of the handler, as a call that performs.
#[test]
fn a_run_of_a_closure_with_a_captured_capability_runs_the_clause() {
    check("cap_local_run.wf");
    check("cap_local_run_ok.wf");
    check("cap_apply.wf");
    check("cap_apply_ok.wf");
    check("cap_stored.wf");
    check("cap_stored_ok.wf");
}

/// The clause gets a reference into a local of the closure (the frame root
/// of the run node), and a `multi` clause makes the run node a `multi`
/// point.
#[test]
fn a_closure_with_a_captured_capability_gives_its_frame_and_resumes_twice() {
    check("cap_keeps_closure_local.wf");
    check("cap_keeps_closure_local_ok.wf");
    check("cap_multi_linear.wf");
    check("cap_multi_linear_ok.wf");
}

/// The clause gets the places that the closure reads (a capture by
/// reference gives a place of the variable), also when a callee runs the
/// closure. The lend of an argument of the perform is no change at the run
/// node: the facts of the clause there give its changes.
#[test]
fn a_clause_gets_the_places_that_a_closure_with_a_captured_capability_reads() {
    check("cap_byref_given.wf");
    check("cap_byref_given_ok.wf");
    check("cap_callee_runs.wf");
    check("cap_callee_runs_ok.wf");
}

/// A closure that a clause makes starts from the states of the clause
/// (plan stage F16): its run in the clause changes the places of the site,
/// before or after `resume`, and a linear capture must be consumed.
#[test]
fn a_closure_that_a_clause_makes_runs_with_the_states_of_the_clause() {
    check("clause_closure_clears_site.wf");
    check("clause_closure_pushes_site.wf");
    check("clause_closure_after_resume.wf");
    check("clause_closure_after_resume_ok.wf");
    check("clause_closure_linear.wf");
    check("clause_closure_linear_ok.wf");
}

/// O3-7: a function value that a perform gives to a local handler. The
/// parameter of the clause holds it, so a run of it in the clause (before or
/// after `resume`, once or twice) changes the places of its environment;
/// a change from the run has the root of the argument (no W0312 against
/// the argument itself), and a linear closure that the clause drops is
/// W0601.
#[test]
fn a_function_value_that_a_perform_gives_runs_in_the_clause() {
    check("o37_op_closure.wf");
    check("op_closure_pre.wf");
    check("op_closure_pre_ok.wf");
    check("op_closure_post.wf");
    check("op_closure_post_ok.wf");
    check("op_closure_twice.wf");
    check("op_closure_once.wf");
    check("op_closure_dropped.wf");
    check("op_closure_run.wf");
}

/// Class C-RR (self-attack of stage F16) with group D: a closure that reads
/// through a captured reference to a container of references runs in a
/// clause (a function value of a perform, a closure that the clause makes)
/// or in the handled body after a clause changes the referent. The node
/// that runs it uses the variables of the references on the chain (W0301).
#[test]
fn a_closure_run_in_a_clause_reads_through_a_captured_reference_to_references() {
    check("crr_op_closure.wf");
}

/// D-CONT-RUN (review of group D, plan stage F17): the node that runs a
/// clause is a call, or the run of a closure with a captured capability.
/// The callee or the closure goes on after the perform while the clause
/// waits at its `resume`, so the region of the continuation holds the run
/// node too. A change of the place there is W0301 at the read of the clause
/// after `resume`.
#[test]
fn the_rest_of_a_callee_after_a_perform_is_in_the_continuation() {
    check("cont_run_callee.wf");
    check("cont_run_closure.wf");
    check("cont_run_multi.wf");
    check("cont_run_param.wf");
}

/// D-CONT-NEST (review of group D, plan stage F17): a clause of an inner
/// handler performs the operation of the outer handler. The continuation of
/// the outer clause is the rest of the inner clause, of the inner handled
/// body and of the outer handled body: the node of the perform maps to the
/// nodes that run the inner clause.
#[test]
fn a_perform_in_an_inner_clause_has_the_rest_of_the_outer_body() {
    check("cont_nest.wf");
    check("cont_nest_param.wf");
    check("cont_nest_post.wf");
}

/// D-CONT-UNWIND (review of group D, plan stage F17): an abort to a handler
/// inside the handled body ends a local whose element the parameter of the
/// clause points into. The cleanup path is in the continuation.
#[test]
fn the_continuation_has_the_cleanup_path_of_an_abort_inside_the_body() {
    check("cont_unwind.wf");
}

/// D-COPY-WAIT (review of group D, plan stage F17): a `multi` re-run copies
/// the frame of an inner clause that waits at its `resume`. The code after
/// the inner `handle` runs before the copy goes on, so it is in the
/// continuation of the inner clause. The clean twin writes an element only.
#[test]
fn a_copy_of_a_waiting_clause_sees_the_rest_of_the_multi_body() {
    check("cont_copy_wait.wf");
    check("cont_copy_wait_ok.wf");
}

/// FP-OWN (review of group D, plan stage F17): the frame of a clause is
/// alive while the clause waits at its own `resume`. A reference into a
/// local of the clause across the `resume` stays valid.
#[test]
fn a_reference_into_a_local_of_the_clause_across_its_resume_is_valid() {
    check("cont_own.wf");
    check("cont_own_variant.wf");
}

/// W0313 over the values of the analysis (plan stage F17, `docs/ir.md`
/// 6.9): a closure that captures the capability of a handler leaves the
/// `handle` in its value, in a local of the site, in a heap slot or through
/// a callee that stores it. The diagnostic is at the `handle` expression,
/// as in the old pipeline (the functions of `tests/programs/62_cap_escape.wf`
/// that the `ir` pipeline checks).
#[test]
fn a_capability_that_leaves_its_handler_is_w0313() {
    check("w0313_cap.wf");
    check("w0313_rebind.wf");
    check("w0313_run_known.wf");
}

/// V046 (plan stage F17): a closure goes to an operation of its own
/// handler. The clause runs it outside the handler, so the handled body gave
/// it to code that can keep it.
#[test]
fn a_capability_that_a_clause_of_its_handler_runs_is_w0313() {
    check("w0313_own_clause.wf");
}

/// D-CLAUSE-RUNS (plan stage F17, found when group D went on): a clause
/// runs a function parameter of its function. The summary of the function
/// has the run (more than once: the clause runs at each perform), so the
/// caller applies the changes and the moves of the value that it gives.
#[test]
fn a_function_value_that_a_clause_runs_is_in_the_summary_of_the_function() {
    check("clause_runs.wf");
    check("clause_runs_once.wf");
}

/// D-MULTI-MID and D-COPY-WAIT-CALL (second review of group D, plan stage
/// F17.1): a `multi` `resume` runs a copy of the callee frame (or of the
/// frame of a closure) again. The copy holds the references that it made
/// into the places of its arguments, so a change of these places between
/// the run node and its `Copy` node (in the clause between two `resume`s,
/// or after the node in the caller) is W0301 at the node.
#[test]
fn a_copy_of_a_callee_frame_sees_the_changes_before_its_second_run() {
    check("multi_mid_callee.wf");
    check("multi_mid_closure.wf");
    check("copy_wait_call.wf");
    check("multi_mid_ok.wf");
}

/// D-FNVAL-ROW (plan stage F17.2): a function item or a function parameter
/// runs with the handlers of the call, so the clause of a local handler of
/// its row runs at the run node (W0312, W0301). A call in a closure body
/// gets the captured capability for the effects of its row: the clause runs
/// at the call. The clean cases have no error, also in `main` (no W0805:
/// FP-W0805-FNVAL).
#[test]
fn a_function_value_runs_the_clauses_of_a_local_handler_of_its_row() {
    check("fnval_row_item.wf");
    check("fnval_row_param.wf");
    check("fnval_row_multi.wf");
    check("fnval_row_closure.wf");
    check("fnval_row_ok.wf");
    check("fnval_row_inert_ok.wf");
}

/// D-ROW-MID (plan stage F17.2): a known callee (or a closure) that waits
/// at a `multi` operation of a handler of a caller gets a copy of its frame
/// at the `Copy` node. A change of the function after the call reaches the
/// copy: W0301 at the call. The clean twin only reads the place.
#[test]
fn a_copy_of_a_callee_frame_sees_the_changes_after_a_row_reentry() {
    check("row_mid_callee.wf");
    check("row_mid_closure.wf");
    check("row_mid_ok.wf");
}

/// Issue #56 (stage C1): a closure that runs a captured function value is a
/// `multi` point only where the value that the caller gives can resume more
/// than once. A known value that performs nothing does not make the run of
/// the closure a `multi` point, also when the program declares a `multi`
/// operation. A known value or a value of a caller that can resume more
/// than once still does (W0503).
#[test]
fn a_closure_that_runs_a_captured_value_has_the_multi_part_of_the_value() {
    check("nested_run_multi.wf");
    check("nested_run_multi_param.wf");
    check("nested_run_multi_ok.wf");
    check("nested_run_multi_once_ok.wf");
}

/// Issue #56 (stage C1): code of a caller that a callee runs can resume
/// more than once in a program with a `multi` operation, so the callee
/// gets a re-entry edge after the run. The run of the value itself is not
/// a second run: the caller gives the value and applies its `multi` part.
/// A `once` closure that the callee runs one time is no W0502. A known
/// value that resumes two times before a run of the `once` closure still
/// gives W0502.
#[test]
fn a_reentry_after_code_of_a_caller_does_not_run_the_values_again() {
    check("run_once_multi.wf");
    check("run_once_multi_ok.wf");
}

/// Issue #57 (stage C1): a call in a handled body that runs function values
/// runs the clauses of a handler whose capability a closure captures only
/// if a value that it runs can perform through that handler. A closure
/// that runs a known closure that performs nothing does not run the clause,
/// so nothing can abort there. A captured function item that performs the
/// effect still runs the clause (W0602).
#[test]
fn a_captured_capability_runs_its_clause_only_for_a_value_that_performs() {
    check("cap_nested_run.wf");
    check("cap_nested_run_ok.wf");
}

/// Issue #58 (stage C1): a call that runs function values runs the clause
/// of the local `Fail` handler only if a value that it runs can fail. A
/// closure that cannot fail does not run the clause: no W0302 for a local
/// that the clause reads, and no W0312 for a place that the clause changes.
/// A closure whose callee can fail still runs it (W0302).
#[test]
fn the_fail_clause_runs_only_for_a_value_that_can_fail() {
    check("run_fail_clause.wf");
    check("run_fail_clause_ok.wf");
}

/// Issue #56 (stage C1): a reference into an `rc` object of a type with no
/// function part reaches no function value. A closure that captures it runs
/// no code of a caller, so its run is no `multi` point. A closure that runs
/// a known function that resumes two times still is (W0503).
#[test]
fn a_reference_into_an_rc_object_with_no_function_part_reaches_no_function_value() {
    check("rc_ref_closure.wf");
    check("rc_ref_closure_ok.wf");
}

/// Stage C1 (self-attack): a store of a linear closure into a function field
/// of a local that held plain data gives the local the linear value
/// (`overwrites`), so an abort before its run is W0602.
#[test]
fn a_store_of_a_linear_closure_into_a_field_makes_the_local_linear() {
    check("part_store_linear.wf");
    check("part_store_linear_ok.wf");
}

/// Hole C1-H1 (stage C1.1): a callee that runs a value of the caller and
/// then a `once` closure runs the closure again if the value can resume
/// more than once (`Run::after`: the caller gives the values and knows if
/// one of them can). A known value, a function parameter of a helper, a
/// local and the other order of the parameters are W0502 (a generic callee:
/// `ir_generics`). A `once` closure that runs first, or a first value that resumes
/// nothing, is no error.
#[test]
fn a_run_after_a_value_that_resumes_two_times_runs_again() {
    check("run_after_multi.wf");
    check("run_after_multi_helper.wf");
    check("run_after_multi_let.wf");
    check("run_after_multi_order.wf");
    check("run_after_multi_ok.wf");
    check("run_after_multi_plain_ok.wf");
}

/// Holes C1-H2 and C1-H3 (follow-up C1.2): a callee that runs a value that
/// can resume more than once gives a `once` closure argument out again on
/// each resume (back, in a field, a struct, an `Option`, through a callee,
/// in a closure that it makes), so the caller can run it two times: the
/// closure is live across the call (W0503). A closure that a callee makes
/// and that runs such a value before the `once` closure runs it again
/// (W0502). A first value that resumes nothing, or a closure that is not
/// `once`, is no error.
#[test]
fn a_callee_gives_a_once_closure_out_again_after_a_multi_value() {
    check("give_out_ret.wf");
    check("give_out_field.wf");
    check("give_out_struct.wf");
    check("give_out_option.wf");
    check("give_out_box.wf");
    check("give_out_nested.wf");
    check("give_out_made_after.wf");
    check("made_run_after_multi.wf");
    check("give_out_ok.wf");
    check("give_out_plain_ok.wf");
}

/// Hole C1-H4 (follow-up C1.3): a closure that performs a `multi` operation
/// through a captured capability runs the code after the perform again on a
/// second resume. A `once` closure that it runs after the perform (a
/// capture, a parameter) runs again (W0502), where a callee runs the
/// closure and where the closure is called directly; a `once` closure that
/// it gives back after the perform is given out again (W0503). Plain data
/// after the perform, a `once` closure before it, and a moved capture of
/// plain data (a resume runs on a copy of the frames) are no error.
#[test]
fn a_closure_that_resumes_two_times_runs_its_once_values_again() {
    check("h4_apply.wf");
    check("h4_direct.wf");
    check("h4_param.wf");
    check("h4_cap.wf");
    check("h4_param_ret.wf");
    check("h4_capture_ret.wf");
    check("h4_plain_ok.wf");
    check("h4_before_ok.wf");
    check("h4_move_ok.wf");
}

/// The codes and lines of the diagnostics of program `name` of
/// `tests/data/handlers/c15/` with the `ir` pipeline and the default
/// groups, and the reason of a fallback to the old pipeline (stage C1.5).
fn c15_codes(name: &str) -> (Vec<(String, usize)>, Option<String>, String) {
    stage_codes("c15", name)
}

/// The codes and lines of the diagnostics of program `name` of
/// `tests/data/handlers/DIR/` with the `ir` pipeline and the default groups,
/// and the reason of a fallback to the old pipeline.
fn stage_codes(dir: &str, name: &str) -> (Vec<(String, usize)>, Option<String>, String) {
    let file = format!("{dir}/{name}");
    let src = program(&file);
    let opts = Options {
        facts: weft_sema::FactGen::Ir,
        ..Options::from_markers(&src)
    };
    let a = analyze_source(&src, opts)
        .unwrap_or_else(|d| panic!("{name} does not parse: {}", d.message));
    let fallback = a.ir_scope.as_ref().and_then(|s| s.fallback.clone());
    let mut got: Vec<(String, usize)> = check_analysis(a, &[])
        .diags
        .iter()
        .map(|d| (format!("{:?}", d.code), line_of(&src, d.span.lo)))
        .collect();
    got.sort();
    (got, fallback, src)
}

/// Checks program `name` of `tests/data/handlers/c15/` with the default
/// groups: it is in scope, and its diagnostics are its markers.
fn c15_check(name: &str) {
    let (got, fallback, src) = c15_codes(name);
    assert!(fallback.is_none(), "{name}: {fallback:?}");
    assert_eq!(got, markers(&src), "{name}");
}

/// Checks program `name` of `tests/data/handlers/c15/`: the `ir` pipeline
/// stops with a fallback whose reason holds `why`, and the old pipeline
/// gives the markers.
fn c15_fallback(name: &str, why: &str) {
    let (got, fallback, src) = c15_codes(name);
    assert!(
        fallback.as_deref().is_some_and(|f| f.contains(why)),
        "{name}: {fallback:?}"
    );
    assert_eq!(got, markers(&src), "{name}");
}

/// Gap G1 of stage C1.5: a loop around a `handle` or a `scope` runs the
/// nested body again, and a loop around a `handle` runs its clause again. A
/// `once` closure that the nested body or the clause runs is called twice
/// (W0502). With no loop, there is no error.
#[test]
fn a_loop_around_a_nested_body_runs_the_body_again() {
    for name in [
        "loop_handle.wf",
        "loop_scope.wf",
        "loop_clause.wf",
        "loop_handle_ok.wf",
        "loop_scope_ok.wf",
    ] {
        c15_check(name);
    }
}

/// Hole C1-H6 and gap G2 of stage C1.5: a resume of a value that the body
/// runs inside a handled body or a scope body runs the code after the
/// nested body again; a perform of a `multi` operation in a handled body
/// runs a nested body after it again. A `once` closure that runs there is
/// called twice. With a value that resumes one time, there is no error.
#[test]
fn a_resume_inside_a_nested_body_runs_the_code_after_it_again() {
    for name in [
        "h6_inner.wf",
        "h6_inner_perform.wf",
        "h6_two.wf",
        "h6_code.wf",
        "h6_code_scope.wf",
        "h6_abort.wf",
        "h6_oldmiss_min.wf",
        "h6_inner_ok.wf",
        "h6_inner_perform_ok.wf",
        "h6_two_ok.wf",
        "h6_code_ok.wf",
        "h6_code_scope_ok.wf",
        "h6_abort_ok.wf",
        "h6_oldmiss_min_ok.wf",
    ] {
        c15_check(name);
    }
}

/// Gap G3 of stage C1.5: a run of a result of a parameter comes after the
/// run of the parameter that gives it. A result that holds a `once`
/// closure (a capture of a closure of the caller, or of a closure that a
/// callee made) runs again when the first run resumes two times. With a
/// first run that resumes one time, there is no error.
#[test]
fn a_run_of_a_result_comes_after_the_run_that_gives_it() {
    for name in [
        "res_run.wf",
        "res_made.wf",
        "res_run2.wf",
        "ret_after.wf",
        "ret_after2.wf",
        "res_run_ok.wf",
        "res_made_ok.wf",
        "ret_after_ok.wf",
    ] {
        c15_check(name);
    }
}

/// Gap G4 of stage C1.5 (issue #68): a stated row is no bound for code of a
/// caller. A value with no row goes on into a parameter whose row has no
/// `multi` effect, and it resumes two times. With a value that resumes one
/// time, there is no error.
#[test]
fn a_stated_row_does_not_hide_a_multi_operation() {
    for name in [
        "g_row_fwd.wf",
        "g_row_ask.wf",
        "g_row_local.wf",
        "g_row_fwd_ok.wf",
        "g_row_local_ok.wf",
    ] {
        c15_check(name);
    }
}

/// The other counterexamples of the reviews of stage C1.5 (keys, recursion,
/// rows, generics, values in data, tasks), their clean twins that the `ir`
/// pipeline accepts, and three clean programs. (The twins that the `ir`
/// pipeline rejects for a reason older than stage C1.5 are not here.)
#[test]
fn the_review_programs_of_stage_c15_keep_their_errors() {
    for name in [
        "dedup_key2.wf",
        "dedup_key3.wf",
        "dedup_key4.wf",
        "dedup_key5.wf",
        "dedup_key6.wf",
        "rec1.wf",
        "rec2.wf",
        "rowcap_local.wf",
        "rowcap_pass.wf",
        "sim_mid.wf",
        "tmo_mid.wf",
        "put_after.wf",
        "gen_id.wf",
        "gen_box.wf",
        "ref_out.wf",
        "ref_vec.wf",
        "vec_run.wf",
        "opt_run.wf",
        "tup_run.wf",
        "struct_run.wf",
        "task_after.wf",
        "task_after2.wf",
        "task_after3.wf",
        "task_fork.wf",
        "task_join.wf",
        "dedup_key4_ok.wf",
        "gen_id_ok.wf",
        "gen_box_ok.wf",
        "ref_vec_ok.wf",
        "vec_run_ok.wf",
        "opt_run_ok.wf",
        "rowcap_local_ok.wf",
        "rowcap_pass_ok.wf",
        "sim_mid_ok.wf",
        "tmo_mid_ok.wf",
        "task_join_ok.wf",
        "gen_k2.wf",
        "nongen_k.wf",
        "task_after3_clean.wf",
    ] {
        c15_check(name);
    }
}

/// The fallback that makes a gap of the analysis of rows safe (stage C1.5,
/// `docs/ir.md` 5.20): a row in a clause body stops the `ir` pipeline, and
/// the old pipeline rejects each program. If the fallback goes away, this
/// test fails: the rows of the clause must be found first. From stage R0d a
/// handler in a closure body is in scope (`cap_nested.wf`, `h4_nested.wf`):
/// the closure summary has the rows of its handled bodies, and the run of
/// the closure is a `multi` point (W0502 and W0503 at the run, as for a
/// closure with no handler). From stage R0e a scope in a closure body is in
/// scope too (`h4_scope.wf`, the same markers). One more review program stops
/// at another fallback (a capability that leaves its handler); `gen_k.wf` is
/// in scope from stage R0f. In
/// `g_row_struct.wf` the callee `run_both` has a type error (W0105): from
/// plan stage R0b its callers get the worst case of its declaration, so the
/// program is in scope, and the type error rejects it.
#[test]
fn the_rows_of_clauses_stay_with_the_old_pipeline() {
    let clause = "a `multi` operation of a handler of a caller in a clause";
    c15_fallback("clause_m.wf", clause);
    c15_fallback("clause_after.wf", clause);
    c15_fallback("clause_after_m.wf", clause);
    c15_check("cap_nested.wf");
    c15_check("h4_nested.wf");
    c15_check("h4_scope.wf");
    c15_fallback("dedup_key.wf", "a capability that leaves its handler");
    // From plan stage R0f the value that code of a caller can run on
    // another thread is a task of the call: `gen_k.wf` is in scope. The
    // `ir` pipeline also gives W0405 there (the move of the `once` value at
    // the task node while the clause of the `multi` handler can run).
    let (got, fallback, src) = c15_codes("gen_k.wf");
    assert!(fallback.is_none(), "gen_k.wf: {fallback:?}");
    for m in markers(&src) {
        assert!(got.contains(&m), "gen_k.wf: {m:?} in {got:?}");
    }
    let (got, fallback, src) = c15_codes("g_row_struct.wf");
    assert!(fallback.is_none(), "g_row_struct.wf: {fallback:?}");
    for m in markers(&src) {
        assert!(got.contains(&m), "g_row_struct.wf: {m:?} in {got:?}");
    }
}

/// Checks program `name` of `tests/data/handlers/c16/` with the default
/// groups: it is in scope, and its diagnostics are its markers (stage C1.6).
fn c16_check(name: &str) {
    let (got, fallback, src) = stage_codes("c16", name);
    assert!(fallback.is_none(), "{name}: {fallback:?}");
    assert_eq!(got, markers(&src), "{name}");
}

/// Hole C1-HA of stage C1.6: a `once` closure goes from a call result into a
/// local through a destructure of a tuple or a struct, a projection of the
/// call, or a binding of a `match` arm (also in a nested tuple, an enum
/// payload, a `Box` and a `Vec`). The local is live across a value that
/// resumes two times: W0503. With a value that does not resume two times,
/// there is no error.
#[test]
fn a_once_closure_from_a_call_result_is_not_many() {
    for name in [
        "ha_tuple.wf",
        "ha_struct.wf",
        "ha_proj.wf",
        "ha_arm.wf",
        "ha_nested.wf",
        "ha_enum.wf",
        "ha_box.wf",
        "ha_vec.wf",
        "ha_tuple_ok.wf",
        "ha_struct_ok.wf",
        "ha_proj_ok.wf",
        "ha_arm_ok.wf",
        "ha_nested_ok.wf",
        "ha_enum_ok.wf",
        "ha_box_ok.wf",
        "ha_vec_ok.wf",
    ] {
        c16_check(name);
    }
}

/// Hole C1-HB of stage C1.6: a local gets a `once` closure by a store into a
/// field (`s.o = Some(g)`), or by a callee that puts it into a field, a
/// nested field, an enum payload or a `Vec` behind a reference argument. The
/// local is live across a value that resumes two times: W0503. With a value
/// that does not resume two times, there is no error.
#[test]
fn a_local_that_gets_a_once_closure_by_a_store_is_not_many() {
    for name in [
        "hb_store.wf",
        "hb_put.wf",
        "hb_hold.wf",
        "hb_put_nested.wf",
        "hb_put_enum.wf",
        "hb_put_vec.wf",
        "hb_store_ok.wf",
        "hb_put_ok.wf",
        "hb_hold_ok.wf",
        "hb_put_nested_ok.wf",
        "hb_put_enum_ok.wf",
        "hb_put_vec_ok.wf",
    ] {
        c16_check(name);
    }
}

/// Hole C1-HC of stage C1.6: a callee (a function item or a closure) runs a
/// value that resumes two times, and then gives a `once` argument back in a
/// struct, as its result, or in a field of a reference argument. The run is
/// at the node `Ret` of the call, so the node of the given value gets the
/// `multi` of `Ret` too: W0503. With a value that does not resume two times,
/// there is no error.
#[test]
fn a_callee_gives_a_once_argument_out_again_after_a_late_run() {
    for name in [
        "hc_struct_out.wf",
        "hc_put_field.wf",
        "hc_ret_tmp.wf",
        "hc_value.wf",
        "hc_struct_out_ok.wf",
        "hc_put_field_ok.wf",
        "hc_ret_tmp_ok.wf",
        "hc_value_ok.wf",
    ] {
        c16_check(name);
    }
}
