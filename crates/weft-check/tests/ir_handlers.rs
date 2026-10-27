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

/// The reason why the `ir` pipeline does not check program `name` with the
/// groups A to D, if it does not.
fn fallback(name: &str) -> Option<String> {
    let src = program(name);
    let a = analyze_source(&src, abcd(&src))
        .unwrap_or_else(|d| panic!("{name} does not parse: {}", d.message));
    a.ir_scope.as_ref().and_then(|s| s.fallback.clone())
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

/// A handler of an effect with a `multi` operation is stage F16: the
/// program is not in scope.
#[test]
fn a_multi_handler_is_not_in_scope_until_stage_f16() {
    let why = fallback("m9_resume_twice_tail.wf");
    assert!(
        why.as_deref().is_some_and(|w| w.contains("multi")),
        "{why:?}"
    );
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
