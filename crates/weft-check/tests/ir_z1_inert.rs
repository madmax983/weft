//! The rules of plan stage R0z (Z1) change no program that is in scope
//! without them.
//!
//! Each program here is in scope without Z1 (the `ir` pipeline rejects it, or
//! the copies give it full facts), and a rule of Z1 notes an error in it. The
//! diagnostics and the scope must be the same with Z1 on and with Z1 off
//! (`weft_sema::analysis::clause::set_z1`). The switch is for the whole
//! process, so this file has one test.

use std::fs;
use std::path::Path;

use weft_check::check_analysis;
use weft_sema::{analyze_source, FactGen, Options};

/// The text of file `rel` of the repository.
fn read(rel: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(rel);
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// The diagnostics (code, unit, span, text) and the fallback of `src`, and
/// the number of the errors of Z1 that the analysis notes.
fn result(src: &str) -> (Vec<String>, Option<String>, usize) {
    let opts = Options {
        facts: FactGen::Ir,
        ..Options::from_markers(src)
    };
    let a = analyze_source(src, opts).unwrap_or_else(|d| panic!("parse: {}", d.message));
    let notes = a.ir_facts.as_ref().map_or(0, |f| f.z1.len());
    let c = check_analysis(a, &[]);
    let fallback = c
        .analysis
        .ir_scope
        .as_ref()
        .and_then(|s| s.fallback.clone());
    let diags = c
        .diags
        .iter()
        .map(|d| {
            format!(
                "{:?} {} {}..{} {}",
                d.code, d.unit, d.span.lo, d.span.hi, d.message
            )
        })
        .collect();
    (diags, fallback, notes)
}

#[test]
fn the_rules_of_z1_change_no_program_that_is_in_scope_without_them() {
    let files = [
        // Rule E notes W0502 at the call of `two`, with the code, span and
        // text of the true W0502 of the check (the review of Z1, round 2).
        "tests/gate/probes/fixes/r0z/rv2_n06_collide_e_bad.wf",
        // Rule A notes W0314 at the spawns of a task that resumes.
        "tests/programs/122_cont_escape.wf",
        "tests/gate/probes/verify/s5/R2c: effects, continuations, on abort and drops/p/or9_v2_multi_body_task.wf",
        "tests/gate/probes/r2/oracle/probes/i3c.wf",
        // Rule B notes W0314 at a task that runs the value of an operation.
        "tests/programs/84_task_stores.wf",
        "tests/gate/probes/fixes/r0j/j05_code_bad.wf",
    ];
    let mut noted = 0;
    for f in files {
        let src = read(f);
        let (on, on_fallback, notes) = result(&src);
        weft_sema::analysis::clause::set_z1(false);
        let (off, off_fallback, off_notes) = result(&src);
        weft_sema::analysis::clause::set_z1(true);
        assert!(
            on_fallback.is_none(),
            "{f}: in scope without Z1: {on_fallback:?}"
        );
        assert_eq!(on, off, "{f}: the diagnostics change with Z1");
        assert_eq!(on_fallback, off_fallback, "{f}");
        assert_eq!(off_notes, 0, "{f}: Z1 is off");
        noted += usize::from(notes > 0);
    }
    // The rules of Z1 fire on these programs: the notes exist, and they
    // change nothing.
    assert!(noted >= 4, "only {noted} programs have notes of Z1");
}
