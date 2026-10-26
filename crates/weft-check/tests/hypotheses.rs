//! The B6 hypotheses on the facts of sema (proofs/link/README.md).
//!
//! The link theorem `thm_w0301_no_ub` takes `bound_before_use` as a
//! hypothesis, and `thm_dataflow_exact` takes `no_gen_kill`. No proof shows
//! that sema gives them. This test runs the lint rules of
//! `proofs/link/lints/` on each function of the corpus with no expected error.
//! A lint there is a function that the theorems do not cover. The test also
//! shows that the lints can fire: on a function with an expected error, and on
//! a synthetic fact set.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use std::fs;
use std::path::Path;

use weft_check::{bridge, check_source};
use weft_datalog::{evaluate, parse_program_named, Database, EvalOptions, Program};
use weft_facts::FnFacts;
use weft_sema::{Analysis, BodyFacts, Options, ROOT_UNIT};
use weft_syntax::SourceFile;

/// The lines with an expected error: a `//~` marker with a code.
fn marked_lines(src: &str) -> Vec<usize> {
    src.lines()
        .enumerate()
        .filter(|(_, l)| {
            l.find("//~")
                .is_some_and(|p| l[p + 3..].split_whitespace().any(|w| w.starts_with('W')))
        })
        .map(|(i, _)| i + 1)
        .collect()
}

/// Returns the first and the last line of a body of the root unit.
fn body_lines(a: &Analysis, b: &BodyFacts, file: &SourceFile) -> Option<(usize, usize)> {
    let (lo, hi) = if let Some(f) = b.func {
        let d = &a.program.fns[f].decl;
        (d.name.span, d.body.as_ref()?.span)
    } else {
        let t = a.program.tests.iter().find(|t| t.name == b.facts.name)?;
        (t.span, t.body.span)
    };
    Some((file.line(lo), file.line_col(hi.hi).0))
}

/// Returns the spec with the lint rules of `proofs/link/lints/`.
fn spec_and_lints(root: &Path) -> Program {
    let mut program = bridge::spec().clone();
    for name in ["unbound_use.dl", "gen_kill.dl"] {
        let path = root.join("proofs/link/lints").join(name);
        let src = fs::read_to_string(&path).expect("the lint file is readable");
        program.extend(parse_program_named(name, &src).expect("the lint file parses"));
    }
    program
}

/// Returns each lint of `program` on facts `f`: the name of the lint and its node.
fn lints(program: &Program, f: &FnFacts) -> Vec<String> {
    let out = evaluate(
        program,
        bridge::database(f),
        EvalOptions { provenance: false },
    )
    .expect("the spec and the lints run");
    out.tuples("lint")
        .iter()
        .map(|t| {
            let shown: Vec<String> = t.iter().map(|v| out.display_value(*v)).collect();
            shown.join(" at ")
        })
        .collect()
}

#[test]
fn the_corpus_functions_meet_the_hypotheses_of_the_link() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let program = spec_and_lints(&root);
    let mut paths: Vec<_> = fs::read_dir(root.join("tests/programs"))
        .expect("tests/programs exists")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "wf"))
        .collect();
    paths.sort();
    let (mut checked_bodies, mut failures, mut marked_lints) = (0, Vec::new(), Vec::new());
    for path in paths {
        let src = fs::read_to_string(&path).expect("the program is readable");
        let name = path
            .file_name()
            .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
        let file = SourceFile::new(&name, src.as_str());
        let marked = marked_lines(&src);
        let c = check_source(&name, &src, Options::from_markers(&src));
        for b in c.analysis.bodies.iter().filter(|b| b.unit == ROOT_UNIT) {
            let Some((first, last)) = body_lines(&c.analysis, b, &file) else {
                continue;
            };
            let found = lints(&program, &b.facts);
            let shown = found
                .iter()
                .map(|l| format!("{name}: `{}`: {l}", b.facts.name));
            if marked.iter().any(|l| (first..=last).contains(l)) {
                marked_lints.extend(shown);
                continue;
            }
            checked_bodies += 1;
            failures.extend(shown);
        }
    }
    assert!(checked_bodies > 500, "only {checked_bodies} bodies");
    assert!(
        failures.is_empty(),
        "the B6 hypotheses fail:\n{}",
        failures.join("\n")
    );
    // The lints can fire: a function with an expected error fails one. If a
    // relation of the lints is renamed or empty, this fails.
    assert!(
        marked_lints
            .iter()
            .any(|l| l.starts_with("37_fn_values.wf: `stored_in_loop`: use_where_unbound at ")),
        "no lint in `stored_in_loop`: {marked_lints:?}"
    );
}

/// The lints of `program` on facts `f` with the variable of each one: the
/// name of the lint, the name of the variable and the node.
fn lints_with_vars(program: &Program, f: &FnFacts) -> Vec<(String, String, String)> {
    let mut p = program.clone();
    let more = "lint_var(\"gen_and_kill\", R, P) :- invalidated_at(R, P), rebound_at(R, P).\n\
                lint_var(\"use_where_unbound\", R, Q) :- unb(R, Q), uses(R, Q).\n";
    p.extend(parse_program_named("lint vars", more).expect("the rules parse"));
    let out = evaluate(&p, bridge::database(f), EvalOptions { provenance: false })
        .expect("the spec and the lints run");
    out.tuples("lint_var")
        .iter()
        .map(|t| {
            let shown: Vec<String> = t.iter().map(|v| out.display_value(*v)).collect();
            let var = shown
                .get(1)
                .and_then(|v| v.strip_prefix('v'))
                .and_then(|i| i.parse::<usize>().ok())
                .and_then(|i| f.vars.get(i))
                .map_or_else(
                    || shown.get(1).cloned().unwrap_or_default(),
                    |v| v.name.clone(),
                );
            (
                shown.first().cloned().unwrap_or_default(),
                var,
                shown.get(2).cloned().unwrap_or_default(),
            )
        })
        .collect()
}

/// True if a lint on variable `var` is one that the `ir` pipeline allows:
/// the versions of the value of a part (the names that start with
/// "value in", stage F8a) get
/// `rebound_at` at each node where they are not current, with no write
/// (`docs/ir.md` 6.3), so they can be unbound at a node that the old
/// lowering would not give them, and rebound where the part is
/// invalidated.
fn allowed_in_ir(var: &str) -> bool {
    var.starts_with("value in `")
}

#[test]
fn the_corpus_components_in_ir_mode_meet_the_hypotheses_of_the_link() {
    // Plan stage F8: the same lints on the facts of the `ir` pipeline, for
    // each body of a corpus program in scope with no expected error of the
    // `ir` pipeline.
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let program = spec_and_lints(&root);
    let mut paths: Vec<_> = fs::read_dir(root.join("tests/programs"))
        .expect("tests/programs exists")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "wf"))
        .collect();
    paths.sort();
    let (mut checked_bodies, mut allowed, mut failures) = (0, 0, Vec::new());
    for path in paths {
        let src = fs::read_to_string(&path).expect("the program is readable");
        let name = path
            .file_name()
            .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
        let file = SourceFile::new(&name, src.as_str());
        let marked = marked_lines(&src);
        let opts = Options {
            facts: weft_sema::FactGen::Ir,
            ..Options::from_markers(&src)
        };
        let c = check_source(&name, &src, opts);
        if !c
            .analysis
            .ir_scope
            .as_ref()
            .is_some_and(weft_sema::Scope::in_scope)
        {
            continue;
        }
        for b in c.analysis.bodies.iter().filter(|b| b.unit == ROOT_UNIT) {
            let Some((first, last)) = body_lines(&c.analysis, b, &file) else {
                continue;
            };
            if marked.iter().any(|l| (first..=last).contains(l)) {
                continue;
            }
            checked_bodies += 1;
            for (lint, var, node) in lints_with_vars(&program, &b.facts) {
                if allowed_in_ir(&var) {
                    allowed += 1;
                    continue;
                }
                failures.push(format!(
                    "{name}: `{}`: {lint} of `{var}` at {node}",
                    b.facts.name
                ));
            }
        }
    }
    eprintln!("{checked_bodies} bodies in ir mode; {allowed} lints of part versions");
    assert!(checked_bodies > 50, "only {checked_bodies} bodies");
    assert!(
        failures.is_empty(),
        "the B6 hypotheses fail in ir mode:\n{}",
        failures.join("\n")
    );
}

#[test]
fn the_gen_kill_lint_finds_a_node_that_invalidates_and_rebinds() {
    // A synthetic fact set: node `n3` invalidates and rebinds reference `r`,
    // and node `n2` only invalidates it.
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let src = fs::read_to_string(root.join("proofs/link/lints/gen_kill.dl"))
        .expect("the lint file is readable");
    let program = parse_program_named("gen_kill.dl", &src).expect("the lint file parses");
    let mut db = Database::new();
    let (r, n2, n3) = (db.sym("r"), db.sym("n2"), db.sym("n3"));
    db.insert("invalidated_at", [r, n2]);
    db.insert("invalidated_at", [r, n3]);
    db.insert("rebound_at", [r, n3]);
    let out = evaluate(&program, db, EvalOptions { provenance: false }).expect("the lint runs");
    let found: Vec<String> = out
        .tuples("lint")
        .iter()
        .map(|t| {
            let shown: Vec<String> = t.iter().map(|v| out.display_value(*v)).collect();
            shown.join(" at ")
        })
        .collect();
    assert_eq!(found, vec!["gen_and_kill at n3".to_string()]);
}
