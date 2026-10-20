//! The B6 hypotheses on the facts of sema (proofs/link/README.md).
//!
//! The link theorem `thm_w0301_no_ub` takes `bound_before_use` as a
//! hypothesis, and `thm_dataflow_exact` takes `no_gen_kill`. No proof shows
//! that sema gives them. This test runs the lint rules of
//! `proofs/link/lints/` on each function of the corpus with no expected error.
//! A lint there is a function that the theorems do not cover.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use std::fs;
use std::path::Path;

use weft_check::{bridge, check_source};
use weft_datalog::{evaluate, parse_program_named, EvalOptions};
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

#[test]
fn the_corpus_functions_meet_the_hypotheses_of_the_link() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut program = bridge::spec().clone();
    for name in ["unbound_use.dl", "gen_kill.dl"] {
        let path = root.join("proofs/link/lints").join(name);
        let src = fs::read_to_string(&path).expect("the lint file is readable");
        program.extend(parse_program_named(name, &src).expect("the lint file parses"));
    }
    let mut paths: Vec<_> = fs::read_dir(root.join("tests/programs"))
        .expect("tests/programs exists")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "wf"))
        .collect();
    paths.sort();
    let (mut checked_bodies, mut failures) = (0, Vec::new());
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
            if marked.iter().any(|l| (first..=last).contains(l)) {
                continue;
            }
            checked_bodies += 1;
            let out = evaluate(
                &program,
                bridge::database(&b.facts),
                EvalOptions { provenance: false },
            )
            .expect("the spec and the lints run");
            for t in out.tuples("lint") {
                let shown: Vec<String> = t.iter().map(|v| out.display_value(*v)).collect();
                failures.push(format!(
                    "{name}: `{}`: {}",
                    b.facts.name,
                    shown.join(" at ")
                ));
            }
        }
    }
    assert!(checked_bodies > 500, "only {checked_bodies} bodies");
    assert!(
        failures.is_empty(),
        "the B6 hypotheses fail:\n{}",
        failures.join("\n")
    );
}
