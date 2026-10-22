//! The preview of group A with no call (plan stage F4).
//!
//! On each body of the corpus with no call, no `perform` and no `resume`,
//! the facts of the `ir` pipeline (`weft_sema::factgen::preview`) make the
//! production checker and the Datalog spec agree. The other bodies of a
//! program do not stop the preview: each body is checked alone.

use std::fs;
use std::path::Path;

use weft_check::{agreement, check_analysis};
use weft_sema::{analyze_source, factgen, irbuild, Options};

#[test]
fn the_checker_and_the_spec_agree_on_the_ir_facts_of_the_bodies_with_no_call() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs");
    let mut files: Vec<_> = fs::read_dir(&dir)
        .map(|d| {
            d.filter_map(Result::ok)
                .map(|e| e.path())
                .filter(|p| p.extension().is_some_and(|x| x == "wf"))
                .collect()
        })
        .unwrap_or_default();
    files.sort();
    let (mut agreed, mut programs) = (0usize, 0usize);
    let mut bad = Vec::new();
    for f in &files {
        let Ok(src) = fs::read_to_string(f) else {
            continue;
        };
        let Ok(a) = analyze_source(&src, Options::from_markers(&src)) else {
            continue;
        };
        let built = irbuild::build(&a);
        let mut bodies = Vec::new();
        for i in 0..built.entries.len() {
            if let (Ok(facts), Some(old)) = (factgen::preview(&a, &built, i), a.bodies.get(i)) {
                let mut b = old.clone();
                b.facts = facts;
                bodies.push(b);
            }
        }
        if bodies.is_empty() {
            continue;
        }
        programs += 1;
        let mut view = a.clone();
        view.bodies = bodies;
        view.diags = Vec::new();
        let checked = check_analysis(view, &[]);
        match agreement(&checked) {
            Ok(n) => agreed += n,
            Err(ds) => {
                for d in ds {
                    bad.push(format!(
                        "{}: `{}`: checker {:?}, spec {:?}, evidence {:?}",
                        f.display(),
                        d.function,
                        d.checker,
                        d.spec,
                        d.evidence
                    ));
                }
            }
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
    eprintln!("the checker and the spec agree on {agreed} bodies of {programs} programs");
    assert!(agreed > 100, "only {agreed} bodies");
}

/// Returns the code and the start of each diagnostic of `a` with only body
/// `body` (and no diagnostic of the analysis).
fn body_diags(a: &weft_sema::Analysis, body: weft_sema::BodyFacts) -> Vec<(String, u32)> {
    let mut view = a.clone();
    view.bodies = vec![body];
    view.diags = Vec::new();
    check_analysis(view, &[])
        .diags
        .iter()
        .map(|d| (format!("{:?}", d.code), d.span.lo))
        .collect()
}

#[test]
fn the_preview_gives_the_old_diagnostics_on_the_bodies_of_the_temporaries_program() {
    // `docs/ir.md` 5.10: `let r = &1; print(r)` (`temp_copy`) has no
    // diagnostic in the old pipeline. A borrow of plain data borrows a
    // promoted temporary, so the facts of the IR agree.
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs/32_temporaries.wf");
    let src = fs::read_to_string(path).unwrap_or_default();
    let a = analyze_source(&src, Options::from_markers(&src))
        .unwrap_or_else(|d| panic!("the program does not parse: {}", d.message));
    let built = irbuild::build(&a);
    let mut seen = Vec::new();
    for (i, e) in built.entries.iter().enumerate() {
        let (Ok(facts), Some(old)) = (factgen::preview(&a, &built, i), a.bodies.get(i)) else {
            continue;
        };
        let mut b = old.clone();
        b.facts = facts;
        let ir = body_diags(&a, b);
        assert_eq!(ir, body_diags(&a, old.clone()), "`{}`", e.name);
        seen.push(e.name.clone());
    }
    assert!(seen.iter().any(|n| n == "temp_copy"), "{seen:?}");
}
