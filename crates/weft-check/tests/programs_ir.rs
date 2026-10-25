//! The program corpus with the facts of the core IR (plan stage F8).
//!
//! The test checks each program of `tests/programs` with `--facts=ir` and the
//! default construct groups (`weft_sema::DEFAULT_GROUPS`). For each program
//! in scope (plan §2.6), the errors must be the `//~` markers of the `ir`
//! pipeline (`common::expected_for`), and the checker must agree with the
//! spec on each body. A marker that has an expectation for one pipeline only
//! (`//~ old: W0301 ir: W0302`) changes the class of the program in the gate,
//! so the gate ledger (`tests/gate/ledger.toml`) must name the program, unless
//! the old pipeline accepts it (then the program is `fixed`).

#![allow(clippy::unwrap_used, clippy::expect_used)]

mod common;

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use common::{actual, expected_for, has_pipeline_markers, write_disagreements, Pipeline};
use weft_check::check_source;
use weft_sema::{FactGen, Options};
use weft_syntax::SourceFile;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn corpus_paths() -> Vec<PathBuf> {
    let mut paths: Vec<_> = fs::read_dir(root().join("tests/programs"))
        .expect("tests/programs exists")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "wf"))
        .collect();
    paths.sort();
    paths
}

/// The result of one program with the default groups: `None` if it is out
/// of scope, else the problems (empty if the program passes).
fn run(path: &Path) -> Option<String> {
    run_with(path, None)
}

/// [`run`] with the construct groups `groups` (the default groups if
/// `None`).
fn run_with(path: &Path, groups: Option<weft_sema::Groups>) -> Option<String> {
    let src = fs::read_to_string(path).expect("the program is readable");
    let name = path
        .file_name()
        .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
    let mut opts = Options {
        facts: FactGen::Ir,
        ..Options::from_markers(&src)
    };
    if let Some(g) = groups {
        opts.ir_groups = g;
    }
    let checked = check_source(&name, &src, opts);
    if !checked
        .analysis
        .ir_scope
        .as_ref()
        .is_some_and(weft_sema::Scope::in_scope)
    {
        return None;
    }
    let file = SourceFile::new(&name, src.as_str());
    let found = actual(&checked, &file);
    let (want, _) = expected_for(&src, Pipeline::Ir);
    let mut msg = String::new();
    if found != want {
        let _ = writeln!(msg, "{name}: expected {want:?}\n  found {found:?}");
        for d in &checked.diags {
            msg.push_str(&d.render(&file));
        }
    }
    write_disagreements(&name, &checked, &mut msg);
    Some(msg)
}

#[test]
fn the_corpus_in_scope_gives_the_markers_of_the_ir_pipeline() {
    let (mut in_scope, mut failures) = (0, Vec::new());
    for path in corpus_paths() {
        if let Some(msg) = run(&path) {
            in_scope += 1;
            if !msg.is_empty() {
                failures.push(msg);
            }
        }
    }
    eprintln!("{in_scope} programs of the corpus are in scope");
    assert!(in_scope >= 19, "only {in_scope} programs are in scope");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn the_corpus_in_scope_of_the_groups_a_and_b_gives_the_markers_of_the_ir_pipeline() {
    // The preview of stage F10a: loops (group B) are not in the default set
    // yet. The loop programs of the corpus keep their markers.
    let ab = weft_sema::Groups::parse("AB").expect("the groups parse");
    let (mut in_scope, mut failures) = (0, Vec::new());
    for path in corpus_paths() {
        if let Some(msg) = run_with(&path, Some(ab)) {
            in_scope += 1;
            if !msg.is_empty() {
                failures.push(msg);
            }
        }
    }
    eprintln!("{in_scope} programs of the corpus are in scope of the groups A and B");
    assert!(in_scope >= 26, "only {in_scope} programs are in scope");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn a_marker_of_one_pipeline_needs_a_ledger_entry() {
    let ledger =
        fs::read_to_string(root().join("tests/gate/ledger.toml")).expect("the ledger is readable");
    let mut found = 0;
    let mut missing = Vec::new();
    for path in corpus_paths() {
        let src = fs::read_to_string(&path).expect("the program is readable");
        // A program that the old pipeline accepts and the ir pipeline
        // rejects is `fixed` (or `new-fp`, which the gate blocks in the
        // corpus): it needs no entry.
        if !has_pipeline_markers(&src) || expected_for(&src, Pipeline::Old).0.is_empty() {
            continue;
        }
        found += 1;
        let name = path
            .file_name()
            .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
        let rel = format!("\"tests/programs/{name}\"");
        if !ledger.contains(&rel) {
            missing.push(rel);
        }
    }
    assert!(found > 0, "no corpus program has a marker of one pipeline");
    assert!(
        missing.is_empty(),
        "these programs have a marker of one pipeline, but the ledger does not name them: {missing:?}"
    );
}

#[test]
fn a_pipeline_word_selects_the_codes_after_it() {
    let src = "fn f() {\n    g()   //~ W0301 old: W0302 ir: W0303 W0304\n}\n";
    let (old, _) = expected_for(src, Pipeline::Old);
    let (ir, _) = expected_for(src, Pipeline::Ir);
    let line = |c: &[&str]| -> Vec<(usize, String)> {
        let mut v: Vec<_> = c.iter().map(|c| (2, (*c).to_string())).collect();
        v.sort();
        v
    };
    assert_eq!(old, line(&["W0301", "W0302"]));
    assert_eq!(ir, line(&["W0301", "W0303", "W0304"]));
    assert!(has_pipeline_markers(src));
    assert!(!has_pipeline_markers("fn f() {} //~ W0301\n"));
}
