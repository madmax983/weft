//! The fact oracle and trace conformance (plan stage F9, `docs/ir.md` 8.5).
//!
//! With `RunOptions::fact_oracle`, the IR engine checks the hypotheses of the
//! proof link on the run: each step of a frame follows a `cfg_edge` of the
//! facts (trace conformance), and the facts of each node cover what the run
//! does there (C1, C2, C4, C5, D1, D4). The tests here check:
//!
//! - a fact set that a test breaks by hand (a `scope_end`, a `points_into`,
//!   an edge, a `uses`, a `moved_at`, a `mutates_at` or a `may_abort`
//!   removed) makes
//!   the run fail with the check of the broken fact;
//! - each program of the corpus that the `ir` pipeline checks and accepts,
//!   and that has a `main`, runs with no failure of the fact oracle;
//! - `--ir-trace` records the IR location of each step of each frame.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

use std::fs;
use std::path::{Path, PathBuf};

use weft_check::{check_source, Checked};
use weft_facts::FnFacts;
use weft_interp::{run_main, run_main_with_facts, run_tests, RunOptions};
use weft_sema::{FactGen, Options};

/// Checks `src` with both pipelines (the `ir` check is in `Checked::ir`).
fn check(src: &str) -> Checked {
    let opts = Options {
        facts: FactGen::Both,
        ..Options::default()
    };
    check_source("test.wf", src, opts)
}

/// Checks `src` with both pipelines and the groups A and B on (the loops
/// of stage F10a, a preview).
fn check_ab(src: &str) -> Checked {
    let opts = Options {
        facts: FactGen::Both,
        ir_groups: weft_sema::Groups::parse("AB").unwrap(),
        ..Options::default()
    };
    check_source("test.wf", src, opts)
}

/// The options of a run with the fact oracle and the memory oracle.
fn opts() -> RunOptions {
    RunOptions {
        fact_oracle: true,
        oracle: true,
        max_steps: Some(10_000_000),
        workers: 1,
        ..RunOptions::default()
    }
}

/// A program with a borrow of a field, a move, a write and an abort.
const SMALL: &str = "struct P { x: u64, v: Vec<u64> }\n\
    fn main() {\n\
    let p = P { x: 1, v: [] }\n\
    let r = &p.x\n\
    print(r)\n\
    print(r + 1)\n\
    let q = p\n\
    q.x = 2\n\
    print(q.x)\n\
    }\n";

/// The error message of a run of `src` whose facts `edit` changes.
fn broken(src: &str, edit: fn(&mut FnFacts)) -> String {
    let c = check(src);
    assert!(c.ir.as_ref().is_some_and(|ir| ir.ok()), "{:?}", c.diags);
    // The facts as the generator gives them pass.
    let ok = run_main_with_facts(&c, &opts(), |_| {});
    assert!(ok.is_ok(), "{:?}", ok.err().map(|e| e.message));
    match run_main_with_facts(&c, &opts(), edit) {
        Ok(_) => panic!("the broken facts pass"),
        Err(e) => e.message,
    }
}

#[test]
fn a_missing_scope_end_fails_the_free_cover() {
    let m = broken(SMALL, |f| f.scope_end.clear());
    assert!(m.starts_with("fact oracle (C4)"), "{m}");
}

#[test]
fn a_missing_points_into_fails_the_points_into_cover() {
    let m = broken(SMALL, |f| f.points_into.clear());
    assert!(m.starts_with("fact oracle (C1)"), "{m}");
}

#[test]
fn a_missing_edge_fails_trace_conformance() {
    let m = broken(SMALL, |f| {
        let print = f
            .nodes
            .iter()
            .position(|n| n.label == "print")
            .expect("a print node");
        f.cfg_edge.retain(|&(_, b)| b.index() != print);
    });
    assert!(m.starts_with("trace conformance"), "{m}");
}

#[test]
fn a_missing_use_fails_the_holder_cover() {
    let m = broken(SMALL, |f| f.uses.clear());
    assert!(m.starts_with("fact oracle (C2)"), "{m}");
}

#[test]
fn a_missing_moved_at_fails_the_move_cover() {
    let m = broken(SMALL, |f| f.moved_at.clear());
    assert!(m.starts_with("fact oracle (D1)"), "{m}");
}

#[test]
fn a_missing_mutates_at_fails_the_change_cover() {
    let m = broken(SMALL, |f| f.mutates_at.clear());
    assert!(m.starts_with("fact oracle (C5)"), "{m}");
}

/// A linear value is live in `main` when the callee aborts.
const ABORT: &str = "linear struct Tx { n: u64 }\n\
    on abort = rollback\n\
    fn rollback(t: Tx) { let Tx(n) = t }\n\
    fn stop(n: u64) / fail { if n > 0 { fail(\"stop\") } }\n\
    fn main() / fail {\n\
    let t = Tx { n: 1 }\n\
    stop(0)\n\
    rollback(t)\n\
    }\n";

#[test]
fn a_missing_may_abort_fails_the_suspension_cover() {
    let src = ABORT.replace("stop(0)", "stop(1)");
    let c = check(&src);
    let first = run_main_with_facts(&c, &opts(), |_| {});
    let m = match run_main_with_facts(&c, &opts(), |f| f.may_abort.clear()) {
        Ok(_) => panic!("the broken facts pass"),
        Err(e) => e.message,
    };
    assert!(
        m.starts_with("fact oracle (D4)"),
        "{m} (with the facts: {:?})",
        first.err().map(|e| e.message)
    );
}

/// The programs of the defects of the fact generator that the fact oracle
/// found (`tests/gate/probes/fixes/f9`): each one passes now.
#[test]
fn the_defects_that_the_fact_oracle_found_are_fixed() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/gate/probes/fixes/f9");
    let files = programs(&dir);
    assert!(files.len() >= 2);
    for p in files {
        let src = fs::read_to_string(&p).unwrap();
        let c = check(&src);
        assert!(c.ir.as_ref().is_some_and(|ir| ir.ok()), "{}", p.display());
        let r = run_main(&c, &opts());
        assert!(failure(&r).is_none(), "{}: {:?}", p.display(), failure(&r));
    }
}

/// A slice from a split points into a side of the split: the facts name
/// the side (`v[..k]`), the concrete place names the elements.
#[test]
fn a_slice_of_a_split_is_inside_its_side() {
    let src = "fn main() {\n let v = Vec.new()\n v.push(1)\n v.push(2)\n\
        let (l, r) = v.split_mut(1)\n print(l[0])\n print(r[0])\n}\n";
    let c = check(src);
    assert!(c.ir.as_ref().is_some_and(|ir| ir.ok()), "{:?}", c.diags);
    let r = run_main(&c, &opts());
    assert!(failure(&r).is_none(), "{:?}", failure(&r));
    assert!(r.unwrap().fact_oracle.unwrap().checks > 0);
}

fn programs(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "wf"))
        .collect();
    v.sort();
    v
}

/// The failure of the fact oracle in a run, if any.
fn failure(r: &Result<weft_interp::RunOutcome, weft_interp::RuntimeError>) -> Option<String> {
    let m = &r.as_ref().err()?.message;
    (m.starts_with("fact oracle") || m.starts_with("trace conformance")).then(|| m.clone())
}

#[test]
fn each_accepted_corpus_program_in_scope_passes_the_fact_oracle() {
    corpus_passes(check);
}

#[test]
fn each_accepted_corpus_program_in_scope_of_the_groups_a_and_b_passes_the_fact_oracle() {
    // The loops of the corpus (stage F10a): back edges, `IterNext`, and the
    // promoted temporaries of a loop body.
    corpus_passes(check_ab);
}

/// A reference that an earlier iteration of a loop took into a promoted
/// temporary points into the old cell of the temporary: the oracle names
/// the cell as the local, and checks it (stage F10a).
#[test]
fn a_reference_of_an_earlier_iteration_into_a_promoted_temporary_has_a_name() {
    let src = "fn main() {\n let v = Vec.new()\n let i = 0\n while i < 4 { v.push(i)\n i += 1 }\n\
        let rs = Vec.new()\n for x in v[] { rs.push(&(x + 1)) }\n print(rs.len())\n}\n";
    let c = check_ab(src);
    assert!(c.ir.as_ref().is_some_and(|ir| ir.ok()), "{:?}", c.diags);
    let r = run_main(&c, &opts());
    assert!(failure(&r).is_none(), "{:?}", failure(&r));
    let report = r.unwrap().fact_oracle.unwrap();
    assert!(report.checks > 0);
    assert_eq!(report.unnamed, 0, "{report:?}");
}

/// A walk down a list widens the reference to `head.next[]..`, and a borrow
/// of a field through it is a place below the wildcard place,
/// `(head.next[]..).next`. In the spec (`wild_at`) such a place is anywhere
/// inside the base `head.next[]`, so it covers each deeper place of the walk
/// at run time (stage F10a, tier 1 `R1_walk_then_write.wf`).
#[test]
fn a_place_below_a_wildcard_place_covers_each_place_inside_its_base() {
    let src = "struct Node { val: u64, next: Vec<Node> }\n\
        fn set_last(head: &Node, x: u64) / mut(head..) {\n\
        let cur = head\n while cur.next.len() > 0 { cur = &cur.next[0] }\n\
        cur.val = x\n print(cur.val)\n}\n\
        fn main() {\n let n = Node { val: 1, next: Vec.new() }\n\
        let m = Node { val: 2, next: Vec.new() }\n\
        m.next.push(Node { val: 3, next: Vec.new() })\n\
        n.next.push(m)\n set_last(&n, 7)\n}\n";
    let c = check_ab(src);
    assert!(c.ir.as_ref().is_some_and(|ir| ir.ok()), "{:?}", c.diags);
    let r = run_main(&c, &opts());
    assert!(failure(&r).is_none(), "{:?}", failure(&r));
}

/// The programs of the defects of stage F10a (`tests/gate/probes/fixes/f10`)
/// pass with the groups A and B on.
#[test]
fn the_defects_of_the_loops_are_fixed() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/gate/probes/fixes/f10");
    for p in programs(&dir) {
        let src = fs::read_to_string(&p).unwrap();
        let c = check_ab(&src);
        let Some(ir) = &c.ir else {
            panic!("{} is not in scope", p.display());
        };
        if !ir.ok() {
            continue;
        }
        let r = run_main(&c, &opts());
        assert!(failure(&r).is_none(), "{}: {:?}", p.display(), failure(&r));
    }
}

/// Each program of the corpus (and of the interpreter tests) that `check`
/// puts in scope and that the `ir` pipeline accepts runs with no failure of
/// the fact oracle.
fn corpus_passes(check: fn(&str) -> Checked) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files = programs(&root.join("../../tests/programs"));
    files.extend(programs(&root.join("tests/programs")));
    let mut ran = 0;
    let mut bad = Vec::new();
    for p in files {
        let src = fs::read_to_string(&p).unwrap();
        let c = check(&src);
        let Some(ir) = &c.ir else {
            continue;
        };
        if !ir.ok() {
            continue;
        }
        let name = p.file_name().unwrap().to_string_lossy().to_string();
        if src.contains("fn main") {
            let r = run_main(&c, &opts());
            bad.extend(failure(&r).map(|m| format!("{name}: {m}")));
            let report = match &r {
                Ok(o) => o.fact_oracle.clone(),
                Err(e) => e.outcome.fact_oracle.clone(),
            };
            let report = report.expect("a report of the fact oracle");
            assert!(report.skipped.is_none(), "{name}: {:?}", report.skipped);
            assert!(report.steps > 0, "{name}: no step");
            ran += 1;
        }
        for t in run_tests(&c, &opts()) {
            if let Some(m) = &t.message {
                if m.contains("fact oracle") || m.contains("trace conformance") {
                    bad.push(format!("{name} test `{}`: {m}", t.name));
                }
            }
            ran += 1;
        }
    }
    assert!(ran >= 3, "only {ran} runs");
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

#[test]
fn the_ir_trace_records_each_location_of_each_frame() {
    let c = check(SMALL);
    let o = run_main(
        &c,
        &RunOptions {
            ir_trace: true,
            engine: weft_interp::Engine::Ir,
            ..RunOptions::default()
        },
    )
    .unwrap();
    assert!(!o.ir_trace.is_empty());
    // One frame (`main`), and each step is a new location.
    let frames: std::collections::BTreeSet<u64> = o.ir_trace.iter().map(|s| s.frame).collect();
    assert_eq!(frames.len(), 1, "{:?}", o.ir_trace);
    for w in o.ir_trace.windows(2) {
        assert_ne!((w[0].block, w[0].stmt), (w[1].block, w[1].stmt));
    }
}
