//! The summary oracle (plan stage F13, `docs/ir.md` 8.5, A3).
//!
//! With `RunOptions::fact_oracle`, the IR engine also checks the summaries
//! that the facts apply at each run node: each place of a frame that a
//! callee (or a closure, or a callee of a callee) changes or reads while the
//! frame waits at the run node must be inside the facts of that node
//! (`mutates_at` or `lends_mut` for a change, `reads_at` for a read). The
//! tests here check:
//!
//! - a summary that a test breaks by hand (a `muts` place, and a `reads`
//!   place, removed at the run node of the caller) makes the run fail with
//!   the summary oracle, and the facts of the generator pass;
//! - stored function values (stage F13: behind a reference, in a `Vec`, in
//!   an `rc` object) that a callee runs pass;
//! - the oracle checks the runs (its count is not zero).

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

use weft_check::{check_source, Checked};
use weft_facts::FnFacts;
use weft_interp::{run_main_with_facts, RunOptions};
use weft_sema::{FactGen, Options};

/// Checks `src` with both pipelines and the groups A, B and C on.
fn check_abc(src: &str) -> Checked {
    let opts = Options {
        facts: FactGen::Both,
        ir_groups: weft_sema::Groups::parse("ABC").unwrap(),
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

/// A callee that changes and reads a place of the caller.
const GROW: &str = "struct W { xs: Vec<u64>, n: u64 }\n\
    fn grow(w: &W) / mut(w.xs) { w.xs.push(w.n) }\n\
    fn main() {\n\
    let w = W { xs: Vec.new(), n: 3 }\n\
    grow(&w)\n\
    print(w.xs.len())\n\
    }\n";

/// The summary oracle of a run of `src` whose facts `edit` changes: the
/// facts as the generator gives them pass, and the edited facts fail.
fn broken(src: &str, edit: fn(&mut FnFacts)) -> String {
    let c = check_abc(src);
    assert!(c.ir.as_ref().is_some_and(|ir| ir.ok()), "{:?}", c.diags);
    let ok = run_main_with_facts(&c, &opts(), |_| {});
    let report = match ok {
        Ok(o) => o.fact_oracle.expect("a fact oracle report"),
        Err(e) => panic!("{}", e.message),
    };
    assert!(report.summary > 0, "the summary oracle checked nothing");
    match run_main_with_facts(&c, &opts(), edit) {
        Ok(_) => panic!("the broken summary passes"),
        Err(e) => e.message,
    }
}

/// The nodes of the facts of `main` whose label is `callee` (its run nodes).
fn run_nodes(f: &FnFacts, callee: &str) -> Vec<weft_facts::NodeId> {
    if f.name != "main" {
        return Vec::new();
    }
    f.nodes
        .iter()
        .enumerate()
        .filter(|(_, n)| n.label == callee)
        .map(|(i, _)| weft_facts::NodeId(u32::try_from(i).unwrap()))
        .collect()
}

#[test]
fn a_missing_muts_place_of_an_applied_summary_fails_the_summary_oracle() {
    let m = broken(GROW, |f| {
        let ns = run_nodes(f, "grow");
        f.mutates_at.retain(|(n, _)| !ns.contains(n));
        f.lends_mut.retain(|(n, _)| !ns.contains(n));
    });
    assert!(m.starts_with("summary oracle (A3)"), "{m}");
    assert!(m.contains("write"), "{m}");
}

#[test]
fn a_missing_reads_place_of_an_applied_summary_fails_the_summary_oracle() {
    // The read of the argument temporary stays: C5 of `main` checks it.
    let m = broken(GROW, |f| {
        let ns = run_nodes(f, "grow");
        let drop: Vec<(weft_facts::NodeId, weft_facts::PlaceId)> = f
            .reads_at
            .iter()
            .filter(|&&(n, q)| ns.contains(&n) && f.place(q).display.starts_with('w'))
            .copied()
            .collect();
        f.reads_at.retain(|x| !drop.contains(x));
    });
    assert!(m.starts_with("summary oracle (A3)"), "{m}");
    assert!(m.contains("read"), "{m}");
}

#[test]
fn a_missing_muts_place_of_a_closure_summary_fails_the_summary_oracle() {
    // A closure changes a captured variable: the run node of the closure in
    // `main` applies its summary.
    let src = "fn main() {\n\
        let v: Vec<u64> = Vec.new()\n\
        let k = || v.push(1)\n\
        k()\n\
        print(v.len())\n\
        }\n";
    let m = broken(src, |f| {
        let ns = run_nodes(f, "k");
        f.mutates_at.retain(|(n, _)| !ns.contains(n));
        f.lends_mut.retain(|(n, _)| !ns.contains(n));
    });
    assert!(m.starts_with("summary oracle (A3)"), "{m}");
}

#[test]
fn stored_function_values_pass_the_summary_oracle() {
    // Stage F13: a closure behind a reference, in a `Vec` behind a
    // reference, and in an `rc` object, that a callee stores and a callee
    // runs.
    let src = "struct W { xs: Vec<u64> }\n\
        struct Cb { f: fn() }\n\
        struct Hook { f: fn() }\n\
        fn keep(f: fn(), cb: &Cb) / mut(cb.f) { cb.f = f }\n\
        fn reg(cb: &Cb, w: &W) / mut(cb.f, w.xs) { cb.f = || w.xs.push(2) }\n\
        fn run_cb(cb: &Cb) { let g = cb.f\n g() }\n\
        fn add(fs: &Vec<fn()>, w: &W) / mut(fs, w.xs) { fs.push(|| w.xs.push(3)) }\n\
        fn run_all(fs: &Vec<fn()>) { let i = 0\n while i < fs.len() { let f = fs[i]\n f()\n i += 1 } }\n\
        fn set_hook(h: Rc<Hook>) / mut(Hook) { h.f = || print(4) }\n\
        fn run_hook(h: Rc<Hook>) { let g = h.f\n g() }\n\
        fn main() {\n\
        let w = W { xs: Vec.new() }\n\
        let cb = Cb { f: || print(0) }\n\
        keep(|| w.xs.push(1), &cb)\n\
        run_cb(&cb)\n\
        reg(&cb, &w)\n\
        run_cb(&cb)\n\
        let fs: Vec<fn()> = Vec.new()\n\
        add(&fs, &w)\n\
        run_all(&fs)\n\
        let h = Rc.new(Hook { f: || print(5) })\n\
        set_hook(h.clone())\n\
        run_hook(h.clone())\n\
        print(w.xs.len())\n\
        }\n";
    let c = check_abc(src);
    assert!(c.ir.as_ref().is_some_and(|ir| ir.ok()), "{:?}", c.diags);
    let o = run_main_with_facts(&c, &opts(), |_| {}).unwrap_or_else(|e| panic!("{}", e.message));
    let r = o.fact_oracle.expect("a fact oracle report");
    assert!(r.skipped.is_none(), "{:?}", r.skipped);
    assert!(r.summary > 0, "{r:?}");
}

/// The facts of `main` with no `points_into` of the variable `var` into a
/// place whose text starts with `into`.
fn drop_points(f: &mut FnFacts, var: &str, into: &str) {
    if f.name != "main" {
        return;
    }
    let drop: Vec<(weft_facts::VarId, weft_facts::PlaceId)> = f
        .points_into
        .iter()
        .filter(|&&(v, q)| f.var(v).name == var && f.place(q).display.starts_with(into))
        .copied()
        .collect();
    assert!(!drop.is_empty(), "no points_into({var}, {into}..)");
    f.points_into.retain(|x| !drop.contains(x));
}

#[test]
fn a_missing_put_fns_place_of_a_closure_in_a_field_fails_the_summary_oracle() {
    // Part `put_fns`: `reg` puts a closure that points into `w` into `cb.f`
    // (review of stage F13, `so02`): the variable of `cb` must point into
    // `w`.
    let src = "struct Entity { hp: i32 }\n\
        struct World { entities: Vec<Entity> }\n\
        struct Cb { f: fn() }\n\
        fn noop() { print(0) }\n\
        fn reg(cb: &Cb, w: &World) / mut(cb.f, w.entities) { cb.f = || w.entities.clear() }\n\
        fn run_ref(cb: &Cb) { let g = cb.f\n g() }\n\
        fn main() {\n\
        let w = World { entities: Vec.new() }\n\
        w.entities.push(Entity { hp: 1 })\n\
        let cb = Cb { f: noop }\n\
        reg(&cb, &w)\n\
        run_ref(&cb)\n\
        print(w.entities.len())\n\
        }\n";
    let m = broken(src, |f| drop_points(f, "cb", "w"));
    assert!(m.starts_with("summary oracle (A3)"), "{m}");
    assert!(m.contains("puts a reference"), "{m}");
}

#[test]
fn a_missing_puts_place_of_an_rc_object_fails_the_summary_oracle() {
    // Part `puts`: `fill_self` puts a reference into `Cache.data[]` into
    // `Cache.refs` (review of stage F13, `so03`): the heap slot of the group
    // must point into it.
    let src = "struct Cache { refs: Vec<&u64>, data: Vec<u64> }\n\
        fn fill_self(c: Rc<Cache>) / mut(Cache) {\n\
        c.data.push(7)\n\
        c.refs.push(&c.data[0])\n\
        }\n\
        fn read0(c: Rc<Cache>) { let r = c.refs[0]\n print(r + 0) }\n\
        fn main() / mut(Cache) {\n\
        let c = Rc.new(Cache { refs: Vec.new(), data: Vec.new() })\n\
        fill_self(c.clone())\n\
        read0(c.clone())\n\
        }\n";
    let m = broken(src, |f| {
        drop_points(f, "value in `Cache.refs`", "Cache.data");
    });
    assert!(m.starts_with("summary oracle (A3)"), "{m}");
    assert!(m.contains("puts a reference"), "{m}");
}

#[test]
fn a_missing_put_fns_place_of_a_closure_in_a_vec_fails_the_summary_oracle() {
    // Part `put_fns`: `add_own` pushes a closure that points into `w` into
    // `fs` (review of stage F13, `so04`).
    let src = "struct Entity { hp: i32 }\n\
        struct World { entities: Vec<Entity> }\n\
        fn add_own(fs: &Vec<fn()>, w: &World) / mut(fs, w.entities) { fs.push(|| print(w.entities.len())) }\n\
        fn run_all(fs: &Vec<fn()>) { let i = 0\n while i < fs.len() { let f = fs[i]\n f()\n i += 1 } }\n\
        fn main() {\n\
        let w = World { entities: Vec.new() }\n\
        w.entities.push(Entity { hp: 1 })\n\
        let fs: Vec<fn()> = Vec.new()\n\
        add_own(&fs, &w)\n\
        run_all(&fs)\n\
        }\n";
    let m = broken(src, |f| drop_points(f, "fs", "w"));
    assert!(m.starts_with("summary oracle (A3)"), "{m}");
    assert!(m.contains("puts a reference"), "{m}");
}

#[test]
fn the_report_counts_what_the_summary_oracle_does_not_check() {
    // A callee writes its own locals: the frame below cannot name them.
    let c = check_abc(GROW);
    let o = run_main_with_facts(&c, &opts(), |_| {}).unwrap_or_else(|e| panic!("{}", e.message));
    let r = o.fact_oracle.expect("a fact oracle report");
    assert!(r.summary > 0, "{r:?}");
    assert!(r.summary_unnamed > 0, "{r:?}");
}

#[test]
fn a_closure_that_captures_a_local_by_reference_and_that_a_callee_stores_passes() {
    // The closure points into the cell root `w (cell)` in the facts; the run
    // gives the place of `w` (review rows `fc/c20`, `fc/c21` of stage F12,
    // which failed the first form of the check of `put_fns`). Without the
    // `points_into` of the cell, the check fails.
    let src = "struct W { xs: Vec<u64> }\n\
        fn put(out: &Vec<fn()>, f: fn()) / mut(out) { out.push(f) }\n\
        fn run_all(fs: &Vec<fn()>) { let i = 0\n while i < fs.len() { let f = fs[i]\n f()\n i += 1 } }\n\
        fn main() {\n\
        let w = W { xs: Vec.new() }\n\
        w.xs.push(1)\n\
        let fs: Vec<fn()> = Vec.new()\n\
        put(&fs, || print(w.xs.len()))\n\
        run_all(&fs)\n\
        }\n";
    let m = broken(src, |f| drop_points(f, "fs", "w"));
    assert!(m.starts_with("summary oracle (A3)"), "{m}");
    assert!(m.contains("puts a reference"), "{m}");
}
