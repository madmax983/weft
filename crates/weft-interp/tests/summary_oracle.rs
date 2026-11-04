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

#[test]
fn a_value_that_a_body_runs_and_that_no_caller_gives_passes_the_summary_oracle() {
    // Follow-up F13.2: `rp` runs a closure that `mk_call` made and that holds
    // `push1`, and `rb` runs a local that a closure gives a new value. The
    // changes of `w.xs` reach the summaries of `rp` and `rb` (before the fix
    // the run nodes in `main` had no `mutates_at` or `lends_mut` for them).
    let src = "struct W { xs: Vec<u64> }\n\
        fn push1(w: &W) { w.xs.push(1) }\n\
        fn noop(w: &W) {}\n\
        fn mk_call(g: fn(&W), w: &W) -> fn() { || g(w) }\n\
        fn call0(f: fn()) { f() }\n\
        fn rp(w: &W) { let f = mk_call(push1, w)\n f() }\n\
        fn rp_callee(w: &W) { let f = mk_call(push1, w)\n call0(f) }\n\
        fn rb(w: &W) { let g = noop\n let set = || { g = push1 }\n set()\n g(w) }\n\
        fn main() {\n\
        let w = W { xs: Vec.new() }\n\
        rp(&w)\n\
        rp_callee(&w)\n\
        rb(&w)\n\
        print(w.xs.len())\n\
        }\n";
    let c = check_abc(src);
    assert!(c.ir.as_ref().is_some_and(|ir| ir.ok()), "{:?}", c.diags);
    let o = run_main_with_facts(&c, &opts(), |_| {}).unwrap_or_else(|e| panic!("{}", e.message));
    let r = o.fact_oracle.expect("a fact oracle report");
    assert!(r.summary > 0, "{r:?}");
}

/// Checks `src` with both pipelines and the groups A to D on.
fn check_abcd(src: &str) -> Checked {
    let opts = Options {
        facts: FactGen::Both,
        ir_groups: weft_sema::Groups::parse("ABCD").unwrap(),
        ..Options::default()
    };
    check_source("test.wf", src, opts)
}

/// Removes the `lends_mut` and `releases_at` facts of each `resume` node.
fn no_resume_summary(f: &mut FnFacts) {
    let resumes: Vec<weft_facts::NodeId> = f
        .nodes
        .iter()
        .enumerate()
        .filter(|(_, n)| n.kind == "resume" && n.label == "resume")
        .map(|(i, _)| weft_facts::NodeId(u32::try_from(i).unwrap()))
        .collect();
    f.lends_mut.retain(|(n, _)| !resumes.contains(n));
    f.releases_at.retain(|(n, _)| !resumes.contains(n));
}

/// A4 (plan stage F17, review of group D): the oracle runs `src` with the
/// groups A to D. The facts of the generator pass, and A4 checked a hit.
/// With no summary at the `resume` nodes, the run fails with A4.
fn broken_resume(src: &str) -> String {
    let c = check_abcd(src);
    assert!(c.ir.as_ref().is_some_and(|ir| ir.ok()), "{:?}", c.diags);
    let report = match run_main_with_facts(&c, &opts(), |_| {}) {
        Ok(o) => o.fact_oracle.expect("a fact oracle report"),
        Err(e) => panic!("{}", e.message),
    };
    assert!(report.resume > 0, "A4 checked nothing: {report:?}");
    match run_main_with_facts(&c, &opts(), no_resume_summary) {
        Ok(_) => panic!("the broken summary of the `resume` passes"),
        Err(e) => e.message,
    }
}

/// The clause holds a reference into an element across its `resume`, and
/// the rest of the handled body writes the element. The `resume` node
/// lends the place.
const RESUME_WRITE: &str = "effect Peek { fn peek() }\n\
    fn main() {\n\
    let v = Vec.new()\n\
    v.push(1)\n\
    handle Peek { fn peek() { let y = &v[0]; resume(()); print(y + 1) } } in {\n\
    peek()\n\
    v[0] = 5\n\
    }\n\
    }\n";

/// A `multi` re-run copies the frame of the inner clause that waits at its
/// `resume` (D-COPY-WAIT): the write after the inner `handle` runs while the
/// copy waits.
const RESUME_COPY: &str = "effect Pick { multi fn pick() -> bool }\n\
    effect Op { fn op() }\n\
    fn main() {\n\
    let v = Vec.new()\n\
    v.push(1)\n\
    handle Pick { fn pick() { resume(true); resume(false) } } in {\n\
    handle Op { fn op() { let y = &v[0]; resume(()); print(y + 1) } } in {\n\
    op()\n\
    let b = pick()\n\
    print(b)\n\
    }\n\
    v[0] = 3\n\
    }\n\
    }\n";

#[test]
fn a_missing_summary_of_a_resume_fails_the_resume_cover() {
    let m = broken_resume(RESUME_WRITE);
    assert!(m.starts_with("summary oracle (A4)"), "{m}");
}

#[test]
fn a_missing_summary_of_a_resume_fails_the_resume_cover_of_a_copied_frame() {
    let m = broken_resume(RESUME_COPY);
    assert!(m.starts_with("summary oracle (A4)"), "{m}");
}

/// A `multi` clause clears `v` between its two `resume`s while a copied
/// callee frame holds a reference into it (D-MULTI-MID of the second review
/// of group D). Each `resume` runs a copy of the frame of `g` again.
const MULTI_MID: &str = "effect Pick { multi fn pick() -> bool }\n\
    fn g(v: &Vec<i64>) / Pick {\n\
    let r = &v[0]\n\
    let b = pick()\n\
    print(r + 1)\n\
    }\n\
    fn main() {\n\
    let v = Vec.new()\n\
    v.push(1)\n\
    handle Pick { fn pick() { resume(true); v.clear(); resume(false) } } in {\n\
    g(&v)\n\
    }\n\
    }\n";

/// Removes the uses at each `Copy` node of a call.
fn no_copy_uses(f: &mut FnFacts) {
    let copies: Vec<weft_facts::NodeId> = f
        .nodes
        .iter()
        .enumerate()
        .filter(|(_, n)| n.kind == "call copy")
        .map(|(i, _)| weft_facts::NodeId(u32::try_from(i).unwrap()))
        .collect();
    f.uses.retain(|(_, n)| !copies.contains(n));
}

/// A4 of copies (plan stage F17.1): the run of a copy of a callee frame
/// whose reference the code before cleared needs a use at the `Copy` node
/// of the run node. The `ir` pipeline rejects the program there (W0301);
/// the run of its facts reaches the dangling read with no oracle failure.
/// With no use at the `Copy` node the oracle fails before the read.
#[test]
fn a_copy_of_a_callee_frame_needs_a_use_at_the_copy_node() {
    let c = check_abcd(MULTI_MID);
    assert!(
        c.ir.as_ref().is_some_and(|ir| ir
            .diags
            .iter()
            .any(|d| d.code == weft_syntax::diag::Code::W0301)),
        "{:?}",
        c.ir.as_ref().map(|ir| &ir.diags)
    );
    let m = match run_main_with_facts(&c, &opts(), |_| {}) {
        Ok(_) => panic!("the run of the copy passes"),
        Err(e) => e.message,
    };
    assert!(!m.contains("oracle (A4)"), "{m}");
    let m = match run_main_with_facts(&c, &opts(), no_copy_uses) {
        Ok(_) => panic!("the run of the copy passes"),
        Err(e) => e.message,
    };
    assert!(m.starts_with("summary oracle (A4)"), "{m}");
}

/// A function value runs in the handled body of a local handler of its
/// effect (D-FNVAL-ROW of the third review of group D). The value is a
/// function item: it runs with the handlers of the call, so the local
/// clause handles its `log` and clears `items` while `report` holds
/// `first`.
const FNVAL_ROW: &str = "effect Log { fn log(m: i64) }\n\
    fn report(items: &Vec<i64>) / Log {\n\
    let first = &items[0]\n\
    log(first + 0)\n\
    print(first + 1)\n\
    }\n\
    fn with_buffer(run: fn(&Vec<i64>) / Log, items: &Vec<i64>) / Log, mut(items) {\n\
    handle Log { fn log(m) { items.clear(); resume(()) } } in {\n\
    run(items)\n\
    }\n\
    }\n\
    fn main() {\n\
    let items = Vec.new()\n\
    items.push(5)\n\
    handle Log { fn log(m) { resume(()) } } in {\n\
    with_buffer(report, &items)\n\
    }\n\
    }\n";

/// Sends the effect `main.Log` past each `call` node that runs a clause
/// (`escapes_at` in place of `performs_at`): the facts of the hole
/// D-FNVAL-ROW before the fix.
fn no_clause_runs(f: &mut FnFacts) {
    let calls: Vec<weft_facts::NodeId> = f
        .performs_at
        .iter()
        .map(|&(n, _)| n)
        .filter(|n| f.nodes.get(n.index()).is_some_and(|x| x.kind == "call"))
        .collect();
    f.performs_at.retain(|(n, _)| !calls.contains(n));
    for n in calls {
        f.escapes_at.push((n, "main.Log".to_string()));
    }
}

/// A5 (plan stage F17.2): the run of a clause of a local handler from a
/// node whose facts send the effect past the function is a failure. The
/// facts of the generator run the clause at the run node of the function
/// value (W0312): the run reaches the dangling read with no failure of A5.
/// With the effect sent past the run node (the facts before the fix of
/// D-FNVAL-ROW), the oracle fails at the run node.
#[test]
fn a_clause_run_from_a_node_that_sends_the_effect_past_fails_the_clause_cover() {
    let c = check_abcd(FNVAL_ROW);
    assert!(
        c.ir.as_ref().is_some_and(|ir| ir
            .diags
            .iter()
            .any(|d| d.code == weft_syntax::diag::Code::W0312)),
        "{:?}",
        c.ir.as_ref().map(|ir| &ir.diags)
    );
    let m = match run_main_with_facts(&c, &opts(), |_| {}) {
        Ok(_) => panic!("the run of the clause passes"),
        Err(e) => e.message,
    };
    assert!(!m.contains("oracle (A5)"), "{m}");
    let m = match run_main_with_facts(&c, &opts(), no_clause_runs) {
        Ok(_) => panic!("the run of the clause passes"),
        Err(e) => e.message,
    };
    assert!(m.starts_with("clause oracle (A5)"), "{m}");
    assert!(m.contains("`with_buffer`"), "{m}");
}
