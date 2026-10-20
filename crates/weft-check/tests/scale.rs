//! The checker stays fast on large functions.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use std::fmt::Write as _;

use weft_check::{check_counted, check_source, Cause};
use weft_sema::Options;
use weft_syntax::SourceFile;

/// `n` times: a reference, a mutation that invalidates it, and a use. Each
/// `let` makes a new reference with the same name.
fn rebind(n: usize) -> String {
    let mut s = String::from("fn big(v: &Vec<u32>) / mut(v) {\n");
    s.push_str(&"    let r = &v[0]\n    v.push(1)\n    print(r)\n".repeat(n));
    s.push_str("}\n");
    s
}

#[test]
fn rebound_references_check_quickly() {
    let n = 1000;
    let src = rebind(n);
    let c = check_source("rebind.wf", &src, Options::default());
    let facts = &c.analysis.bodies[0].facts;
    let (r, work) = check_counted(facts);
    assert_eq!(r.violations.error.len(), n);
    assert_eq!(r.invalidations.len(), n);
    // The evidence of each error is the push just before the use.
    let file = SourceFile::new("rebind.wf", src.as_str());
    for inv in &r.invalidations {
        let at = file.line(facts.node(inv.at).span);
        let used = file.line(facts.node(inv.used_at).span);
        assert_eq!(at + 1, used, "{inv:?}");
    }
    // The first checker took more than 30 s: it searched from each
    // invalidating node. Now each reference has three searches in the part of
    // the graph that can reach its uses: the part, the propagation and the
    // evidence. A temporary reference has one. The parts are small, so the
    // sum of their sizes is about linear in the size of the function.
    assert!(work.searches <= 4 * n as u64 + 1, "{work:?}");
    assert!(work.part_nodes <= 3 * facts.nodes.len() as u64, "{work:?}");
    assert_eq!(work.overlaps, 0, "{work:?}");
}

/// A name, the number of uses `n`, the program and a test for the cause.
type CauseCase = (&'static str, usize, String, fn(&Cause) -> bool);

/// A program for each other cause of W0301, with `n` uses of an invalid
/// reference. The node just before each use invalidates it. In the `lend` and
/// `wildcard` programs, each `let` makes a new reference and each reference has
/// `n` invalidating nodes. In the `move` and `scope end` programs, one reference
/// has `n` invalidating nodes. The `move` program is smaller. It has a moved
/// variable and a temporary reference for each use, and the checker runs one
/// search for each of them.
fn causes() -> Vec<CauseCase> {
    causes_of([500, 500, 300, 1000])
}

/// The programs of [`causes`], with `n[i]` uses for cause `i`.
fn causes_of(n: [usize; 4]) -> Vec<CauseCase> {
    let program = |n: usize, head: &str, prelude: &str, body: &str| {
        format!("{head} {{\n{prelude}{}}}\n", body.repeat(n))
    };
    vec![
        (
            "lend",
            n[0],
            program(
                n[0],
                "fn big(f: fn(&Vec<u32>), v: &Vec<u32>)",
                "",
                "    let r = &v[0]\n    f(v)\n    print(r)\n",
            ),
            |c| matches!(c, Cause::Lend(_)),
        ),
        (
            "wildcard",
            n[1],
            program(
                n[1],
                "fn big(g: fn(&Vec<u32>) -> &u32, v: &Vec<u32>) / mut(v)",
                "",
                "    let r = g(v)\n    v.push(1)\n    print(r)\n",
            ),
            |c| matches!(c, Cause::Mutation(_)),
        ),
        (
            "move",
            n[2],
            format!(
                "fn take(v: Vec<u32>) {{}}\n{}",
                program(
                    n[2],
                    "fn big()",
                    "    let keep = Vec.new()\n    keep.push(1)\n    let r = &keep[0]\n",
                    "    let v = Vec.new()\n    v.push(1)\n    r = &v[0]\n    take(v)\n    print(r)\n",
                )
            ),
            |c| matches!(c, Cause::Move(_)),
        ),
        (
            "scope end",
            n[3],
            format!(
                "struct Entity {{ hp: i32 }}\n{}",
                program(
                    n[3],
                    "fn big()",
                    "    let keep = Entity { hp: 1 }\n    let r = &keep.hp\n",
                    "    { let inner = Entity { hp: 2 }; r = &inner.hp }\n    print(r)\n",
                )
            ),
            |c| matches!(c, Cause::ScopeEnd(_)),
        ),
    ]
}

/// The evidence search is the same for each cause: one search for each
/// reference. One search for each invalidating node would take much longer.
#[test]
fn each_cause_checks_quickly() {
    for (name, n, src, cause) in causes() {
        let c = check_source("causes.wf", &src, Options::default());
        let Some(body) = c.analysis.bodies.iter().find(|b| b.facts.name == "big") else {
            panic!("{name}: no body");
        };
        let facts = &body.facts;
        let (r, work) = check_counted(facts);
        assert_eq!(r.violations.error.len(), n, "{name}");
        assert_eq!(r.invalidations.len(), n, "{name}");
        let file = SourceFile::new("causes.wf", src.as_str());
        for inv in &r.invalidations {
            assert!(cause(&inv.cause), "{name}: {inv:?}");
            let at = file.line(facts.node(inv.at).span);
            let used = file.line(facts.node(inv.used_at).span);
            assert_eq!(at + 1, used, "{name}: {inv:?}");
        }
        // At most four searches for each reference and its evidence, not one
        // for each invalidating node, each in a small part of the graph.
        assert!(work.searches <= 4 * n as u64 + 50, "{name}: {work:?}");
        assert!(
            work.part_nodes <= 3 * facts.nodes.len() as u64,
            "{name}: {work:?}"
        );
        assert!(work.overlaps <= 2 * n as u64, "{name}: {work:?}");
    }
}

/// The checker takes less than 1 s for each cause of W0301 with 1000 uses
/// of an invalid reference, also in a debug build, and so do the mutations of
/// [`rebind`]. Each search is shared by the references that have the same
/// invalidating nodes, and the invalidating nodes of each place come from one
/// pass over the nodes.
#[test]
fn each_cause_checks_in_time() {
    let mut cases = causes_of([1000; 4]);
    cases.push(("mutation", 1000, rebind(1000), |c| {
        matches!(c, Cause::Mutation(_))
    }));
    for (name, n, src, cause) in cases {
        let c = check_source("causes.wf", &src, Options::default());
        let Some(body) = c.analysis.bodies.iter().find(|b| b.facts.name == "big") else {
            panic!("{name}: no body");
        };
        let start = std::time::Instant::now();
        let r = weft_check::check(&body.facts);
        let time = start.elapsed();
        assert_eq!(r.violations.error.len(), n, "{name}");
        assert!(r.invalidations.iter().all(|i| cause(&i.cause)), "{name}");
        assert!(time.as_millis() < 1000, "{name}: {time:?}");
    }
}

/// `n` blocks, each with a local, a reference into it and a use. Each local
/// and each reference has a search of its own.
fn blocks(n: usize) -> String {
    let mut s = String::from("struct E { hp: u64 }\nfn f() {\n");
    for i in 0..n {
        let _ = writeln!(
            s,
            "    {{ let x{i} = Vec.new()\n      x{i}.push(1)\n      let r = &x{i}[0]\n      print(r) }}"
        );
    }
    s.push_str("}\n");
    s
}

/// `n` struct types and a function with a local of each. Each local shows its
/// type, and the names come from the definitions with no copy (QR15).
fn many_types(n: usize) -> String {
    let mut s = String::new();
    for i in 0..n {
        let _ = writeln!(s, "struct S{i} {{ x: u64 }}");
    }
    s.push_str("fn f() {\n");
    for i in 0..n {
        let _ = writeln!(s, "    let a{i} = S{i} {{ x: 1 }}");
    }
    s.push_str("}\n");
    s
}

/// Sema and the checker take less than 1 s for 1000 blocks with a local and
/// a reference each, and for 1000 types with a local each, also in a debug
/// build. The first checker searched the whole function for each variable,
/// and sema copied the names of all types for each local.
#[test]
fn many_locals_check_in_time() {
    for (name, src) in [("blocks", blocks(1000)), ("types", many_types(1000))] {
        let start = std::time::Instant::now();
        let c = check_source("many.wf", &src, Options::default());
        let time = start.elapsed();
        assert!(c.ok(), "{name}: {:?}", c.diags);
        assert!(time.as_millis() < 1000, "{name}: {time:?}");
    }
}

/// A walk through a function value: `cur = step(cur)`, `calls` times in a
/// straight line, then in `loops` loops. The result of each call points into
/// the wildcard place of its argument. With `push`, a mutation of `head.next`
/// invalidates `cur` before its last use.
fn walk(calls: usize, loops: usize, push: bool) -> String {
    let mut s = String::from(
        "struct Node { val: u64, next: Vec<Node> }\n\
         fn walk(step: fn(&Node) -> &Node, head: &Node, n: u64) / mut(head.next) {\n\
         \x20   let cur = step(head)\n",
    );
    s.push_str(&"    cur = step(cur)\n".repeat(calls));
    for i in 0..loops {
        let _ = write!(
            s,
            "    let i{i} = 0\n    while i{i} < n {{ cur = step(cur)\n        i{i} += 1 }}\n"
        );
    }
    if push {
        s.push_str("    head.next.push(Node { val: 1, next: Vec.new() })\n");
    }
    s.push_str("    print(cur.val)\n}\n");
    s
}

/// A place below a wildcard place gets no deeper wildcard place, and the
/// checker compares the outermost wildcard bases only. The first checker took
/// time 2^depth: 32 calls took 47 s, and 4 loops did not finish.
#[test]
fn nested_wildcard_places_check_quickly() {
    for (calls, loops) in [(32, 0), (0, 4), (64, 8), (1000, 0)] {
        for push in [false, true] {
            let src = walk(calls, loops, push);
            let c = check_source("walk.wf", &src, Options::default());
            assert!(c.analysis.diags.is_empty(), "{:?}", c.analysis.diags);
            let body = c.analysis.bodies.iter().find(|b| b.facts.name == "walk");
            let Some(body) = body else { panic!("no body") };
            // Each call result is a one-place wildcard place of its own, but no
            // place is below two wildcard steps.
            let nested = body.facts.places.iter().any(|p| {
                p.steps
                    .iter()
                    .filter(|s| weft_facts::is_wild_step(s))
                    .count()
                    > 1
            });
            assert!(
                !nested,
                "{calls} calls, {loops} loops: nested wildcard places"
            );
            let (r, work) = check_counted(&body.facts);
            let facts = &body.facts;
            let cur = r
                .violations
                .error
                .iter()
                .filter(|(v, _)| facts.var(*v).name == "cur")
                .count();
            assert_eq!(cur, usize::from(push), "{src}");
            assert!(
                work.overlaps < 20_000,
                "{calls} calls, {loops} loops: {work:?}"
            );
        }
    }
}

/// The work of sema and of the checker for a program: the counts of sema, and
/// the sum of the counts of the checker over the bodies.
fn work_of(src: &str) -> (weft_sema::Work, usize, u64, u64) {
    let c = check_source("work.wf", src, Options::default());
    assert!(c.analysis.diags.is_empty(), "{:?}", c.analysis.diags);
    let (mut overlaps, mut searches) = (0, 0);
    for b in &c.analysis.bodies {
        let (_, w) = check_counted(&b.facts);
        overlaps += w.overlaps;
        searches += w.searches;
    }
    (c.analysis.work, c.analysis.lowerings, overlaps, searches)
}

/// `n` loops one after the other (QA7), and `n` updates of an untyped integer
/// (QA8).
fn seq_loops(n: usize) -> String {
    let mut s = String::from("fn f(n: u64) {\n    let s = 0\n");
    for i in 0..n {
        let _ = write!(
            s,
            "    let i{i}: u64 = 0\n    while i{i} < n {{ s += 1\n        i{i} += 1 }}\n"
        );
    }
    s.push_str("    print(s)\n}\n");
    s
}

/// A name, a program of size `n`, and a size.
type Shape = (&'static str, fn(usize) -> String, usize);

/// The work of sema and of the checker grows linearly with the shapes of the
/// round-2 reports: a walk through a function value in a line and in loops
/// (QA4), many loops (QA7) and many updates of an untyped integer (QA8). Each
/// count for `2n` is at most a little more than twice the count for `n`.
#[test]
fn sema_and_check_work_grow_linearly() {
    let shapes: [Shape; 4] = [
        ("walk in a line", |n| walk(n, 0, true), 200),
        ("walk in loops", |n| walk(0, n, true), 8),
        ("loops", seq_loops, 300),
        (
            "integer updates",
            |n| {
                format!(
                    "fn f() {{\n    let s = 0\n{}    print(s)\n}}\n",
                    "    s += 1\n".repeat(n)
                )
            },
            1000,
        ),
    ];
    let linear = |a: u64, b: u64| b <= 2 * a + a / 4 + 64;
    for (name, make, n) in shapes {
        let (wa, la, oa, sa) = work_of(&make(n));
        let (wb, lb, ob, sb) = work_of(&make(2 * n));
        let as_u64 = |x: usize| u64::try_from(x).unwrap_or(u64::MAX);
        let pairs = [
            ("lowerings", as_u64(la), as_u64(lb)),
            (
                "loop passes",
                as_u64(wa.loop_passes),
                as_u64(wb.loop_passes),
            ),
            (
                "loop copies",
                as_u64(wa.loop_copies),
                as_u64(wb.loop_copies),
            ),
            ("type steps", as_u64(wa.type_steps), as_u64(wb.type_steps)),
            (
                "holder steps",
                as_u64(wa.holder_steps),
                as_u64(wb.holder_steps),
            ),
            ("overlaps", oa, ob),
            ("searches", sa, sb),
        ];
        for (what, a, b) in pairs {
            assert!(
                linear(a, b),
                "{name}: {what} {a} for {n}, {b} for {}",
                2 * n
            );
        }
    }
}
