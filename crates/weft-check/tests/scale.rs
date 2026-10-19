//! The checker stays fast on large functions.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use std::fmt::Write as _;
use std::time::{Duration, Instant};

use weft_check::{check, check_counted, check_source, Cause};
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
    let start = Instant::now();
    let r = check(facts);
    let time = start.elapsed();
    assert_eq!(r.violations.error.len(), n);
    assert_eq!(r.invalidations.len(), n);
    // The evidence of each error is the push just before the use.
    let file = SourceFile::new("rebind.wf", src.as_str());
    for inv in &r.invalidations {
        let at = file.line(facts.node(inv.at).span);
        let used = file.line(facts.node(inv.used_at).span);
        assert_eq!(at + 1, used, "{inv:?}");
    }
    // About 0.35 s in a debug build. The first checker took more than 30 s.
    assert!(time < Duration::from_secs(1), "{time:?}");
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
    let program = |n: usize, head: &str, prelude: &str, body: &str| {
        format!("{head} {{\n{prelude}{}}}\n", body.repeat(n))
    };
    vec![
        (
            "lend",
            500,
            program(
                500,
                "fn big(f: fn(&Vec<u32>), v: &Vec<u32>)",
                "",
                "    let r = &v[0]\n    f(v)\n    print(r)\n",
            ),
            |c| matches!(c, Cause::Lend(_)),
        ),
        (
            "wildcard",
            500,
            program(
                500,
                "fn big(g: fn(&Vec<u32>) -> &u32, v: &Vec<u32>) / mut(v)",
                "",
                "    let r = g(v)\n    v.push(1)\n    print(r)\n",
            ),
            |c| matches!(c, Cause::Mutation(_)),
        ),
        (
            "move",
            300,
            format!(
                "fn take(v: Vec<u32>) {{}}\n{}",
                program(
                    300,
                    "fn big()",
                    "    let keep = Vec.new()\n    keep.push(1)\n    let r = &keep[0]\n",
                    "    let v = Vec.new()\n    v.push(1)\n    r = &v[0]\n    take(v)\n    print(r)\n",
                )
            ),
            |c| matches!(c, Cause::Move(_)),
        ),
        (
            "scope end",
            1000,
            format!(
                "struct Entity {{ hp: i32 }}\n{}",
                program(
                    1000,
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
        let start = Instant::now();
        let r = check(facts);
        let time = start.elapsed();
        assert_eq!(r.violations.error.len(), n, "{name}");
        assert_eq!(r.invalidations.len(), n, "{name}");
        let file = SourceFile::new("causes.wf", src.as_str());
        for inv in &r.invalidations {
            assert!(cause(&inv.cause), "{name}: {inv:?}");
            let at = file.line(facts.node(inv.at).span);
            let used = file.line(facts.node(inv.used_at).span);
            assert_eq!(at + 1, used, "{name}: {inv:?}");
        }
        // Each one takes less than 0.3 s in a debug build.
        assert!(time < Duration::from_secs(1), "{name}: {time:?}");
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
    for (calls, loops) in [(32, 0), (0, 4), (64, 8)] {
        for push in [false, true] {
            let src = walk(calls, loops, push);
            let c = check_source("walk.wf", &src, Options::default());
            assert!(c.analysis.diags.is_empty(), "{:?}", c.analysis.diags);
            let body = c.analysis.bodies.iter().find(|b| b.facts.name == "walk");
            let Some(body) = body else { panic!("no body") };
            let wild = body.facts.places.iter().filter(|p| p.is_wildcard()).count();
            assert!(
                wild <= 2,
                "{calls} calls, {loops} loops: {wild} wildcard places"
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
