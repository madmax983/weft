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

/// A name, the number of uses `n`, the program, a test for the cause, and
/// true if the node just before each use invalidates it.
type CauseCase = (&'static str, usize, String, fn(&Cause) -> bool, bool);

/// A program for each other cause of W0301, with `n` uses of an invalid
/// reference. In the `lend` and `wildcard` programs, each `let` makes a new
/// reference and each reference has `n` invalidating nodes. In the `move`,
/// `scope end` and `unwound` programs, one reference has `n` invalidating
/// nodes. The `move` program is smaller. It has a moved variable and a
/// temporary reference for each use, and the checker runs one search for each
/// of them. In the `unwound` program, the abort path of each handled body
/// leaves the scope of a local (`unwound_at`), and so does the normal path.
/// The end of the scope on the normal path comes first, so it is the evidence.
/// In the `move part` and `release` programs, each reference has one
/// invalidating node.
fn causes() -> Vec<CauseCase> {
    causes_of([500, 500, 300, 1000, 300, 300, 300])
}

/// The programs of [`causes`], with `n[i]` uses for cause `i`.
fn causes_of(n: [usize; 7]) -> Vec<CauseCase> {
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
            true,
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
            true,
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
            true,
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
            true,
        ),
        (
            "move part",
            n[4],
            format!(
                "struct In {{ x: Vec<u64> }}\nstruct Out {{ a: In, b: In }}\nfn take(i: In) {{}}\n{}",
                program(
                    n[4],
                    "fn big()",
                    "",
                    "    let s = Out { a: In { x: Vec.new() }, b: In { x: Vec.new() } }\n    let r = &s.a.x\n    take(s.a)\n    print(r.len())\n",
                )
            ),
            |c| matches!(c, Cause::MovePart(_)),
            true,
        ),
        (
            "unwound",
            n[5],
            format!(
                "struct Entity {{ hp: i32 }}\n{}",
                program(
                    n[5],
                    "fn big()",
                    "    let keep = Entity { hp: 1 }\n    let r = &keep.hp\n",
                    "    handle Fail { fn fail(m) { () } } in {\n        let inner = Entity { hp: 2 }\n        r = &inner.hp\n        fail(\"x\")\n    }\n    print(r)\n",
                )
            ),
            |c| matches!(c, Cause::ScopeEnd(_)),
            false,
        ),
        (
            "release",
            n[6],
            format!(
                "struct Entity {{ hp: i32 }}\nstruct World {{ entities: Vec<Entity> }}\neffect Peek {{ fn peek(e: &Entity) }}\n{}",
                program(
                    n[6],
                    "fn big(world: &World) / mut(world.entities)",
                    "",
                    "    handle Peek {\n        fn peek(e) {\n            resume(())\n            print(e.hp)\n        }\n    } in {\n        peek(&world.entities[0])\n        world.entities.clear()\n    }\n",
                )
            ),
            |c| matches!(c, Cause::Release(_)),
            true,
        ),
    ]
}

/// The evidence search is the same for each cause: one search for each
/// reference. One search for each invalidating node would take much longer.
#[test]
fn each_cause_checks_quickly() {
    for (name, n, src, cause, next) in causes() {
        let c = check_source("causes.wf", &src, Options::default());
        let Some(body) = c.analysis.bodies.iter().find(|b| b.facts.name == "big") else {
            panic!("{name}: no body");
        };
        let facts = &body.facts;
        if name == "unwound" {
            assert!(facts.unwound_at.len() >= n, "{name}");
        }
        let (r, work) = check_counted(facts);
        assert_eq!(r.violations.error.len(), n, "{name}");
        assert_eq!(r.invalidations.len(), n, "{name}");
        let file = SourceFile::new("causes.wf", src.as_str());
        for inv in &r.invalidations {
            assert!(cause(&inv.cause), "{name}: {inv:?}");
            let at = file.line(facts.node(inv.at).span);
            let used = file.line(facts.node(inv.used_at).span);
            assert!(at < used, "{name}: {inv:?}");
            if next {
                assert_eq!(at + 1, used, "{name}: {inv:?}");
            }
        }
        // A few searches for each use, not one for each invalidating node,
        // each in a small part of the graph.
        assert!(work.searches <= 6 * n as u64 + 50, "{name}: {work:?}");
        assert!(
            work.part_nodes <= 3 * facts.nodes.len() as u64,
            "{name}: {work:?}"
        );
        assert!(work.overlaps <= 2 * n as u64, "{name}: {work:?}");
    }
}

/// The work of the checker grows linearly for each cause of W0301 with 1000
/// uses of an invalid reference, and for the mutations of [`rebind`]. A clock
/// is not stable on a loaded machine, so the test counts the work.
///
/// References that point into the same places share their witnesses. The
/// search of each reference runs in the part of the graph that can reach its
/// uses from a witness. A gen node reaches only nodes of its own strongly
/// connected component or of a later one, so the part has no node of an
/// earlier component than the first gen node.
#[test]
fn each_cause_checks_in_linear_work() {
    let mut cases = causes_of([1000; 7]);
    cases.push((
        "mutation",
        1000,
        rebind(1000),
        |c| matches!(c, Cause::Mutation(_)),
        true,
    ));
    for (name, n, src, cause, _) in cases {
        let c = check_source("causes.wf", &src, Options::default());
        let Some(body) = c.analysis.bodies.iter().find(|b| b.facts.name == "big") else {
            panic!("{name}: no body");
        };
        let (r, work) = check_counted(&body.facts);
        assert_eq!(r.violations.error.len(), n, "{name}");
        assert!(r.invalidations.iter().all(|i| cause(&i.cause)), "{name}");
        let nodes = body.facts.nodes.len() as u64;
        assert!(work.searches <= 6 * n as u64 + 50, "{name}: {work:?}");
        assert!(work.part_nodes <= 3 * nodes, "{name}: {work:?}");
    }
}

/// A name, a program with `n` references, the expected number of errors, and
/// the code of the errors.
type LongCase = (&'static str, String, usize, &'static str);

/// Programs where many references or moved variables live long: each one is
/// made at the start and used at the end, so the part of the graph between
/// them is large. `fields` and `refs` have no error, `refs, one push` has an
/// error for each reference after one mutation, and `refs, push in a loop`
/// has them in a loop. `moves` declares each vector at the start and moves
/// each one late (W0302).
fn long_lived(n: usize) -> Vec<LongCase> {
    let lets = |f: &dyn Fn(usize) -> String| (0..n).map(f).collect::<String>();
    let uses = lets(&|i| format!("    print(r{i})\n"));
    let refs = lets(&|i| format!("    let r{i} = &v[{i}]\n"));
    vec![
        (
            "fields",
            format!(
                "struct S {{ a: u64, b: u64 }}\nfn big(s: &S) / mut(s.b) {{\n{}{uses}    s.b = 2\n}}\n",
                lets(&|i| format!("    let r{i} = &s.a\n"))
            ),
            0,
            "W0301",
        ),
        (
            "refs",
            format!("fn big(v: &Vec<u32>) / mut(v) {{\n{refs}{uses}    v.push(1)\n}}\n"),
            0,
            "W0301",
        ),
        (
            "refs, one push",
            format!("fn big(v: &Vec<u32>) / mut(v) {{\n{refs}    v.push(1)\n{uses}}}\n"),
            n,
            "W0301",
        ),
        (
            "refs, push in a loop",
            format!(
                "fn big(v: &Vec<u32>) / mut(v) {{\n{refs}    loop {{\n{uses}        v.push(1)\n    }}\n}}\n"
            ),
            n,
            "W0301",
        ),
        (
            "moves",
            format!(
                "fn big() {{\n{}{}}}\n",
                lets(&|i| format!("    let v{i} = Vec.new()\n")),
                lets(&|i| if i == 0 {
                    String::new()
                } else {
                    format!("    if v{i}.len() == 0 {{ v{i} = v{} }}\n", i - 1)
                })
            ),
            0,
            "W0302",
        ),
    ]
}

/// The work of the checker grows linearly when many references or moved
/// variables live long ([`long_lived`]). The witnesses of the references
/// into one place are found once. Each part starts at the first gen node of
/// its search. When the parts of the references with the same witness nodes
/// have cost as much as the graph, the references share one search of the
/// whole graph.
#[test]
fn long_lived_references_check_in_linear_work() {
    let n = 1000;
    for (name, src, errors, code) in long_lived(n) {
        let c = check_source("long.wf", &src, Options::default());
        assert!(
            c.analysis.diags.is_empty(),
            "{name}: {:?}",
            c.analysis.diags
        );
        let Some(body) = c.analysis.bodies.iter().find(|b| b.facts.name == "big") else {
            panic!("{name}: no body");
        };
        let (r, work) = check_counted(&body.facts);
        let found = match code {
            "W0301" => r.violations.error.len(),
            _ => r.violations.use_after_move.len(),
        };
        assert_eq!(found, errors, "{name}");
        let nodes = body.facts.nodes.len() as u64;
        assert!(work.searches <= 4 * n as u64, "{name}: {work:?}");
        assert!(work.part_nodes <= 3 * nodes, "{name}: {work:?}");
        assert!(work.shared <= 1, "{name}: {work:?}");
    }
}

/// The loop cases of [`long_lived`] with the facts of the `ir` pipeline and
/// the groups A and B on (the preview of stage F10a): the analysis of the
/// loop widens at its head, the facts have one node for each statement, and
/// the work of the checker stays linear. A chain of `n` locals that rotate
/// their values in a loop needs `n` visits of the head, and gives one error.
#[test]
fn long_lived_references_in_a_loop_check_in_linear_work_with_the_ir_facts() {
    let n = 1000;
    let opts = || Options {
        facts: weft_sema::FactGen::Ir,
        ir_groups: weft_sema::Groups::parse("AB").unwrap(),
        ..Options::default()
    };
    let lets = |f: &dyn Fn(usize) -> String| (0..n).map(f).collect::<String>();
    let mut chain =
        String::from("struct E { hp: u64 }\nfn big(w: &Vec<E>, d: &Vec<u64>) / mut(w) {\n");
    let m = 100;
    for i in 0..m {
        let _ = writeln!(chain, "    let r{i} = &d[0]");
    }
    chain.push_str("    let k = 0\n    while k < 3 {\n");
    for i in 0..m - 1 {
        let _ = writeln!(chain, "        r{i} = r{}", i + 1);
    }
    let _ = writeln!(
        chain,
        "        r{} = &w[0].hp\n        k += 1\n    }}",
        m - 1
    );
    chain.push_str("    w.clear()\n    print(r0)\n}\n");
    let cases = vec![
        (
            "refs, push in a loop",
            format!(
                "fn big(v: &Vec<u32>) / mut(v) {{\n{}    loop {{\n{}        v.push(1)\n    }}\n}}\n",
                lets(&|i| format!("    let r{i} = &v[{i}]\n")),
                lets(&|i| format!("    print(r{i})\n"))
            ),
            n,
        ),
        ("a chain of locals", chain, 1),
    ];
    for (name, src, errors) in cases {
        let c = check_source("long.wf", &src, opts());
        assert!(
            c.analysis
                .ir_scope
                .as_ref()
                .is_some_and(weft_sema::Scope::in_scope),
            "{name}: {:?}",
            c.analysis
                .ir_scope
                .as_ref()
                .and_then(|s| s.fallback.clone())
        );
        let Some(body) = c.analysis.bodies.iter().find(|b| b.facts.name == "big") else {
            panic!("{name}: no body");
        };
        let (r, work) = check_counted(&body.facts);
        assert_eq!(r.violations.error.len(), errors, "{name}");
        let nodes = body.facts.nodes.len() as u64;
        assert!(work.searches <= 4 * n as u64, "{name}: {work:?}");
        assert!(work.part_nodes <= 3 * nodes, "{name}: {work:?}");
        assert!(work.shared <= 1, "{name}: {work:?}");
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

/// A struct with `n` fields, a function that gives each field a new value,
/// and a function that makes the struct with a literal.
fn many_fields(n: usize) -> String {
    let fields: Vec<String> = (0..n).map(|i| format!("f{i}: u64")).collect();
    let values: Vec<String> = (0..n).map(|i| format!("f{i}: 1")).collect();
    let mut s = format!(
        "struct Big {{ {} }}\nfn set(b: &Big) / mut(b) {{\n",
        fields.join(", ")
    );
    for i in 0..n {
        let _ = writeln!(s, "    b.f{i} = 1");
    }
    let _ = write!(
        s,
        "}}\nfn make() -> Big {{ Big {{ {} }} }}\n",
        values.join(", ")
    );
    s
}

/// An enum with `n` variants and a `match` with an arm for each.
fn many_variants(n: usize) -> String {
    let variants: Vec<String> = (0..n).map(|i| format!("V{i}(u64)")).collect();
    let arms: Vec<String> = (0..n).map(|i| format!("V{i}(x) => x")).collect();
    format!(
        "enum E {{ {} }}\nfn f(e: E) -> u64 {{ match e {{ {} }} }}\n",
        variants.join(", "),
        arms.join(", ")
    )
}

/// `n` handlers one after the other, each around one operation.
fn many_handlers(n: usize) -> String {
    let mut s = String::from("effect Note { fn note(x: u64) }\nfn f() {\n");
    for i in 0..n {
        let _ = writeln!(
            s,
            "    handle Note {{ fn note(x) {{ resume(()) }} }} in note({i})"
        );
    }
    s.push_str("}\n");
    s
}

/// Sema and the checker take less than 2 s for 4000 blocks with a local and
/// a reference each, for 3200 types with a local each, for a struct with
/// 16000 fields, for a `match` of 8000 variants and for 4000 handlers. The
/// first checker searched the whole function for each variable. Sema copied
/// the names of all types for each local, searched the fields and the
/// variants by name, compared each `mut` place of a signature with each other
/// one, compared each field of a struct literal with each given field, gave
/// each variant all the arms of a `match`, and looked at all the earlier
/// values, calls, locals and edges for each handler. Then these shapes took
/// 2 s to 11 s in a release build.
///
/// A clock is not stable on a loaded machine. So the bound is about five to
/// thirty times the time of a release build, and the test runs only in a
/// release build: `cargo test --release -p weft-check --test scale`. In a
/// debug build, [`many_locals_check`] checks the same shapes, smaller, with no
/// clock.
#[test]
#[cfg_attr(debug_assertions, ignore = "a time bound needs a release build")]
fn many_locals_check_in_time() {
    for (name, src) in many_locals([4000, 3200, 16000, 8000, 4000]) {
        let start = std::time::Instant::now();
        let c = check_source("many.wf", &src, Options::default());
        let time = start.elapsed();
        assert!(c.ok(), "{name}: {:?}", c.diags);
        assert!(time.as_millis() < 2000, "{name}: {time:?}");
    }
}

/// The shapes of [`many_locals_check_in_time`], with the sizes `n`.
fn many_locals(n: [usize; 5]) -> [(&'static str, String); 5] {
    [
        ("blocks", blocks(n[0])),
        ("types", many_types(n[1])),
        ("fields", many_fields(n[2])),
        ("variants", many_variants(n[3])),
        ("handlers", many_handlers(n[4])),
    ]
}

/// The shapes of [`many_locals_check_in_time`] check with no error in a debug
/// build too, and the work of the checker for the blocks grows linearly.
#[test]
fn many_locals_check() {
    for (name, src) in many_locals([1000, 300, 1000, 1000, 100]) {
        let c = check_source("many.wf", &src, Options::default());
        assert!(c.ok(), "{name}: {:?}", c.diags);
        for b in &c.analysis.bodies {
            let (_, work) = check_counted(&b.facts);
            let nodes = b.facts.nodes.len() as u64;
            assert!(work.part_nodes <= 3 * nodes, "{name}: {work:?}");
        }
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

/// A program with a place field in one struct and a type `T{d-1}` of depth
/// `d`, where each level has `f` fields of the level below it. `T0` holds the
/// struct with the place field, so each of the `f` to the power `d - 1` paths
/// ends at a place field. With `back`, `T0` also holds the deepest type, so
/// the types make a cycle. A body makes `locals` new values of the deepest
/// type (review round 3, Q3-4).
fn type_dag(d: usize, f: usize, locals: usize, back: bool) -> String {
    let mut s = String::from("struct Frame: !Move { buf: [u8; 4], cur: &u8 in self.buf[] }\n");
    if back {
        let _ = writeln!(
            s,
            "struct T0 {{ x: u64, fr: Frame, back: Option<Box<T{}>> }}",
            d - 1
        );
    } else {
        s.push_str("struct T0 { x: u64, fr: Frame }\n");
    }
    for i in 1..d {
        let fields: Vec<String> = (0..f).map(|j| format!("f{j}: T{}", i - 1)).collect();
        let _ = writeln!(s, "struct T{i} {{ {} }}", fields.join(", "));
    }
    let _ = writeln!(s, "fn make() -> T{} {{ make() }}", d - 1);
    s.push_str("fn f() {\n");
    for i in 0..locals {
        let _ = writeln!(s, "    let t{i} = make()");
    }
    s.push_str("    print(1)\n}\n");
    s
}

/// A program with `n` structs that each hold a place field and an
/// `Option<Box<..>>` of each other struct, as the nodes of a syntax tree do.
/// A body makes two new values of the first struct.
fn mutual_types(n: usize) -> String {
    let mut s = String::from("struct Frame: !Move { buf: [u8; 4], cur: &u8 in self.buf[] }\n");
    for i in 0..n {
        let fields: Vec<String> = (0..n)
            .filter(|&j| j != i)
            .map(|j| format!("f{j}: Option<Box<A{j}>>"))
            .collect();
        let _ = writeln!(s, "struct A{i} {{ fr: Frame, {} }}", fields.join(", "));
    }
    s.push_str("fn make() -> A0 { make() }\nfn f() {\n    let a = make()\n    let b = make()\n    print(1)\n}\n");
    s
}

/// The search for place fields walks each full type once for a body, so its
/// work grows with the number of types, not with the `f` to the power `d`
/// paths through them (Q3-4). Before the table of paths, depth 16 with three
/// fields and five locals took about a minute. A cycle of types, types that
/// each hold all the others, and a type that grows at each depth (review of
/// R3a) also cost linear work.
#[test]
fn place_fields_of_a_deep_type_are_found_in_linear_work() {
    for back in [false, true] {
        let (wa, ..) = work_of(&type_dag(16, 3, 5, back));
        let (wb, ..) = work_of(&type_dag(32, 3, 5, back));
        // With no cycle the search walks each level. With the cycle it stops
        // at the first level below the root.
        let least = if back { 1 } else { 16 };
        assert!(
            wa.place_types >= least && wa.place_types <= 2 * 16 + 16,
            "{wa:?}"
        );
        assert!(wb.place_types <= 2 * wa.place_types + 16, "{wa:?} {wb:?}");
    }
    let (wa, ..) = work_of(&mutual_types(8));
    let (wb, ..) = work_of(&mutual_types(16));
    assert!(wa.place_types >= 8 && wa.place_types <= 4 * 8 + 8, "{wa:?}");
    assert!(wb.place_types <= 2 * wa.place_types + 8, "{wa:?} {wb:?}");
    // Each depth of `G` makes a new type: `G<(T, T)>`, `G<(T, Frame)>` and so
    // on. The search stops at the second `G` on the way.
    let (wg, ..) = work_of(
        "struct Frame: !Move { buf: [u8; 4], cur: &u8 in self.buf[] }\n\
         struct G<T> { x: T, a: Option<Box<G<(T, T)>>>, b: Option<Box<G<(T, Frame)>>> }\n\
         fn f() {\n    let g = G { x: 1, a: None, b: None }\n    print(g.x)\n}\n",
    );
    assert!(wg.place_types >= 1 && wg.place_types <= 8, "{wg:?}");
}

/// `n` helper closures in one body. Each helper calls the `back` helpers
/// before it (review round 3, Q3-2: `r3/quality/repro/Q3_closure_*.wf`).
fn helper_closures(n: usize, back: usize) -> String {
    let mut s = String::from("struct Out { v: Vec<u64> }\nfn render(out: &Out) / mut(out.v) {\n");
    for i in 0..n {
        let calls: Vec<String> = (i.saturating_sub(back)..i)
            .rev()
            .map(|j| format!("h{j}()"))
            .collect();
        if calls.is_empty() {
            let _ = writeln!(s, "    let h{i} = || out.v.push({i})");
        } else {
            let _ = writeln!(s, "    let h{i} = || {{ {} }}", calls.join("; "));
        }
    }
    let _ = writeln!(s, "    h{}()\n}}", n - 1);
    s
}

/// A property query looks at each closure summary one time, so closures that
/// call each other cost polynomial work, not work that grows by a factor for
/// each closure (Q3-2). Before the fix, 16 helpers that each call the two
/// helpers before them took about 4 s in a release build.
#[test]
fn closures_that_call_closures_cost_polynomial_work() {
    for back in [1, 2, 16] {
        let (wa, ..) = work_of(&helper_closures(8, back));
        let (wb, ..) = work_of(&helper_closures(16, back));
        assert!(wa.closure_queries > 0, "{wa:?}");
        // Two times the closures: at most eight times the work (a cubic
        // bound: n queries of n closures, and a closure that calls n others).
        assert!(
            wb.closure_queries <= 8 * wa.closure_queries + 64,
            "back {back}: {wa:?} {wb:?}"
        );
    }
}
