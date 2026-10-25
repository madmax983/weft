//! Loops in the `ir` pipeline (plan stage F10, group B; `docs/ir.md` 5.14,
//! 6.6).
//!
//! Each test checks a program with `--facts=ir` and the groups A and B on
//! (the preview of stage F10a: group B is not in the default set yet). The
//! `//~ CODE` markers are the diagnostics of the `ir` pipeline.

use std::fmt::Write as _;
use std::fs;
use std::path::Path;

use weft_check::check_analysis;
use weft_sema::{analyze_source, factgen, irbuild, Options};

/// The options of the `ir` pipeline with the groups A and B on.
fn ab(src: &str) -> Options {
    Options {
        facts: weft_sema::FactGen::Ir,
        ir_groups: weft_sema::Groups::parse("AB").unwrap_or(weft_sema::Groups::NONE),
        ..Options::from_markers(src)
    }
}

/// The line of byte offset `lo` of `src`.
fn line_of(src: &str, lo: u32) -> usize {
    src.get(..lo as usize)
        .map_or(0, |s| s.matches('\n').count() + 1)
}

/// The codes and lines of the diagnostics of `src` with the `ir` pipeline
/// and the groups A and B on. The program must be in scope.
fn ab_codes(src: &str) -> Vec<(String, usize)> {
    let a = analyze_source(src, ab(src))
        .unwrap_or_else(|d| panic!("the program does not parse: {}", d.message));
    assert!(
        a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope),
        "{:?}",
        a.ir_scope.as_ref().and_then(|s| s.fallback.clone())
    );
    let mut got: Vec<(String, usize)> = check_analysis(a, &[])
        .diags
        .iter()
        .map(|d| (format!("{:?}", d.code), line_of(src, d.span.lo)))
        .collect();
    got.sort();
    got
}

/// The `//~ CODE` markers of `src` as (code, line), sorted.
fn markers(src: &str) -> Vec<(String, usize)> {
    let mut want: Vec<(String, usize)> = src
        .lines()
        .enumerate()
        .filter_map(|(i, l)| {
            l.split("//~ ")
                .nth(1)
                .map(|c| (c.trim().to_string(), i + 1))
        })
        .collect();
    want.sort();
    want
}

/// The text of a file of the repository.
fn repo_file(rel: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(rel);
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

#[test]
fn the_bodies_of_the_wild_programs_keep_their_markers() {
    // `tests/programs/35_wild_places.wf`, `102_wild_instances.wf` and
    // `103_wild_lend.wf` guard the precision of wildcard places and of
    // one-place instances. The programs use function values, handlers and
    // tasks (groups C to E), so the gate keeps them out of scope with the
    // groups A and B. Each body that the fact generator supports alone gets
    // the facts of the `ir` pipeline, and its diagnostics must be the markers
    // on its lines: `find` (a `for` with a `return`) and `again` (a call
    // result in a loop: no one-place instance on a cycle, so the result of
    // the iteration before can be inside the result of this one).
    let mut seen = Vec::new();
    for rel in [
        "tests/programs/35_wild_places.wf",
        "tests/programs/102_wild_instances.wf",
        "tests/programs/103_wild_lend.wf",
    ] {
        let src = repo_file(rel);
        let a = analyze_source(&src, Options::from_markers(&src))
            .unwrap_or_else(|d| panic!("{rel} does not parse: {}", d.message));
        let built = irbuild::build(&a);
        let want = markers(&src);
        for (i, e) in built.entries.iter().enumerate() {
            let irbuild::Outcome::Built(b) = e.outcome else {
                continue;
            };
            let (Ok(facts), Some(old)) = (factgen::preview(&a, &built, i), a.bodies.get(i)) else {
                continue;
            };
            let Some(body) = built.program.bodies.get(b.index()) else {
                continue;
            };
            let lines = line_of(&src, body.origin.span.lo)..=line_of(&src, body.origin.span.hi);
            let mut one = old.clone();
            one.facts = facts;
            let mut view = a.clone();
            view.bodies = vec![one];
            view.diags = Vec::new();
            let mut got: Vec<(String, usize)> = check_analysis(view, &[])
                .diags
                .iter()
                .map(|d| (format!("{:?}", d.code), line_of(&src, d.span.lo)))
                .filter(|(_, l)| lines.contains(l))
                .collect();
            got.sort();
            let mine: Vec<(String, usize)> = want
                .iter()
                .filter(|(_, l)| lines.contains(l))
                .cloned()
                .collect();
            assert_eq!(got, mine, "{rel}: `{}`", e.name);
            seen.push(e.name.clone());
        }
    }
    for name in ["find", "again", "hit", "kids", "two"] {
        assert!(seen.iter().any(|n| n == name), "`{name}`: {seen:?}");
    }
}

#[test]
fn a_chain_of_reference_locals_in_a_loop_carries_each_place() {
    // RR1 (`tests/gate/probes/r2/redteam/repro/RR1_loop_chain.wf`, the part
    // `ref_chain` of groups A and B): ten locals rotate their values, so
    // the place of `r9` reaches `r0` after ten visits of the loop head. The
    // widening of the analysis does not stop before the chain is complete.
    let full = repo_file("tests/gate/probes/r2/redteam/repro/RR1_loop_chain.wf");
    let src = full
        .split("// Function values.")
        .next()
        .unwrap_or_default()
        .to_string();
    assert!(src.contains("fn ref_chain"));
    assert_eq!(ab_codes(&src), markers(&src));
    // The same chain with twenty locals and no other function.
    let mut long = String::from(
        "struct Entity { hp: i32 }\nstruct World { entities: Vec<Entity> }\n\
         fn chain(world: &World, d: &Vec<i32>) / mut(world.entities) {\n",
    );
    for i in 0..20 {
        let _ = writeln!(long, "    let r{i} = &d[0]");
    }
    long.push_str("    let m = 0\n    while m < 30 {\n");
    for i in 0..19 {
        let _ = writeln!(long, "        r{i} = r{}", i + 1);
    }
    long.push_str("        r19 = &world.entities[0].hp\n        m += 1\n    }\n");
    long.push_str("    world.entities.clear()\n    print(r0)   //~ W0301\n}\n");
    assert_eq!(ab_codes(&long), markers(&long));
}

#[test]
fn a_reference_local_that_a_loop_gives_a_new_value_keeps_each_value() {
    // V041 (`loop_ref_control.wf` of the claims file): `cur` is `a` in the
    // first iteration and `b` later, so the clear through `cur` changes
    // `b.entities` too: W0301 at the caller and W0703 in the public
    // function.
    let src = repo_file("tests/gate/probes/verify/review_core/Core_S2/probes/loop_ref_control.wf");
    let got = ab_codes(&src);
    assert_eq!(
        got,
        vec![("W0301".to_string(), 16), ("W0703".to_string(), 22)]
    );
}

#[test]
fn a_loop_that_walks_deeper_places_widens_and_ends() {
    // `cur = &cur.next[0]` gives a place two steps deeper at each visit of
    // the loop head; the second form ten steps. The widening makes the
    // place a wildcard place, so the analysis ends, and a change below `l`
    // after the loop invalidates `cur`.
    let src = "\
struct Link { v: u64, next: Vec<Link> }
fn walk(l: &Link, n: u64) / mut(l..) {
    let cur = l
    let i = 0
    while i < n {
        cur = &cur.next[0]
        i += 1
    }
    l.next[0].next.clear()
    print(cur.v)   //~ W0301
}
fn walk_far(l: &Link, n: u64) / mut(l..) {
    let cur = l
    let i = 0
    while i < n {
        cur = &cur.next[0].next[0].next[0].next[0].next[0]
        i += 1
    }
    l.next.clear()
    print(cur.v)   //~ W0301
}
fn walk_clean(l: &Link, n: u64) {
    let cur = l
    let i = 0
    while i < n {
        cur = &cur.next[0]
        i += 1
    }
    print(cur.v)
}
fn main() {}
";
    assert_eq!(ab_codes(src), markers(src));
}

#[test]
fn a_for_loop_borrows_its_elements_for_each_iteration() {
    // `docs/ir.md` 5.14: the iterator points into the elements, and each
    // `IterNext` uses it, so a push in the body invalidates the iterator.
    // An element is a reference into the elements. A scalar element is a
    // copy, and a change of another field keeps the iterator valid.
    let src = "\
struct Entity { hp: i32, ids: Vec<u64> }
struct World { entities: Vec<Entity>, score: u64 }
fn grow(v: &Vec<u64>) / mut(v) {
    for x in v[] {   //~ W0301
        v.push(x)
    }
}
fn keep(world: &World) / mut(world.entities) {
    let first = &world.entities[0]
    for e in world.entities[] {
        print(e.hp)
    }
    world.entities.clear()
    print(first.hp)   //~ W0301
}
fn elem_ref(world: &World) / mut(world.entities) {
    let last = &world.entities[0]
    for e in world.entities[] {
        last = e
    }
    world.entities.clear()
    print(last.hp)   //~ W0301
}
fn other_field(world: &World) / mut(world.score) {
    for e in world.entities[] {
        world.score += 1
        print(e.hp)
    }
}
fn sum(v: &Vec<u64>) -> u64 {
    let s = 0
    for x in v[] { s += x }
    s
}
fn range(n: u64) -> u64 {
    let s = 0
    for i in 0..n { s += i }
    s
}
fn main() {}
";
    assert_eq!(ab_codes(src), markers(src));
}

#[test]
fn a_borrow_of_plain_data_in_a_loop_stays_valid_in_later_iterations() {
    // The constant-borrow fix (`docs/ir.md` 5.9, 5.10): `&(i + 1)` borrows
    // a promoted temporary. Its `Live` runs again in each iteration, and
    // the first value after a `Live` writes nothing, so the references of
    // the earlier iterations stay valid (the old pipeline accepts it too).
    let src = "\
fn f(n: u64) {
    let v = Vec.new()
    let i = 0
    while i < n {
        v.push(&(i + 1))
        i += 1
    }
    print(v.len())
}
fn main() {}
";
    assert_eq!(ab_codes(src), markers(src));
}

#[test]
fn an_iterator_over_a_variant_payload_ends_when_the_base_gets_a_new_value() {
    // Stage F8d: `for x in e.A.v { e = .. }` (a06) must stay rejected: the
    // iterator is a reference into `(e as A)`.
    let src = "\
struct Other { b: i32 }
struct Bag { v: Vec<i32> }
enum Two { A(Bag), B(Other) }
fn f() {
    let w = Vec.new()
    w.push(1)
    let e = Two.A(Bag { v: w })
    for x in e.A.v {   //~ W0301
        e = Two.B(Other { b: 1000 })
        print(x)
    }
}
fn main() {}
";
    assert_eq!(ab_codes(src), markers(src));
}

#[test]
fn a_loop_reads_back_what_the_iteration_before_stored_behind_a_parameter() {
    // Tier 2 lost faults (`verify/s5/R2a: .../W3_store_behind.wf`, `W3b`):
    // iteration `i` pushes `e` (a place of `v`) into `*out`, and iteration
    // `i + 1` reads it back, borrows into it, and clears the kids of the
    // new `e` (the same place). The heap slot of `*out` carries the place
    // around the loop. The second function stores a deeper place at each
    // iteration: the heap slot widens, and the analysis ends. The read of
    // the slot (`c`) is W0301 too (stage F10.1, heap slot variables): `e`
    // points anywhere into `*v` (the wildcard place of the result of
    // `find`), so the change of `e.kids` makes the slot invalid, as it makes
    // `out` invalid in the old pipeline. Only the write through `e` itself
    // keeps `e` valid (`writes_via`).
    let src = "\
struct Entity { hp: i32, id: u64, kids: Vec<Entity> }
struct Link { v: u64, next: Vec<Link> }
fn find(v: &Vec<Entity>, id: u64) -> Option<&Entity> {
    for e in v[] { if e.id == id { return Some(e) } }
    None
}
fn behind(v: &Vec<Entity>, out: &Vec<&Entity>, n: u64) / mut(v.., out) {
    let i = 0
    while i < n {
        match find(v, 1) {
            Some(e) => {
                let c = out[out.len() - 1]   //~ W0301
                let k = &c.kids[0]
                e.kids.clear()
                print(k.hp)   //~ W0301
                out.push(e)
            }
            None => {}
        }
        i += 1
    }
}
fn deeper(l: &Link, out: &Vec<&Link>, n: u64) / mut(out) {
    out.push(l)
    let i = 0
    while i < n {
        let cur = out[out.len() - 1]
        out.push(&cur.next[0])
        i += 1
    }
    print(out.len())
}
fn main() {}
";
    assert_eq!(ab_codes(src), markers(src));
}

#[test]
fn a_local_that_gets_its_type_later_in_a_loop_has_ir() {
    // Stage F10.1 (hole H-B of the review of stage F10): the lowering visits
    // a loop body in more than one pass, and the first pass does not know
    // the type of `best` or `o` yet. The THIR tables keep the decisions of
    // the last pass, so the body has IR and the `ir` pipeline checks it.
    let best = "struct Entity { hp: i32 }
fn f(es: &Vec<Entity>) / mut(es) {
    let best = None
    for e in es[] {
        let better = match best { Some(b) => e.hp > b.hp, None => true }
        if better { best = Some(e) }
    }
    es.clear()
    match best { Some(b) => print(b.hp), None => {} }   //~ W0301
}
fn main() { let es = Vec.new(); es.push(Entity { hp: 1 }); f(&es) }
";
    let next = "fn main() {
    let v = Vec.new()
    v.push(1)
    let o = None
    let i = 0
    while i < 2 {
        match o { Some(r) => print(r), None => {} }
        o = Some(&v[0])
        i += 1
    }
    v.push(2)
    match o { Some(r) => print(r), None => {} }   //~ W0301
}
";
    for src in [best, next] {
        assert_eq!(ab_codes(src), markers(src), "{src}");
    }
}

#[test]
fn a_reference_in_a_heap_slot_is_invalid_in_the_next_iteration_after_a_change() {
    // Stage F10.1 (hole H-A of the review of stage F10, f10/variants/h and
    // lc22): iteration k stores `&v[0]` behind `out` and clears `v`;
    // iteration k + 1 reads it back. A callee that copies the held
    // references of another `Vec` (`q9_extend_fp`) and a promoted temporary
    // in a loop stay valid.
    let src = "\
struct Entity { hp: i32 }
fn next_iter(v: &Vec<Entity>, out: &Vec<&Entity>, n: u64) / mut(v.., out) {
    let i = 0
    while i < n {
        if i > 0 { print(out[out.len() - 1].hp) }   //~ W0301
        out.push(&v[0])
        v.clear()
        v.push(Entity { hp: 2 })
        i += 1
    }
}
fn read_back(dst: &Vec<&Entity>, src: &Vec<Entity>) / mut(dst, src) {
    let i = 0
    while i < src.len() { dst.push(&src[i]); i += 1 }
    src.clear()
    print(dst[0].hp)   //~ W0301
}
fn extend(dst: &Vec<&Entity>, src: &Vec<&Entity>) / mut(dst) {
    let i = 0
    while i < src.len() { dst.push(src[i]); i += 1 }
}
fn promoted() {
    let v = Vec.new()
    let i = 0
    while i < 3 { v.push(&(i + 1)); i += 1 }
    print(v[0])
}
fn main() {}
";
    assert_eq!(ab_codes(src), markers(src));
}
