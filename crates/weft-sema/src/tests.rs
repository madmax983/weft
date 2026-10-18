//! Tests for semantic analysis.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use weft_facts::{FnFacts, PlaceId, VarId};

use crate::{analyze_source, Options};

/// Returns the facts of the body of function `name`.
fn facts(src: &str, name: &str) -> FnFacts {
    let a = analyze_source(src, Options::default()).expect("the source parses");
    a.bodies
        .into_iter()
        .find(|b| b.facts.name == name)
        .map(|b| b.facts)
        .expect("the function exists")
}

fn var(f: &FnFacts, name: &str) -> VarId {
    let i = f
        .vars
        .iter()
        .position(|v| v.name == name)
        .expect("the variable exists");
    VarId(u32::try_from(i).unwrap())
}

fn place(f: &FnFacts, display: &str) -> PlaceId {
    let i = f
        .places
        .iter()
        .position(|p| p.display == display)
        .expect("the place exists");
    PlaceId(u32::try_from(i).unwrap())
}

#[test]
fn locals_and_by_value_parameters_own_their_roots() {
    let f = facts(
        "fn f(v: Vec<u64>, r: &Vec<u64>) { let w = Vec.new(); w.push(1) }",
        "f",
    );
    assert!(f.owner.contains(&(place(&f, "v"), var(&f, "v"))));
    assert!(f.owner.contains(&(place(&f, "w"), var(&f, "w"))));
    // The referent of a reference parameter has no owner in the function.
    let r = place(&f, "r");
    assert!(!f.owner.iter().any(|&(p, _)| p == r));
}

#[test]
fn a_reference_through_an_rc_handle_points_into_the_handle() {
    let f = facts(
        "struct C { items: Vec<u64> }
         fn f(a: Rc<C>) { let r = &a.items[0]; print(r) }",
        "f",
    );
    let r = var(&f, "r");
    assert!(f.points_into.contains(&(r, place(&f, "C.items[]"))));
    assert!(f.points_into.contains(&(r, place(&f, "a.*"))));
}

#[test]
fn a_block_value_into_a_block_local_is_held_across_the_end() {
    let f = facts(
        "fn f() { let r = { let v = Vec.new(); v.push(1); &v[0] }; print(r) }",
        "f",
    );
    let held = var(&f, "block value");
    let v = var(&f, "v");
    assert!(f.points_into.contains(&(held, place(&f, "v[]"))));
    let end = f
        .scope_end
        .iter()
        .find(|&&(x, _)| x == v)
        .map(|&(_, n)| n)
        .expect("v goes out of scope");
    let used = f
        .uses
        .iter()
        .find(|&&(x, _)| x == held)
        .map(|&(_, n)| n)
        .expect("the block value is used");
    assert!(f.cfg_edge.contains(&(end, used)));
}

#[test]
fn a_reference_used_as_a_value_reads_its_places() {
    let f = facts(
        "struct S { n: u64 } fn f(s: &S) -> u64 { let c = &s.n; c + 1 }",
        "f",
    );
    let n = place(&f, "s.n");
    assert!(f.reads_at.iter().any(|&(_, p)| p == n));
}

#[test]
fn a_compound_assignment_through_a_reference_mutates_its_places() {
    let f = facts(
        "struct S { n: u64 } fn f(s: &S) { let c = &s.n; c += 1 }",
        "f",
    );
    let n = place(&f, "s.n");
    assert!(f.mutates_at.iter().any(|&(_, p)| p == n));
    // `c` keeps its value: the assignment does not rebind it.
    let c = var(&f, "c");
    assert_eq!(f.rebound_at.iter().filter(|&&(v, _)| v == c).count(), 1);
}

#[test]
fn a_temporary_goes_out_of_scope_at_the_end_of_its_statement() {
    let f = facts(
        "fn mk() -> Vec<u64> { Vec.new() } fn f() { let r = &mk()[0]; print(r) }",
        "f",
    );
    let t = place(&f, "temporary");
    let (_, owner) = *f
        .owner
        .iter()
        .find(|&&(p, _)| p == t)
        .expect("the temporary has an owner");
    let end = f
        .scope_end
        .iter()
        .find(|&&(v, _)| v == owner)
        .map(|&(_, n)| n)
        .expect("the temporary goes out of scope");
    assert_eq!(f.node(end).label, "end of statement");
    let r = var(&f, "r");
    let used = f
        .uses
        .iter()
        .filter(|&&(v, _)| v == r)
        .map(|&(_, n)| n)
        .max()
        .expect("r is used");
    assert!(end < used);
}

#[test]
fn a_handler_clause_runs_at_each_operation_it_handles() {
    let f = facts(
        "effect Log { fn log(m: String) }
         fn take(v: Vec<u64>) {}
         fn f() {
             let v: Vec<u64> = Vec.new()
             handle Log { fn log(m) { let u = Vec.new(); take(v); resume(()) } } in log(\"x\")
         }",
        "f",
    );
    let log = f
        .nodes
        .iter()
        .position(|n| n.label == "log")
        .map(|i| weft_facts::NodeId(u32::try_from(i).unwrap()))
        .expect("the operation has a node");
    assert!(f.moved_at.contains(&(var(&f, "v"), log)));
    assert!(f.scope_end.contains(&(var(&f, "u"), log)));
}

#[test]
fn a_move_of_a_field_moves_a_part() {
    let f = facts(
        "struct P { a: Vec<u64>, b: Vec<u64> }
         fn take(v: Vec<u64>) {}
         fn f() { let p = P { a: Vec.new(), b: Vec.new() }; take(p.a); take(p) }",
        "f",
    );
    let a = place(&f, "p.a");
    let p = var(&f, "p");
    let (_, n) = *f
        .moved_part
        .iter()
        .find(|&&(m, _)| m == a)
        .expect("p.a moves");
    assert!(f.moved_at.contains(&(p, n)));
    // The move of the whole local is not a part move.
    assert_eq!(f.moved_part.len(), 1);
}

#[test]
fn a_loop_reads_the_elements_at_each_iteration() {
    let f = facts("fn f(v: &Vec<u64>) { for x in v[] { print(1) } }", "f");
    let elems = place(&f, "v[]");
    let header = f
        .nodes
        .iter()
        .position(|n| n.label == "for")
        .map(|i| weft_facts::NodeId(u32::try_from(i).unwrap()))
        .expect("the loop has a header");
    assert!(f.reads_at.contains(&(header, elems)));
}
