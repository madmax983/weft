//! Tests for semantic analysis.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use weft_facts::{FnFacts, PlaceId, RootKind, VarId};

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

#[test]
fn an_unknown_function_result_points_anywhere_inside_its_argument() {
    let f = facts(
        "struct E { hp: i32 } struct W { es: Vec<E> }
         fn f(g: fn(&W) -> &E, w: &W) { let r = g(w); print(r.hp) }",
        "f",
    );
    let any = place(&f, "w..");
    assert!(f.place(any).is_wildcard());
    assert!(f.points_into.contains(&(var(&f, "r"), any)));
}

#[test]
fn a_closure_refers_to_captured_values_that_are_not_plain_data() {
    let f = facts(
        "fn take(v: Vec<u64>) {}
         fn f() { let n: u64 = 1; let v: Vec<u64> = Vec.new(); let g = || { print(n); take(v) }; g() }",
        "f",
    );
    let g = var(&f, "{closure}");
    assert!(f.points_into.contains(&(g, place(&f, "v"))));
    assert!(!f.points_into.contains(&(g, place(&f, "n"))));
    // The move of `v` comes before the closure gets its value.
    let v = var(&f, "v");
    let (_, moved) = *f.moved_at.iter().find(|&&(x, _)| x == v).expect("v moves");
    let (_, bound) = *f
        .rebound_at
        .iter()
        .find(|&&(x, _)| x == g)
        .expect("g is bound");
    assert!(moved < bound);
}

#[test]
fn a_compound_assignment_to_a_reference_field_writes_its_place() {
    let f = facts(
        "struct Frame: !Move { buf: [u8; 4], cur: &u8 in self.buf[] }
         fn f(fr: &Frame) / mut(fr.buf) { fr.cur += 1 }",
        "f",
    );
    let buf = place(&f, "fr.buf[]");
    assert!(f.mutates_at.iter().any(|&(_, p)| p == buf));
    let cur = place(&f, "fr.cur");
    assert!(!f.mutates_at.iter().any(|&(_, p)| p == cur));
}

/// Returns the node with label `label`.
fn node(f: &FnFacts, label: &str) -> weft_facts::NodeId {
    f.nodes
        .iter()
        .position(|n| n.label == label)
        .map(|i| weft_facts::NodeId(u32::try_from(i).unwrap()))
        .expect("the node exists")
}

/// Returns the signature of function `name`.
fn sig(src: &str, name: &str) -> crate::FnSig {
    let a = analyze_source(src, Options::default()).expect("the source parses");
    let i = a
        .program
        .fns
        .iter()
        .position(|f| f.name == name)
        .expect("the function exists");
    a.sigs[i].clone()
}

#[test]
fn a_perform_passes_its_reference_arguments_to_the_clause() {
    let f = facts(
        "effect Bump { fn bump(v: &Vec<u64>) }
         fn f() {
             let v: Vec<u64> = Vec.new()
             handle Bump { fn bump(x) { let e = &x[0]; x.push(1); print(e); resume(()) } } in bump(&v)
         }",
        "f",
    );
    let n = node(&f, "bump");
    let v = place(&f, "v");
    assert!(f.call_arg.contains(&(n, v, 0)));
    // The clause parameter has its own root. A mutation through it is a mutation
    // of the argument at the operation, and it needs no declaration.
    let x = place(&f, "x");
    assert_eq!(f.roots[f.place(x).root.index()].kind, RootKind::Arg);
    assert!(!f.param_rooted(x));
    assert!(f.points_into.contains(&(var(&f, "e"), place(&f, "x[]"))));
    assert!(f.mutates_at.contains(&(n, v)));
    assert!(f.call_mut.contains(&(n, v, 0)));
}

#[test]
fn an_operation_of_an_outer_handler_lends_its_arguments() {
    let f = facts(
        "effect Bump { fn bump(v: &Vec<u64>) }
         fn f(v: &Vec<u64>) / Bump { bump(v) }",
        "f",
    );
    assert!(f.lends_mut.contains(&(node(&f, "bump"), place(&f, "v"))));
    assert!(f.mutates_at.is_empty());
}

#[test]
fn a_closure_argument_passes_its_captures() {
    let f = facts(
        "struct E { hp: i32 } struct W { es: Vec<E> }
         fn run(g: fn(), w: &W) {}
         fn f(w: &W) { let r = &w.es[0]; run(|| print(r.hp), w) }",
        "f",
    );
    let n = node(&f, "run");
    assert!(f.call_arg.contains(&(n, place(&f, "w.es[]"), 800)));
    assert!(f.call_arg.contains(&(n, place(&f, "w"), 1)));
}

#[test]
fn a_call_of_a_function_parameter_lends_its_reference_arguments() {
    let f = facts("struct W { n: u64 } fn f(g: fn(&W), w: &W) { g(w) }", "f");
    assert!(f.lends_mut.contains(&(node(&f, "g"), place(&f, "w"))));
    assert!(f.may_abort.contains(&node(&f, "g")));
}

#[test]
fn a_closure_parameter_root_needs_no_declaration() {
    let f = facts(
        "struct W { n: u64 } fn f(w: &W) / mut(w.n) { let h = |x: &W| x.n += 1; h(w) }",
        "f",
    );
    let xn = place(&f, "x.n");
    assert!(!f.param_rooted(xn));
    // The call mutates the argument instead.
    assert!(f.mutates_at.contains(&(node(&f, "h"), place(&f, "w.n"))));
}

#[test]
fn a_signature_states_what_the_body_lends_to_its_function_parameters() {
    let s = sig(
        "struct W { n: u64 } fn apply(f: fn(&W), w: &W) { f(w) }",
        "apply",
    );
    let lp = &s.effects.lent;
    assert_eq!(lp.len(), 1, "{lp:?}");
    assert_eq!((lp[0].param, lp[0].arg), (0, Some(0)));
    let place = lp[0].place.as_ref().expect("the caller can name the place");
    assert_eq!(place.root, crate::program::SigRoot::Param(1));
    assert!(place.steps.is_empty());
}

#[test]
fn a_signature_states_what_a_returned_closure_does() {
    let s = sig(
        "struct W { n: u64 } fn mk(w: &W) -> fn() { || { w.n += 1; log.info(\"x\") } }",
        "mk",
    );
    // The maker has the effects of the closure.
    assert!(s.effects.named.contains("Log"));
    assert_eq!(s.effects.muts.len(), 1);
    let ret = s.effects.ret.expect("the returned closure has a summary");
    assert!(ret.named.contains("Log"));
    assert_eq!(ret.muts.len(), 1);
    assert_eq!(ret.muts[0].text, "w.n");
    assert!(ret.abort);
}
