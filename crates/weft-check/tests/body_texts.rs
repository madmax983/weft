//! Diagnostic texts and rules for linear values, `!Move` values, patterns and
//! modes in bodies.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use weft_check::{bridge, check, check_source};
use weft_facts::{FnFacts, NodeId, Span, VarId, VarInfo, VarKind};
use weft_sema::Options;
use weft_syntax::SourceFile;

/// Returns the rendered errors of a program.
fn errors(src: &str) -> String {
    let checked = check_source("t.wf", src, Options::default());
    let file = SourceFile::new("t.wf", src);
    checked.diags.iter().map(|d| d.render(&file)).collect()
}

#[test]
fn a_user_effect_is_named_as_written_in_the_hints() {
    let out = errors(
        "effect Log2 { fn log2(msg: String) }\n\
         pub fn loud() { log2(\"x\") }\n\
         fn quiet() / par { log2(\"x\") }\n\
         pub fn std_log() { info(\"x\") }\n",
    );
    assert!(out.contains("must state its effects: `/ Log2`"), "{out}");
    assert!(out.contains("add `Log2` to the effects"), "{out}");
    assert!(out.contains("must state its effects: `/ log`"), "{out}");
    assert!(
        !out.contains("`/ log2`") && !out.contains("add `log2`"),
        "{out}"
    );
}

#[test]
fn a_linear_closure_says_that_it_needs_a_call() {
    let out = errors(
        "linear struct Tx { id: u64 }\n\
         fn rollback(t: Tx) { let Tx(i) = t }\n\
         fn ignore(f: fn()) {}\n\
         fn f() { let t = Tx { id: 1 }\n ignore(|| rollback(t)) }\n",
    );
    assert!(
        out.contains(
            "error[W0601]: a closure moves a linear value, but it can go out of scope without a call"
        ),
        "{out}"
    );
}

#[test]
fn a_place_field_with_no_value_is_named() {
    let out = errors(
        "struct Frame: !Move { buf: [u8; 4], cur: &u8 in self.buf[] }\n\
         fn f() { let fr = Frame { buf: [1, 2, 3, 4] }\n print(fr.cur) }\n",
    );
    assert!(
        out.contains("error[W0304]: `fr.cur` is used before it has a value"),
        "{out}"
    );
}

#[test]
fn a_match_names_the_type_that_it_does_not_cover() {
    let out = errors("fn f(o: Option<u64>) -> u64 { match o { Some(x) => x } }\n");
    assert!(
        out.contains("error[W0120]: this `match` does not cover every value of `Option<u64>`"),
        "{out}"
    );
}

#[test]
fn the_loop_iterator_is_named_in_w0503() {
    let out = errors(
        "effect Choice { multi fn choose() -> bool }\n\
         fn f(xs: &[u64] @ uniq) / Choice { for x in xs[] { let b = choose() } }\n",
    );
    assert!(
        out.contains("error[W0503]: the loop iterator is not `many`"),
        "{out}"
    );
}

#[test]
fn a_literal_names_its_range() {
    let out = errors("fn f() { let x: u8 = 256\n let y: i8 = -129 }\n");
    assert!(out.contains("`256` does not fit in `u8`"), "{out}");
    assert!(out.contains("`-129` does not fit in `i8`"), "{out}");
}

/// Facts with one variable and a chain of `n` nodes.
fn chain(n: usize, edit: impl FnOnce(&mut VarInfo)) -> (FnFacts, VarId, Vec<NodeId>) {
    let mut f = FnFacts {
        name: "t".into(),
        ..FnFacts::default()
    };
    let mut info = VarInfo::plain("x", VarKind::Local, Span::default(), "T");
    edit(&mut info);
    let v = f.add_var(info);
    let nodes: Vec<NodeId> = (0..n)
        .map(|_| f.add_node(Span::default(), "n", ""))
        .collect();
    for w in nodes.windows(2) {
        f.cfg_edge.push((w[0], w[1]));
    }
    (f, v, nodes)
}

#[test]
fn use_before_set_needs_a_value_on_every_path() {
    // n0 declares x; n1 uses it: W0304.
    let (mut f, v, n) = chain(3, |_| {});
    f.unset_at.push((v, n[0]));
    f.uses.push((v, n[1]));
    let r = check(&f);
    assert!(r.violations.use_before_set.contains(&(v, n[1])));
    assert_eq!(
        r.violations,
        bridge::check_spec(&f).expect("spec evaluates")
    );
    // A value at n1 comes before the use at n2.
    let (mut f, v, n) = chain(3, |_| {});
    f.unset_at.push((v, n[0]));
    f.rebound_at.push((v, n[1]));
    f.uses.push((v, n[2]));
    let r = check(&f);
    assert!(r.violations.use_before_set.is_empty());
    assert_eq!(
        r.violations,
        bridge::check_spec(&f).expect("spec evaluates")
    );
}

#[test]
fn overwrites_of_a_live_linear_value_are_errors() {
    // n0 gives x a value; n1 gives a part of it a new value while it is live.
    let (mut f, v, n) = chain(3, |i| i.linear = true);
    f.rebound_at.push((v, n[0]));
    f.overwrites.push((v, n[1]));
    f.moved_at.push((v, n[2]));
    let r = check(&f);
    assert!(r.violations.overwritten.contains(&(v, n[1])));
    assert_eq!(
        r.violations,
        bridge::check_spec(&f).expect("spec evaluates")
    );
    // After a move, a new part loses nothing.
    let (mut f, v, n) = chain(3, |i| i.linear = true);
    f.rebound_at.push((v, n[0]));
    f.moved_at.push((v, n[1]));
    f.overwrites.push((v, n[2]));
    let r = check(&f);
    assert!(r.violations.overwritten.is_empty());
    assert_eq!(
        r.violations,
        bridge::check_spec(&f).expect("spec evaluates")
    );
}

#[test]
fn a_part_holder_is_named_by_its_part() {
    let out = errors(
        "struct Wrap<T> { x: T }\n\
         fn f(v: &Vec<u64>) / mut(v) { let w = Wrap { x: &v[0] }\n w.x = &v[1]\n v.clear()\n print(w.x) }\n",
    );
    assert!(
        out.contains("error[W0301]: the value in `w.x` used after it was invalidated"),
        "{out}"
    );
}

#[test]
fn a_name_bound_twice_is_named() {
    let out = errors("fn f() { let (a, a) = (1, 2) }\n");
    assert!(
        out.contains("error[W0107]: `a` is bound twice in this pattern"),
        "{out}"
    );
}

#[test]
fn a_generic_drop_names_the_argument() {
    let out = errors(
        "linear struct Tx { id: u64 }\n\
         fn drop_it<T>(a: T, n: u64) {}\n\
         fn keep_first<T>(a: T, b: T) -> T { a }\n\
         fn rollback(t: Tx) { let Tx(i) = t }\n\
         fn f() { let t = Tx { id: 1 }\n drop_it(t, 1) }\n\
         fn g() { let t = Tx { id: 1 }\n let u = Tx { id: 2 }\n rollback(keep_first(t, u)) }\n",
    );
    assert!(
        out.contains("error[W0601]: linear value `t` is dropped without being consumed"),
        "{out}"
    );
    // Two parameters of the type: the diagnostic cannot name one of them.
    assert!(
        out.contains("error[W0601]: linear value `temporary` is dropped without being consumed"),
        "{out}"
    );
}

#[test]
fn a_linear_operand_across_an_abort_is_named() {
    let out = errors(
        "linear struct Tok { id: u64 }\n\
         fn spend(a: Tok, b: Tok) { let Tok(i) = a\n let Tok(j) = b }\n\
         fn risky() -> Tok / fail { fail(\"no\")\n Tok { id: 2 } }\n\
         fn f() / fail { spend(Tok { id: 1 }, risky()) }\n",
    );
    assert!(
        out.contains(
            "error[W0602]: linear value `argument` is live across `risky`, which can abort"
        ),
        "{out}"
    );
}
