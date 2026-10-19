//! The text of diagnostics: messages and notes.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use weft_check::check_source;
use weft_sema::Options;
use weft_syntax::diag::Diagnostic;

/// Checks a program and returns its diagnostics with one code.
fn diags(src: &str, code: &str) -> Vec<Diagnostic> {
    check_source("t.wf", src, Options::default())
        .diags
        .into_iter()
        .filter(|d| d.code == code)
        .collect()
}

fn notes(d: &Diagnostic) -> Vec<&str> {
    d.notes.iter().map(|n| n.text.as_str()).collect()
}

#[test]
fn w0702_names_a_user_effect_as_written() {
    let src = "effect Log2 { fn log2(msg: String) }\nfn quiet() / par { log2(\"x\") }\n";
    let d = diags(src, "W0702");
    assert_eq!(d.len(), 1);
    assert_eq!(
        d[0].message,
        "`log2` performs `Log2`, which the signature does not allow"
    );
    assert_eq!(
        notes(&d[0]),
        ["add `Log2` to the effects after `/`, or handle it here"]
    );
    // A standard effect has a lowercase alias.
    let d = diags("fn quiet() / par { log.info(\"x\") }\n", "W0702");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(
        notes(&d[0]),
        ["add `log` to the effects after `/`, or handle it here"]
    );
}

#[test]
fn w0602_is_reported_once_for_each_value() {
    let src = "linear struct Lock { id: u64 }\nfn release(l: Lock) { let Lock(i) = l }\nfn risky() / fail { fail(\"no\") }\n\nfn f() / fail {\n    let l = Lock { id: 1 }\n    risky()\n    risky()\n    risky()\n    release(l)\n}\n";
    let d = diags(src, "W0602");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(
        d[0].message,
        "linear value `l` is live across `risky`, which can abort"
    );
    let n = notes(&d[0]);
    assert_eq!(n.len(), 3, "{n:?}");
    assert_eq!(n[2], "and 2 more sites that can abort, at lines 8, 9");
}

#[test]
fn w0602_lists_at_most_five_other_sites() {
    let mut src = String::from(
        "linear struct Lock { id: u64 }\nfn release(l: Lock) { let Lock(i) = l }\nfn risky() / fail { fail(\"no\") }\n\nfn f() / fail {\n    let l = Lock { id: 1 }\n",
    );
    src.push_str(&"    risky()\n".repeat(8));
    src.push_str("    release(l)\n}\n");
    let d = diags(&src, "W0602");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(
        notes(&d[0])[2],
        "and 7 more sites that can abort, at lines 8, 9, 10, 11, 12, ..."
    );
}

/// The prelude of the W0602 tests: a linear type with no `on abort`.
const LOCK: &str = "linear struct Lock { id: u64 }\nfn release(l: Lock) { let Lock(i) = l }\nfn risky() / fail { fail(\"no\") }\n\n";

#[test]
fn w0602_names_one_other_site_and_each_line_once() {
    let src = format!(
        "{LOCK}fn f() / fail {{\n    let l = Lock {{ id: 1 }}\n    risky()\n    risky()\n    release(l)\n}}\n"
    );
    let d = diags(&src, "W0602");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(notes(&d[0])[2], "and 1 more site that can abort, at line 8");
    // Three sites on one line, and one on the next line.
    let src = format!(
        "{LOCK}fn f() / fail {{\n    let l = Lock {{ id: 1 }}\n    risky(); risky(); risky()\n    risky()\n    release(l)\n}}\n"
    );
    let d = diags(&src, "W0602");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(
        notes(&d[0])[2],
        "and 3 more sites that can abort, at lines 7, 8"
    );
}

#[test]
fn w0503_is_reported_once_for_each_value() {
    let src = "effect Choice { multi fn choose() -> bool }\nlinear struct Token { id: u64 }\n    on abort = spend\nfn spend(t: Token) { let Token(i) = t }\nfn branchy() -> bool / Choice {\n    let t = Token { id: 1 }\n    let a = choose()\n    let b = choose()\n    let c = choose()\n    spend(t)\n    b\n}\n";
    let d = diags(src, "W0503");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(
        d[0].message,
        "`t` is not `many`, but it is live across `choose`, which can resume more than once"
    );
    let first = src.find("choose()\n").unwrap();
    assert_eq!(d[0].span.lo, u32::try_from(first).unwrap());
    assert_eq!(
        notes(&d[0])[1],
        "and 2 more operations that can resume more than once, at lines 8, 9"
    );
}

#[test]
fn w0302_is_reported_once_for_each_value() {
    let src =
        "fn moved(v: Vec<u32>) {\n    let w = v\n    print(v)\n    print(v)\n    print(v)\n}\n";
    let d = diags(src, "W0302");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(d[0].message, "`v` used after it was moved");
    assert_eq!(
        notes(&d[0])[1],
        "and 2 more uses after a move, at lines 4, 5"
    );
}

#[test]
fn w0301_is_reported_once_for_each_reference_and_mutation() {
    let src = "fn bad(v: &Vec<u32>) / mut(v) {\n    let r = &v[0]\n    v.push(1)\n    print(r)\n    print(r)\n    print(r)\n}\n";
    let d = diags(src, "W0301");
    assert_eq!(d.len(), 1, "{d:?}");
    let n = notes(&d[0]);
    assert_eq!(n[3], "used at line 4");
    assert_eq!(n[4], "and 2 more uses, at lines 5, 6");
    // Two mutations give two errors.
    let src = "fn bad(v: &Vec<u32>) / mut(v) {\n    let r = &v[0]\n    v.push(1)\n    print(r)\n    let r = &v[0]\n    v.push(2)\n    print(r)\n}\n";
    assert_eq!(diags(src, "W0301").len(), 2);
}

#[test]
fn w0301_is_reported_once_for_each_use_and_mutation() {
    // `w` and the hidden holder of `w.x` are invalid at one use for one
    // mutation: one error names `w`, and a note names the holder.
    let src = "struct Entity { hp: i32 }\nstruct World { entities: Vec<Entity> }\nstruct Wrap<T> { x: T }\nfn f(b: &World) / mut(b.entities) {\n    let w = Wrap { x: &b.entities[0] }\n    let e = &b.entities[0]\n    w.x = e\n    b.entities.clear()\n    print(w.x.hp)\n}\n";
    let d = diags(src, "W0301");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(d[0].message, "`w` used after it was invalidated");
    let n = notes(&d[0]);
    assert!(
        n.iter()
            .any(|t| t.starts_with("also the value in `w.x` : &Entity in b.entities[]")),
        "{n:?}"
    );
    // A stored closure and the reference to its holder, in one call: one error,
    // with no hidden name in braces.
    let src = "struct Entity { hp: i32 }\nstruct World { entities: Vec<Entity> }\nstruct Cb { f: fn() }\nfn run_ref(cb: &Cb) {\n    let g = cb.f\n    g()\n}\nfn stored_use(world: &World) / mut(world.entities) {\n    let r = &world.entities[0]\n    let cb = Cb { f: || print(r.hp) }\n    world.entities.clear()\n    run_ref(&cb)\n}\n";
    let d = diags(src, "W0301");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(d[0].message, "`cb` used after it was invalidated");
    let n = notes(&d[0]);
    assert!(
        n.iter()
            .any(|t| t.starts_with("also the stored closure : fn() -> ()")),
        "{n:?}"
    );
    assert!(n.iter().all(|t| !t.contains('{')), "{n:?}");
    // A closure with no name.
    let src = "fn twice(f: fn()) { f()\n f() }\nfn g() {\n    let v = Vec.new()\n    v.push(1)\n    let r = &v[0]\n    twice(|| { print(r + 1)\n v.clear() })\n}\n";
    let d = diags(src, "W0301");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(d[0].message, "the closure used after it was invalidated");
    // The iterators of two nested loops have different use nodes: two errors,
    // also though the span of the outer loop holds the inner loop.
    let src = "fn f(v: &Vec<u64>) / mut(v) {
    for x in v[] {
        for y in v[] {
            v.push(1)
        }
    }
}
";
    let d = diags(src, "W0301");
    assert_eq!(d.len(), 2, "{d:?}");
    // A callee that stores the closure and runs it two times: one error, from
    // the second run. The stored value is not there before the call.
    let src = "struct Wrap { f: fn() }
fn st(f: fn()) { let w = Wrap { f: f }
 let g = w.f
 g()
 g() }
fn g() {
    let v = Vec.new()
    v.push(1)
    let r = &v[0]
    st(|| { print(r + 1)
 v.clear() })
}
";
    let d = diags(src, "W0301");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(d[0].message, "the closure used after it was invalidated");
}

#[test]
fn the_public_diagnose_resolves_line_numbers() {
    // A library user calls `diagnose` on the facts of one body. The notes give
    // line numbers, not the offsets of the nodes.
    let src = "fn bad(v: &Vec<u32>) / mut(v) {\n    let r = &v[0]\n    v.push(1)\n    print(r)\n    print(r)\n}\n";
    let a = weft_sema::analyze_source(src, Options::default()).unwrap();
    let file = weft_syntax::SourceFile::new("t.wf", src);
    let mut texts = Vec::new();
    for b in a.bodies.iter().filter(|b| b.unit == weft_sema::ROOT_UNIT) {
        let r = weft_check::check(&b.facts);
        for d in weft_check::diagnose::diagnose(&b.facts, &r, &file) {
            texts.extend(d.notes.into_iter().map(|n| n.text));
        }
    }
    assert!(texts.iter().any(|t| t == "used at line 4"), "{texts:?}");
    assert!(
        texts.iter().any(|t| t == "and 1 more use, at line 5"),
        "{texts:?}"
    );
    assert!(
        texts
            .iter()
            .all(|t| !t.contains("line:") && !t.contains('\u{1}')),
        "{texts:?}"
    );
}

#[test]
fn w0501_is_reported_once_for_each_continuation() {
    let src = "effect Log { fn log(m: u64) }\nfn f() {\n    handle Log { fn log(m) {\n        resume(())\n        resume(())\n        resume(())\n    } } in log(1)\n}\n";
    let d = diags(src, "W0501");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(notes(&d[0])[1], "and 1 more resume, at line 6");
}

#[test]
fn w0805_needs_a_handler_for_each_effect_that_is_not_standard() {
    // A clause runs outside its own handler.
    let src = "effect Note { fn note(m: u64) }\nfn f() -> u64 {\n    handle Note { fn note(m) { note(m); resume(()) } } in { note(1) }\n    1\n}\nfn main() {\n    print(f())\n    print(f())\n}\n";
    let d = diags(src, "W0805");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(
        d[0].message,
        "`main` performs `Note`, and no handler handles it"
    );
    assert_eq!(
        notes(&d[0]),
        [
            "the runtime handles only the standard effects; handle `Note` in `main`",
            "and 1 more site, at line 8"
        ]
    );
    // A test block too.
    let src = "effect Note { fn note(m: u64) }\ntest \"noisy\" { note(1) }\n";
    let d = diags(src, "W0805");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(
        d[0].message,
        "test \"noisy\" performs `Note`, and no handler handles it"
    );
    // A handled effect and a standard effect need no handler.
    let src = "effect Note { fn note(m: u64) }\nfn main() / clock {\n    handle Note { fn note(m) { resume(()) } } in note(1)\n    sleep(1.ms)\n    log.info(\"x\")\n}\n";
    assert_eq!(diags(src, "W0805"), Vec::new());
    // Another function may let the effect escape.
    let src = "effect Note { fn note(m: u64) }\nfn other() { note(1) }\n";
    assert_eq!(diags(src, "W0805"), Vec::new());
    // A user effect with the name of a standard effect shows its identity.
    let src = "effect Log { fn log(m: u64) }\nfn main() { log(1) }\n";
    let d = diags(src, "W0805");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(
        d[0].message,
        "`main` performs `main.Log`, and no handler handles it"
    );
    // Two user effects with one name: each error shows the identity.
    let src = "effect Note { fn note(m: u64) }\nmod a {\n    pub effect Note { fn note(m: u64) }\n    pub fn f() / Note { note(2) }\n}\nfn main() {\n    note(1)\n    a.f()\n}\n";
    let d = diags(src, "W0805");
    let messages: Vec<&str> = d.iter().map(|d| d.message.as_str()).collect();
    assert_eq!(
        messages,
        [
            "`main` performs `main.Note`, and no handler handles it",
            "`main` performs `main.a.Note`, and no handler handles it"
        ]
    );
    assert_eq!(
        notes(&d[1]),
        ["the runtime handles only the standard effects; handle `main.a.Note` in `main`"]
    );
}

#[test]
fn w0803_and_w0805_tell_a_user_log_from_the_standard_log() {
    // With no runtime, `main` must handle the standard `Log` (W0803) and the
    // user `Log` (W0805). The user effect shows its identity.
    let src =
        "effect Log { fn log(m: u64) }\nfn main() / log {\n    log(1)\n    log.info(\"x\")\n}\n";
    let opts = Options {
        no_runtime: true,
        ..Options::default()
    };
    let d: Vec<Diagnostic> = check_source("t.wf", src, opts)
        .diags
        .into_iter()
        .filter(|d| d.code == "W0803" || d.code == "W0805")
        .collect();
    let messages: Vec<(&str, &str)> = d
        .iter()
        .map(|d| (d.code.as_str(), d.message.as_str()))
        .collect();
    assert_eq!(
        messages,
        [
            (
                "W0805",
                "`main` performs `main.Log`, and no handler handles it"
            ),
            ("W0803", "with no runtime, `main` must handle `Log` itself")
        ]
    );
}

#[test]
fn w0601_names_the_generic_item_value_and_the_type() {
    let src = "linear struct Tx { id: u64 }\n    on abort = rollback\nfn rollback(tx: Tx) { let Tx(i) = tx }\nfn begin() -> Tx { Tx { id: 1 } }\nfn sink<T>(x: T) {}\nfn feed_tx(x: Tx, f: fn(Tx)) { f(x) }\nfn feed<T>(x: T, f: fn(T)) { f(x) }\n\nfn typed() {\n    feed_tx(begin(), sink)\n}\nfn generic() {\n    feed(begin(), sink)\n}\n";
    let d = diags(src, "W0601");
    assert_eq!(d.len(), 2, "{d:?}");
    for x in &d {
        assert_eq!(x.message, "`sink` drops a value of the linear type `Tx`");
        assert_eq!(
            notes(x),
            ["`sink` can drop a value of its type parameter here; a linear value must be consumed on every normal path"]
        );
    }
}

#[test]
fn w0601_at_a_generic_drop_of_a_closure_says_that_the_closure_moves_a_linear_value() {
    let src = "linear struct Tx { id: u64 }\nfn rollback(tx: Tx) { let Tx(i) = tx }\nfn gen_drop<T>(x: T) {}\nfn closure_arg() {\n    let tx = Tx { id: 1 }\n    gen_drop(|| rollback(tx))\n}\n";
    let d = diags(src, "W0601");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(
        d[0].message,
        "a closure moves a linear value, but it can go out of scope without a call"
    );
}

#[test]
fn w0601_at_a_generic_drop_names_a_local_called_temporary() {
    // The name of the local, not a callee text: no name is a marker.
    let src = "linear struct Tx { id: u64 }\nfn sink<T>(x: T) {}\nfn named() {\n    let temporary = Tx { id: 1 }\n    sink(temporary)\n}\n";
    let d = diags(src, "W0601");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(
        d[0].message,
        "linear value `temporary` is dropped without being consumed"
    );
}
