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
fn w0501_is_reported_once_for_each_continuation() {
    let src = "effect Log { fn log(m: u64) }\nfn f() {\n    handle Log { fn log(m) {\n        resume(())\n        resume(())\n        resume(())\n    } } in log(1)\n}\n";
    let d = diags(src, "W0501");
    assert_eq!(d.len(), 1, "{d:?}");
    assert_eq!(notes(&d[0])[1], "and 1 more resume, at line 6");
}
