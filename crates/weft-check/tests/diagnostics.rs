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
