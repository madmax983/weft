//! The checker stays fast on large functions.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use std::time::{Duration, Instant};

use weft_check::{check, check_source};
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
    // About 0.25 s in a debug build. The first checker took more than 30 s.
    assert!(time < Duration::from_secs(1), "{time:?}");
}
