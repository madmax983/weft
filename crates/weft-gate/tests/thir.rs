//! Test D0, part 1 (plan stage T3), on each program of tier 1: the THIR tables
//! that the old lowering records, against the syntax tree, the facts and the
//! final types (`weft_sema::thir::d0`).
//!
//! A debug build is slower than a release build, so a program can time out
//! here. The test skips a timeout as unknown, prints its path, and fails if
//! more than 1 % of the programs time out. `weft-gate thir --tier 1` runs the
//! same check with a release build.
//!
//! Set `WEFT_GATE_SKIP=1` to skip the test in a quick local loop.

use std::path::{Path, PathBuf};
use std::time::Instant;

use weft_gate::manifest::{self, Options};
use weft_gate::{pool, snapshot, thir};

fn repo() -> PathBuf {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    std::fs::canonicalize(&dir).unwrap_or(dir)
}

#[test]
fn d0_holds_on_tier1() {
    if std::env::var_os("WEFT_GATE_SKIP").is_some_and(|v| v == "1") {
        eprintln!("skipped: WEFT_GATE_SKIP=1");
        return;
    }
    let repo = repo();
    let m = manifest::build(
        &repo,
        &manifest::tier1_roots(),
        Options {
            exclude_copies: false,
        },
    )
    .unwrap_or_else(|e| panic!("the manifest cannot be built: {e}"));
    let total = m.entries.len();
    let workers = std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get);
    pool::install_panic_hook();
    let start = Instant::now();
    let sum = thir::run(&repo, m.entries, workers, snapshot::LIMIT, |_| {})
        .unwrap_or_else(|e| panic!("D0 cannot run: {e}"));
    let text = sum.to_markdown("tier 1");
    let out = repo.join("target/gate/thir-tier1.md");
    if let Some(dir) = out.parent() {
        std::fs::create_dir_all(dir).unwrap_or_else(|e| panic!("make {}: {e}", dir.display()));
    }
    std::fs::write(&out, &text).unwrap_or_else(|e| panic!("write {}: {e}", out.display()));
    eprintln!(
        "D0 on {total} programs of tier 1 in {:.1} s; summary in {}",
        start.elapsed().as_secs_f64(),
        out.display()
    );
    for p in &sum.timeouts {
        eprintln!("  unknown (a timeout of this build): {p}");
    }
    assert!(total > 3000, "tier 1 has {total} programs");
    assert!(
        sum.timeouts.len() * 100 <= total,
        "{} of {total} programs time out",
        sum.timeouts.len()
    );
    assert!(
        sum.counts.is_empty() && sum.crashes.is_empty(),
        "D0 fails on tier 1:\n{text}"
    );
    assert!(sum.checked * 10 > sum.bodies * 9, "{text}");
}
