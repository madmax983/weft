//! Runs the corpus over many seeds and worker counts. Programs whose output does
//! not depend on the schedule must print the same text for every seed.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

use std::fs;
use std::path::Path;

use weft_interp::{run_main, RunOptions};
use weft_sema::Options;

#[test]
fn schedule_independent_programs_agree_over_seeds() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs");
    for name in [
        "abort_on_abort",
        "cancel_sibling",
        "timeout",
        "fork",
        "multi_choose",
        "multi_heap",
        "steal",
        "scope_abort",
        "effects_log",
        "rc_cycle",
        "blocking",
    ] {
        let src = fs::read_to_string(dir.join(format!("{name}.wf"))).unwrap();
        let c = weft_check::check_source(name, &src, Options::default());
        let mut first: Option<String> = None;
        for seed in 0..40 {
            for workers in 1..5 {
                let opts = RunOptions {
                    seed,
                    workers,
                    quantum: 50 + seed * 7,
                    max_steps: Some(2_000_000),
                    ..RunOptions::default()
                };
                let out = match run_main(&c, &opts) {
                    Ok(o) => o.stdout,
                    Err(e) => panic!("{name} seed {seed} workers {workers}: {e}"),
                };
                match &first {
                    None => first = Some(out),
                    Some(f) => assert_eq!(f, &out, "{name} seed {seed} workers {workers}"),
                }
            }
        }
    }
}
