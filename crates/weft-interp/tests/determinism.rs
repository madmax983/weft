//! Property test: the same seed always gives the same output and trace.

#![allow(clippy::unwrap_used, clippy::expect_used, missing_docs)]

use std::fs;
use std::path::Path;

use proptest::prelude::*;
use weft_interp::{run_main, run_tests, RunOptions};
use weft_sema::Options;

fn program(name: &str) -> String {
    let p = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/programs")
        .join(format!("{name}.wf"));
    fs::read_to_string(p).unwrap()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]

    #[test]
    fn same_seed_same_run(seed in any::<u64>(), workers in 1usize..6) {
        let opts = RunOptions { seed, workers, max_steps: Some(2_000_000), ..RunOptions::default() };
        for name in ["cancel_sibling", "steal", "scope_join", "timeout", "fork", "preempt"] {
            let c = weft_check::check_source(name, &program(name), Options::default());
            let a = run_main(&c, &opts).unwrap();
            let b = run_main(&c, &opts).unwrap();
            prop_assert_eq!(&a, &b);
            // Every task that spawned also finished.
            let spawned = a.trace.iter().filter(|e| matches!(e, weft_interp::TraceEvent::Spawn { .. })).count();
            let finished = a.trace.iter().filter(|e| matches!(e, weft_interp::TraceEvent::Finish { .. })).count();
            prop_assert_eq!(spawned + 1, finished);
        }
        let c = weft_check::check_source("sim", &program("sim"), Options::default());
        let a = run_tests(&c, &opts);
        let b = run_tests(&c, &opts);
        prop_assert_eq!(a, b);
    }
}

/// The order inside `sim.run` depends only on its seed and its number of
/// simulated workers, not on `--seed` or `--workers` of the run (ADR 0010).
#[test]
fn simulation_order_does_not_depend_on_the_run() {
    let c = weft_check::check_source("sim_workers", &program("sim_workers"), Options::default());
    let base = run_tests(&c, &RunOptions::default());
    assert!(base.iter().all(|t| t.passed));
    for seed in [0, 1, 2, 7] {
        for workers in [1, 2, 3, 8] {
            let opts = RunOptions {
                seed,
                workers,
                ..RunOptions::default()
            };
            let out: Vec<String> = run_tests(&c, &opts)
                .into_iter()
                .map(|t| t.outcome.stdout)
                .collect();
            let want: Vec<String> = base.iter().map(|t| t.outcome.stdout.clone()).collect();
            assert_eq!(out, want, "seed {seed}, workers {workers}");
        }
    }
}
