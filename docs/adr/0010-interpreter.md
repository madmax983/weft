# ADR 0010: The reference interpreter

Status: accepted. Date: 2026-10-18.

## Decision

- `crates/weft-interp` runs checked programs on a machine with an explicit frame stack.
  A perform captures a delimited continuation. A `once` continuation uses the verified
  state machine `lifecycle::Continuation`.
- Unwinding runs `on abort` for each live linear value. `lifecycle::Linear` proves that a
  linear value is consumed or aborted at most once. That each live value is finished
  comes from the checker (W0601) and the unwinder, and is tested, not proved.
- One deterministic scheduler with virtual workers. Work stealing obeys `stealable(T)`.
  Preemption happens at loop back-edges.
- `sim.run(seed)` replaces every root handler: virtual clock, seeded randomness,
  simulated network and scheduler. The same seed gives the same trace.

- `weft run FILE` runs `fn main` and `weft test FILE` runs the test blocks, through
  `weft_interp::{run_main, run_tests}`. Both check the program first and do not run it
  if it has errors, unless `--unchecked` is given. `--seed` and `--workers` (1 to
  1024) set the scheduler. Errors and a failure give exit code 1; with `--unchecked`,
  the exit code shows only the run. The binary writes the output and the log of each
  test before its result line. A file with no test blocks gets a note.

## Consequences

- The interpreter demonstrates the runtime design. It does not measure task density or
  native performance (Phase 2).
