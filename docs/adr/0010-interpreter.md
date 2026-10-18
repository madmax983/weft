# ADR 0010: The reference interpreter

Status: accepted. Date: 2026-10-18.

## Decision

- `crates/weft-interp` runs checked programs on a machine with an explicit frame stack.
  A perform captures a delimited continuation. A `once` continuation uses the verified
  state machine `lifecycle::Continuation`.
- Unwinding runs `on abort` exactly once per live linear value (`lifecycle::Linear`).
- One deterministic scheduler with virtual workers. Work stealing obeys `stealable(T)`.
  Preemption happens at loop back-edges.
- `sim.run(seed)` replaces every root handler: virtual clock, seeded randomness,
  simulated network and scheduler. The same seed gives the same trace.

## Consequences

- The interpreter demonstrates the runtime design. It does not measure task density or
  native performance (Phase 2).
