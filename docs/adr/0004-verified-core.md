# ADR 0004: A verified core in Verus

Status: accepted. Date: 2026-10-18.

## Decision

- `crates/weft-verified` holds the code that decides the core rules: the place algebra,
  the gen/kill least fixpoint, the mode lattice, and the continuation and linear-value
  state machines.
- Verus verifies the crate. `cargo` compiles the same source: the `verus!` macro removes
  specs and proofs. So the proof is about the shipped code.
- `proofs/borrowing` and `proofs/effects` hold the soundness models (ADR 0008).

## Consequences

- CI runs Verus at a pinned revision (`proofs/VERUS_VERSION`).
- No `assume`, `admit` or `external_body` in verified code.
