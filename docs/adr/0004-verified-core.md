# ADR 0004: A verified core in Verus

Status: accepted. Date: 2026-10-18.

## Decision

- `crates/weft-verified` holds verified code for the core rules: the place algebra, the
  gen/kill least fixpoint, the mode lattice, and the continuation and linear-value state
  machines.
- What uses it now:
  - The checker (`rules.rs`) decides W0301, W0312, W0402, W0405 and W0703 with
    `places::{invalidates, within, overlaps}`, and every dataflow rule with
    `dataflow::propagate`. The bridge uses `places::{step_alias, step_within}`, and
    sema uses `places::within` for the `in` place checks.
  - The interpreter guards continuations with `lifecycle::Continuation` and linear
    values with `lifecycle::Linear`.
  - Not yet used: `modes::{bottom, submode, join}` and `places::concat`. The checker
    decides mode rules with flags in the facts (`nonportable`, `uniq`, `shared`), and
    sema substitutes signature places with its own code. A later stage can move these
    checks to the verified functions.
- Verus verifies the crate. `cargo` compiles the same source: the `verus!` macro removes
  specs and proofs. So the proof is about the shipped code.
- `proofs/borrowing` and `proofs/effects` hold the soundness models (ADR 0008).

## Consequences

- CI runs Verus at a pinned revision (`proofs/VERUS_VERSION`).
- No `assume`, `admit` or `external_body` in verified code.
