# ADR 0004: A verified core in Verus

Status: accepted. Date: 2026-10-18.

## Decision

- `crates/weft-verified` holds verified code for the core rules: the place algebra, the
  gen/kill least fixpoint, the mode lattice, and the continuation and linear-value state
  machines.
- What uses it now:
  - The checker (`rules.rs`) decides W0301, W0312, W0402, W0405 and W0703 with
    `places::{invalidates, within, overlaps}`, W0203 with `places::within`
    (`inside_stated`), and every dataflow rule with `dataflow::propagate`. The bridge
    uses `places::{step_alias, step_within}`, and sema uses `places::within` for the
    returned places of W0204.
  - The checker decides the mode rules with `modes::{bottom, submode, join}`: W0406
    and W0403 compare the uniqueness of a value with `uniq`, and W0401 and `pinned`
    compare the join of the modes of the captures of a task with the mode that crosses
    threads (`weft_facts::CROSSES_THREADS`). Sema joins the uniqueness of two values
    with `modes::join` (`weft_facts::join_uniq`) and finds pinned tasks with
    `modes::submode` (review S5b, F9).
  - The interpreter guards continuations with `lifecycle::Continuation` and linear
    values with `lifecycle::Linear`.
  - Not yet used: `places::concat`. Sema substitutes signature places with its own
    code.
- Verus verifies the crate. `cargo` compiles the same source: the `verus!` macro removes
  specs and proofs. So the proof is about the shipped code.
- `proofs/borrowing` and `proofs/effects` hold the soundness models (ADR 0008).

## Consequences

- CI runs Verus at a pinned revision (`proofs/VERUS_VERSION`).
- No `assume`, `admit` or `external_body` in verified code.
