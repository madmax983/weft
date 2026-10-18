# ADR 0002: A Datalog specification and a specialized checker

Status: accepted. Date: 2026-10-18.

## Context

The design says the rules are a Datalog program, and that a fast checker must agree
with it. Polonius showed that a general engine is slow for Rust, but the model is good.

## Decision

- `spec/weft.dl` is the specification. Semantic analysis writes per-function facts
  (`crates/weft-facts`). The facts are not relational to compute; the rules are.
- `crates/weft-datalog` is our own engine. It loads rules at run time (for user lint
  rules) and records provenance (for derivation trees). Compile-time engines cannot do
  both.
- `crates/weft-check` implements each rule group with specialized code. It uses the
  verified place algebra and one verified gen/kill propagation (ADR 0004).
- Agreement is a test gate: on every corpus program and on random fact sets, the
  checker and the spec give equal violation sets.

## Consequences

- Each diagnostic has a derivation: `weft check --explain` prints it.
- A rule change needs three edits: the spec, the checker, and a test. The agreement
  tests find a missed edit.
