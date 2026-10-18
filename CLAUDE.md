# CLAUDE.md

Guide for agents that work in this repository.

## What this is

Weft Phase 1: a checker for places, modes and effects, specified in Datalog
(`spec/weft.dl`), with a Verus-verified core and a reference interpreter. Read
`README.md`, `docs/plan/phase1.md` and `docs/adr/` first.

## Rules

- TDD: spec rule, proof (core rules), failing test, implementation, refactor.
- A rule change needs: `spec/weft.dl`, `crates/weft-check/src/rules.rs`, and a program in
  `tests/programs` with `//~ CODE` markers. The agreement tests must pass.
- Facts: `crates/weft-facts`. Fact generation: `crates/weft-sema/src/body/`.
- Verified code (`crates/weft-verified`) must verify: no `assume`, `admit`,
  `external_body`. Run `verus crates/weft-verified/src/lib.rs --crate-type=lib`.
- Comments and docs: ASD-STE100 Simplified Technical English. Short sentences.
- Before a commit: `cargo fmt --all`, `cargo clippy --workspace --all-targets -- -D warnings`,
  `cargo test --workspace`.
- No `unwrap()` in production code. No `unsafe`.

## Useful commands

```bash
cargo run -p weft-cli -- check --explain FILE    # diagnostics and derivations
cargo run -p weft-cli -- facts FILE FUNCTION     # facts in Datalog syntax
cargo run -p weft-cli -- agree FILE              # checker vs spec
cargo test -p weft-check --test programs         # the corpus
cargo test -p weft-check --test agreement_random # random agreement
```
