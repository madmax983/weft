# CLAUDE.md

Guide for agents that work in this repository.

## What this is

Weft Phase 1: a checker for places, modes and effects, specified in Datalog
(`spec/weft.dl`), with a Verus-verified core and a reference interpreter. Read
`README.md`, `docs/plan/phase1.md` and `docs/adr/` first.

## Rules

- TDD: spec rule, proof (core rules), failing test, implementation, refactor.
- A rule change needs all of these (ADR 0002):
  1. the rule in `spec/weft.dl`;
  2. the same rule in `crates/weft-check/src/rules.rs`;
  3. for a new sink relation, a field in `Violations` (`crates/weft-facts`);
  4. in `crates/weft-check/src/bridge.rs`: `each_fact` for a new input relation, and
     `violations()` and `VIOLATION_RELATIONS` for a new sink;
  5. the diagnostic in `crates/weft-check/src/diagnose.rs`;
  6. the code text in `crates/weft-check/src/codes.rs` (`weft explain`);
  7. a program in `tests/programs` with `//~ CODE` markers, with a bad case and a clean case;
  8. the generator in `crates/weft-check/tests/agreement_random.rs` for a new input relation.
  The agreement tests must pass.
- Facts: `crates/weft-facts`. Fact generation: `crates/weft-sema/src/body/`.
- Verified code (`crates/weft-verified`) must verify: no `assume`, `admit`,
  `external_body`. Run `proofs/verify-all.sh` (it also runs `proofs/link`, which includes
  the `weft-verified` sources).
- Comments and docs: ASD-STE100 Simplified Technical English. Short sentences.
- Before a commit: `cargo fmt --all`, `cargo clippy --workspace --all-targets -- -D warnings`,
  `cargo test --workspace`.
- No `unwrap()` in production code. No `unsafe`.

## Useful commands

```bash
cargo run -p weft-cli -- check --explain FILE    # diagnostics and derivations
cargo run -p weft-cli -- facts FILE FUNCTION     # facts in Datalog syntax
cargo run -p weft-cli -- agree FILE              # checker vs spec
cargo run -p weft-cli -- run FILE --seed 1       # run main in the interpreter
cargo run -p weft-cli -- test FILE               # run the test blocks
cargo test -p weft-check --test programs         # the corpus
cargo test -p weft-check --test agreement_random # random agreement
```
