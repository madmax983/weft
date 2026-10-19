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

- Each diagnostic that a spec rule derives has a derivation: `weft check --explain`
  prints it. Other diagnostics have no derivation. Sema reports names (with W0107 for
  a dependency name that hides another name), types (with W0116 for raw pointers),
  signatures, `in` places (W0203, W0204), moves out of a borrowed place (W0303),
  reference fields (W0605), patterns that miss a value (W0120), W0313, W0314, W0315,
  W0406, W0705, effect inference that does not become stable (W0704) or does not
  converge (W0706), W0802 and the `fip` checks. The driver reports W0803 and W0805. The
  CLI reports unknown file markers (W0804), and the package loader reports W0901 and
  W0902.
- W0120 checks a matrix of the arm patterns, with a budget of 20 000 steps for each
  `match`. A row that matches anything ends the check of its part at once, so a wide
  `match` with `_` in the other columns costs little. A `match` that needs more steps
  is W0120 too: the check cannot show that the arms cover each value.
- W0304 (`use_before_set`): `let x: T` with no value declares `x`. A use of `x` on a
  path with no assignment before it is W0304. A closure and a handler clause use what
  they capture where they are made. So an assignment inside a closure does not give
  `x` a value for the code after the closure. A compound assignment such as `x += 1`
  reads `x`. A place field of a `!Move` struct with no value works in the same way
  (ADR 0007).
- Agreement is over the facts that sema emits. It does not show that the facts are
  complete.
- A rule change needs all of these edits:
  1. the rule in `spec/weft.dl`;
  2. the rule in `crates/weft-check/src/rules.rs`;
  3. for a new sink relation, a field in `Violations` (`crates/weft-facts`);
  4. in `crates/weft-check/src/bridge.rs`: `each_fact` for a new input relation, and
     `violations()` and `VIOLATION_RELATIONS` for a new sink;
  5. the diagnostic in `crates/weft-check/src/diagnose.rs`;
  6. the code text in `crates/weft-check/src/codes.rs` (`weft explain`);
  7. a program in `tests/programs` with `//~ CODE` markers, with a bad case and a clean
     case;
  8. the generator of `crates/weft-check/tests/agreement_random.rs` for a new input
     relation.
- Tests find some missed edits: the agreement tests (on the corpus and on random facts),
  `corpus_exercises_every_rule` (each sink relation holds for some corpus body), and
  `every_code_in_the_sources_is_explained` (each code has a text).
