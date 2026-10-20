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
  checker and the spec give equal violation sets. The gate compares the evidence of
  the diagnostics too (`weft_check::evidence`, review S5b, F7): each `error(R, P)` has
  one piece of evidence and each `task_conflict(T, P)` one conflict, and each one is a
  derivation of the spec. A probe rule for each rule of `invalidated_at`, `frees_at`
  and `task_conflict` names the places of the derivation; the probes come from the
  rules of the spec, so a new rule of these relations needs no edit.

## Consequences

- Each diagnostic that a spec rule derives has a derivation: `weft check --explain`
  prints it with the diagnostic that it explains. A diagnostic holds the keys of the
  spec facts that it reports (`Diagnostic::facts`), and the corpus test
  `each_violation_has_one_diagnostic` checks that each violation has one diagnostic.
  Other diagnostics have no derivation.
- Each check of places, modes, effects and tasks is a rule of the spec, except the
  checks below. Review S5b (F8) moved these checks from sema and the driver to the
  spec: W0203 (`arg_outside`, with `inside_stated`), W0406 (`not_uniq`), W0705
  (`arg_effect_outside`), W0802 (`sim_in_lib`), W0803 (`embedded_effect`) and W0805
  (`unhandled_effect`). Sema gives their input facts (`arg_at`, `param_in`,
  `uniq_param`, `arg_aliased`, `fn_arg_effect`, `param_effect`, `sim_run_at`,
  `started()`, `no_runtime()`, `std_effect`).
- Sema reports names (with W0107 for a dependency name that hides another name),
  types (with W0116 for raw pointers), signatures (W0201), returned places (W0204),
  moves out of a borrowed place (W0303), reference fields (W0605), contradictory modes
  (W0119), patterns that miss a value (W0120), W0313, W0314, W0315, W0701, effect
  inference that does not become stable (W0704) or does not converge (W0706), a loop
  whose lowering does not become stable (W0707) and the `fip` checks. The CLI reports
  unknown file markers (W0804), and the package loader reports W0901 and W0902. These
  checks stay outside the spec for these reasons:
  - The checks of names, types and signatures (W01xx, W0201, W0303, W0605, W0119,
    W0120, W0701 and the `fip` checks) look at types, signatures and the syntax tree.
    They do not use the places, modes or effects of a body.
  - W0315 looks at the nesting of a `return`, `break` or `continue` in the syntax
    tree: the handled bodies, clauses and scope bodies around it. It uses no fact, as
    W0111 does not.
  - W0313 and W0314 are about the handler that a perform reaches. Sema finds it by
    the lexical scope, and it follows the capability set of each value
    (`caps::Held`) through locals, parts, closures, stores, callees and clauses, in
    the value flow that also gives `points_into`. The facts have no relation for
    these sets, so a rule of the spec would copy one input fact for each error and
    check nothing. They can move when the facts get relations for the capability
    sets of values.
  - W0204 compares each value that leaves a body with the places that the signature
    allows and with the roots that end there: a return, a store behind a reference
    parameter or into an `rc` object, the value of a closure or of a `handle`. The
    facts have no relation for a value that leaves the body, and the check has seven
    forms with their own texts. The form with a stated place is the check of W0203
    (`inside_stated`), so it can move with a fact for each return.
  - W0704, W0706 and W0707 report the state of the inference and of the lowering,
    not a rule of a body.
- W0120 checks a matrix of the arm patterns, with a budget of 20 000 steps for each
  `match`. A row that matches anything ends the check of its part at once, so a wide
  `match` with `_` in the other columns costs little. A `match` that needs more steps
  is W0120 too: the check cannot show that the arms cover each value.
- W0304 (`use_before_set`): `let x: T` with no value declares `x`. A use of `x` on a
  path with no assignment before it is W0304. A closure uses what it captures where it
  is made. A handler clause uses it at each node that runs the clause, and the
  diagnostic shows the read in the clause. So an assignment inside a closure does not
  give `x` a value for the code after the closure. A compound assignment such as
  `x += 1` reads `x`. A place field of a `!Move` struct with no value works in the same
  way (ADR 0007). Each variable gets one W0304, at its first use. A note lists the
  other uses, as for W0301 and W0602.
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
- The diagnostic of step 5 names the facts that it reports
  (`Diagnostic::with_facts`, `bridge::fact_key`), so that `weft check --explain` can
  link each derivation to it.
- Tests find some missed edits: the agreement tests (on the corpus and on random facts,
  also for the evidence), `the_spec_has_the_sinks_and_inputs_of_the_bridge` (each sink
  relation of the spec is in `VIOLATION_RELATIONS`, and the bridge emits each input
  relation), `each_violation_has_one_diagnostic`,
  `corpus_exercises_every_rule` (each rule of the spec fires, and each sink relation
  holds, for some corpus body: a probe rule with the body of each rule shows it),
  `every_code_in_the_sources_is_explained` (each code has a text) and
  `every_code_has_a_test` (a test names each code of the table).
- The corpus runner counts the errors. A marker `//~ W0601 W0601` expects two errors
  with that code on the line.
