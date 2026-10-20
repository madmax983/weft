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
  rules of the spec, so a new rule of these relations needs no edit. The node of the
  evidence of W0301 must also reach the use as the rules of `invalid(R, Q)` say: on a
  path of `cfg_edge`, with no new value of the reference after that node.

## Consequences

- Each diagnostic that a spec rule derives has a derivation: `weft check --explain`
  prints it with the diagnostic that it explains. A diagnostic holds the keys of the
  spec facts that it reports (`Diagnostic::facts`), and the corpus test
  `each_violation_has_one_diagnostic` checks that each violation has one diagnostic.
  A key holds the index of its body (`bridge::body_key`): two bodies can have the
  same name (functions of two modules, or two tests), and sema gives equal bodies
  equal ids. Other diagnostics have no derivation.
- Each check of places, modes, effects and tasks is a rule of the spec, except the
  checks below. Review S5b (F8) moved these checks from sema and the driver to the
  spec: W0203 (`arg_outside`, with `inside_stated`), W0406 (`not_uniq`), W0705
  (`arg_effect_outside`), W0802 (`sim_in_lib`), W0803 (`embedded_effect`), W0805
  (`unhandled_effect`), and the stated-place forms of W0204 and W0605 (`ref_outside`,
  with `inside_stated`). Sema gives their input facts (`arg_at`, `param_in`,
  `uniq_param`, `arg_aliased`, `fn_arg_effect`, `param_effect`, `sim_run_at`,
  `started()`, `no_runtime()`, `std_effect`, `ref_at`, `ref_in`). For a closure that
  runs where a captured local must be `@ uniq`, sema gives `uniq_param` at each node
  that runs the closure, and `arg_aliased` only where the local is not `@ uniq`, so
  the rule decides W0406 there too. A node of `sim_run_at`, `ref_at` and `ref_in` has
  no edges: only its rule reads it.
- These checks stay in sema, or in the CLI and the package loader, for these
  reasons:
  - Names, types and signatures: W01xx (with W0107 for a dependency name that hides
    another name and W0116 for raw pointers), W0201, W0119 (contradictory modes in a
    type), W0120 (patterns that miss a value), the `fip` checks, and the W0605 of a
    struct declaration (a reference field of a struct that is not `!Move`, or a field
    whose place is not in `self`). They look at types, declarations and the syntax
    tree, not at the places, modes or effects of a body.
  - W0303 (a move out of a borrowed place) looks at the type of the place: a place
    behind a reference cannot give its value away. It needs no flow.
  - W0502 in sema (`keep_modes`): a `once` closure goes into a place of plain data,
    such as a field of type `fn()`. It compares the mode of a value with the type of
    its target where sema unifies the two types, as W0102 does. The other form of
    W0502, a `once` closure that runs twice, is `use_after_move` in the spec.
  - W0504: a clause of `Fail.fail` resumes or names its continuation. Sema finds it
    in the syntax tree of the clause, as W0315 does.
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
  - W0204 has more forms than the stated place. A reference into a root that ends
    at an exit leaves through that exit: a local, a by-value parameter or a temporary
    of the function at a return; a local of a closure or of a clause at its return; a
    store behind a reference parameter or into an `rc` object; the value of a
    `handle`. And a returned reference must state its place (a signature check).
    The facts have no relation for the value that leaves at each exit, or for the
    roots that end there, and sema knows these only after the body (the places of
    operation results, `op_refs`). These forms can move when the facts get such
    relations. The stated-place form moved, because it is the check of W0203.
  - W0701 compares the signature that a public function infers with the signature
    that it states. The inferred row is in the places of the signature
    (`summary_to_sig`), and the inference over the call graph gives it. The facts
    of a body name the places of the body, and the spec has no relation for the
    signature of a body.
  - W0704, W0706 and W0707 report the state of the inference and of the lowering,
    not a rule of a body.
  - The CLI reports unknown file markers (W0804), and the package loader reports
    W0901 and W0902. They look at the files and the manifest.
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
  link each derivation to it. A violation whose site the facts do not give
  (`ArgSite`, `RefSite`) still gets an error, with the fact as its text.
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
