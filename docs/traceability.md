# Traceability

This matrix connects each rule of `docs/design.md` and each guarantee of the ADRs to the
parts that enforce it: the spec rule in `spec/weft.dl`, the check in sema
(`crates/weft-sema`), the part of the reference interpreter (`crates/weft-interp`), the
tests and the proofs. It is plan item W10.

How to read it:

- **Spec** names the sink relation of `spec/weft.dl` and its code. The production
  checker (`crates/weft-check/src/rules.rs`) has the same rule. The agreement tests
  compare the two on every corpus body and on random fact sets (ADR 0002).
- **Sema** names the module that emits a code or the facts. A code that only sema
  emits has no spec rule.
- **Interp** names the run-time part. "Oracle" means the checks of
  `crates/weft-interp/src/oracle.rs` (ADR 0010), which the interpreter program tests
  and the corpus runs turn on.
- **Tests** names corpus programs (`tests/programs/NN_*.wf`, by number), interpreter
  programs (`crates/weft-interp/tests/programs/*.wf`, by name) and test files.
- **Proof** names a theorem of `proofs/` or a verified function of
  `crates/weft-verified`. "None" means that only tests cover the rule.
- **Status** says what is not enforced, with the ADR that records it.

The first version of this file came from section (1) of the fidelity review of round 2.
The last section lists the round 2 changes.

## Places and mutation (design: "Places and mutation", ADR 0003)

| Rule | Spec | Sema | Interp | Tests | Proof | Status |
| --- | --- | --- | --- | --- | --- | --- |
| A reference type includes its place | `points_into` | W0203 at a call (`body/call.rs`), W0204 at a return and a store (`body/stmt.rs`, `body/late.rs`) | references are a cell and a path (`heap.rs`) | 12, 35, 101, 110, 116, 117 | none | yes |
| A function declares the places that it mutates | `unauthorized_mut` (W0703) | the signature rows (`program.rs`), inference (`infer.rs`) | none | 13, 20, 28, 100 | none | yes |
| `mut(p)` invalidates strictly inside `p`, through an unstable step | `invalidated_at` (rule 3) | `mutates_at` facts, step stability from the type (`props.rs`, `program.rs`) | oracle: a freed cell, a moved `Vec` buffer | 01, 02, 30, 35, 76 | `places::invalidates` (verified); link L1 `thm_lkills_implies_invalidates`, `thm_invalidates_exact_typed`; borrowing B1, B3 | yes |
| References to `p` and into stable parts survive | the same rule | the same facts | none | 01, 30 | `lemma_no_self_invalidation`, `lemma_stable_suffix_survives` | yes |
| The use of an invalidated reference is an error | `error` (W0301) | `uses`, `rebound_at`, `cfg_edge` (`body/`) | oracle: dangling references, dead locals | 02, 05, 37, 76, 100, 101 | `dataflow::propagate` (verified); link L2 `thm_w0301_no_ub` (hypotheses `facts_ok`, `bound_before_use`) | yes; `ret_ok` is false for the `in` form (`proofs/link/README.md`) |
| A move or the end of an owner frees what it owns | `frees_at`, `owner`, `moved_part` | `body/drops.rs`, `body/stmt.rs` | `heap.rs` `end_cell`, `drop_value` | 29, 32, 127 | none | yes |
| A value is not used after a move | `use_after_move` (W0302) | `moved_at` | fault "used after it was moved" | 04, 110, 127 | none | yes |
| A place gets a value before a use | `use_before_set` (W0304) | `unset_at`, `empty_at` | fault "used before it has a value" | 75, 89, 112 | none | yes |
| Arguments of one call do not alias a mutated argument | `alias_conflict` (W0312) | `call_mut`, `call_arg` (`body/call.rs`) | none | 12, 34, 38, 41 | none | yes; the `in` form allows the alias (ADR 0005) |
| Places and `mut` are inferred in bodies and stated in public signatures | `unauthorized_mut` | W0701 (`body/stmt.rs`), `infer.rs` | none | 13, 28, 43 | none | yes |
| `mut(w..)` means anywhere inside `w` | `wild_at` | `mut(p..)` is `mut(p)` plus held places (`program.rs`) | none | 35, 102, 103 | `lemma_deeper_mutation_weaker` | yes |
| Roots: a local, a parameter, a global | the roots of the facts | locals, parameters, `rc` groups | none | 01 | none | no globals in Phase 1 (ADR 0003) |
| The facts of sema are complete | none | `body/` | none | the sema unit tests, the corpus diagnostics, `crates/weft-check/tests/hypotheses.rs` (`bound_before_use`, `no_gen_kill`) | none | tested only (`proofs/README.md`) |

## Modes and threads (design: "Modes and threads", ADR 0006)

| Rule | Spec | Sema | Interp | Tests | Proof | Status |
| --- | --- | --- | --- | --- | --- | --- |
| A shared-mutable reference is nonportable | `shared_mut_capture` (W0403), `pinned` | `body/tasks.rs`, `body/caps.rs` | a pinned task stays on its worker | 03, 130, 131, 133 | none | yes |
| `fork` and stealable closures are portable | `nonportable_capture` (W0401), `stealable` | the mode marks of captures (`body/caps.rs`) | `is_stealable`; oracle: a stealable task that reaches an `Rc`, a `Weak` or a `Scope` | 03, 31, 33, 133, 134, 137; `steal` | none | yes |
| Data that several threads see is `shared` or split `uniq` | W0403, W0405 | `body/tasks.rs` | oracle: the race detector | 03, 08 | B4 `task_soundness` proves a reference-based rule | partial: reads from several threads need no `shared` (ADR 0006) |
| One mode on each axis; `uniq` and `shared` contradict | none | W0119 (`program.rs`) | none | 50 | none | yes |
| `@ shared` is read-only | `shared_mutation` (W0402) | `body/` | none | 03, 28, 37, 111 | none | a callback of a higher-order function (ADR 0005) |
| A `@ uniq` parameter gets a unique reference | none | W0406 (`body/call.rs`) | none | 12, 74, 111 | none | yes |
| Mode crossing for plain data | the mode flags of the facts | `props.rs` | none | 03 | `modes::{submode, join}` (verified, not used) | implicit |

## Linear and immovable types (design: "Linear and immovable types", ADR 0007)

| Rule | Spec | Sema | Interp | Tests | Proof | Status |
| --- | --- | --- | --- | --- | --- | --- |
| A linear value is consumed on each normal path | `unconsumed`, `overwritten` (W0601) | `rebound_at`, `moved_at`, `empty_at`, `overwrites` | `lifecycle::Linear`; oracle: a linear leak | 04, 32, 72, 126, 127 | `lifecycle::Linear` (verified); link L3 `consume_linked` | yes |
| Live across an abort only with `on abort` | `abort_unhandled` (W0602) | `may_abort`, `spared_at`, `unwound_at` | the unwinder (`machine/effects.rs`) | 04, 37, 63, 124 | effects E3 `lemma_capture_rules`; link L3 `unwind_linked` | yes |
| `on abort` runs only in unwinding, with the root handlers | none | W0118 (`program.rs`) | `run_on_abort` | 120; `abort_on_abort`, `clause_abort` | effects model: `on abort` is atomic | yes (ADR 0007) |
| No linear value or unique borrow is live across `multi` | `live_across_multi` (W0503) | `multi_at`, `clause_multi`, `body_multi` | a `multi` resume copies the frames | 05, 39, 124, 125; `multi_choose`, `multi_heap`, `multi_nested_drop` | effects E5 `lemma_capture_rules` | yes |
| A `!Move` value keeps its address | `moved_immovable` (W0604) | `body/stmt.rs` | a cell never moves (`heap.rs`) | 11, 73 | none | yes |
| Only a `!Move` struct holds a reference, and only into `self` (self-referential structs) | none | W0605 | none | 11, 73 | none | yes |
| A struct has a finite size | none | W0117 (`program.rs`) | none | 50 | none | yes |
| Task handles are linear | `unconsumed` | the prelude `Task<T>` | the handle is a `Linear` | 14 | none | yes |

## Effects and handlers (design: "Effects and handlers", ADR 0005)

| Rule | Spec | Sema | Interp | Tests | Proof | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Rows after `/`, inferred in bodies, stated in public signatures | `unauthorized_effect` (W0702) | W0701, `infer.rs`, W0706 | none | 05, 09, 13, 18 | none | yes |
| An effect of another module has a path (`handle a.Note`, `/ util.Note`) | none | `effects::resolve`, W0101 for an unknown or a private effect | `compile.rs` `effect_of` | 141; `effect_paths`; `crates/weft-cli/tests/units.rs` | none | yes (round 2, RR11) |
| Each effect has one identity | the identities in the facts | `effects::identity`; W0107 for a dependency `main` | the same identities | 64, 141; `shadow_log`; `units.rs` | none | yes (round 2, QA5) |
| A bare call reaches its operation | none | `Program::find_op`; W0107 for an operation that a prelude or built-in name hides, and for an ambiguous bare call | the same `find_op` | 142 | none | yes (round 2, RR15) |
| Handlers are lexical | none | the handler stack of the lowering | `find_handler` (the topmost frame) | 05, 64; `effects_log`, `shadow_log` | effects E4 | yes |
| A perform is a call with the footprint of the handler | `mutates_at` from `performs_at` and `footprint`; `call_arg` (W0312) | `body/call.rs` `perform_op` | none | 05, 41, 85, 86 | borrowing B2 (`resume` and `perform` as calls) | yes |
| Effect polymorphism is silent | none | `infer.rs` | none | 18 | none | yes |
| Continuations are `once` by default | `use_after_move` of the continuation (W0501) | `body/call.rs` `resume` | `lifecycle::Continuation` | 05; `once_twice` | `lifecycle::Continuation` (verified); effects E2; link L3 `resume_linked` | yes |
| A continuation does not leave its clause | none | W0313, W0314 | the record ends with its clause | 62, 122 | effects rule 3 | yes |
| A clause of `fail` cannot resume | none | W0504 | none | 121 | none | yes |
| Dependency authority | none | none | none | `units.rs`, `tests/packages/hidden` | none | `weft-cli` `package.rs` (W0901, W0902) |
| A user effect of a dependency needs a handler of the caller | none | the caller names it with a path (`pub` effects only) | none | `units.rs` | none | yes (round 2, RR11) |

## Memory, runtime and concurrency (design: "Memory without a garbage collector", "Concurrency and the async runtime", ADRs 0003, 0006, 0010)

| Rule | Spec | Sema | Interp | Tests | Proof | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `rc` groups: a mutation through a clone is `mut(group)` | `invalidated_at` on group roots | the group roots, handle places (`body/`) | counted cells (`heap.rs`); `leaked_rc` | 20, 33, 87, 116; `rc_cycle` | none | yes |
| `fip` functions update in place | none | W1001 to W1004 (`fip.rs`) | none | 16, 23, 49 | none | yes |
| A GC pointer is a stable step; libraries never need the GC | the step stability of `extern type` | `props.rs`, `program.rs`; W0902 (`weft-cli`) | none | 13; `crates/weft-cli/tests/cli.rs` | none | yes; no GC tier in Phase 1 (ADR 0001) |
| Only binaries and tests install root handlers; an intercept forwards | `root_handler_in_lib` (W0801) | W0802 | none | 15, 40 | none | yes |
| `main` and the tests handle each effect that is not standard | none | the driver (`diagnose::root_effects`, W0805) | fault "no handler" | 51; `root_handlers` | none | yes |
| The no-runtime profile | none | W0803 (driver) | `RunOptions::no_runtime` | 19, 19b; `no_runtime_marker`, `task_fail_embedded` | none | yes |
| Scopes are the only way to spawn; children cannot outlive the scope | `joined_at` at the scope end | W0115, `body/tasks.rs` | `scope_wait`, the unwinder cancels children | 07, 14, 61, 132; `scope_join`, `scope_abort` | none | yes |
| Cancellation runs `on abort` | W0602 at scope ends, joins and calls | `may_abort` | `check_interrupt`, the unwinder | 63, 131; `cancel_sibling`, `timeout` | none | yes |
| Tasks that can run at one time have separate footprints | `task_conflict` (W0405) | `task_reads`, `task_writes`, `spawned_at`, `joined_at` | oracle: the race detector | 08, 100, 102, 106, 130 | B4 `task_soundness` (reference-based, ADR 0006) | yes |
| Preemption at back-edges | none | none | `Op::BackEdge` | `preempt` | none | yes |
| Work stealing follows the modes | `stealable` | the mode marks | `is_stealable` | 33, 134; `steal` | none | yes |
| Foreign calls are `blocking` | the effect rows | the extern default `Blocking` | the blocking pool | 09; `blocking` | none | yes |
| The simulation replaces the root handlers | none | `sim.run` (`body/call.rs`) | `machine/` simulation, lexical, with its own scheduler | 10, 135; `sim`, `sim_lexical`, `sim_tasks`, `sim_workers` | none | the network is not simulated (ADR 0010) |
| `main` gets the root capabilities through `env` | none | `Env { fs, net, stdout }` | `env_value` | 06 | none | the clock and the randomness come through the row (ADR 0005) |
| The result of arithmetic fits in its integer type | none | W0102 for a literal; `FnFacts::int_ops` | `Op::CheckInt` | 24; `int_width` | none | yes (round 2, RR14) |

## Syntax and names (ADR 0009, docs/grammar.md)

| Rule | Spec | Sema | Interp | Tests | Proof | Status |
| --- | --- | --- | --- | --- | --- | --- |
| A named argument binds by name where the callee has names | none | `body/args.rs` `order_args`; W0104, W0103 | `call_fn`, `positional_struct`, the order of `FnFacts::arg_order` | 65, 77, 135, 140; `named_args`, `op_named_args` | none | yes (round 2, RR10, RR13) |
| A callee with no names takes no named argument | none | `no_names` (W0104); `t.join` and `t.detach` take no argument (W0103) | none | 140 | none | yes (round 2, RR13) |
| Jumps do not leave a handled body, a clause or a scope | none | W0315, W0111 | none | 60, 80 | none | yes |
| Raw pointers only in foreign signatures, locals and closure parameters | none | W0116 | none | 31 | none | yes |
| Nesting and chain limits; the tools run on a 2 MiB stack | none | none | none | `crates/weft-cli/tests/limits.rs` | none | yes |

## The checker, the spec and the proofs (ADRs 0002, 0004, 0008)

| Guarantee | Where | Tests | Proof | Status |
| --- | --- | --- | --- | --- |
| The checker equals the spec on the facts | `rules.rs` and `spec/weft.dl` | `crates/weft-check/tests/programs.rs` (each corpus body), `agreement_random.rs` | none | yes |
| Each spec rule fires for a corpus body | `spec/weft.dl` | `corpus_exercises_every_rule` | none | yes |
| The exec core computes the spec functions | `crates/weft-verified` | its unit tests | Verus, 67 verified | yes |
| The exec core agrees with the models | `proofs/link` | `proofs/link/check-copies.sh` | Verus, 235 verified (B6) | gaps in `proofs/link/README.md` |
| Group borrowing is sound in its model | `proofs/borrowing` | `proofs/borrowing/mutations/run.sh` | B1 to B5, 169 verified | the model gaps in its README |
| Algebraic effects are sound in their model | `proofs/effects` | `proofs/effects/mutations/run.sh` | E1 to E5, 122 verified | the model gaps in its README |
| A documented mutation test for each theorem | `proofs/*/mutations/` | the three `run.sh` scripts | none | yes (round 2, FD15) |

## Round 2 changes

The review of round 2 (lenses redteam, quality, oracle, fidelity, interp) gave these
findings. Each row names the stage that changed the tree and where the change is
recorded.

| Finding | Change | Record |
| --- | --- | --- |
| QA10, FD14, QA4, RR1 (QA1), QA7, QA8, QA3, QA6, FD8, QA13 (R2a) | corpus counts, the loop fixpoint and its limit, quadratic paths, the order of `in` places, a write through a wildcard reference, rule r29 in the corpus | ADRs 0002, 0003 |
| OR2, RR7, RR12, OR1, OR3, RR2, FD3, QA11, QA12 (R2b) | captures by value at the closure, late captures, returned closures, repeated callbacks, references in `rc` objects, one W0301 for each use | ADRs 0003, 0005, 0006 |
| FD1 (QA2), FD2, FD4, FD9, FD13, RR3, RR5, RR6, RR8, RR9, OR4, OR6, OR9, IP1, IP4 (R2c) | the effects of `on abort` (W0118), copies of nested `multi` continuations, affine and `!Move` values at `multi`, continuations that leave a clause, `resume` frees, drops of `Vec.clear` and of generic items, `sim_root` | ADRs 0003, 0005, 0007; `proofs/effects/README.md` |
| OR5, OR7, OR8, RR4, IP2, IP3, IP5, IP6, IP7, IP9, IP10, IP11, OR10, FD11 (R2d) | whole-local accesses for W0405, task runs of function parameters, the scope capability, pinned tasks, lexical child failures, lexical simulation | ADRs 0003, 0006, 0010 |
| RR10, RR13 (R2e) | named arguments bind by name in sema and in the interpreter; W0104 for an unknown name and for a callee with no names | ADR 0009 |
| RR11 (R2e) | effect paths in `handle` and in rows, `pub` effects, hints with a name that the user can write | ADR 0005, `docs/grammar.md` |
| QA5, RR15 (R2e) | W0107 for a dependency `main`, for an operation that a prelude or built-in name hides and for an ambiguous bare call; `find_op` searches modules outward | ADR 0005 |
| RR14 (R2e) | the interpreter checks the integer type of each arithmetic result | ADR 0010 |
| OR11 (R2e) | the oracle checks in `weft-interp`, behind `RunOptions::oracle` and `--oracle`, on in the interpreter tests and the corpus runs | ADR 0010 |
| FD5, IP8 (R2e) | the proof READMEs say what tests the facts; `hypotheses.rs` runs the B6 lints on the corpus | `proofs/README.md`, `proofs/link/README.md` |
| FD6, FD7 (R2e) | the stale derivation printer sentence goes; the proof counts are the Verus counts | ADR 0009, `docs/grammar.md`, the proof READMEs |
| FD15 (R2e) | mutation scripts for `proofs/borrowing` and `proofs/effects` | ADR 0008 |
| FD12 (R2e) | this file | plan item W10 |
| QA9 (R2e) | `call_fn_as` and `diagnose` split into parts; a type of its own for the mode marks of a capability set | `docs/architecture.md` |
| Review of R2e | W0103 and W0104 for an argument of `t.join` and `t.detach`, which sema lowers; the portability oracle follows the place of a reference; W0107 only for an operation that a prelude or built-in name hides, and at an ambiguous bare call; a note for an effect that a nearer item hides; written effect names only for the effects of a body, and a map for `by_identity`; the mutation scripts need a Verus error count | ADRs 0005, 0008, 0009, 0010 |
