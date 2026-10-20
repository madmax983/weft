# Traceability

This matrix connects each rule of `docs/design.md` and each guarantee of the ADRs to the
parts that enforce it: the spec rule in `spec/weft.dl`, the check in sema
(`crates/weft-sema`), the part of the reference interpreter (`crates/weft-interp`), the
tests and the proofs. It is plan item W10.

How to read it:

- **Spec** names the sink relation of `spec/weft.dl` and its code. The production
  checker (`crates/weft-check/src/rules.rs`) has the same rule. The agreement tests
  compare the two on every corpus body and on random fact sets, with the evidence of
  W0301 and W0405 (ADR 0002). `weft check --explain` prints the derivation of each
  violation, linked to its diagnostic.
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
Review stage S5b brought it up to date. The last sections list the round 2 changes, the
S5b and S5c changes and the round 3 changes. The section "Core IR acceptance targets"
lists the rules that stay open until the core IR, with a target file for each one. The
corpus numbers are unique (`corpus_numbers_are_unique`); S5b gave new numbers to four
files that shared a number (`52_raw_pointers`, `53_overwritten`, `54_stealable`,
`55_alias_in_one_task`).

## Places and mutation (design: "Places and mutation", ADR 0003)

| Rule | Spec | Sema | Interp | Tests | Proof | Status |
| --- | --- | --- | --- | --- | --- | --- |
| A reference type includes its place | `points_into`; `arg_outside` (W0203) and `ref_outside` (W0204 with a stated place, W0605), with `inside_stated` | `arg_at`, `param_in` at a call (`body/call.rs`); `ref_at`, `ref_in` at a return and a place field (`body/stmt.rs`, `body/expr.rs`); the other forms of W0204 at a return and a store (`body/stmt.rs`, `body/oprefs.rs`, `body/expr.rs`) | references are a cell and a path (`heap.rs`) | 12, 35, 73, 91, 95, 101, 110, 116, 117 | `places::within` (verified) for W0203, W0204 and W0605 | yes; the forms of W0204 with a root that ends stay in sema (ADR 0002) |
| A function declares the places that it mutates | `unauthorized_mut` (W0703) | the signature rows (`program.rs`), inference (`infer.rs`) | none | 13, 20, 28, 100 | none | yes |
| `mut(p)` invalidates strictly inside `p`, through an unstable step | `invalidated_at` (rule 3) | `mutates_at` facts, step stability from the type (`props.rs`, `program.rs`) | oracle: a freed cell, a moved `Vec` buffer | 01, 02, 30, 35, 76 | `places::invalidates` (verified); link L1 `thm_lkills_implies_invalidates`, `thm_invalidates_exact_typed`; borrowing B1, B3 | yes |
| References to `p` and into stable parts survive | the same rule | the same facts | none | 01, 30 | `lemma_no_self_invalidation`, `lemma_stable_suffix_survives` | yes |
| The use of an invalidated reference is an error | `error` (W0301) | `uses`, `rebound_at`, `cfg_edge` (`body/`) | oracle: dangling references, dead locals | 02, 05, 05b, 37, 76, 100, 101 | `dataflow::propagate` (verified); link L2 `thm_w0301_no_ub` (hypotheses `facts_ok`, `bound_before_use`) | yes; `ret_ok` is false for the `in` form (`proofs/link/README.md`) |
| A move or the end of an owner frees what it owns | `frees_at`, `owner`, `moved_part`; a move of a part invalidates each reference that overlaps the part (`invalidated_at` with `overlaps`) | `body/drops.rs`, `body/stmt.rs` | `heap.rs` `end_cell`, `drop_value`; an abort path ends the cells of the frames that it unwinds (`end_cell_value`) | 29, 31, 32, 34, 127, 152 | none | yes; a reference to the whole value is invalid after a part move, also for a read of another part (ADR 0003) |
| The value of a frame leaves it after the end of the frame | the facts of the tail move and of the hidden variable (`error`, `use_after_move`, `task_conflict`, `abort_unhandled`) | `frame_value_start`, `frame_value_end` (`body/stmt.rs`): the tail of a scope body, a handled body and a clause moves inside the frame; the temporaries of these frames end at their end; a `multi` handled body moves its tail in each run (`handled_again`) | a scope body, a handled body and a clause are code frames of their own | 150, 151 | none | yes (round 3, O3-1, O3-14, O3-2, O3-3) |
| A value is not used after a move | `use_after_move` (W0302) | `moved_at` | fault "used after it was moved"; oracle: a display of a moved value | 04, 04b, 110, 127, 150 | none | yes |
| A place gets a value before a use | `use_before_set` (W0304, one error for each variable) | `unset_at`, `empty_at`; the place fields of each full type (`Lower::place_paths`) | fault "used before it has a value" | 75, 89, 112, 154 | none | yes |
| Arguments of one call do not alias a mutated argument | `alias_conflict` (W0312) | `call_mut`, `call_arg` (`body/call.rs`) | none | 12, 38, 41, 55 | `places::overlaps` (verified) | yes; the `in` form allows the alias (ADR 0005) |
| Places and `mut` are inferred in bodies and stated in public signatures | `unauthorized_mut` | W0701 (`body/stmt.rs`), `infer.rs` | none | 13, 28, 43, 90 | `places::within` (verified) | yes; a row with only pass-through parameters has nothing to state (90) |
| `mut(w..)` means anywhere inside `w` | `wild_at` | `mut(p..)` is `mut(p)` plus held places (`program.rs`) | none | 35, 102, 103 | `lemma_deeper_mutation_weaker` | yes |
| Roots: a local, a parameter, a global | the roots of the facts | locals, parameters, `rc` groups | none | 01 | none | no globals in Phase 1 (ADR 0003) |
| The facts of sema are complete | none | `body/` | none | the sema unit tests, the corpus diagnostics, `crates/weft-check/tests/hypotheses.rs` (`bound_before_use`, `no_gen_kill`) | none | tested only (`proofs/README.md`) |

## Modes and threads (design: "Modes and threads", ADR 0006)

| Rule | Spec | Sema | Interp | Tests | Proof | Status |
| --- | --- | --- | --- | --- | --- | --- |
| A shared-mutable reference is nonportable | `shared_mut_capture` (W0403), `pinned` | `body/tasks.rs`, `body/caps.rs`; `VarInfo::capture_mode` | a pinned task stays on its worker | 03, 03b, 130, 131, 133 | `modes::{submode, join}` (verified) | yes |
| `fork` and stealable closures are portable | `nonportable_capture` (W0401), `stealable` | the mode marks of captures (`body/caps.rs`) | `is_stealable`; oracle: a stealable task that reaches an `Rc`, a `Weak` or a `Scope` | 03, 03b, 52, 54, 133, 134, 137; `steal` | `modes::{submode, join}` (verified): the join of the capture modes must cross threads | yes |
| Data that several threads see is `shared` or split `uniq` | W0403, W0405 | `body/tasks.rs` | oracle: the race detector | 03, 03b, 08 | B4 `task_soundness` proves a reference-based rule | partial: reads from several threads need no `shared` (ADR 0006) |
| One mode on each axis; `uniq` and `shared` contradict | none | W0119 (`program.rs`) | none | 50 | none | yes |
| `@ shared` is read-only | `shared_mutation` (W0402) | `body/` | none | 03, 03b, 28, 37, 111 | none | a callback of a higher-order function (ADR 0005) |
| A `@ uniq` parameter gets a unique reference | `not_uniq` (W0406) | `uniq_param`, `arg_aliased` (`body/call.rs`, `body/late.rs` for a closure that runs later) | none | 12, 74, 91, 111 | `modes::submode` (verified) | yes |
| Mode crossing for plain data | the mode flags of the facts | `props.rs`; the uniqueness of a join (`weft_facts::join_uniq`) | none | 03, 03b | `modes::{submode, join}` (verified, used by the checker and sema) | implicit |

## Linear and immovable types (design: "Linear and immovable types", ADR 0007)

| Rule | Spec | Sema | Interp | Tests | Proof | Status |
| --- | --- | --- | --- | --- | --- | --- |
| A linear value is consumed on each normal path | `unconsumed`, `overwritten` (W0601); a move of a part with a linear rest does not end the value (`rest_linear`, `ends_linear`) | `rebound_at`, `moved_at`, `empty_at`, `overwrites`, `rest_linear` (`body/drops.rs` `rest_linear`) | `lifecycle::Linear`; oracle: a linear leak | 04, 04b, 53, 72, 88, 126, 127, 150, 153 | `lifecycle::Linear` (verified); link L3 `consume_linked` | yes; a `Vec` of linear values has no consumer, and a move of an element leaves the other elements (ADR 0007) |
| Live across an abort only with `on abort` | `abort_unhandled` (W0602), also for a linear value that moves into a task where it starts (`spawned_at`, `moved_at`, and a linear capture of the task, `captures`) | `may_abort` (also at the end of a scope that can have a child), `spared_at`, `unwound_at`; `props.rs`: `Task<T>` passes the lack of `on abort` on from `T` | the unwinder (`machine/effects.rs`): the values of the frames, the cells of a closure, the captures of a task (also one that a cancel stops before it starts), and the results of tasks and fork branches that are done | 04, 04b, 37, 63, 124, 151, 153, 161, 162, 163; `abort_closure_cells`, `abort_block_cells`, `abort_task_captures`, `abort_task_result`, `abort_fork_result`, `abort_fork_fail_result`, `abort_cancelled_start`, `abort_handle_late`, `abort_handle_kept`, `abort_handle_given`, `interrupt_nested_unwind`, `abort_paths_on_every_seed` | effects E3 `lemma_capture_rules`; link L3 `unwind_linked` | yes; open until the core IR: a spawn whose handle is not kept, a `fork` with a linear branch value with no `on abort`, a generic body that holds a `Task<T>` across an abort, a generic body whose task closure or fork branch takes a value of a type parameter (ADR 0007) |
| `on abort` runs only in unwinding, with the root handlers | none | W0118 (`program.rs`): the effects; the parameter type with the type parameters of the function in order; no type parameter in `drops` or `holds`; no result that can be linear; no change below a reference that the value holds | `run_on_abort` | 120, 160; `abort_on_abort`, `clause_abort` | effects model: `on abort` is atomic | yes (ADR 0007) |
| No linear value or unique borrow is live across `multi` | `live_across_multi` (W0503) | `multi_at`, `clause_multi`, `body_multi` | a `multi` resume copies the frames | 05, 05b, 39, 124, 125; `multi_choose`, `multi_heap`, `multi_nested_drop` | effects E5 `lemma_capture_rules` | yes |
| A `!Move` value keeps its address | `moved_immovable` (W0604) | `body/stmt.rs` | a cell never moves (`heap.rs`) | 11, 73 | none | yes |
| Only a `!Move` struct holds a reference, and only into `self` (self-referential structs) | `ref_outside` (W0605) for a new value of the field and a struct literal | W0605 for the declaration (`program.rs`); `ref_at`, `ref_in` (`body/stmt.rs`, `body/expr.rs`) | none | 11, 73, 95 | `places::within` (verified) | yes |
| A struct has a finite size | none | W0117 (`program.rs`) | none | 50 | none | yes |
| Task handles are linear | `unconsumed` | the prelude `Task<T>` | the handle is a `Linear` | 14 | none | yes |

## Effects and handlers (design: "Effects and handlers", ADR 0005)

| Rule | Spec | Sema | Interp | Tests | Proof | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Rows after `/`, inferred in bodies, stated in public signatures | `unauthorized_effect` (W0702) | W0701, `infer.rs`, W0704, W0706 | none | 05, 05b, 09, 13, 18, 90 | none | yes |
| A function argument stays inside the row of its parameter type | `arg_effect_outside` (W0705) | `fn_arg_effect`, `param_effect` (`body/call.rs`): a closure, a function item, or a function value whose type states a row | none | 13, 91 | none | yes |
| An effect of another module has a path (`handle a.Note`, `/ util.Note`) | none | `effects::resolve`, W0101 for an unknown or a private effect | `compile.rs` `effect_of` | 141; `effect_paths`; `crates/weft-cli/tests/units.rs` | none | yes (round 2, RR11) |
| Each effect has one identity | the identities in the facts | `effects::identity`; W0107 for a dependency `main` | the same identities | 64, 141; `shadow_log`; `units.rs` | none | yes (round 2, QA5) |
| A bare call reaches its operation | none | `Program::find_op`; W0107 for an operation that a prelude or built-in name hides, and for an ambiguous bare call | the same `find_op` | 142 | none | yes (round 2, RR15) |
| Handlers are lexical | none | the handler stack of the lowering | `find_handler` (the topmost frame) | 05, 05b, 64; `effects_log`, `shadow_log` | effects E4 | yes |
| A perform is a call with the footprint of the handler | `mutates_at` from `performs_at` and `footprint`; `call_arg` (W0312) | `body/call.rs` `perform_op`; W0301 shows the footprint | none | 05, 05b, 41, 85, 86 | borrowing B2 (`resume` and `perform` as calls) | yes |
| Effect polymorphism is silent | none | `infer.rs`; no W0701 for a pass-through row | none | 18, 90 | none | yes |
| Continuations are `once` by default | `use_after_move` of the continuation (W0501) | `body/call.rs` `resume` | `lifecycle::Continuation` | 05, 05b; `once_twice` | `lifecycle::Continuation` (verified); effects E2; link L3 `resume_linked` | yes |
| A continuation does not leave its clause | none | W0313, W0314 | the record ends with its clause | 62, 122 | effects rule 3 | yes; W0313 and W0314 stay in sema (ADR 0002) |
| A clause of `fail` cannot resume | none | W0504 | none | 121 | none | yes |
| Dependency authority | none | none | none | `units.rs`, `tests/packages/hidden`, `w0901_says_that_only_standard_effects_need_authority` | none | `weft-cli` `package.rs` (W0901, W0902); only the standard effects need authority |
| A user effect of a dependency needs a handler of the caller | none | the caller names it with a path (`pub` effects only) | none | `units.rs` | none | yes (round 2, RR11) |

## Memory, runtime and concurrency (design: "Memory without a garbage collector", "Concurrency and the async runtime", ADRs 0003, 0006, 0010)

| Rule | Spec | Sema | Interp | Tests | Proof | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `rc` groups: a mutation through a clone is `mut(group)` | `invalidated_at` on group roots | the group roots, handle places (`body/`) | counted cells (`heap.rs`); `leaked_rc` | 20, 33, 87, 116; `rc_cycle` | none | yes |
| `fip` functions update in place | none | W1001 to W1004 (`fip.rs`) | none | 16, 23, 49 | none | yes |
| A GC pointer is a stable step; libraries never need the GC | the step stability of `extern type` | `props.rs`, `program.rs`; W0902 (`weft-cli`) | none | 13; `crates/weft-cli/tests/cli.rs` | none | yes; no GC tier in Phase 1 (ADR 0001) |
| Only binaries and tests install root handlers; an intercept forwards | `root_handler_in_lib` (W0801), `sim_in_lib` (W0802) | `handler`, `clause_performs`, `sim_root`, `sim_run_at` | none | 15, 40, 92 | none | yes |
| `main` and the tests handle each effect that is not standard | `unhandled_effect` (W0805) | `started()`, `std_effect` (`lib.rs`, `body/stmt.rs`) | fault "no handler" | 51, 93; `root_handlers` | none | yes |
| The no-runtime profile | `embedded_effect` (W0803) | `no_runtime()` | `RunOptions::no_runtime` | 19, 19b, 93; `no_runtime_marker`, `task_fail_embedded` | none | yes |
| Scopes are the only way to spawn; children cannot outlive the scope | `joined_at` at the scope end | W0115, `body/tasks.rs` | `scope_wait`, the unwinder cancels children | 07, 14, 61, 132, 150; `scope_join`, `scope_abort` | none | yes |
| Cancellation runs `on abort` | W0602 at scope starts and ends, joins and calls, and at a spawn or a `fork` that moves a linear value into the task | `may_abort`, `spawned_at`, `moved_at` | `check_interrupt`: a cancel waits while an unwinding or an `on abort` function runs (`Machine::defers`), and a failure of a child of a scope below the unwinding waits too (`Machine::live_base`); the unwinder, also for the captures of a task that never started | 63, 131, 151, 161, 163; `cancel_sibling`, `timeout`, `abort_cancelled_start`, `abort_task_captures`, `interrupt_cancel_on_abort`, `interrupt_scope_fail_on_abort`, `interrupt_inside_on_abort` | none | yes |
| A `with_timeout` deadline aborts its block at a suspension point | none | the `raises` part (W0118) | `Machine::expired`, a set of the deadlines that passed; `late_timeout` times out the outermost block on the stack above the innermost unwinding; a block below an unwinding waits for its end, and a block of an `on abort` function times out at once (`Machine::live_base`) | `timeout`, `timeout_continuation`, `timeout_same_deadline`, `timeout_advance`, `interrupt_timeout_on_abort`, `interrupt_inside_on_abort`, `interrupt_clause_value`, `interrupt_wait_clause_value` | none | yes (ADR 0010) |
| Tasks that can run at one time have separate footprints | `task_conflict` (W0405) | `task_reads`, `task_writes`, `spawned_at`, `joined_at` | oracle: the race detector logs each read and write, also a read through a reference in an operand or a callee, with no limit on the records of a cell | 08, 100, 102, 106, 130, 150 | B4 `task_soundness` (reference-based, ADR 0006) | yes |
| Preemption at back-edges | none | none | `Op::BackEdge` | `preempt` | none | yes |
| Work stealing follows the modes | `stealable` | the mode marks | `is_stealable` | 54, 134; `steal` | `modes::{submode, join}` (verified) | yes |
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
| Raw pointers only in foreign signatures, locals and closure parameters | none | W0116 | none | 52 | none | yes |
| Nesting and chain limits; the tools run on a 2 MiB stack | none | none | none | `crates/weft-cli/tests/limits.rs` | none | yes |

## The checker, the spec and the proofs (ADRs 0002, 0004, 0008)

| Guarantee | Where | Tests | Proof | Status |
| --- | --- | --- | --- | --- |
| The checker equals the spec on the facts | `rules.rs` and `spec/weft.dl` | `crates/weft-check/tests/programs.rs` (each corpus body), `agreement_random.rs` | none | yes |
| The evidence of W0301 and W0405 is a derivation of the spec, one for each violation | `crates/weft-check/src/evidence.rs` (probe rules from the spec; the node of W0301 reaches the use as `invalid` says) | the corpus agreement, `evidence_agrees_with_spec`, `each_invalid_use_has_the_first_evidence` (all gen nodes), the evidence unit tests | none | yes (S5b, F7) |
| The diagnostic is the derivation (design: "What the checker rejects") | `Diagnostic::facts`, `bridge::fact_key`, `bridge::body_key` (the key holds the body); `weft check --explain` and `--json` | `each_violation_has_one_diagnostic` (with corpus 94, two bodies with one name), `the_facts_of_two_bodies_with_one_name_have_two_keys`, `explain_links_each_derivation_to_its_diagnostic`, `json_notes_keep_their_lines`, `a_violation_with_no_site_is_still_an_error` | none | yes (S5b, F13); the checks of ADR 0002 that stay in sema have no derivation |
| Each check of places, modes, effects and tasks is a rule of the spec | `spec/weft.dl` | `the_spec_has_the_sinks_and_inputs_of_the_bridge`, `the_rules_of_the_codes_are_the_sinks_of_the_spec` | none | partial: the forms of W0204 with a root that ends, W0313, W0314, W0315, W0502 for a place of plain data, W0504 and W0701 stay in sema, with the reasons in ADR 0002 |
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

## Review S5b changes

| Finding | Change | Record |
| --- | --- | --- |
| F8 | W0203, W0406, W0705, W0802, W0803, W0805 and the stated-place forms of W0204 and W0605 (`ref_outside`) are rules of the spec, with input facts from sema; the other forms of W0204, W0313, W0314, W0315, W0502 for a place of plain data, W0504 and W0701 stay in sema | ADR 0002, `spec/weft.dl`, corpus 91, 92, 93, 95 |
| F9 | the checker and sema use `modes::{submode, join}` for W0401, W0403, W0406, `pinned` and the uniqueness of joined values, branch states and closure captures | ADRs 0004, 0006, `crates/weft-verified/README.md` |
| F7 | the agreement compares the evidence with the spec, also the reach of the node of W0301 to the use; a guard for the sinks and inputs of the bridge | ADR 0002 |
| F13 | W0301 at a perform, or at a call that performs, shows the footprint of the handler; JSON notes keep their lines; each derivation names the diagnostic of its own body; no W0701 for a row with only pass-through parameters | `docs/architecture.md`, corpus 90, 94 |
| Diagnostics | W0704 names each inferred part (`infer::PARTS`); one W0304 for each variable, with a note for each later read in a clause; W0801, W0702, W0803 and W0805 name the standard effect when a user effect has its name; W0901 says that only standard effects need authority | ADRs 0002, 0005 |
| Corpus | unique numbers for each program | `corpus_numbers_are_unique` |

## Review S5c changes

| Finding | Change | Record |
| --- | --- | --- |
| QR4 | `weft_sema::on_large_stack` runs analysis, the checker and the interpreter on one thread with a 256 MiB stack; function types use `Arc`, so `Analysis` and `Checked` are `Send` and `Sync`; `weft_sema::on_current_stack` keeps them on the thread of the caller, so a test shows that 2 MiB is sufficient | `docs/architecture.md`, `limits.rs` (`the_library_has_its_own_stack`, `pipeline`), `the_current_stack_has_no_new_thread` |
| W0301 cost | W0301, W0302 and W0304 search the part of the graph that can reach the uses from the first gen node (`rules::part_of`, `rules::ranks`), with the verified propagation in the part; references into one list of places share their witnesses, and references with the same witness nodes share a search of the whole graph (`Ctx::whole`) | `docs/architecture.md`, `scale.rs` (`each_cause_checks_in_linear_work`, `long_lived_references_check_in_linear_work`), `agreement_random.rs` (`shared_witnesses_agree_with_spec`) |
| QR15, QR16 | types show the names of the definitions with no copy; sema borrows signatures, bodies, effects and type shapes; a struct literal finds its missing fields in the set of given ones; a `handle` looks only at its own calls, operation arguments, resumes and clause edges, and at the locals with a `sticky` capability | `scale.rs` (`many_locals_check_in_time` in a release build, `many_locals_check`) |
| QR17 | index types for functions, modules, effects and types (`weft_sema::ids`); an enum for diagnostic codes (`weft_syntax::diag::Code`); the roots of call places (`body::roots`, also `roots::TASK`) and the ids of split sides have ranges of their own; a stored value that a function value at a call is known to be has the root of that value there (`Reach::known`) | ADR 0005, corpus 143 |
| QR19 | one `local_ty`, one `multi_node` for each effect, no unused method or silenced value; `handle`, `call_value`, `perform_op` and `assign` split into parts | `docs/architecture.md` |
| QR22 | a proptest mutates corpus programs, also the modes of their functions, and checks them on a 2 MiB thread, with the agreement of the checker and the spec | `crates/weft-check/tests/mutations.rs` |
| Coverage | each module of `weft-sema` and `weft-check` has 85% or more of its lines covered (`cargo llvm-cov`) | `ids.rs` tests |

## Review round 3 changes (stage R3a)

| Finding | Change | Record |
| --- | --- | --- |
| O3-13, F3-9 | the race detector logs a read through a reference in an operand or a callee (`Machine::deref_value`); with the oracle, a display of a moved value or through a dangling reference is a fault; an abort path ends the cells of the frames that it unwinds | ADR 0010; `guards.rs` (`the_oracle_reports_what_the_stock_machine_lets_pass`, `the_oracle_accepts_reads_after_a_join_and_an_unwound_frame`) |
| I3-12 | the race detector keeps the last access of each task, path and kind, with no limit | ADR 0010; `oracle.rs` (`a_race_after_many_accesses_is_found`) |
| Q3-5 | the clock asserts of three tests become counts of work or a test that runs only in a release build | `tests.rs` (`step_facts_of_a_wide_struct_are_linear`), `props.rs` (`a_wide_recursive_type_is_fast`), `limits.rs` (`explain_folds_a_long_derivation_in_time`) |
| O3-1, O3-14 | the tail of a scope body and of a handled body moves at the tail, inside the frame; a scope or a `handle` in statement position drops its value; a `multi` handled body moves its tail in each run | ADRs 0003, 0005; corpus 150 |
| O3-2, O3-3, F3-7 | a hidden variable holds the value of a scope body, a handled body and a clause across the end of the frame; the temporaries of these frames end at their end; a temporary of a clause that `resume` gives ends at the end of the `handle`; the end of a scope that can have a child can abort | ADRs 0003, 0006; corpus 151 |
| F3-5 | a move of a part invalidates each reference that overlaps the part | `spec/weft.dl`, ADR 0003; corpus 152 |
| R3RT1 | `rest_linear(V, P)`: a move of a part that leaves a linear part does not end the value (`ends_linear`), for W0601 and W0602 | `spec/weft.dl`, ADRs 0003, 0007; corpus 153 |
| Q3-1, Q3-4 | the place fields of each full type, in a table: a second use of a generic definition with other arguments is walked; a type that cannot hold a place field is not walked; a recursive struct or enum whose cycle is on the way stops the search with a path that stands for each place field below it, also for a type that grows at each depth; each type is walked once for each set of cycles on the way; a type with more than 64 paths gets one path for each part | ADR 0007; corpus 154; `scale.rs` (`place_fields_of_a_deep_type_are_found_in_linear_work`, also cyclic, mutually recursive and growing types); `props.rs` (`place_fields_and_cycles_of_the_definitions`) |

### Review of stage R3a

| Finding | Change | Record |
| --- | --- | --- |
| place fields of a recursive type (the search did not stop on `Nest<T> { next: Option<Box<Nest<Box<T>>>> }`, gave no path below a recursion, and was exponential on a cycle) | the search of Q3-1 above; an assignment of a new value gives its place fields hidden variables, and `None` has none; a `let` or an assignment that moves a value uses its place fields (W0304) | ADR 0007; corpus 154 |
| R3RT1 shapes | a move of a field of a `linear` struct or enum leaves the shell; a clause that moves a part of a capture leaves the rest at each node that runs the clause (`Summary::rest_captures`); the drop check of a generic body (`dropped_params`, `held_params`) does not end a value at a move that leaves a rest | ADR 0007; corpus 153 |
| a task handle in a frame tail in statement position | a moved-out frame value with a task handle is dropped as `{ h }` is (W0601) | ADR 0003; corpus 150 |
| O3-13 shapes | the race detector logs the test of a literal pattern and a copy of a part in a destructure through a reference; the log drops the records of a joined task that each task that can still run sees | ADR 0010; `guards.rs`; `oracle.rs` (`the_log_forgets_a_joined_task_that_each_task_sees`) |
| diagnostic texts | the destructure hint follows the type (a tuple, a struct, or no consumer for a `Vec`); a closure that captures a local of a scope body names the local; W0602 at the end of a scope says that a task can fail; a temporary of a scope body or a clause ends at the end of that frame | `diagnose.rs` |

## Review round 3 changes (stage R3x)

| Finding | Change | Record |
| --- | --- | --- |
| F3-4 | the parameter of an `on abort` function has the type with the type parameters of the function in order (W0118) | ADR 0007; corpus 160 |
| F3-3 | an `on abort` function with a type parameter in `drops` or `holds`, or with a result that can be linear, is W0118 | ADR 0007; corpus 160 |
| F3-1 | an `on abort` function whose parameter type holds a reference cannot change its parameter (W0118): the row cannot show a change of the value apart from a change through the reference | ADR 0007; corpus 160 |
| F3-6, O3-4, I3-1 | `Task<T>` has `on abort` for W0602 only if `T` has no linear part or has `on abort` (`props.rs`); a spawn whose handle is not kept, a `fork` with linear branch values and a `join` of a linear result that can abort stay open until the core IR (`tests/ir_targets/f3_6_task_results.wf`) | ADR 0007; corpus 162 |
| F3-8 | W0602 at a spawn or a `fork` for each linear value with no `on abort` that moves into the task: a scope can cancel the task before it runs | `spec/weft.dl`, `rules.rs`, `diagnose.rs`, `codes.rs`, ADRs 0006, 0007; corpus 161 |
| I3-2 | the unwinder finishes the cells of a closure (`ClosureVal::owned`), the captures of a task (`CodeFrame::owned`, also before the task starts), the result of a task that is done when its handle unwinds, the results of the children at the unwind of a scope or a `fork` and at a failed `fork`; a task whose handle the unwinder finished finishes its own value | ADR 0010; `abort_*` programs; `abort_paths_on_every_seed` |
| I3-3 | an unwinding defers the interrupts of its task (a cancel, a deadline, a failure of a child) until it ends; the outer unwinder finishes the value that an inner unwinding gives | ADR 0010; `interrupt_*` programs |
| I3-4 | a set of the deadlines that passed (`Machine::expired`), not one interrupt slot for each task; a deadline is not lost when the block goes into a continuation after `sim.clock.advance` | ADR 0010; `timeout_same_deadline`, `timeout_advance` |

## Review of stage R3x

| Finding | Change | Record |
| --- | --- | --- |
| block cells | a call of a closure that moved its captures takes them into cells of its frame (`take_captures`), as a task does; the unwinder finishes them also when no local holds the closure, as for the block of `with_timeout` | ADR 0010; `abort_block_cells` |
| kept handle | the unwind of a scope takes only the results of tasks whose handle was dropped, used or finished, not of a task whose live handle left the frames that unwind (`Heap::handle_dropped`) | ADR 0010; `abort_handle_kept`, `abort_handle_given` |
| deferral | an unwinding defers only the interrupts of the frames below it; a deadline of a block and a failure of a child of a scope that an `on abort` function runs hold at once (`Machine::live_base`) | ADR 0010; `interrupt_inside_on_abort` |
| F3-8 run nodes | W0602 for a task start asks that the closure of the task captures a linear variable with no `on abort`, so a block or a closure that consumes its value and then spawns into an outer scope is clean | `spec/weft.dl`, `rules.rs`, `diagnose.rs`, `codes.rs`, ADRs 0006, 0007; corpus 163 |
| generic gaps | a generic body whose task closure or fork branch takes a value of a type parameter, and one that holds a `Task<T>` across an abort, stay open until the core IR | ADRs 0006, 0007 |

## Core IR acceptance targets

The core IR replaces the fact generation of `crates/weft-sema/src/body/`. Each row is a
realistic blocker of review round 3 whose fix is in the fact generation. Its file in
`tests/ir_targets` has bad cases (`fn bad_NAME()`) that the checker accepts today and
that fault at run time, controls that the checker finds today, and clean cases that
its test blocks run. The markers give the correct result. The test `ir_targets` of
`weft-check` expects the checker to miss at least one marker in each file and to give no
error with no marker. When the checker reports each marker, that test fails, and the
file moves to `tests/programs`. The test `ir_targets` of `weft-interp` makes sure that
each bad case faults, that each clean case runs clean with the oracle for each seed and
worker count that it tries, and that each marker is in a function that a bad case
reaches.

| Rule | Finding | File | Status |
| --- | --- | --- | --- |
| A by-reference binding of a `match` whose type holds references gets the held places of the part, as a field read through a reference does, also when the binding leaves the arm or the arm changes the places after the binding (W0301, W0312; ADR 0003) | R3RT2 | `tests/ir_targets/r3rt2_match_through_ref.wf` | open: the checker does not enforce it yet |
| A caller adds the places that the references behind a reference argument point into to `call_arg`, to the reads of the call node and to the reads of a task that makes the call, for a call of an item, a function value or a closure (W0312, W0405; ADR 0003) | R3RT3 | `tests/ir_targets/r3rt3_held_refs_at_call.wf` | open: the checker does not enforce it yet |
| A place that a callee lends to a closure or a clause, and that the caller cannot name, gets a root of its own; a hidden variable owns it and goes out of scope right after the call, or at the end of the `handle` on the abort path; a store of it behind a reference parameter or into an `rc` object is W0204 for a closure and a clause; also through a function value, a nested higher-order call and a nested perform (W0301, W0204; ADRs 0003, 0005) | F3-2 | `tests/ir_targets/f3_2_callee_local_refs.wf` | open: the checker does not enforce it yet |
| A spawn whose handle is not kept drops `T` (W0601 at the spawn, or where a plain linear value in the same position gets it: an `if`, a block, a loop body, a closure call, the body of the scope; W0602 at the scope for a linear `T` with no `on abort`; `T` in `drops` in a generic body); a `fork` that can abort needs `on abort` for each linear type of a branch value (W0602 at the `fork`); a `join` that can abort needs `on abort` for a linear `T` (W0602 at the `join`) (ADRs 0006, 0007) | F3-6 (O3-4, I3-1) | `tests/ir_targets/f3_6_task_results.wf` | open: the checker does not enforce it yet |
| A run of a function value that can be a closure stored in a place (a field, an element or a part, also behind a reference, in a `Box`, or in a value that a callee returns) writes and reads what each closure stored there writes and reads; a task or a fork branch has this footprint, also when its callee reads the closure from a container behind a reference parameter (W0405, W0301; ADRs 0005, 0006) | O3-5 | `tests/ir_targets/o3_5_field_closure_tasks.wf` | open: the checker does not enforce it yet |
| A place through an `Rc` handle also reads the handle place, also in the reads of a task, so a move, a new value or the end of the scope of the handle (also in a loop body), or a move or a new value of the field or the value that holds it, conflicts with the task (W0405; ADR 0003) | O3-6 | `tests/ir_targets/o3_6_rc_handle_tasks.wf` | open: the checker does not enforce it yet |
