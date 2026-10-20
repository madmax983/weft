# Review round 2, lens "fidelity": spec and design fidelity

Commit: 328a39b (worktree `/home/user/wt-edge`, branch `review/r2`). I did not change the
worktree. I built `target/release/weft` there. All scratch files are in
`SCRATCH/r2/fidelity/`
(below: `FID/`). Each finding has a repro in `FID/repro/` (`FDn_*.wf` and `FDn_run.sh`).

## Summary

- 15 findings: 3 blockers, 2 majors, 10 minors.
- The three blockers come from part (3): rules that the proofs need, but the checker does
  not mirror. Two are model assumptions that no ADR records: `on abort` is atomic (FD1)
  and no reference is stored in the heap (FD3). One is a gap between the effects model
  and the interpreter for nested `multi` continuations (FD2).
- Agreement holds. `weft agree` agrees on every corpus, example and interpreter program,
  under each profile, on 8 041 mutated programs that parse, and on 11 997 programs of the
  oracle and red-team lenses. I found no disagreement and no crash.
- The proof claims hold. At the pinned Verus revision (`1888846b`): borrowing 169,
  effects 122, link 233, `weft-verified` 66, all with 0 errors. The 26 link mutations are
  all caught (17 "link only"), as `proofs/link/README.md` says. I re-ran two effects
  mutations; they give the documented result (121 verified, 1 error). No proof source has
  `assume`, `admit`, `external_body` or an axiom.
- Most claims in README.md, `docs/architecture.md`, the ADRs and the crate docs are true.
  The false ones are in FD5 (major), FD6, FD7, FD9 and FD13 (minor).
- The round-1 fixes hold (see the last section).

| Id | Severity | Short statement |
| --- | --- | --- |
| FD1 | blocker | The effects of an `on abort` function are not checked: a perform there has no handler, and a mutation there invalidates nothing |
| FD2 | blocker | Nested `multi` continuations share one exec record: an accepted program faults ("resumed after it was dropped") |
| FD3 | blocker | A reference stored into an `rc` object outlives its owner: no rule mirrors the "no stored references" assumption of the borrowing proof |
| FD4 | major | The multi rule does not count affine or `!Move` values; the interpreter copies them at each resume; no ADR records this |
| FD5 | major | `proofs/README.md` says that the agreement tests check the sema-fact hypotheses of the link; they do not |
| FD6 | minor | ADR 0009 says that the derivation printer recurses; it uses a stack |
| FD7 | minor | Per-module proof counts are stale (`places` 27, not 25; link `examples` 23, not 22) |
| FD8 | minor | No corpus program fires spec rule r29 (a lent wildcard place); the coverage test checks only sinks |
| FD9 | minor | The spec header gives `forwards(H)` a second meaning; a diagram shows a `task_writes → mutates_at` rule that the spec does not have |
| FD10 | minor | "`main` receives the root capabilities through `env`" has no enforcement and no ADR |
| FD11 | minor | Two design statements have no enforcement and no ADR: `@ shared` for data that several threads see, and globals as place roots |
| FD12 | minor | `docs/traceability.md` is still missing |
| FD13 | minor | The effects README names an exec effects checker in `weft-verified`; there is none |
| FD14 | minor | W0109, W0110 and W0113 have no test |
| FD15 | minor | The borrowing and effects mutation tables have no script |

## Method

1. I read CLAUDE.md, README.md, the design, the architecture, the plan, the spec, the
   eleven ADRs, the three proof READMEs, the crate docs and the round-1 reports.
2. I mapped each design rule and each ADR guarantee to a spec rule, a sema check, the
   interpreter or a test (tables below). For rules with no clear enforcement I wrote a
   probe program (`FID/p/`, about 45 probes).
3. I checked the claims of the docs against the code: file and function names, numbers
   and limits, command behaviour, exit codes, proof counts and mutation results.
4. For part (3), I read the "rules the checker must mirror" of both proof reports and the
   "Scope and limitations" of both proof READMEs. For each rule and each model assumption
   I looked for the mirror rule in `spec/weft.dl`, `rules.rs` or sema, and wrote a probe.
5. I compared `places::invalidates` in `rules.rs` (`Ctx::invalidates`) with the B3 kill
   rule, and the B1 CFG of the link with the facts that sema emits. I wrote a lint rule
   (`FID/genkill.dl`) that finds a node that both invalidates and rebinds a reference.
6. Agreement: `weft agree` on every program, under `--lib`, `--no-runtime` and both;
   two mutation harnesses (`FID/tools/mutagree*.py`); the programs of the other lenses
   (`FID/tools/agree_list.py`). A lint file with one lint per spec rule
   (`FID/rulecov.dl`) measures which spec rules fire on the corpus.
7. `cargo test --release -p weft-check` passes (all suites).

## Findings

### FD1 (blocker): the effects of an `on abort` function are not checked

**What.** The effects proof models `on abort` as atomic: "It cannot perform or fail"
(`proofs/effects/README.md`, "Scope and limitations"). The checker does not mirror this
assumption. No rule rejects an `on abort` function with effects. No node gets the
effects of the `on abort` functions that the unwinder can run there. The design wants
async cleanup in `on abort` ("it covers async cleanup with the same rule"), so the gap
between the model and the language is a decision, but no ADR records it.

Two failures follow:

1. An `on abort` function performs a user effect. The unwinder runs it with no handler
   environment. The interpreter stops with `no handler for Ask.ask on this task`. This
   happens also when a handler of `Ask` is in scope around the whole computation
   (`FD1_onabort_perform_outer_handler.wf`), and when no handler exists at all
   (`FD1_onabort_perform_no_handler.wf`: no W0805, no W0702).
2. An `on abort` function mutates an `rc` group (`/ mut(Node)`, three pushes). The caller
   holds `r = &a.items[0]` across the `handle` whose body aborts. No node of the caller
   has `mutates_at(_, Node...)`, so W0301 is missing. The stock interpreter prints a value.
   The instrumented interpreter of the oracle lens reports "access to a freed cell"
   (`FD1_onabort_mutates_group.wf`).

**Repro.** `FID/repro/FD1_run.sh`.

**Fix.** Choose one and record it in ADR 0007:
- Require an `on abort` function with no effects except `Async`/root effects, and no
  `mut` (sema check at `on abort =`, next to W0118). This matches the proof.
- Or treat each `may_abort` node as a call of the `on abort` function of each live
  linear value that has one: its named effects go to `escapes_at`, its `mut` places to
  `mutates_at` at the node (and at the call node of the caller that observes the abort),
  and the unwinder runs it with the handler environment of the frame. Then extend the
  effects model, or list the gap in its README.

### FD2 (blocker): nested `multi` continuations share one exec record

**What.** A clause of a `multi` operation `pick` holds its fresh continuation `k` while
it performs the `multi` operation `choose` of an outer handler. The checker accepts this:
rule 2 of the effects proof applies only to a fresh `once` continuation. The outer clause
resumes twice. `copy_frames` (`crates/weft-interp/src/machine/effects.rs`) copies the
code frames, but the `Frame::Clause { cont }` of the copy keeps the same record of `k`.
The first copy returns without a resume; `drop_now` marks `k` as `Dropped` and drops its
frames. The second copy resumes `k`, and the interpreter stops: `a continuation was
resumed after it was dropped`. The effects model allows this run: a `multi` record is
never used, and `holds_fresh` is false for it.

`proofs/link/README.md` ("Differences", `ex_multi_dropped_resume`) states the exec/model
difference, but no ADR, no interpreter doc and no open list says that accepted programs
fault. The interpreter doc says that it supports multi-shot continuations.

**Repro.** `FID/repro/FD2_run.sh`: `FD2_multi_nested_drop.wf` faults;
`FD2_control_resume_first.wf` (the same program with the branches swapped) runs.

**Fix.** Do not drop the frames of a fresh `multi` continuation at a clause return while
another copy can resume it: give each copy of a `Clause` frame its own record (copy the
nested continuation with the frames), or keep the frames and do not mark the record
`Dropped`. Add the program to `crates/weft-interp/tests/programs`.

### FD3 (blocker): a reference stored into an `rc` object outlives its owner

**What.** The borrowing proof assumes "No stored references ... the 'no back channels'
assumption that makes the frame of `callee_effect` valid" (`proofs/borrowing/README.md`).
Weft lets a generic container hold references (`Vec<&u64>`, ADR 0003), and an `rc`
object is reachable from any function with a handle, like a global. `stash(c: Rc<Cache>,
x: &u64) / mut(Cache)` pushes `x` into `c.refs`. `fill` calls it with `&v[0]` of its own
local `v`, and `v` goes out of scope at the end of `fill`. `read` later uses `c.refs[0]`.
The checker accepts. The stock interpreter stops with `a place does not exist`; the
instrumented interpreter reports a dangling reference.

The known ADR 0003 item ("a reference stored behind a reference parameter") names only
reference parameters (`FD3_known_ref_param_backchannel.wf` shows that shape). The `rc`
group is a channel with no parameter at all, so the caller side cannot follow it.

**Repro.** `FID/repro/FD3_run.sh`.

**Fix.** Treat a store into a place under an `rc` group root (and under a reference
parameter) as an escape: the stored references must not point into a local, a by-value
parameter or a temporary of the function (a check like W0204), or the store must give the
group the places of the stored references in every function. Record the rule in ADR 0003.

### FD4 (major): the multi rule does not count affine or `!Move` values

**What.** The design says: "Everything live across its perform site must be `@ many`",
and "Values are affine by default: usable at most once". `once_var(V)` in the spec is
only linear, `uniq`, a `once` closure or a continuation. So an owned `Vec` that is moved
after `choose()`, and a `!Move` struct with a self-reference, can be live across a
`multi` operation. The checker accepts both. The interpreter makes this safe by a deep
copy of the owned cells at each resume (`copy_frames`: "Cells that the frames own get
fresh copies"). So:

- the semantics of a `multi` resume (a deep copy of owned values, but not of `rc`
  objects) is a decision in the interpreter only. No ADR and no design text records it;
- a `!Move` value gets a new address in each copy, which conflicts with ADR 0007 and
  the design ("keep a fixed address for their whole life");
- the effects proof (E5) has no affine values, so it does not cover the copy;
- a native runtime cannot copy an arbitrary owned value (a `Box`, an extern resource).

**Repro.** `FID/repro/FD4_run.sh` (`FD4_multi_affine.wf`, `FD4_multi_immovable.wf`: 0
errors; the facts show `immovable(v0)` and `multi_at`, and no `once_var`).

**Fix.** At least, count `immovable(V)` as not `many` in `live_across_multi`. Then decide
the rule for affine values (not `many`, or copied) and record it in ADR 0005 and ADR 0007.

### FD5 (major): `proofs/README.md` overstates what the agreement tests check

**What.** `proofs/README.md`: "The facts that sema emits and the glue in `rules.rs` are
hypotheses of the link: tests check them (agreement with the Datalog spec)." Agreement
(`driver::agreement_with`) runs the checker and the spec on the same `b.facts`. It checks
the glue in `rules.rs`. It cannot check the fact hypotheses of the link (`facts_ok`: each
binding gives the group of the model; `bound_before_use`; `ret_ok`). ADR 0002 says this
too: "It does not show that the facts are complete." Example: the OR1 repro of the oracle
lens violates `facts_ok` (the result of `reader(&v)` gets no place), faults at run time,
and agrees.

**Repro.** `FID/repro/FD5_run.sh`.

**Fix.** Say: "The glue in `rules.rs` is tested by agreement with the spec. The facts are
tested only by the sema unit tests and the corpus diagnostics; `ret_ok` and
`bound_before_use` have no test."

### FD6 (minor): ADR 0009 has a stale claim about the derivation printer

ADR 0009: "The derivation printer of `check --explain` is not covered yet: it recurses
once for each derivation step." `bridge::render` uses a stack, and `limits.rs` tests it
on a 2 MiB thread (also `docs/architecture.md`). Repro: `FD6_run.sh`. Fix: delete the
sentence.

### FD7 (minor): per-module proof counts are stale

`crates/weft-verified/README.md` gives `places` 25; Verus gives 27 (`--verify-module
places`). `proofs/link/README.md` gives `places` 25 and `examples` 22; Verus gives 27 and
23. The totals (66, 233) are correct. Repro: `FD7_run.sh` (it verifies a copy).

### FD8 (minor): no corpus program fires spec rule r29

`FID/rulecov.dl` has one lint for each of the 76 rules of the spec. 75 fire on
`tests/programs`. Rule r29 does not:
`invalidated_at(R, P) :- points_into(R, Path), lends_mut(P, M), wild_at(M, B), prefix(B, Path).`
`FD8_r29_wild_lend.wf` fires it, and the checker agrees. `corpus_exercises_every_rule`
checks only the sink relations. So only the random agreement test finds a change of r29
in one of the spec and `rules.rs`, and no test finds the same wrong change in both. Fix:
add the probe to the corpus; extend the test to each rule (the lint method works).

### FD9 (minor): two meanings of `forwards(H)`; a diagram edge with no rule

- The spec header lists the input `forwards(H)` as "H is a root handler of `sim.run`
  (W0802 checks it)". The spec also derives `forwards(H)` as "a clause performs the
  effect outward". One name has two meanings, and a user lint over `forwards` sees the
  `sim.run` handlers too. Fix: rename the input (`sim_root(H)`) and add
  `forwards(H) :- sim_root(H).`
- `docs/architecture.md` draws `s.spawn → task_writes(T, M) → mutates_at`. The spec has
  no such rule; sema writes `mutates_at` at the spawn node itself (round-1 F8 said this
  too). Fix: draw the edge from the spawn to `mutates_at` and say "sema".

Repro: `FD9_run.sh`.

### FD10 (minor): root capabilities do not come through `env`

The design says: "`main` receives the root capabilities (filesystem, network, clock,
randomness) through `env`." In Phase 1 the effect row is the capability. A `main` with no
`env`, and a helper, perform `Rand` and `Clock` (`FD10_env_capabilities.wf`, 0 errors, it
runs). No ADR records the decision. Fix: one line in ADR 0005.

### FD11 (minor): two design statements with no enforcement and no ADR

- "Data visible to several threads must be `shared`, or split into `uniq` parts." Two
  fork branches read through one aliased reference that is not `@ shared`, and the
  checker accepts (`FD11_shared_not_required.wf`). This is safe (W0403 and W0405 cover
  writes), but ADR 0006 does not say that reads need no `@ shared`.
- "A root is a local, a parameter or a global." The grammar has no global item. ADR 0003
  lists the roots without globals, but does not say that globals are out of scope.

### FD12 (minor): `docs/traceability.md` is still missing

The design header and plan W10 name it (round-1 F11). Repro: `FD12_run.sh`. The plan has
it after this round; I list it so that the final listing does not miss it.

### FD13 (minor): the effects README names a non-existent exec checker

`proofs/effects/README.md`: "`check` is a Verus spec. The exec checker in
`crates/weft-verified` is not linked to it here." `weft-verified` has no effects checker.
The production effects rules are the sema facts (`may_abort`, `multi_at`,
`clause_multi`, `body_multi`, `resumes_at`) and the spec rules W0602 and W0503. That is
the real unlinked part. Repro: `FD13_run.sh`.

### FD14 (minor): three codes have no test

W0109 (impl of an unnamed type), W0110 (parameter type missing) and W0113 (variant
pattern outside `match`) are emitted and explained, but no corpus program, unit test or
CLI test names them. Repro: `FD14_run.sh`.

### FD15 (minor): the borrowing and effects mutation tables have no script

ADR 0008 asks for "a documented mutation test" for each theorem. Only `proofs/link` has
`mutations/run.sh`. The borrowing (9 rows) and effects (8 rows) tables cannot be re-run
from the tree. I re-ran two effects rows by hand; they hold. Repro: `FD15_run.sh`.

## (1) Design rules and ADR guarantees: what enforces them

Spec rule names are from `spec/weft.dl`. "Sema" names the function that emits the code.

### Places and mutation

| Rule | Enforced by | Status |
| --- | --- | --- |
| A reference type includes its place | sema W0203 (`call_fn_as`), W0204 (`check_returned_refs`); `points_into` | yes |
| A function declares the places it mutates | spec `unauthorized_mut` (W0703) | yes |
| `mut(p)` invalidates strictly inside, through an unstable step | spec `invalidated_at` rule 1, verified `places::invalidates`, link L1 | yes |
| References to `p` and to stable parts survive | same rule; lemmas `lemma_no_self_invalidation`, `lemma_stable_suffix_survives` | yes |
| Use of an invalidated reference is an error | spec `error` (W0301) | yes, except FD1 (2), FD3 |
| Inferred in bodies, stated in public signatures | sema W0701 (`lower_fn`), `infer.rs` | yes |
| `mut(w..)` | sema makes `mut(p..)` equal to `mut(p)`; `lemma_deeper_mutation_weaker` | yes |
| Roots: local, parameter, global | no globals | none (FD11) |

### Modes and threads

| Rule | Enforced by | Status |
| --- | --- | --- |
| A shared-mutable reference is nonportable | spec `shared_mut_capture` (W0403, fork), `pinned` (spawn) | yes |
| `fork` and stealable closures are portable | spec `nonportable_capture` (W0401), `stealable` | yes |
| Data that several threads see is `shared` or split `uniq` | W0403 and W0405 only | partial (FD11) |
| Mode crossing | flags in the facts | implicit |
| One mode per axis; `uniq` and `shared` contradict | sema W0119 (`resolve`) | yes |
| `@ shared` is read-only | spec `shared_mutation` (W0402) | yes (callback case is a recorded ADR 0005 gap) |
| `uniq` expected | sema W0406 | yes |

### Linear and immovable types

| Rule | Enforced by | Status |
| --- | --- | --- |
| Consumed on every normal path | spec `unconsumed`, `overwritten` (W0601) | yes |
| Live across an abort only with `on abort` | spec `abort_unhandled` (W0602), sema `may_abort` | yes |
| `on abort` only during unwinding | interpreter, `lifecycle::Linear`, link L3 | yes; its effects: FD1 |
| No linear value live across `multi` | spec `live_across_multi` (W0503) | yes |
| `!Move` keeps its address | spec `moved_immovable` (W0604) | yes, except `multi` copies (FD4) |
| Self-referential structs | sema W0605 | yes |
| Task handles are linear | prelude `Task<T> { linear, on_abort }`, W0601 | yes |

### Effects and handlers

| Rule | Enforced by | Status |
| --- | --- | --- |
| Rows after `/`, inferred, stated in public signatures | spec `unauthorized_effect` (W0702), sema W0701 | yes, except `on abort` (FD1) |
| Lexical handlers | sema perform resolution; interpreter `find_handler` (`rposition`) | yes (no spec rule; S5 item F8) |
| A perform is a call with the footprint | spec `mutates_at :- performs_at, footprint`; `call_arg` at the perform (W0312) | yes |
| Silent effect polymorphism | `infer.rs` | yes |
| `once` by default | spec `use_after_move` on the continuation (W0501) | yes |
| `multi`: everything live is `many` | spec `live_across_multi` | partial (FD4) |
| Dependency authority | `weft-cli` package loader W0901 | yes |

### Memory, runtime and concurrency

| Rule | Enforced by | Status |
| --- | --- | --- |
| Owned values freed at scope end | spec `frees_at`, `owner` | yes |
| `rc` groups | sema group roots and handle places; spec rules | yes, except FD3 |
| `fip` | sema `fip.rs` (W1001-W1004) | yes (not in the spec) |
| GC pointer is a stable step; libraries never need the GC | `extern type` stability; W0902 | yes |
| Only binaries and tests install root handlers; intercept = forward | spec `root_handler_in_lib`, `forwards` (W0801); sema W0802 | yes |
| `main` and tests handle each non-standard effect | driver `diagnose::root_effects` (W0805) | yes, except `on abort` (FD1) |
| No-runtime profile | W0803 (driver) | yes |
| Scopes are the only way to spawn | sema W0115 (`spawn`) | yes |
| Children cannot outlive the scope | sema `joined_at` at the scope end | yes |
| Cancellation runs `on abort` | interpreter `check_interrupt`; W0602 at scope ends, joins and calls | yes (probes `scope_cancel*.wf`) |
| Separate footprints, also on one thread | spec `task_conflict` (W0405) | yes (B4 proves another rule; ADR 0006) |
| Preemption at back-edges | interpreter `Op::BackEdge` (not a cancellation point) | yes |
| Work stealing follows modes | spec `stealable`; interpreter `is_stealable` | yes |
| Foreign calls are `blocking` | sema: extern default `Blocking` | yes |
| Simulation replaces the root handlers | `sim.run` (sema, interpreter) | yes |
| `main` gets the root capabilities through `env` | none | none (FD10) |
| Libraries cannot name a runtime | no runtime names exist | vacuous |

ADR guarantees: I probed about 30 statements of ADRs 0002, 0003, 0005, 0006, 0007 and 0009
(`FID/p/adr*.wf`, `w0304.wf`, `b2_*.wf`, `e1_*.wf`, `scope_cancel*.wf`, `lexical.wf`,
`loop_iter.wf`, `same_node.wf`, `extern_blocking.wf`). Each one holds, except the cases in
FD1 to FD4. The other gaps that I saw are in the recorded ADR lists.

## (2) Claims checked

True: the README quick start (each command, exit codes 0, 1 and 2, option rejection,
markers); the architecture tables (verified pieces and their users, stack sizes,
`MAX_INDENT` 32, `CHAIN_FOLD` 8, `CHAIN_KEEP` 3, nesting budget 768 = 96 levels,
`CHAIN_PART` 32, `infer::growth_limit`, `infer::parts_limit` = 2n + 32, `SIG_PLACE_STEPS`
8, W0120 budget 20 000, `MAX_LOOP_PASSES` 8); ADR 0002 (where each sema code is emitted,
the 8-step checklist equals CLAUDE.md); ADR 0004 and 0006 (modes and `concat` unused); ADR
0010 (`--workers` 1 to 1024, the note for a file with no tests); the interpreter doc
("at most once"); each theorem, lemma and example that the proof READMEs name exists;
the proof counts and the link mutation table.

False or stale: FD5 (major), FD6, FD7, FD9, FD12, FD13 (minor).

## (3) Rules that the proofs need

Effects proof, rules 1-6:

| Rule | Mirror in the checker | Status |
| --- | --- | --- |
| 1. Abort and multi rules at each suspension point | sema `may_abort` at calls, resumes, scope ends and joins; spec `multi_at` from `clause_multi`, `body_multi`; corpus 63; probes `e1_resume_abort.wf`, `e1_call_multi.wf` | mirrored |
| 2. A fresh `once` continuation is a `once` value | `once_var` of the continuation; corpus 63 | mirrored (closure case is a known item) |
| 3. A handle body cannot return its own capability | sema W0313 (`check_cap_escape`) | mirrored (ADR 0005 lists the opens) |
| 4. A perform goes to the topmost handler frame | interpreter `find_handler` uses `rposition` | mirrored |
| 5. The unwinder drops nested continuations | interpreter `drop_frames` (`Frame::Clause`) | mirrored; `multi` record sharing: FD2 |
| 6. Clauses run in the handle-site environment, return no capability | sema clause environment, W0313; corpus 63 | mirrored |
| Model assumption: `on abort` is atomic | none | FD1 |
| Model assumption: no affine values | none | FD4 |

Borrowing proof, notes 1-5 and assumptions:

| Rule | Mirror in the checker | Status |
| --- | --- | --- |
| 1. Closures, handlers and continuations hold references | closure `points_into`; corpus 36 | mirrored |
| 2. A closure call, a perform and a resume mutate the captures; a call that reaches a local handler gets its footprint | probes `b2_resume_mut.wf`, `b2_call_fp.wf` (call, `apply`, generic `apply_t`, item value) | mirrored |
| 3. Payload steps unstable; an enum assignment mutates | corpus 30 | mirrored |
| 4. Join with one place per reference | multi-place `points_into` | not mirrored; recorded in `proofs/link/README.md` |
| 5. B4 is reference-based | W0405 is access-based | not mirrored; recorded in ADR 0006 |
| Assumption: no stored references | none for `rc` groups | FD3 (reference parameters: known ADR 0003 item) |

Models against the checker:

- B3 kill rule and `rules.rs`: `Ctx::invalidates` is exactly "same root, then
  `places::invalidates`", as `invalidates_in_model` states. The other kill rules of
  `rules.rs` (free, wildcard, lend) only add nodes to `gen`. Stability in sema comes from
  the type at each position (`elem_step`, `Deref` per `extern type`, split sides with the
  stability of the element step, handle places `h.*` unstable), as `typed_by` needs.
- B1 CFG and the facts: the link needs that no node both invalidates and rebinds a
  reference (else the checker is stricter). The lint `FID/genkill.dl` finds no such node
  in the corpus, in the interpreter programs or in `FID/p/genkill1.wf` and
  `genkill2.wf` (`r = if c { grow(w) } else { r }`, `&grow(w).kids[0]`, a loop, a block).
  A B1 node has one instruction; a sema node can use and mutate at once. W0312 covers
  the cases that I tried (`same_node.wf`: an earlier operand invalidates, a later operand
  reads).
- A closure that gives a captured reference a new value on one path does not rebind it at
  the call (`rebind_closure.wf`): this is safe.

## (4) Agreement runs

| Set | Programs | Result |
| --- | --- | --- |
| `tests/programs`, `crates/weft-interp/tests/programs`, `std/prelude.wf`, `examples/*`, `tests/packages/*` | 109 | agree |
| The 105 corpus and interpreter programs with `--lib`, `--no-runtime`, both | 3 × 105 | agree |
| Line mutations (delete, duplicate, swap, insert) | 4 000 (1 339 parse) | agree, no crash |
| Mutations that keep the braces | 8 000 (6 702 parse) | agree, no crash |
| Programs of the oracle and red-team lenses (random sample) | 12 000 (11 997 parse) | agree, no crash |
| `cargo test --release -p weft-check` | all suites | pass |

## Round-1 fixes that hold

F1 (owner frees), F3 (perform `call_arg`), F4 (closure parameter mutation), F5 (closure
linear, tuple `on abort`), F6 (`forwards` from clause performs), F10 (proofs exist,
`verify-all.sh` fails on a missing crate), F11 (README commands work; derivation claim of
ADR 0002 is now limited to spec diagnostics; `weft explain` knows each code), F12 (W0312
recorded with the `in` workaround), F14 (`overwritten` and `stealable` have corpus
programs). Still open as recorded S5 items: F7, F8, F9, F13. Still missing: the
traceability file (FD12).

## Files

- Report: `FID/../fidelity.md` (this file).
- Repros: `FID/repro/` (`FD1_run.sh` ... `FD15_run.sh` and the `.wf` files).
- Probes: `FID/p/`. Tools: `FID/tools/`. Logs: `FID/agree_corpus.txt`,
  `FID/mutagree_4000.txt`, `FID/mutagree2_8000.txt`, `FID/agree_other_lenses.txt`,
  `FID/verify_all.log`, `FID/link_mutations.log`.
