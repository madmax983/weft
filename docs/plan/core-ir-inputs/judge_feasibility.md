# Judge: feasibility and migration risk

Status: judgement of the three core IR designs. Date: 2026-10-20. Base: commit `b073ea7`
of `/home/user/weft` (git status is clean; I changed nothing there, in `wt-core` or in
`wt-edge`). The R3a binary is the copy `ir/work/machine/weft-r3a`.

Lens: size, how much of `body/` survives, how the side-by-side migration and the diff
gate work, how long until the old path can go, precision regressions (false positives)
on the corpus and the design examples, and performance.

`SCRATCH` is `SCRATCH`.
`ir/...` is `SCRATCH/ir/...`.

## 1. Scores

| Design | Score (0-10) | One line |
| --- | --- | --- |
| minimal (`design_minimal.md`) | **7.0** | Smallest change, keeps the tested domain, rolls out by construct group with a fallback for each body. It leaves four realistic handler shapes open, and its estimates are optimistic. |
| machine (`design_machine.md`) | **5.5** | Best de-risking tools (a sketch that compiles, oracles, measured gate cost). But it is a full rewrite, stage S4 lands all features at once, and its W0313 change loses corpus markers. |
| MIR (`design_mir.md`) | **5.0** | Most rigorous gate (claims test, signed ledger, staged scopes). But it is the largest and longest plan, it changes run-time behaviour in four ways, and its capture rule D5 likely adds a corpus false positive. |

Recommendation (section 6): take **minimal** as the migration vehicle. Graft the handler
frame order of machine (it closes M-new and M1 to M4), the gate rules of MIR (claims
test, signed ledger), and the run-time oracles of machine. Do not take MIR D5, MIR D9,
choice A or the use-based W0313 of machine during the migration.

## 2. What I checked

I did not trust the numbers of the designs. I measured them or read the source.

| Item | Result | How |
| --- | --- | --- |
| Size of `body/` | 19 008 lines (`wc -l`). The designs say 19 097 (MIR, machine) and 18 415 in functions (minimal). The difference is small. | `wc -l crates/weft-sema/src/body/*.rs` |
| Inference mixed into `body/` | 191 call sites of `unify` and `inf` | `grep` over `body/*.rs`. Minimal says "about 190". All three designs must split this out. |
| Corpus | 129 files, 1 019 `//~` markers. Only 31 files have `fn main` and 5 have test blocks. So the oracle can run at most 36 of 129 corpus programs. | `grep` |
| Markers by code | W0301 286, W0405 86, W0601 77, **W0313 61**, **W0204 45**, W0314 44, W0503 39 | `grep -oh "//~ W[0-9]*"` |
| Interpreter golden programs | 42 `.wf` with 42 `.out` in `crates/weft-interp/tests/programs` | `ls` |
| Probe files | 59 846 files, 57 266 distinct by content (`md5sum`). 50 052 are oracle sweeps of rounds 2 and 3. | `find` over `SCRATCH`. This agrees with MIR (56 932) and machine (57 247). |
| Check time today | Corpus: 129 files in 4.4 s (34 ms each, with process start). 200 files of `r3/oracle/sweep2`: 1.26 s (6.3 ms each). 200 random sweep files: 8.1 s (40 ms each). Process start: about 3 ms. | `time` with `ir/probes/weft` and `weft-r3a`. The machine was loaded by the other workflow. |
| Oracle run time | 200 random sweep files, seed 1, workers 4: 8.5 s (42 ms each) | `weft run --unchecked --oracle` |
| Facts of the corpus | about 110 000 fact lines. `cfg_edge` is the largest relation (17 974). `105_walk_writes.wf` has 11 310. | `weft facts` |
| Machine sketch | `cargo test --offline`: 6 tests pass, also `each_relation_has_a_source` | `ir/work/machine/weft_ir_sketch` |
| Minimal sketch | a copy of `core_sketch.rs` compiles with `rustc -W missing_docs`, no warning | `ir/work/judge/core_sketch_copy.rs` |
| New unsound probes | `mir/postres.wf`, `machine/m1_post_resume.wf`, `m6b_resume_result_ref.wf`, `m8_abort_value_into_body.wf`, `m10_abort_value_callee_local.wf`: R3a accepts each one, and `--oracle` faults on each one (a read of a freed cell) | `weft-r3a check` and `run --unchecked --oracle` |
| Capture rule probe | `ir/work/judge/p/d5_count.wf`: a closure that changes a captured integer and leaves its function (`counter`), and the same closure in an `Rc`. Today: accepted, and the oracle run is clean. | my probe |

## 3. Cross-cutting findings

These hold for more than one design. Each design must plan for them.

### 3.1 Which design closes the realistic handler shapes

The ship rule allows at most two review rounds after the IR lands. A realistic soundness
blocker blocks the PR. So a shape that a design leaves open is schedule risk.

| Shape | Probe | MIR | machine | minimal |
| --- | --- | --- | --- | --- |
| M-new / M1: clause code after `resume` changes a place that the body value points into | `postres.wf`, `m1_post_resume.wf` | closed (after-body node) | closed (`Exit` then `Post`) | **open**: the whole clause runs at the perform node (4.8, "Clause runs") |
| M2: the result of `resume` | `m6b_resume_result_ref.wf` | partly: the resume summary has `_0` | closed (`ret` of the continuation) | unclear: `Π(h)` gives "the value of the handled body" |
| M3: a clause value that points into a local of the handled body; the unwinding frees it | `m8_abort_value_into_body.wf` | **open**: the edge is `unwind exit` → abort node → return node (4.1, 4.9). The cleanup frees `w` first, then the abort node binds `dest`. | closed (`AbortValue` before the cleanup) | **open**: the abort node `A` has `unwound_at` and `rebound_at(dest)` at one node (4.8). This also breaks its own claim A5 (`no_gen_kill`). |
| M4: the same with a local of a callee | `m10_abort_value_callee_local.wf` | unclear: the callee frame root ends "at the return node of `C`"; the abort path is not stated | closed (callee frame root) | **open**: F3-2 stays ("callee locals have no name") |

Machine tags M1, M2 and M3 "realistic". I agree: clean-up code after `resume` (commit,
release, log) and an early-exit handler that returns a reference into its argument are
common forms.

### 3.2 W0313 is an escape rule, not a use rule

`codes.rs` says: "A closure that performs through a local handler cannot leave the
handled computation: not as its value ..., not through a local outside it". The corpus
tests the escape, also when nothing uses the value later:

- `62_cap_escape.wf`: `as_result` (`let f = handle ... in || log("late")`, `f` is not used),
  `in_tuple`, `in_struct`, `in_closure`;
- `83_kept_values.wf`: `copies`, `copies_vec`, `takes_out` (the escaped value goes into an
  outer local that nothing uses later).

A design that makes W0313 "W0301 on a capability root" reports only a use after the
`handle`. Then these markers go away. This is a lost error in the gate and a change of the
documented rule.

- machine does this in stage S4 (section 4.7). It is not optional.
- MIR does it only in the optional stage M9. Until then W0313 stays in sema and reads the
  new abstract values.
- minimal keeps `caps.rs`. It makes only the continuation part use-based (D17). The
  shown cases of `122_cont_escape.wf` use the escaped closure later, so the risk is small.

### 3.3 W0204 moves to the exit node

All three designs make the local forms of W0204 (a returned reference into a local, a
by-value parameter or a temporary) an error of the return slot at the `Return` or exit
node. The corpus has 45 W0204 markers on the line of the returned expression.
`diagnose.rs` must report the span of the assignment to `_0`, or many markers move. No
design says which span it reports. This is cheap to fix, but each design must state it.

### 3.4 The oracle cannot classify every difference

The gates use the oracle to sort a difference into "fixed" or "regression". The oracle
needs `fn main` or a test block. In the corpus, 93 of 129 programs have neither. The
markers protect the corpus. But in the probe sets a non-runnable program, or a fault that
six seeds do not show, looks "clean". So a lost error with a clean oracle must not pass
on its own:

- MIR: a reviewer signs each such ledger entry. Good.
- minimal: each difference must be in `expected.toml` with a finding id. Good.
- machine: "No fault: an old false positive that the IR removes; record it". No review.
  This can hide a regression.

### 3.5 The limits and scale tests

`crates/weft-cli/tests/limits.rs` runs the whole pipeline on 20 000-term chains
(`1 + 1 + ...`, `t && t || t ...`) and on deep nesting up to the documented limits.
`crates/weft-check/tests/scale.rs` asserts work bounds (`searches <= 4n + 1`,
`part_nodes <= 3 * nodes`). An ANF builder makes a temporary for each operand. A CFG design
makes a `SwitchInt` and a join for each `&&` and `||`: 40 000 branches in that test. Each
builder must be iterative or use the stack growth of today, and each analysis must stay
linear on long straight chains. No design names these two test files in its exit
criteria, except machine (cost gate) and MIR (check 8). Minimal names `scale.rs` only.

### 3.6 Gate cost

From my measurements (6 to 40 ms for each check, 42 ms for each oracle run):

| Gate | Cost |
| --- | --- |
| Both pipelines on all 57 266 programs | about 12 to 76 core-minutes (3 to 20 minutes on 4 cores) |
| MIR baseline: oracle with seeds 1 to 8 and workers 1 and 4 on each program | about 57 000 × 16 × 42 ms = 10.6 core-hours (about 2.7 hours on 4 cores), more with the 10 s timeouts. It runs once. |
| machine: oracle only on programs whose verdict differs, six configurations | small |
| minimal: each commit, 1 750 programs | about 2 to 3 minutes |

All three gates are affordable. MIR's baseline is the heaviest, but it runs once.

## 4. Each design

### 4.1 minimal

**Size and reuse.**

- New: builder about 4 700 lines (2 286 of them moved from `body/`), Core types, printer
  and validator about 1 450, Core compiler about 900, gate about 600.
- `body/`: 2 086 lines deleted, 2 286 moved, 14 043 kept and "cut by a third" to about
  9 500. About 76 % of `body/` survives as code. This is the most reuse of the three.
- The cut "by a third" is an estimate. Appendix B only puts each function into a bin. It
  does not show the cut. The kept code also changes more than "minimal" suggests: the
  input language (AST to Core), `Summary` (42 hand-written fields to the generic `RELS`
  table), the post-passes (to the worklist `settle`), the place resolver (with the new
  pointer word `@`) and the call rule. This is a large refactor of 14 000 lines.

**Migration and gate.**

- The best rollout of the three: six construct groups (4a straight-line to 4f generics).
  A body with a construct of a group that is not on yet falls back to the old generator
  (`Unsupported(construct)`). So each group lands and gets gate coverage on its own.
- Parity tests before any fact changes: D0 (types), D1 (the exports `by_value`,
  `arg_order`, `int_ops`), D3 (runs), D4 (traces, optional).
- Gate: 177 repository programs and about 1 570 curated probes at each commit; about
  55 700 generated programs each night. Each difference needs an entry with a finding id.
- Weak point: "new false positive ... blocks, unless an entry justifies it". This allows
  a justified false positive in the corpus. MIR and machine forbid any new false positive
  in the corpus.

**Time until the old path can go.** The plan says about 40 days of one agent stream: S5
(new default, old behind the switch for one review round, then deleted) at about day 30.
S4 is 12 to 15 days for the refactor above. I think that is optimistic by a factor of
about two. A realistic plan is 60 to 80 agent-days in all. This is still the shortest.

**Precision risk on the corpus: low.**

- The abstract domain stays: part holders, one-place instances, `writes_via`, `kept`
  captures, the widening, the handler order. These features have corpus tests
  (`102_wild_instances.wf`, `103_wild_lend.wf`, `35_wild_places.wf`, `143_arg_roots.wf`).
- Rule CAPTURE keeps `Kept` for plain data with no borrow. `count += 1` is not a borrow,
  so `125_multi_values.wf` (`shared_closure`) and my `d5_count.wf` stay clean.
- New stricter rules, each a possible false positive: the must-move check of linear
  outer variables in inner bodies (its R3), an owner for the cell of a reference local,
  early borrows of rule ORDER-2, the `Caller` lend of rule OPAQUE, and `uses(ret, exit)`.
  The design lists them, and the gate classifies them.
- No run-time change except D15 (loop tail temporaries end at each iteration). Choice A is
  not taken: rule ORDER-2 keeps the read points of the machine. This is the safest choice
  for a migration.

**Performance: about today.** One node for each Core statement and early borrows add
facts. But the builder runs once, not in each inference round. `lower_loop` and the
inference loop stay, so their cost stays too.

**Strengths.** Smallest change; most reuse; per-group rollout with a fallback for each
body; no user-visible change except D15; lowest precision risk; shortest time until
`body/` can go; the old generator stays for one review round after the switch.

**Flaws.**

- M-new, M1, M3 and M4 stay open (3.1). Its abort node binds and frees on one node, which
  breaks its own claim A5.
- It keeps `lower_loop`, the flow-insensitive state and the summary language. LOOP,
  STATE, SUM, FNVAL, STORE and CAP stay partly (52 unsound partly, 37 stay). In round 2
  and the open lists, 47 % and 72 % of the unsound findings were in group B of
  `root_causes.md` (value flow and summaries), where most of these classes are. So the
  two review rounds after landing can still find blockers there.
- Its 91 "by construction" claims exceed the baseline of `root_causes.md` (83), although
  it does not meet several of the conditions of that baseline (one fixpoint, `on abort`
  as a call, move paths). 43 of them depend on one shared rule. There is no claims test
  that checks them.
- Two copies of a 14 000-line generator live side by side in S4, while R3a and later
  fixes land in the old one.
- Handled bodies and scope bodies stay inline and become code units only in S6 (its R8).
- The S4 estimate (12 to 15 days) is optimistic.

### 4.2 machine

**Size and reuse.**

- New: about 23 500 lines of code and 3 000 lines of tests (typeck 4 500, IR 2 500,
  builder 6 000, analysis 3 500, summaries 2 000, facts 2 500, W0313/W0314 600,
  `compile_ir` 1 800).
- `body/` goes completely. `typeck` is "new code (a copy of the inference parts of
  `Lower`)". So no part of `body/` survives as code. The precision features must come back
  as features of a new analysis.
- The plan gives no calendar time. By size it is close to MIR: I estimate 14 to 20 weeks
  of one engineer for S0 to S6.

**Migration and gate.**

- Strong tools: a sketch crate that compiles, with a verifier and a test that each of the
  73 input relations has a source; a measured gate cost; a fact oracle, a summary oracle
  and a trace-conformance check; and an exit criterion of a fresh sweep of 50 000
  generated programs. These tools aim at the new single points of failure.
- **S4 is one "very large" stage.** The analysis, the summaries, effect inference over the
  IR, the fact generator, W0313 and W0314 land together. There is no scope by feature
  (as MIR M4 to M7) and no fallback for each body (as minimal). This is a big-bang step
  inside the migration.
- S3a makes the IR interpreter the default and deletes `compile.rs` before the new facts
  exist. From S3a to S5 the old checker checks programs that the IR interpreter runs.
  The design has no parity test between the old `by_value`/`arg_order`/`int_ops` and the
  IR decisions (minimal has D1). A mismatch is class TWO again for that window.
- The gate inputs omit the 42 interpreter golden programs, which matter most for S3a.
  (`cargo test --workspace` still runs them.)
- A lost error with a clean oracle is recorded with no review (3.4).
- The false-positive budget is 0.5 % of the inputs that `old` accepts. On about 57 000
  inputs that is up to about 280 new false positives outside the corpus. That is loose.

**Time until the old path can go.** `compile.rs` goes early (S3a). `body/` goes at S6,
after S4 (very large) and S5 (cut over, old kept for one review round). Long.

**Precision risk on the corpus: high.**

- The design says so itself (R2, high): one-place instances, known closures at a node,
  part holders, split ids and `writes_via` must come back as features of the analysis.
- The W0313 change (3.2) loses corpus markers in S4: at least `as_result`, `in_tuple`,
  `in_struct`, `in_closure` of `62_cap_escape.wf` and `copies`, `copies_vec`, `takes_out`
  of `83_kept_values.wf`. The design does not plan an escape rule. These are lost errors,
  not false positives, but exit criterion 2 (each corpus file passes its markers) blocks
  S4 until someone adds one.
- It keeps `KeptCell` and the unwind order of the interpreter. So it has fewer
  user-visible changes than MIR: only choice A and the loop tail temporaries.

**Performance: medium risk.** One node for each instruction, a copy of each cleanup chain
for each abort destination, an `AbortValue` node for each pair of a suspending node and a
handler, and heap slots. The SCC fixpoint replaces the re-lowering of `infer.rs`, which
can save time. The cost gate (2x time, 3x facts) is concrete and measured.

**Strengths.** Closes M1 to M4; the most careful analysis of the machine order; a sketch
that compiles; run-time oracles; measured gate cost; fewer user-visible changes than MIR.

**Flaws.** Full rewrite with no reuse of `body/`; S4 is a big bang; W0313 semantics change
loses corpus markers; loose FP budget and unreviewed lost errors; the S3a to S5 window
with no capture parity test; no time estimate.

### 4.3 MIR

**Size and reuse.**

- New: about 28 000 lines (IR 2 000, type check 5 000, builder 5 000, analysis 3 000,
  summaries 2 500, facts 1 500, interpreter 1 600, gate 1 500, tests 2 500, proofs 3 500).
  Removed: about 21 000.
- About 4 000 lines of `body/` move into the type check. The rest goes. So about 20 % of
  `body/` survives as code.
- Effort: 14 to 18 weeks for M0 to M8, and about 6 more for M9. The longest plan.

**Migration and gate.**

- The most rigorous gate: a manifest by content hash; a baseline with oracle verdicts at
  16 configurations; seven difference classes; a ledger; a reviewer signs each lost error
  with a clean oracle; and **check 7, the claims test**: each "by construction" verdict
  with a repro must be rejected, or the verdict changes. This is the best defence against
  overclaimed verdicts, and the other designs lack it.
- Staged scopes by feature: M4 first-order bodies, M5 closures, M6 handlers, M7 tasks.
  Good, but the new pipeline is not usable for real programs before M8, so the old
  pipeline is frozen for about four months.
- **M8 deletes `body/` at the switch**, before the two review rounds. There is no old
  generator to compare or bisect with during those rounds. Minimal and machine keep the
  old one for one round.

**Time until the old path can go.** M8, after 14 to 18 weeks. Then two review rounds.

**Precision risk on the corpus: high.**

- **D5 (capture rule).** A plain-data capture is `ByCopy` only if the function never
  assigns or borrows the variable. Else it is `ByRef`, which points into `cell(x)`. A
  closure `|| count += 1` assigns `count`, so it becomes `ByRef`.
  - `125_multi_values.wf`, `shared_closure`: the closure goes into `Rc.new(Hook { .. })`.
    By 3.5.5, a store of a reference to a local of the body into a `Group` root is a
    W0204 store. The corpus expects only W0503 there. So D5 likely adds a corpus false
    positive.
  - My `d5_count.wf`, `counter`: a returned closure that counts. Today it is accepted and
    runs clean under the oracle. By 3.5.21, a closure that outlives a captured local is
    W0301 or W0204. MIR lists this risk (9.1), but this is a common user program.
- Step 3 of 4.6 makes interface roots concrete for each actual. This adds real aliasing
  errors inside closures, and some can be new false positives.
- Versions (D8) give flow-sensitive `points_into` with no spec change. This is a
  precision gain (STATE: V069, OL-NR-flow, R3RT10) and it offsets some of the risk.

**Run-time changes.** D3 (choice A: `x + { x = 5; 1 }` gives 2), D4 (loop tail
temporaries), D5 (capture by copy) and D9 (the interpreter unwind order changes to the
order of the effects model). Machine and minimal change the model instead of the
interpreter for the unwind order. Each change needs ADR text and ledger entries.

**Performance: highest risk.** A version for each definition of a reference-holding path,
one node for each statement, and step 3 of 4.6, which copies the facts of a closure for
each actual (a cap and a widening limit it). Effect inference re-runs the analysis and the
fact generation in each round. The budget (2x time) is right, but the design has no
measurement.

**Strengths.** The best gate (claims test, signed ledger, staged scopes); versions as a
precision gain; the most "by construction" removals (114); a clear path to the proofs.

**Flaws.** Largest and longest; old pipeline frozen for months; `body/` deleted before the
review rounds; four run-time changes; D5 likely adds a corpus false positive; M3 and
probably M4 stay open (3.1); performance not measured.

## 5. Summary table under the lens

| Criterion | minimal | machine | MIR |
| --- | --- | --- | --- |
| New lines (production) | about 7 650 new or moved, about 14 000 adapted | about 23 500 | about 20 500 (28 000 with tests, gate and proofs) |
| `body/` that survives as code | about 76 % (cut to about 50 %) | 0 % | about 20 % (inference) |
| Rollout | 6 groups, fallback for each body | one big S4 stage | 4 feature stages, no fallback |
| Old path kept after the switch | one review round | one review round | none |
| Time until `body/` goes (my estimate) | 60 to 80 agent-days | 14 to 20 weeks | 14 to 18 weeks (+6 for M9) |
| Run-time changes | D15 only | choice A, loop temporaries | choice A, loop temporaries, captures, unwind order |
| Corpus precision risk | low | high (port features; W0313 markers) | high (D5; step 3) |
| Performance risk | low | medium (measured) | high (not measured) |
| Gate rigor | good (expected.toml, parity tests) | good tools, weak rule for lost errors | best (claims test, signed ledger) |
| Realistic shapes left open | M-new/M1, M3, M4 | none of M1 to M4 | M3, maybe M4 |
| Classes left partly open | LOOP, STATE, SUM, FNVAL, STORE, CAP, PART, GEN | FNVAL, SUM, STORE, GEN as "one rule" | FNVAL, SUM, part of STATE |

## 6. Recommendation

Use **minimal** as the migration vehicle. It has the lowest risk of each kind under this
lens, and it removes `body/` soonest. It is also the only plan whose rollout can land in
small, gated steps while the old generator is the reference. Then fix its gaps with
grafts from the other two designs.

### 6.1 Grafts, in order of priority

1. **Handler frame order from machine (before the switch, in group 4d).**
   - After the handled body, bind `dest` at an `Exit` node. Then apply the part of each
     clause after its first resume point at a `Post` node. Use MIR's query `after_resume`
     (the nodes that a resume point reaches) on the `RELS` projection. This closes M-new
     and M1.
   - Split the abort node `A` of minimal 4.8 into an `AbortValue` node (it binds `dest`)
     and an unwind node after it (`unwound_at`). This closes M3 and restores A5.
   - Give the result of `resume` the value of the handled body (M2).
   - Add a callee frame root for places in a local of a callee that the callee gives to an
     operation or a callback. Its owner ends at the return node of the call and on its
     abort path (M4, F3-2). This needs a new `EffectSig` part, so plan it in group 4c/4d.
   - Put `postres.wf`, `m1_post_resume.wf`, `m6b_resume_result_ref.wf`,
     `m8_abort_value_into_body.wf` and `m10_abort_value_callee_local.wf` into the curated
     gate set at S0.
2. **Gate rules from MIR.**
   - The claims test: each "by construction" verdict of Appendix A with a repro must be
     rejected; else fix the code or change the verdict.
   - A lost error with a clean oracle needs a signed reviewed reason, also in
     `expected.toml`.
   - No new false positive in the corpus or the examples, with no exception. A stricter
     rule that would add one (the must-move check, an early borrow) changes the corpus
     only with an ADR.
3. **Tools from machine.**
   - Make the Core types, the validator and a test "each relation of `FnFacts` has a row in
     `RELS` and a template" the deliverable of S1, as the machine sketch does.
   - The fact oracle and the summary oracle (machine 6.3, checks 3 and 4) on each accepted
     gate program, with priority for the `RELS` projection and substitution, which are
     minimal's new single points of failure.
   - A cost gate: at most 2x the check time and 3x the facts, with `scale.rs` and
     `limits.rs` in the exit criteria of each group.
   - A fresh sweep of the generators (50 000 programs, new seeds) before the switch.
4. **Keep W0313 escape-based.** Keep `caps.rs` through the migration. Do not take machine's
   use-based W0313 or extend minimal's D17 to handler capabilities until the spec has an
   escape rule that keeps the 61 corpus markers.
5. **Do not take** MIR D5 (use `Kept`), MIR D9 (keep the interpreter unwind order and
   change the model), or choice A (keep rule ORDER-2). Each one is a user-visible change or
   a precision loss with no gain for the migration.
6. **After the ship (not on the migration path).** The Core can lower to a CFG with one
   more pass (minimal 9.3). Then replace `lower_loop` by one fixpoint, add MIR's reference
   versions for flow-sensitive `points_into`, add move paths, and turn the `EffectSig`
   parts into queries. This is where MIR and machine are strongest, and the Core keeps
   that path open.

### 6.2 Plan changes for minimal

- Re-estimate S4 at 25 to 35 agent-days, and time-box each group.
- State the span that `diagnose.rs` reports for W0204 at the exit node (3.3).
- Make the builder iterative on long chains, and run `limits.rs` in the S2 exit criteria.
- Start from the commit that merges R3a, and apply the freeze rules of minimal 8.4.
- Keep the old generator behind the switch for one review round, as the plan says.

## 7. Files

- This judgement: `docs/plan/core-ir-inputs/judge_feasibility.md`.
- My probe: `SCRATCH/ir/work/judge/p/d5_count.wf`.
- The compiled copy of the minimal sketch: `SCRATCH/ir/work/judge/core_sketch_copy.rs`.
- The probe list and the timing sample: `SCRATCH/ir/work/judge/allwf.txt`,
  `SCRATCH/ir/work/judge/sample.txt`.
