# Judge: proofs and specification

Status: judgement of the three core IR designs. Date: 2026-10-20. Lens: proofs and
specification. I changed nothing in `/home/user/weft`, `/home/user/wt-core` or
`/home/user/wt-edge`. My scratch files are in `ir/work/judge_proofs/`.

`SCRATCH` is `SCRATCH`.
`ir/...` is `SCRATCH/ir/...`. "MIR", "machine" and "minimal" are
`docs/plan/core-ir-inputs/design_mir.md`, `docs/plan/core-ir-inputs/design_machine.md` and `docs/plan/core-ir-inputs/design_minimal.md`. A reference such
as "machine 4.4" is a section of that design.

Note on the base: `/home/user/weft` is now at `b25faf0` (the R3a commits `616f99c` and
`b25faf0` are merged). The designs start from `b073ea7`. The spec at `b25faf0` has 74
input relations, with `rest_linear`.

The questions of this lens:

1. Which design lets the B6 link extend from "exec core to model" to "IR to facts"?
2. Which design matches the B1 CFG model?
3. Which design matches the effects machine (`proofs/effects/src/model.rs`)?
4. Which design makes the comparison of the checker with the interpreter oracle exact?
5. Which design gives the clearest written semantics, and keeps the spec the single
   source of the rules?

## 1. Scores

| Design | Score (0-10) | One line |
| --- | --- | --- |
| machine | **8.0** | The IR is the machine of the proofs. Its frame order follows the effects model, and it found four real defects (M1 to M4). It has the best oracle plan and the most exact model changes. It has no fact versions, so the static-group hypothesis of the link stays open, and its handled bodies cannot move an outer local. |
| MIR | **7.0** | It has the two best ideas for the link: one fact variable for each definition (versions), and a verified fact-generation kernel that the link includes. But its unwind-order claim is wrong, its abort path binds the `handle` value after the unwinding (M3 and M4 stay open), and its landing pads are optional. |
| minimal | **4.0** | A tree in A-normal form that the old walk reads. The fact CFG comes from the walk, the loop re-lowering and a worklist, so no embedding theorem is possible. It keeps three orders that the effects machine does not have. It says so: the link stays a test. |

Scores for each question (my judgement, 0 to 10):

| Question | MIR | machine | minimal |
| --- | --- | --- | --- |
| 1. B6 link from IR to facts | 8 | 7 | 3 |
| 2. B1 CFG model | 7 | 7 | 4 |
| 3. Effects machine | 6 | 9 | 3 |
| 4. Exact oracle comparison | 7 | 9 | 3 |
| 5. Written semantics and spec | 7 | 7.5 | 4 |

Recommendation (section 7): use **machine** as the base. Graft the versions, the verified
fact kernel, the `ByCopy` capture and the `Upvar` base of MIR. Graft the
relation-table test and the per-component validator rules of minimal. Fix five
points that all three designs get wrong or leave open (section 6).

## 2. What I checked

I did not take the claims of the designs as true. This table lists what I read or ran.

| Item | Result | How |
| --- | --- | --- |
| The link hypotheses | `facts_ok` needs one static group `g[v]` for each variable at each node (`instr_groups_ok`). `rebound_at` is only a B1 binding (`binds`). `invalidated_at` has only the call rule. | `proofs/link/src/dataflow_link.rs` lines 125-264 |
| The B1 join | `sub_state` needs `a.locals == b.locals`. The set of locals is fixed. | `proofs/borrowing/src/cfg.rs` |
| The B1 `Call` | `Call { args, ret }` binds `ret.dst` at the call node. `Ret` names an argument and a path. | `proofs/borrowing/src/model.rs` lines 154-189 |
| The unwind order of the effects model | `max_slot` takes the slot with the largest resource id: the newest `Acquire`, a dynamic order. `step_unwind_drop` runs before `step_unwind_abort`, and the error predicates have a `holds_fresh` guard. | `proofs/effects/src/model.rs` lines 265-271, 553-617, 729-739 |
| The spec rules of `invalid` | `invalid(R, Q) :- invalidated_at(R, P), cfg_edge(P, Q).` and `invalid(R, Q) :- invalid(R, P), cfg_edge(P, Q), !rebound_at(R, P).` A rebind after a free hides the free. A rebind at the free node does not. | `spec/weft.dl` lines 206-208 |
| The machine sketch crate | It builds. Its 6 tests pass (`cargo test --offline`, target in `ir/work/judge_proofs/target`). | `ir/work/machine/weft_ir_sketch` |
| The relation list of the machine sketch | The list is a string in the test, not the spec. It has 73 names. The spec at `b25faf0` has 74: `rest_linear` is missing. | `ir/work/judge_proofs/spec_inputs.txt`, `machine_list.txt`, `comm` |
| The minimal type sketch | It compiles with `rustc -W missing_docs` and no warning. | `ir/work/minimal/core_sketch.rs` |
| M1, M3 and M4 (machine appendix A) | The checker accepts each probe at `b073ea7`, at `616f99c` and with `target/debug/weft` of `b25faf0`. `run --unchecked --oracle` faults on each one: "a read of a freed cell". M2 is the same. | the three binaries |

## 3. The five questions

### 3.1 The B6 link from IR to facts

Today the link proves L2 on B1 CFGs. The facts of sema are hypotheses: `facts_ok`,
`bound_before_use` and (for exactness) `no_gen_kill`. A design helps the link if three
things are true:

- The fact CFG is a function of the IR (and of the summaries), not of a walk.
- Each IR statement maps to one B1 instruction, and the facts of that statement are the
  link facts of that instruction.
- The code that makes the facts is code that Verus can see. The link principle is "each
  theorem is about the code that the checker runs" (`proofs/link/README.md`). The link
  includes sources with `#[path]`. It does not copy them.

| Point | MIR | machine | minimal |
| --- | --- | --- | --- |
| Fact CFG is a function of the IR | yes: one node for each statement, a call node and a return node, fixed `Handle` and `Scope` nodes (4.1) | yes: one node for each statement, fixed phases `Main`, `Ret`, `FrameEnd`, `AbortValue`, `Exit`, `Post`, `Landing`, `Copy` (4.1) | no: the walk emits the CFG, `lower_loop` re-lowers loops with a rewind, and the worklist `settle` adds abort and task-end nodes (4.10, 4.11) |
| One static group for each variable | **yes, mostly**: one version for each definition of a reference path (4.2). A version has one rvalue, so one group in most cases. | no: one variable for each move path. Its `points_into` is the union of all its definitions. Versions are only an option (9.3), and OL-NR-flow "stays" (5.3). | no: `points_into` stays flow-insensitive (D18) |
| Where the fact rules live | **in `weft-verified/src/factgen.rs`**, for the reference fragment. Sema calls it. The link includes it (7.5). | in `weft-ir` (plain Rust). L2-IR proves a statement about "the templates", but no design text puts them where Verus can see them (7.5). | in `weft-sema`. "A Verus proof of the fact generator itself stays out of scope." A Rust test compares templates on the corpus (7.4). |
| `bound_before_use` | from versions: a use is only where its definition reaches (7.5) | from verifier rule V4 on each component (4.8 A6) | from validator rules V2 and V3 on each body (4.14 A6) |
| `no_gen_kill` | D16 and the `Assign` shape | the `Ret`, `FrameEnd`, `Exit`, `Post` phases | the separate bind node; but the abort node `A` of 4.8 both unwinds and rebinds `dest` (see 4.3 below) |
| A staged proof plan | items 1 to 4 of 7.5 | **L0, L2-IR, L2-free, L2-clo, L4**, with the hypothesis that each step removes (7.5) | stage S8: a Rust test |

MIR has the best mechanism (versions and a verified kernel). Machine has the best plan
(more steps, and L4 for the effects side). Minimal cannot state an embedding theorem,
because the Core is a tree and the walk decides the CFG.

### 3.2 The B1 CFG model

| Point | MIR | machine | minimal |
| --- | --- | --- | --- |
| Frees in B1 | `Free { x }`, `Free { x, path }` (7.1) | **`Alloc { x }`, `Free { x }`, `FreeSub { x, path }`** (7.1) | `Free { x }` (7.1) |
| A local that starts again in a loop | not covered: B1 has a fixed set of locals, and MIR adds no `Alloc` | covered by `Alloc` | not covered |
| Split places (`v[..k]`, `v[k..]`) | no `Split` projection (2.4) | **`Proj::Split(SplitId, Side)`** (2.2), so `thm_split_sound` of L1 applies to α | no `Split` projection (2.2) |
| The call and its return node | the table puts `ret` on the B1 `Call` at the call node (7.1). This contradicts D16 (the return node binds). | the same contradiction: `Call { args, ret }`, `ret from Σ.ret` (7.1), but `Ret` binds (4.1) | the only design that sees the problem: call node `Call { ret: None }`, bind node `Copy` (7.1). But `Copy` needs a source variable, and none exists. |
| Closures | "No closures in the link goes away" (7.5). This is too strong (section 6). | L2-clo, with the summary hypothesis named (7.1) | "the link can take it with the B2 lemmas" (7.4). Too strong. |
| Captures and frees | `ByCopy` copies the value into the environment (D5). A `Free` of the variable does not touch it. Clean for B1 plus `Free`. | `KeptCell`: the cell outlives its variable (2.2, R11). B1 plus `Free` cannot express this. | `Kept`: the same exception as machine (2.2) |

Neither MIR nor machine is complete here. MIR is better on groups (versions) and
captures. Machine is better on frees (`Alloc`) and places (`Split`).

### 3.3 The effects machine

This question has the largest difference between the designs.

| Point | MIR | machine | minimal |
| --- | --- | --- | --- |
| A body is a block of the model | yes, also the handled body (D2) | yes (7.4) | no: handled bodies and scope bodies are inline (D7). The Core compiler must outline them (6.2). |
| Capabilities | `CapRef::Value` or `Row`, `CapArg` for each effect of the row (2.6). The table of 7.4 maps only `Value` to `Perform`. | **`CapOperand::{Local, Row, Root}` and `CapArgs::Lexical(env)`**: this is `Call { block, caps }` (2.2). `Sig::caps`, `Sig::rets` and `Sig::kmode` each have a source (7.4). | `CapRef::{Local(HandleId), Caller}`. The mapping to `Sig::caps` is not stated (7.3). |
| The unwinder as code | `Unwind(l)` and `UnwindResume`. No form for the drop of a fresh continuation. Not compiled before the optional stage M9. | **`UnwindValue`, `UnwindKont`, `UnwindExit` = `step_unwind_abort`, `step_unwind_drop`, `step_unwind_pop`**. The unwinder runs them from stage S3b. | unwind points (a scope and a count). No statement for each step. |
| Unwind order in a frame | **wrong claim**: "D9 takes the order of the model, so the model does not change" (7.4 item 3). The cleanup chain is static ("newest first" by `StorageLive`, 6.3). The model order is dynamic (`max_slot`: largest resource id). After `consume(a); a = acquire()`, the model takes `a` first, the chain takes the later local first. | correct: change `max_slot` to compare slots, not resource ids (7.4 change 1). A static chain can then match the model. | correct, same as machine (D14, 7.3) |
| A clause frame and its fresh continuation | the interpreter changes to "continuation first", which is the model order (D9, 6.3) | the model changes. Machine names the exact guards: `step_unwind_drop` needs empty slots, `step_unwind_abort` and the error predicates drop `holds_fresh`, `inv_b` must follow (7.4 change 2). | the model changes (7.3). Less detail. |
| Clause code after `resume` | runs at the after-body node (4.9). Closes M1. | runs at `Post`, after `Exit` (4.4). Closes M1. | the whole clause runs at the perform (4.8, "the order of today stays"). M1 stays. |
| A clause that does not resume (M3, M4) | **stays open**. The cleanup chain of the handled body runs first, then the abort node, then the return node binds a new version of `dest` (4.1, 4.9). By spec rule 207, the rebind hides the free. M4 has no frame-root end on the abort path. | closed: `AbortValue` binds `dest` before the cleanup chain (4.4). This is the order of the machine: the clause returns, `drop_now`, then `deliver`. The callee frame root ends on the abort path (4.3). | M3 is caught, but by a node that both unwinds and rebinds `dest` (4.8). This breaks its own claim A5 (`no_gen_kill`, 4.14). M4 stays (F3-2 stays). |
| `multi` re-runs through a handler of a caller | re-entry edges (D10) | re-entry edges (4.4) | none: OL-R2a stays (9.3) |
| Moves of linear values into calls | a model change is needed (7.4 item 2) | `Call { block, caps, moves }` and the `inv_b` argument (7.4 change 3) | not stated |
| CFG lift of the effects checker | named (7.4 item 1) | **the join of `SS` stated: `env` equal, `lin` equal, `k` the conjunction** (7.4 change 4) | "the same work for each IR design" (7.3) |
| A link theorem for effects | none | **L4: the linear and `multi` rules on the facts imply `check(embed_eff(program))`** (7.5) | none |

Machine is the only design whose fact order follows the effects machine on each
handler path. The evidence: the machine view predicted M1 to M4, and I confirmed that
the checker accepts M1, M3 and M4 at `b25faf0` and the oracle faults.

### 3.4 An exact comparison with the interpreter oracle

The comparison is exact when three things are true. The interpreter runs the IR that
the facts come from. The order of the IR is the run-time order, also on abort paths.
Each run-time step maps to one fact node.

| Point | MIR | machine | minimal |
| --- | --- | --- | --- |
| The interpreter runs the IR | stage M3 (`from_ir.rs`), before the facts change | stage S3a (`compile_ir`), before the facts change | stage S6, after the switch of the facts (S5). Until then the facts come from the Core and the interpreter from the AST. |
| Abort paths run from the IR | only at optional stage M9 (landing pads) | **stage S3b: the unwinder runs the cleanup blocks** | never in this design: unwind points are not code |
| IR statements that never run | `Recopy` ("Not compiled", 6.2), cleanup blocks before M9 | none: the re-entry `Copy` is a fact phase, not a statement | `EarlyBorrow` runs; unwind points do not |
| Step-to-node map | each `Op` carries its IR location (6.5) | each op carries its `NodeKey` (6.3 check 2) | by span only, and only in the optional test D4 (6.3) |
| Path cover (`is_cfg_trace` on real runs) | check A1 of the fact oracle | **check 2, trace conformance**: each two steps of one frame follow a `cfg_edge`, also the splice, the abort copy for the destination that the run took, and a re-entry | none |
| Fact oracle | C1, C4, D1, C5, A3 (6.5) | C4, C1, C5, F4, D1, D4 (6.3 check 3) | none (the gate runs the memory oracle only) |
| Summary oracle | partly: check C5/A3 covers writes of a callee to caller memory | **check 4: changes, frees, reads and result pointers of each call, mapped through σ** | none (a test of the `RELS` table) |

Machine makes the comparison the most exact. It also tests the one hypothesis that no
design can prove (summary soundness) on each run.

### 3.5 Written semantics and the spec

| Point | MIR | machine | minimal |
| --- | --- | --- | --- |
| Read point of an operand | choice A: "an operand is read where it is written". One sentence. | choice A | the machine of today: a formation point and an access point, five exceptions, an "inert" test (ORDER-2). Correct, but hard to state and to prove. |
| What the semantics is | P2: "The IR is the semantics". But `Recopy` and the cleanup blocks do not run until M9. | each IR form has its interpreter op and its model step (tables in 0, 6.1, 7.4). Design rules: no right side changes memory or suspends (2.1). | today's machine, written as a tree; abort paths are computed, not written |
| Evidence that the text is consistent | text only | **a sketch crate that compiles, with verifier rules V1 to V7 and tests**; the template table is the output of a test | a type sketch that compiles |
| Internal inconsistencies | D9 (see 3.3); `Call` with `ret` versus D16 | handled, clause and scope bodies reach outer locals as `(*env.k)` (3.8, 3.24, 6.1), but V9 forbids `Move` through `Deref(Ref)`, and 3.25 and 4.6 write `_0 = move x` for an outer `x`. V11 allows `Row(E)` only in a function, a test or a closure, so a handled body cannot perform an effect of a caller. | A5 versus the abort node (see 3.3) |
| Local W0204 forms as spec derivations | **yes: `Return` uses `_0` after the frees; `error(_0, ret)`** (3.5.1, 4.8) | no: `check_returns` stays a check over `refs(_0)` (4.2) | yes, the same as MIR (3.1, 4.5) |
| Every spec input has a source | stated, and `rest_linear` is covered (4.7) | a test, but with a hard-coded list that misses `rest_linear` | a test over the fields of `FnFacts` (`RELS`, 4.7). It cannot go stale. |
| Spec changes | none before M8; optional rules at M9 (5.5) | none before S7 | one reserved step id (the pointer word) |

## 4. Strengths and flaws of each design

### 4.1 machine (8.0)

Strengths:

- The IR copies the machine: a body is a frame and a block, a statement is a B1 node,
  capabilities and continuations are values, the unwinder is code. Each table maps an IR
  form to an interpreter op and a model step.
- The fact order of the handler paths is the machine order: `Exit`, then `Post` (clause
  code after `resume`), and `AbortValue` before the cleanup chain. This view predicted
  M1 to M4. I confirmed that each one is accepted today and faults under the oracle.
- The exact changes of the effects model: `max_slot` by slot, the `step_unwind_drop`
  guard and the error predicates, `Call` with moves, and the `SS` join for the CFG lift.
- The most complete B1 extension: `Alloc`, `Free`, `FreeSub`. `Split` projections make
  L1 (`thm_split_sound`) apply to α with no change.
- A staged link plan (L0, L2-IR, L2-free, L2-clo, L4). L4 is the only plan that links
  the effects facts to the effects model.
- The interpreter runs the IR before the facts change, and runs the cleanup chains at
  S3b. Trace conformance checks `is_cfg_trace` on real runs. The summary oracle tests
  the summary hypothesis.
- Copies of the cleanup chain for each abort destination make `spared_at` and
  `unwound_at` a fact of the CFG. This is the pending-list semantics of the model.
- A sketch crate that compiles, with verifier tests.

Flaws:

- No versions. A reference local with two definitions has one variable with the union
  of the places. `facts_ok` needs one static group for each variable, so L2-IR does not
  remove `facts_ok` as 7.5 says. OL-NR-flow stays (5.3).
- The fact templates live in `weft-ir`, not in a crate that Verus verifies. L2-IR is
  then a theorem about a spec copy, which the link rules forbid.
- The B1 embedding puts `ret` on the call node (7.1), but the facts bind at `Ret`. The
  B1 instruction of the `Ret` node is not stated.
- Handled, clause and scope bodies cannot move an outer local: `(*env.k)` and V9
  conflict. The interpreter allows the move (the body takes the capture when it reads
  it), and O3-14 needs it.
- V11 forbids `Row(E)` in a handled body and a clause. The resolution of capabilities in
  nested bodies (3.1.7 allows only `ByRef` and `KeptCell` for these bodies) is not
  complete.
- `KeptCell` keeps the "cell outlives its variable" exception. B1 with `Free` cannot
  express it.
- The local forms of W0204 stay a check outside the spec.
- The relation list of the test is hard-coded and misses `rest_linear`.
- The change of `step_unwind_drop` also touches L3 (`unwind_drop_linked` in
  `lifecycle_link.rs`) and the mutation tests. 7.4 does not list them.

### 4.2 MIR (7.0)

Strengths:

- Versions (4.2): one fact variable for each definition of a reference path. Each
  variable gets the group of one rvalue. This is the shape that `facts_ok` and
  `instr_groups_ok` need, with no spec change. It also gives `bound_before_use`.
- A verified fact kernel (`weft-verified/src/factgen.rs`) for the reference fragment,
  which sema calls and the link includes with `#[path]` (7.5). This is the only design
  that keeps the link rule "the theorem is about the code that runs".
- One `Call` terminator for items, values, operations, `resume` and tasks. B2
  (`lemma_perform_is_call`) maps a perform and a resume to `Invoke` directly.
- `ByCopy` captures copy the value into the environment (D5). No cell outlives its
  variable, so B1 with `Free` stays simple.
- `Upvar` bases (W5) let a clause, a handled body and a scope body move an outer local.
- Local W0204 forms become `error(_0, ret)` in the spec.
- The after-body node closes M1 (M-new), and `ResumeResult` closes M2.
- The claims test of the gate (8.2 check 7) ties each "by construction" verdict to a
  repro.

Flaws:

- D9 is wrong as written. A static cleanup chain cannot follow `max_slot` (largest
  resource id). The model must change too, as machine and minimal say.
- The abort path binds `dest` after the cleanup chain. M3 and M4 stay open. The order
  also differs from the machine (`deliver` after `drop_now`, with the value made before).
- No `UnwindKont` form: the drop of a fresh continuation is not a statement.
- `Recopy` never runs, and the cleanup blocks run only at optional stage M9. So "the IR
  is the semantics" (P2) is not true on abort and re-entry paths.
- B1 with `Free` but no `Alloc`: a local of a loop body cannot start again.
- No `Split` projection.
- The B1 embedding puts `ret` on the call node, against D16.
- A version is "rebound" at a later definition of its path (4.2). That is not a B1
  binding. The link must read it as "unbound from here" (`unb`), and 7.5 does not say so.
- The effects table maps only `CapRef::Value` to `Perform`.

### 4.3 minimal (4.0)

Strengths:

- Validator rules V2 and V3 hold for each body, so `bound_before_use` covers closure and
  clause components too.
- It is the only design that sees that a two-node call needs two B1 instructions (7.1).
- The `RELS` table test over the fields of `FnFacts` cannot go stale.
- Local W0204 forms become spec derivations.
- The unwind order stays the order of the interpreter, and the model changes to it. This
  order is static, so a chain can state it.
- The text is honest about what stays a test (7.4).

Flaws:

- The Core is a tree. The fact CFG comes from the walk, the loop re-lowering and the
  worklist. So `embed(core)` is not a function of the Core, and no theorem
  `facts(core) == link_facts(embed(core))` is possible.
- Handled and scope bodies are inline. The interpreter and the effects model run them as
  frames and blocks.
- The whole clause runs at the perform (M1 stays). No re-entry for a handler of a caller
  (OL-R2a stays). On these runs the run is not a path of the fact CFG, so the
  hypothesis `is_cfg_trace` of `cfg_soundness` fails.
- The abort node both unwinds and rebinds `dest` (gen and kill at one node). This breaks
  claim A5 and puts the node outside `thm_dataflow_exact`.
- Unwind points are not code. `on abort` is not a call. No statement maps to the steps
  of the unwinder.
- `points_into` stays flow-insensitive. `Kept` cells outlive their variables.
- ORDER-2 keeps the late reads of today. The written rule (formation point, access point,
  inert parts) is hard to state and to prove.
- No fact oracle. The interpreter runs the Core only after the facts switch.

## 5. Where the designs disagree, and which side is right

| Topic | MIR | machine | minimal | Right side for the proofs |
| --- | --- | --- | --- | --- |
| Unwind order in a frame | dynamic "newest", model unchanged | static, reverse slot order; `max_slot` by slot | as machine | machine and minimal. A chain is static. |
| Clause frame or fresh continuation first | continuation first; the interpreter changes | clause frame first; the model changes | as machine | Both work. Machine is cheaper at run time, but it costs a re-proof of `inv_b` and L3. MIR keeps the proofs and changes the visible order of `on abort` output. I prefer MIR here: a change of a verified model is more work than a change of the interpreter, and no user code depends on this order today. |
| Value of a clause that does not resume | bound after the cleanup | `AbortValue` before the cleanup | bound at the cleanup node | machine |
| Copy captures | `ByCopy` (no cell) | `KeptCell` | `Kept` | MIR |
| Outer locals in once-run bodies | `Upvar` base | `(*env.k)` | inline (a local of the same body) | MIR |
| Variables | versions | move paths | locals and part holders | MIR |
| Read point | choice A | choice A | late reads with early borrows | choice A |

## 6. Gaps that all three designs share

These points must be in ADR 0012 for any design.

1. **The return node of a call has no B1 instruction.** All three bind the result at a
   separate node. B1 binds `ret` at the `Call`. The embedding must be: call node
   `Call { args, ret: None }`, and return node `Child` (or a chain of `Child`, or `Copy`)
   from the argument variable that `ret_ok` names. Then `no_gen_kill` holds, and
   `ret_ok` stays the only open condition. No design states this.
2. **Closure values in B1 cannot be copied, stored or passed to a call**
   (`proofs/borrowing/README.md`, "Scope and limitations"). In each IR a closure
   aggregate is an ordinary value that moves into calls and fields. So "closures are in
   the link" (L2-clo) needs a B1 extension first: closure values as call arguments. All
   three designs claim more than B1 gives.
3. **Re-entry nodes (`Recopy`, `Copy`) have no B1 instruction.** A `multi` resume copies
   cells. B1 has no frame copy. The link must leave these nodes out, or B1 needs a copy
   step. E5 covers the linear part only.
4. **Multi-place references at joins.** Versions remove most multi-place variables, but
   a `Deref` of a local that two versions reach still gives two places. The B1
   multi-place extension ("not done") stays needed for joins, or the IR needs a phi with
   one group for each edge.
5. **B1 plus `Free` needs the locals of the two edges of a join to be equal**
   (`sub_state` checks `a.locals == b.locals`). Storage rules (MIR W3, machine V4 to V6,
   minimal V2) give this. The link must state it as a lemma of the verifier rules.
6. **Summary soundness** stays a hypothesis in all three. Only machine tests it on each
   run (the summary oracle).

## 7. Recommendation

Take **machine** as the base. Its IR is the shape that the proofs need, its frame order
is the order of the effects machine, and its oracles make the comparison with the
interpreter exact. Change and graft these points:

From MIR:

1. **Versions** (MIR D8, 4.2): one fact variable for each definition of a reference path.
   This removes the static-group part of `facts_ok` and OL-NR-flow. State in the link that
   a later definition makes an old version unbound (`unb`), not rebound.
2. **The verified fact kernel** (MIR 7.5): put the templates of the reference fragment
   (`Borrow`, `Child`, `Copy`, `Read`, `Write`, `Call`, `MkClosure`, `Invoke`, `Free`,
   `Alloc`) in `weft-verified`. The fact generator calls them. The link includes them
   with `#[path]`, and `check-copies.sh` lists them. Then L2-IR is a theorem about the
   code that runs.
3. **`ByCopy` captures** (MIR D5) in place of `KeptCell`. No cell outlives its variable.
4. **The `Upvar` base** (MIR W5) for clause, handled and scope bodies. A move of an upvar
   is then legal and is a move of the outer storage variable. This fixes the conflict of
   `(*env.k)` with V9.
5. **`error(_0, ret)`** for the local forms of W0204 (MIR 3.5.1). The check moves into the
   spec.
6. **The claims test** of the gate (MIR 8.2 check 7).
7. **Continuation frames first** (MIR D9, second half): change the interpreter, not the
   effects model, for the order of a clause frame and its fresh continuation. In the
   cleanup chain of a clause, `UnwindKont(k)` then comes first, before the values of the
   clause (machine 3.1.6 puts it last). Keep the machine change of `max_slot` (by slot)
   for the order inside a frame.

From minimal:

8. **The relation table test** (minimal 4.7, `RELS`): generate the list of relations from
   `FnFacts` and from the input list of the spec, not from a string. This would have
   found the missing `rest_linear`.
9. **The per-component validator rules** (minimal V2, V3) as the source of
   `bound_before_use` for each component.

Fix in machine:

10. V11: allow `Row(E)` in each body whose capability environment resolves `E` to the row.
11. 7.1: state the two-node call embedding of section 6, item 1.
12. 7.4: list the proofs that the change of `max_slot` touches: `inv_b` (`own.rs`,
    `own_steps.rs`), L3 (`unwind_linked` uses `step_unwind_abort`), the examples and
    the mutation tests of `proofs/effects` and `proofs/link`. Without graft 7, also
    `unwind_drop_linked`.

Keep from machine: `AbortValue` before the cleanup, `Exit` then `Post`, `UnwindKont`,
copies of cleanup chains for each destination, mandatory landing pads (S3b), trace
conformance, the fact oracle, the summary oracle, B1 with `Alloc`, `Free` and
`FreeSub`, `Split` projections, the effects changes for moves and the `SS` join, and
the link steps L0 to L4.

Order of proof work after the switch: L0 (verifier rules as a Verus spec), then L2-IR on
the reference fragment with versions and the verified kernel, then L2-free (B1 with
`Alloc` and `Free`, and the join lemma of section 6, item 5), then the B1 extension for
closure arguments and L2-clo, then the effects CFG lift and L4. Each step removes one
hypothesis of `proofs/link/README.md`, "What stays only tested".

Do not take for the proofs: minimal as the base (no embedding is possible), MIR D9 as
written, the MIR abort-node order, and `KeptCell`.

## 8. Files

- This judgement: `docs/plan/core-ir-inputs/judge_proofs.md`.
- The spec input list and the machine list that I compared:
  `ir/work/judge_proofs/spec_inputs.txt`, `ir/work/judge_proofs/machine_list.txt`.
- The build of the machine sketch: `ir/work/judge_proofs/target/`.
- The probes that I ran: `ir/work/machine/m1_post_resume.wf`,
  `m6b_resume_result_ref.wf`, `m8_abort_value_into_body.wf`,
  `m10_abort_value_callee_local.wf`.
