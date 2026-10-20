# ADR 0012: A core IR between the typed tree and the facts

Status: proposed. Date: 2026-10-20.

The specification is `docs/ir.md`. The plan is `docs/plan/core-ir.md`. The inputs of the
design (the root-cause analysis, the semantics map, the lowering map, three designs and
three judge reports) are in `docs/plan/core-ir-inputs/`; a reference `ir/<name>.md` below
names one of them. This ADR records the decisions, their reasons and the alternatives.

## Context

- Semantic analysis lowers the surface AST straight to facts
  (`crates/weft-sema/src/body/`, 19 410 lines at `b25faf0`). Each surface form needs its
  own special case: temporaries, block tails, handled-body tails, partial moves, closures
  in fields and containers, handler clauses, `resume`, `multi` re-runs, tasks, generics,
  `on abort`, loops. The cases meet.
- Three internal review rounds each found about 20 soundness blockers, almost all in fact
  generation. The classification of rounds 1 to 3 (`docs/plan/core-ir-inputs/root_causes.md`) has 180 unsound
  findings and 53 false positives in 27 root-cause classes. Ten soundness regressions came
  from fixes: a fix in one class broke an assumption of another class.
- The interpreter compiles the AST a second time (`crates/weft-interp/src/compile.rs`).
  Sema exports decisions to it by span (`FnFacts::by_value`, `arg_order`, `int_ops`).
  Where the two lowerings differ, an accepted program faults (class TWO; the late reads
  N1 to N3 of `docs/plan/core-ir-inputs/semantics.md`).
- The proofs (`proofs/borrowing`, `proofs/effects`, `proofs/link`) treat the facts of sema
  as hypotheses. No form between the AST and the facts can carry a theorem.
- The ship rule allows at most two review rounds after the core IR lands. So the
  migration must find by itself what a review round would find.
- Three designs (MIR, machine, minimal) and three judge reports (soundness, feasibility,
  proofs) prepared this decision. The machine design scored highest under the soundness
  lens (8.0) and the proofs lens (8.0); the minimal design scored highest under the
  feasibility lens (7.0). Each judge named grafts from the other designs.

## Decision

Build the core IR of the machine design, with the grafts below. The numbers are the
sections of the specification.

### The IR

- **D1. One IR between the typed tree and the facts (§1).** The IR copies the machines
  that the interpreter and the proofs use: a body is a frame (function, test, closure,
  clause, handled body, scope body); a statement or a terminator is one fact node;
  capabilities, continuations, the unwinder and `multi` copies are explicit IR forms. The
  IR holds no places, no effect rows and no function value sets, so it is built once,
  before effect inference.
- **D2. A typed tree with final types first, in two phases (§2).** The old lowering first
  records the THIR tables (types, callees, argument order, implicit dereferences, integer
  types) during its last lowering. Before `body/` goes away, a standalone `typeck`
  replaces the recorder, with a parity test against the recorded tables (D0).
- **D3. Places (§3, §6.3).** A place is a local and projections, with an explicit `Deref`
  (`Ref`, `Box`, `Rc`), `Field`, `Variant`, `Index`, `Elems` and `Split`. A clause, a
  handled body and a scope body name the locals of their site as upvar locals; a move of
  an upvar local moves the site local. A closure holds its captures in its environment.
- **D4. Operands are read where they are written (choice A, §5.1.1).** The interpreter
  moves to the read point that the facts already assume. This closes the late-read
  findings N1 to N3 by construction.
- **D5. Temporaries and frame ends (§5.1.2, §5.1.4).** A temporary ends at the end of its
  statement; a block tail belongs to the statement around the block; the tail temporaries
  of a loop body end at each iteration. A frame ends in the order of the machine: the
  value goes into `_0`, a scope body waits for its tasks, the locals end, the tail
  temporaries end, the parameters end, and then `Return`.
- **D6. `Dead` is the drop (§5.1.3).** `Dead(l)` drops what is left in `l` and ends the
  cell; it always emits `scope_end`. An `Assign` drops the old value. `Drop` exists only
  for a place behind a pointer, right before its new value. So each free has a statement
  that the verifier checks.
- **D7. Rule CAPTURE (§5.1.7).** A closure captures by move if a body moves the variable;
  it keeps the cell (`Kept`) if the variable is plain data and no body borrows it; else it
  captures by reference. A by-reference capture points into the cell root of the variable,
  which only the end of the variable frees. No reference can point into a kept cell
  (verifier rule V13).
- **D8. Capabilities and continuations are values (§5.1.8).** A perform names a `Cap`
  local, an upvar local, a capability field of an environment, or the row of the caller.
  A call passes the lexical capability environment. A continuation is a `Kont` local, and
  `resume` is a call of it.
- **D9. Cleanup chains are code (§5.1.6).** Each terminator that can abort (also `assert`,
  `ScopeWait`, `Join`, `Fork`) names a cleanup block. A chain finishes `_0` if it has a
  value, then the temporaries newest first, then the locals from the highest slot, then
  the parameters. This is the order of the interpreter today, which unwinds the operand
  stack (the value of the frame) first. In a clause the fresh continuation unwinds first.
  The interpreter runs the chains (landing pads) before the cut over.

### The facts

- **D10. Phases (§6.2).** A terminator that hands control to another frame has a fixed
  list of nodes: `Main`, `Ret`, `FrameEnd`, `AbortValue`, `Exit`, `Post`, `Landing`,
  `Copy`. A value binds where it exists, before each free that comes after it. No node
  binds and frees one variable.
- **D11. Splices and abort destinations (§6.5).** A handled body and a scope body are
  spliced into the component of their site. Each cleanup chain is copied once for each
  abort destination. `unwound_at` and `spared_at` follow from the CFG.
- **D12. The handler order of the machine (§6.5, §6.7).** `Exit` binds the value of the
  `handle` to `_0` of the handled body and to the values of the clauses. `Post` applies the
  part of each clause after its first resume point (a `Resume`, or a run node whose
  summary resumes). `AbortValue` binds the value of a clause that does not resume before
  the cleanup of the handled body. `Landing` and `Post` end the clause frames.
- **D13. Re-entry edges for `multi` (§6.5).** Each `multi` suspension point gets an edge
  back through a `Copy` node, for a local handler and for a handler of a caller. `Copy`
  rebinds only the variables whose places are all in the copied frames.
- **D14. One analysis, no post-passes (§6.6).** A fixpoint for each body (with widening at
  loop heads) and a fixpoint over the call graph (the effect inference) give the abstract
  values. The facts are a pure function of the IR, the states and the summaries.
- **D15. One summary procedure (§6.7).** One summary type and one `apply` serve items,
  closures, clauses (before and after resume), continuations, tasks, stored values and
  `on abort` functions. The relation table `RELS`, checked against `spec/weft.dl` and
  `FnFacts`, says which part carries each relation. Frame roots name the frames that a
  body cannot see: the caller, each callee at each call node, the clause frames, the
  handled body at each `resume`.
- **D16. The spec and the facts schema do not change before the cut over (§1.2).** A
  difference in the diagnostics is then a difference in the facts. `uses(_0)` at each
  `Return` makes the spec derive the local forms of W0204 (`error(_0, Return)`), which
  `diagnose.rs` reports as W0204 at the span of the returned expression.
- **D17. W0313 stays an escape rule (§6.9).** It reads the capability and continuation
  roots of the analysis and keeps the spans of today. A use-based `error` on such a root
  folds into the W0313 diagnostic. W0314 reads the `tasks` part.

### The migration

- **D18. Side by side, by construct group (plan).** `--facts=old|ir|both` and
  `--engine=ast|ir`. A program uses the new facts only if each of its bodies uses only
  enabled construct groups (A first-order, B loops, C closures and function values, D
  handlers, E tasks, F generics). Else it uses the old pipeline as a whole.
- **D19. The diff gate (plan, "The gate").** It compares the old and the new diagnostics
  and facts on the repository programs and on every probe of rounds 1 to 3, of their
  stage verifiers (V001 to V138) and of the IR design: about 57 000 distinct programs. The oracle
  verdict of each program is cached for each interpreter. An accepted program that faults
  blocks a stage, also when the old pipeline accepts it too, unless the ledger names an
  open finding with the verdict "stays". A lost error with a clean oracle needs a signed
  ledger entry. No new false positive in the repository programs. A claims test checks each
  verdict "by construction" and "one rule" against its repro. A fresh sweep of 50 000
  generated programs runs before the cut over.
- **D20. Removal last.** After the cut over and one review round, `typeck` replaces the
  recorder, and then `body/`, the re-lowering loop of `infer.rs`, `compile.rs` and the
  span-keyed exports go away.

## Consequences

- The lowering-mechanics classes of `docs/plan/core-ir-inputs/root_causes.md` go by construction (TEMP, TAIL,
  DROP, ORDER, ACCESS, DEREF, CALLS, ENV, INNER, SUSP, LOOP, VAL, POST, TYPES, TWO,
  MULTI, two PART findings): 87 of 180 unsound findings. The value-flow classes go to one
  rule each (FNVAL, SUM, STORE, GEN, STATE, CAP): 64 findings. 29 stay (spec, types,
  inference bounds, names, `rc` identity). The new findings M1 to M4, J1 to J6, map N1 and
  N2, and semantics N1 to N4 close.
- A new feature needs a builder rule and, if it has a new kind of effect, a summary part
  and a `RELS` row. Each run node and each template gets it at once. The pattern "a feature
  adds a mechanism at the sites that its author knew" has no sites to miss.
- The risk moves into two single points: the analysis and the summary procedure. The fact
  oracle, the summary oracle, trace conformance and the claims test aim at them.
- Run-time behaviour changes in four places, and `docs/design.md` and ADR 0010 state them:
  `x + { x = 5; 1 }` gives 2, not 6; the tail temporaries of a loop body end at each
  iteration; a clause unwinds its fresh continuation before its own values; a plain
  capture that a closure borrows ends with its variable.
- The checker can reject programs that it accepts today and that run cleanly: a returned
  closure that borrows a captured plain value (J5d is unsound today, so this is a fix), an
  overwrite through a reference of a maybe-linear value. The gate lists each one.
- Diagnostics name temporaries by their kind and origin. Some corpus markers move; the
  ledger gives the reason of each move.
- Until the standalone `typeck` (D20), the old lowering still runs in the new pipeline: it
  records the typed tree and gives the `typeck` diagnostics, and the new pipeline drops
  its other diagnostics and its facts.
- The effects model changes `max_slot` to compare slots (proofs track). The interpreter
  takes the model order for a clause frame and its fresh continuation.
- Effect inference becomes a monotone fixpoint over summaries. W0707 (the loop pass bound)
  and W0704 (the parts limit) go away; W0706 stays as a guard.
- The checklist of ADR 0002 changes at its step "fact generation": a new input relation
  needs a template entry or a summary part and a `RELS` row
  (`crates/weft-sema/src/factgen/rels.rs`). `CLAUDE.md` names the new places.
- Size: about 23 500 new lines of code and 3 000 lines of tests; about 21 000 lines go
  away. The plan has 57 stages of a few hours each in its main sequence and 8 in its
  proofs track, and expects follow-up stages for the differences that the gate finds in
  each construct group.
- These gaps stay and are recorded here:
  1. B1 binds the result of a call at the call; the IR binds at `Ret`. The link uses a
     two-node embedding: `Call { ret: None }`, then `Child` or `Copy` from the argument
     that `ret_ok` names.
  2. B1 forbids copying, storing or passing closure values. The closure step of the link
     (L2-clo) needs a B1 extension first.
  3. The link includes only Verus code, so the verifier rules that L0 needs (V1 to V7,
     V12) move into `crates/weft-verified` before L0 (plan stage P3).
  4. Re-entry (`Copy`) nodes have no B1 instruction.
  5. A reference that two versions reach at a join gives two places: B1 needs its
     multi-place extension, or the IR a phi with one group for each edge.
  6. B1 with `Free` needs a lemma that the sets of locals agree at a join (from V4 to V6).
  7. The soundness of summaries and of the abstract values stays a tested hypothesis.
  8. W0313, W0314 and the store forms of W0204 stay Rust checks over the analysis until
     the spec gets relations for capability roots and stores.
  9. Moves and linear values use the variable of the whole local, as the R3a encoding does
     today (PART V023 stays a false positive; R3RT1 stays closed by the R3a rule
     `rest_linear`).

## Alternatives

- **Keep `body/` and fix the findings one by one.** Three rounds show that each round
  finds about 20 new blockers, and that fixes break other classes. Rejected.
- **The MIR design as the base** (`docs/plan/core-ir-inputs/design_mir.md`). It has the best gate and the best
  ideas for the link (versions, a verified fact kernel). But its abort path binds the
  `handle` value after the cleanup chain (M3 stays open), its callee frame root does not
  end on abort paths (M4), its `Recopy` forgets invalidations of outer places (J4 would
  regress), its return node binds and frees at once, and continuations have no root. Its
  unwind-order claim is wrong (`max_slot` is a dynamic order). We take its upvars, its
  resume point, its handle value, its fact oracle, its claims test, its ledger, and,
  after the migration, its versions and its verified kernel.
- **The minimal design as the base** (`docs/plan/core-ir-inputs/design_minimal.md`). It keeps 76 % of `body/`
  and has the lowest regression risk. But the whole clause still runs at the perform
  (J1, M1 stay), clause and callee frames have no roots (F3-2, M4, a J6 regression), `on
  abort` stays atomic, and the classes LOOP, STATE, SUM, FNVAL, CAP and STORE keep the
  mechanisms that gave most of the round-2 and open-list blockers. Its Core is a tree, so
  no embedding theorem into B1 is possible. We take its capture rule, its relation table,
  its validator rules for each component, its rollout by construct group and its parity
  tests.
- **Read operands at the operator (choice B, minimal rule ORDER-2).** No run-time change,
  but the read point needs "formation point, access point, inert parts": a rule that is
  hard to state and to prove, and one more single point of failure. Choice A is the MIR
  rule and matches what the facts assume today.
- **`KeptCell` for each plain capture (machine), or `ByCopy` (MIR D5).** `KeptCell` leaves
  J5 and J5d open (a closure borrows a kept cell after its variable ended). `ByCopy` makes
  `|| count += 1` write a copy, or (with MIR's assignment test) rejects a returned counter
  closure and likely adds a corpus false positive (`125_multi_values.wf`). Rule CAPTURE
  keeps the counter and rejects the borrow.
- **W0313 as W0301 on a capability root (machine, MIR stage M9).** It reports only a use
  after the `handle`, so the escape markers of `62_cap_escape.wf` and `83_kept_values.wf`
  go away, and the documented rule changes. Rejected for the migration; an escape relation
  in the spec is an option.
- **The interpreter unwind order for a clause and its continuation (machine).** It keeps
  the interpreter, but it changes `step_unwind_drop`, the error predicates, `inv_b` and
  L3. We change the interpreter instead; no user program depends on this order.
- **Delete `compile.rs` when the interpreter first runs the IR (machine S3a).** Then the
  old checker checks a different compiler for months, and nothing is left to compare with
  during the review rounds. We keep `--engine=ast` until the removal stages.
- **Reference versions in the migration (MIR D8).** They make `points_into`
  flow-sensitive with no spec change, but they add variables and need the `Copy` rule.
  They come after the removal (track P), before the link step L2-IR.
- **A fallback for each body (minimal).** Mixed programs need a conversion between the
  summaries of the two pipelines. A fallback for each program needs none, and the gate
  reports the coverage of each group.
- **A standalone `typeck` first (all three designs).** It puts the highest-risk work before
  any output. The recorder gives the tables at once, right by construction, and moves the
  extraction to the end, where the recorded tables are its oracle.
