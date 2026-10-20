# Root causes of the soundness findings in fact generation

Status: analysis for the core IR design. Date: 2026-10-20. Source: commit b073ea7 and the
reports of review rounds 1 to 3.

## Summary

- I classified 290 findings. 180 are unsound findings: the checker accepts a program that
  faults or breaks a design rule. 53 are false positives. The others are duplicates
  (27), interpreter defects (17), findings that are not about soundness (11), a
  false hypothesis of the proof link (1) and a finding that the fixer rejected (1).
- Each finding has one primary root cause. There are 27 classes in three groups:
  lowering mechanics, value flow and summaries, and causes outside fact generation.
- Take a core IR of the form in "The IR that the verdicts assume". It removes by construction
  the classes of 83 of the 180 unsound findings (46%). It removes partly the classes
  of 70 findings (39%). It does not remove the classes of 27 findings (15%).
- Of the 83 findings that the IR removes by construction, 44 need only the five features of
  the task: explicit temporaries, moves, drops, closure environments and suspension points.
  39 also need an explicit dereference, one call terminator, one body for each inner
  body, one fixpoint over the IR, or (for 4 of them) an interpreter that runs the IR.
- For the false positives the numbers are 25 (47%), 18 (34%) and
  10 (19%).
- 104 of the 180 unsound findings (58%) have at least one cause, primary or
  secondary, in a class that the IR removes by construction.
- The largest classes in fact generation are function values (FNVAL), closure environments
  (ENV), summaries (SUM), capabilities (CAP), temporaries (TEMP), inner bodies (INNER) and
  stored references (STORE). The IR removes ENV, TEMP and INNER by construction. It removes
  FNVAL, SUM, CAP and STORE only partly. These four are questions of the abstract value domain
  and of the summary language, not of the lowering.
- Ten soundness regressions and fourteen false-positive regressions came from fixes. In each
  soundness regression, a fix in one class broke an assumption of the code of another class. A
  uniform IR removes most of these interactions, because one mechanism replaces the special
  cases that met.
- The verdicts have conditions. The interpreter runs the same IR. The analysis over the IR is one
  fixpoint. There is one capture rule. Drop elaboration has cleanup paths and explicit `on abort`
  calls. The IR has move paths. Without the first condition, the IR is a third lowering of the
  AST. The section "Requirements for the IR design" lists them.

## Scope and method

### Sources

- Round 1: `redteam_review.md` (RT1 to RT24), `spec_review.md` (F1 to F14),
  `quality_review.md` (QR1 to QR22), `interp_report.md`.
- Round 2: `r2/oracle.md` (OR), `r2/redteam.md` (RR), `r2/fidelity.md` (FD), `r2/quality.md`
  (QA), `r2/interp.md` (IP).
- Round 3: `r3/oracle.md` (O3), `r3/redteam.md` (R3RT), `r3/fidelity.md` (F3), `r3/interp.md`
  (I3), `r3/quality.md` (Q3).
- Open lists: the sections "From S3/S4 ... recorded in ADRs" and "Open after ..." of
  `round1b_tasks.md`, and the `not_resolved` items of the stage results. Ids start with `OL-`.
- Stage verifiers: the `blocker` and `major` issues of the `verify probe` and `verify review`
  steps in `round1a_results.json`, `round1b_results.json` and `round2_results.json`. They are
  numbered V001 to V138 in file order (Appendix B). They are part of the internal review
  rounds, and they show the regressions of the fixes.
- Code: `crates/weft-sema/src/body/`, `crates/weft-interp/src/code.rs` and `compile.rs`,
  `spec/weft.dl`, `crates/weft-facts`, ADR 0002, 0003, 0005, 0006 and 0007.

### Kinds and counts

| Kind | Meaning | Rows |
| --- | --- | --- |
| U | Unsound: the checker accepts a program that faults or breaks a design rule. A difference between sema and the interpreter that makes an accepted program fault is U. | 180 |
| FP | False positive that fact generation or a rule causes | 53 |
| H | A hypothesis of the proof link is false; no unsound acceptance | 1 |
| DUP | The same defect as another row (Appendix A names it) | 27 |
| I | A defect of the interpreter only | 17 |
| N | Not about soundness: names, messages, speed, a crash, docs | 11 |
| REJ | The fixer could not reproduce it | 1 |

Unsound findings by source: review reports 94 (round 1: 31, round 2: 25, round 3: 20, open lists: 18), stage verifiers 86 (round 1: 47, round 2: 39).

Rules for the counts:

- Each counted finding has one primary cause. The counts use only the primary cause. The
  secondary causes are in the tables and in Appendix A.
- I split a finding with independent causes: RT3 into RT3a, RT3b and RT3c, RT24 into RT24a
  to RT24d. F5 counts only its tuple part; its closure part is RT8.
- A finding that names several shapes counts once. The class text names its shapes.
- Reports of the docs, the proofs, the speed and the messages are not in the tables. They are
  not soundness findings. These are: round-1 F7 to F14; QR1 to QR22 except QR5, QR6 and QR7;
  FD5 to FD15; QA4, QA5 and QA8 to QA13; IP9 to IP11; I3-5 to I3-13; F3-10 and F3-12 to F3-15;
  Q3-2, Q3-4 and Q3-5. Appendix A lists some of them as N or I where a class text names them.

### The IR that the verdicts assume

The task names five features: explicit temporaries, moves, drops, closure environments and
suspension points. The verdicts assume the usual form of these features in a MIR-like IR:

1. A body is a CFG of statements and terminators over typed locals. Each intermediate value is
   a local with `StorageLive` and `StorageDead`.
2. An operand is `copy p`, `move p` or a constant. A place is a local and projections, with an
   explicit `Deref`.
3. Drop elaboration writes `Drop(p)` on normal paths and on cleanup paths. A drop of a value
   with `on abort` on a cleanup path is a call of that function.
4. A closure literal is an aggregate of its environment (`&x` or `move x`). Each closure,
   handler clause, handled body and scope body is a body of its own, as each one is a `Code`
   unit of the interpreter today.
5. One `Call` terminator serves items, values, methods, performs and resumes. Each terminator
   that can suspend has an explicit abort edge, and a multi point has a re-entry edge.
6. The builder runs after type inference. One fixpoint over the IR gives the facts.

Features 2, 4 (one body for each inner body), 5 (one `Call` terminator) and 6 go beyond the five
named features. The column "Five features" of the overview says if a class needs only the five
named features.

### Verdicts

- **By construction**: no IR program can show the defect, because the IR has no form for it.
  For example, with storage statements, no temporary can lack an end.
- **Partly**: the IR removes the part that comes from one surface form. The class also needs a
  decision about the abstract domain, the summaries, the spec or the language.
- **Not at all**: the cause is outside the lowering of a body.

## Overview

Groups: A is lowering mechanics, B is value flow and summaries, C is outside fact generation.
A* is lowering mechanics that needs the interpreter to run the IR.

| Class | Root cause | Group | U | FP | Verdict | Five features | IR feature |
| --- | --- | --- | --- | --- | --- | --- | --- |
| [TEMP](#temp) | Temporaries and hidden values have no storage and no end | A | 9 | 0 | By construction | yes | Each value is a local with `StorageLive` and `StorageDead` |
| [TAIL](#tail) | The tail value of a frame or a branch is not a move | A | 4 | 1 | By construction | yes | Each value-giving construct ends in `dest = move p` or `dest = copy p` |
| [DROP](#drop) | Drops, frees and unwinder calls are not explicit | A | 8 | 1 | By construction | yes | Drop elaboration: `Drop(p)` on normal and cleanup paths; `on abort` is a `Call` |
| [ORDER](#order) | Evaluation order and the node of an access are implicit | A | 1 | 0 | By construction | yes | Each access is an operand of one statement |
| [ACCESS](#access) | Reads and writes are not explicit operands | A | 3 | 0 | By construction | no | `copy p` and `move p` operands, assignment destinations, `Len(p)` |
| [DEREF](#deref) | Dereference is implicit (places through references and handles) | A | 7 | 1 | By construction | no | Places with an explicit `Deref` projection |
| [CALLS](#calls) | Each call form has its own argument code | A | 8 | 3 | By construction | no | One `Call` terminator for items, values, methods, performs and resumes |
| [ENV](#env) | The closure environment is not explicit | A | 15 | 5 | By construction | yes | A closure is an aggregate of its environment; its body takes the environment |
| [INNER](#inner) | Inner bodies are not bodies: closures, clauses, handled and scope bodies are re-applied by hand | A | 9 | 3 | By construction | no | One IR body for each closure, clause, handled body and scope body |
| [SUSP](#susp) | Suspension points and their abort edges are not explicit | A | 5 | 5 | By construction | yes | Suspension terminators with explicit abort edges to cleanup paths |
| [MULTI](#multi) | The re-run of code by a multi resume is not explicit | B | 2 | 1 | Partly | - | Re-entry edges after each multi suspension point |
| [LOOP](#loop) | Loops are lowered by repeated passes, not analysed by a fixpoint | A | 3 | 1 | By construction | no | A worklist fixpoint over back edges |
| [STATE](#state) | The state of a local is lowering state, not a dataflow fact | B | 3 | 8 | Partly | - | A dataflow fact for each local at each point, with joins |
| [VAL](#val) | Value propagation is written once for each surface form | A | 2 | 3 | By construction | yes | `Assign` and `Aggregate` statements, one transfer function each |
| [POST](#post) | Post-passes after the body run in a fixed order | A | 5 | 1 | By construction | no | One fixpoint for all facts of a body |
| [TWO](#two) | Two lowerings of one AST: sema and the interpreter disagree | A* | 4 | 0 | By construction, if the interpreter runs the IR | no | The interpreter runs (or compiles from) the same IR |
| [TYPES](#types) | Facts are made before the types are final | A | 0 | 1 | By construction | no | The IR is built after type inference |
| [FNVAL](#fnval) | Function values: callee sets travel in types and side channels | B | 22 | 2 | Partly | - | A callee operand; a closure analysis or summaries must give its bodies |
| [STORE](#store) | Stored references: no region for a reference behind a reference or in a function value | B | 9 | 0 | Partly | - | One store form for functions, closures and clauses; no regions |
| [PART](#part) | Partial moves and partial initialization have no move paths | B | 3 | 1 | Partly | - | Move paths for init state and drops; spec rules per path |
| [GEN](#gen) | Generic flow: values of a type parameter | B | 7 | 1 | Partly | - | Values of `T` flow like other values; instantiation stays |
| [CAP](#cap) | Capabilities and continuations are not values | B | 11 | 2 | Partly | - | Capabilities and continuations as values with storage |
| [SUM](#sum) | Summary parts are designed by hand for each feature | B | 13 | 3 | Partly | - | Summary parts as queries over the callee IR |
| [SPEC](#spec) | A rule of the spec or a fact model is too weak or too coarse | C | 13 | 3 | Not at all | - | None |
| [TYPE](#type) | Type properties, signature checks and prelude signatures | C | 12 | 4 | Not at all | - | None |
| [INF](#inf) | Bounds of the inference over the call graph | C | 1 | 1 | Not at all | - | None |
| [NAMES](#names) | Names and visibility | C | 1 | 2 | Not at all | - | None |
| | **Total** | | **180** | **53** | | | |

| Verdict | Unsound | Share | False positives | Share |
| --- | --- | --- | --- | --- |
| By construction (A) | 79 | 44% | 25 | 47% |
| By construction if the interpreter runs the IR (A*) | 4 | 2% | 0 | 0% |
| Partly (B) | 70 | 39% | 18 | 34% |
| Not at all (C) | 27 | 15% | 10 | 19% |

### By round

| Round | Unsound | A and A* | B | C |
| --- | --- | --- | --- | --- |
| Round 1 (reports and stage verifiers) | 78 | 41 (53%) | 23 (29%) | 14 (18%) |
| Round 2 (reports, S5a and R2a-R2e verifiers) | 64 | 25 (39%) | 30 (47%) | 9 (14%) |
| Round 3 (reports) | 20 | 12 (60%) | 4 (20%) | 4 (20%) |
| Open lists | 18 | 5 (28%) | 13 (72%) | 0 (0%) |

Round 1 found mostly lowering mechanics. Round 2 and the open lists moved to value flow and
summaries. The fixes of round 1 closed the common shapes. The next shapes were in data, at
function boundaries and in function values. Round 3 found lowering mechanics again, at the
edges of frames: tails, temporaries, and values that leave a handled body, a clause or a
scope. Each new kind of frame or value needs the same special cases again.

## Classes

### TEMP

**Temporaries and hidden values have no storage and no end.** Group A. Verdict: **By construction**.

- Unsound (9): RT4, RT18, V007, V015, V072, OL-3c, O3-2, O3-3, F3-7.
- False positives (0): none.
- Proof hypotheses (1): IP8.
- Secondary cause of: V020.

*Now.* Sema gives a root only to some temporaries (`temp_root`). Helpers such as `hold`, `hold_later`, `hold_operand`, `hold_moved`, `hold_part` and `hold_as` hold an operand on its way to a call. The end of a temporary depends on the surface form. It can be the end of a statement (`stmt_temps`), the end of a handled body, a scope body or a clause, or a jump in a later operand. The hidden values have rules of their own: the iterator of `for`, the part holders and the unset place fields.

*Findings.* A temporary has no owner (V007). A value leaves a frame before the temporaries of the frame end (O3-2, O3-3, F3-7). An operand is not held while the later operands run (RT4, V015, V072, OL-3c). A hidden variable does not get the properties of its source (RT18). A hidden variable has no binding (IP8).

*Why by construction.* In the IR each intermediate value is a local. The builder writes `StorageLive` where the value starts and `StorageDead` where it ends. One rule gives the end for each frame kind: the end of the statement, or the end of the frame. A reference to a temporary is a reference to a local. So the owner rule applies with no special case: a move or an end frees the root. An operand is a local that lives until the `Call` terminator. A value that leaves a frame moves into the destination of the instruction that runs the frame. This move comes before the `StorageDead` of the temporaries of the frame. The iterator and the part holders are typed locals.

*Conditions.* The storage rules must be the rules of the interpreter. The interpreter already has them (`Op::StmtBegin`, `Op::StmtEnd`, one `Code` unit for each frame). See TWO.

### TAIL

**The tail value of a frame or a branch is not a move.** Group A. Verdict: **By construction**.

- Unsound (4): V059, V118, O3-1, O3-14.
- False positives (1): V058.
- Secondary cause of: OR6.

*Now.* Each frame kind has its own code for its tail value: block, `if`, `match`, `handle`, clause, `scope`, closure body, loop body and statement. A bare place as a tail moves in the interpreter. Sema treated it as a move only in some frames.

*Findings.* The arm tail of `if` and `match` (V059). The tail of a discarded block (V118). The tail of a `scope` body (O3-1). The tail of a `multi` handled body (O3-14). The false positive V058 has the same cause.

*Why by construction.* Each construct that gives a value lowers to `dest = operand`. The operand is `move p` for a value that is not plain data, else `copy p`. A discarded value gets a new destination, and the builder drops it. So one rule covers each frame. A re-entry edge (MULTI) repeats the move for each resume.

### DROP

**Drops, frees and unwinder calls are not explicit.** Group A. Verdict: **By construction**.

- Unsound (8): RT1, RT14, V002, V057, FD1, O3-4, F3-1, F3-3.
- False positives (1): V083.
- Secondary cause of: V010, OL-3c, OR6, V117, V119, F3-6.

*Now.* There is no drop instruction. A free comes from `moved_at` and `scope_end` through the `owner` rule. Sema finds a drop of a linear value with one check for each form. The forms are a `_` pattern, `print`, an overwrite, a prelude function with a `drops` part (`Vec.clear`), a generic body (a pass over its type parameters), and an abort edge (`unwound_at`). The unwinder calls `on abort` functions, but these calls are not calls in the facts.

*Findings.* A move or a scope end frees nothing (RT1). A linear value goes away in a pattern, in an argument of `print` or at an overwrite (RT14, V002). A generic `T` moves into a holder that goes away (V057). The effects and changes of an `on abort` function do not count (FD1, F3-1, F3-3). A spawn statement drops a task result (O3-4). In the false positive V083, an abort edge does not end a linear owner.

*Why by construction.* Drop elaboration, as in MIR, writes an explicit `Drop(p)` where an initialized value that is not plain data goes away. These points are the end of storage, an overwrite (`Drop(p); p = v`), a `_` pattern, a discarded temporary and each unwind edge (cleanup blocks). On a cleanup path, the `Drop` of a type with `on abort` is a `Call` of that function. So its effects, its changes and its `drops` part apply at that node, with the rules of a call. The `drops` part of a generic body is then "a `Drop` of a place whose type holds `T`". The builder finds it from the types.

*Conditions.* The library decides what a drop of an extern type does: `Task<T>`, `Vec<T>`, the values of `fork` (F3-6 and RR8 are in TYPE). The effects proof models `on abort` as atomic. If the checker treats it as a call, the model must change. Else W0118 stays, and the IR only makes its input explicit.

### ORDER

**Evaluation order and the node of an access are implicit.** Group A. Verdict: **By construction**.

- Unsound (1): RT2.
- False positives (0): none.
- Secondary cause of: RT4.

*Now.* Sema keeps a current node and queues of pending uses and reads (`pend_uses`, `pend_reads`). The next `emit` writes them into the next node. That node can be in another component or in another branch.

*Findings.* Uses go to the wrong node (RT2). The same cause is a part of RT4.

*Why by construction.* In the IR each use and each read is an operand of one statement or terminator. There is no queue. The order of the arguments is the order of the assignments to their locals.

### ACCESS

**Reads and writes are not explicit operands.** Group A. Verdict: **By construction**.

- Unsound (3): RT10, OL-R2d-box, OR8.
- False positives (0): none.
- Secondary cause of: V013, OR5, O3-6.

*Now.* Sema records reads only in some forms: field paths, call arguments and `print`. These were not reads or writes: a use of a reference variable as a value, a use or a new value of a whole local, an index borrow, and a borrow through a `Box`.

*Findings.* RT10, OR8, OL-R2d-box. The same cause is a part of V013, OR5 and O3-6.

*Why by construction.* In the IR a read is a `copy p` or `move p` operand. A write is the destination of an assignment. `&v[i]` lowers to a bounds check that reads `Len(v)`. `&(*b).items` has a `Deref` of `b`, so it reads `b`. Fact generation writes `reads_at` and `mutates_at` from the operands and the destinations only.

*Conditions.* The access rules of the spec give the precision (V013 is in SPEC).

### DEREF

**Dereference is implicit (places through references and handles).** Group A. Verdict: **By construction**.

- Unsound (7): RT9, V008, V014, V020, V098, O3-6, R3RT2.
- False positives (1): V085.
- Secondary cause of: RT3a, OL-4a, OL-S5a-store, OL-R2d-box, V076, V077, R3RT3.

*Now.* Sema resolves a place through a reference, an `Rc` handle, a `Box` or a reference in a part. It has one mechanism for each form: `held_refs`, roots such as `*rs`, handle dependencies (`handle.*`) and `by_ref` bindings in `match`.

*Findings.* `c += 1` on a reference local (RT9). A compound assignment through a reference in a field (V014). A write through a tuple part (V098). Handle dependencies of `Rc` results and receivers (V008, V020, O3-6). A `match` through a reference (R3RT2). The false positive V085 has a bogus `*v..` root.

*Why by construction.* An IR place is a local and a list of projections, with an explicit `Deref` (`(*x).f` in MIR). `c += 1` on `c: &u64` is `(*c) += 1`. A place below a `Deref` is a place of the target of the reference. So a write there changes the target and reads the reference. A place through `(*h)` of a handle depends on `h`, because `h` is in its path.

*Conditions.* The abstract domain of the analysis still gives the places that a reference can point to (`points_into`, held references). The IR removes "a form forgot the dereference". It does not remove the abstraction.

### CALLS

**Each call form has its own argument code.** Group A. Verdict: **By construction**.

- Unsound (8): RT17, RT24a, F3, V035, V039, V042, V136, R3RT3.
- False positives (3): OL-S5c-w0312, O3-7, R3RT7.
- Secondary cause of: RT5, RT6, RR10.

*Now.* Sema has separate code for each call form. The forms are item calls (`call_fn_as`), value calls (`call_value`), method calls with special cases (`join`, `detach`, `spawn`, `sim.run`), performs (`perform_op`), `resume`, `fork` and the runs of a closure. Each form decides on its own the call arguments, the held references, the named arguments, the `in` places and the aliasing.

*Findings.* A perform is not checked as a call (F3, V035, R3RT7). One test for `&T` arguments is written three times (V042). A value call has no alias pairs (V039). `join` and `detach` ignore their arguments (V136). The references behind a reference argument are not call arguments (R3RT3). A check exists only on the path of a direct call (RT17, RT24a). False positives: O3-7, OL-S5c-w0312.

*Why by construction.* The IR has one `Call` terminator with a callee operand and argument operands. A perform is the same terminator with a capability operand. `resume` is a call of the continuation. The builder computes the call arguments, the held references, the `in` places and the aliasing once, for each kind.

### ENV

**The closure environment is not explicit.** Group A. Verdict: **By construction**.

- Unsound (15): RT5, RT8, V009, V017, V018, V027, OL-5, OR2, RR4, RR7, V103, V104, V116, V125, V134.
- False positives (5): V012, RR12, O3-11, R3RT5, F3-11.
- Secondary cause of: F5, V002, V015, V035, V061, V108, F3-8.

*Now.* Sema lowers a closure body in place, with the values that the captures have where the closure is made. The captures are a list in the summary. A capture by value is a `moved_at` at the node that makes the closure. A node that runs the closure applies the summary again. Then nine "late join" functions (`late.rs`) add the values that the captured variables have at that node. Later fixes compute the modes of a closure from its captures.

*Findings.* A closure argument holds references (RT5, V027). Modes (RT8, OL-5). The values of captures at the run node (RR7, V103, V104; false positives O3-11, F3-11). The time of the move of a capture (OR2, V017, V116; false positive R3RT5). A capture of the scope capability (RR4, V134). Captures of a clause (V009, V018). Copy captures (V125; false positives V012, RR12).

*Why by construction.* A closure literal lowers to an aggregate of its environment. The aggregate has `&x` for a capture by reference and `move x` for a capture by value. The closure body is a body whose first parameter is the environment. So the modes of the closure are the type properties of its environment fields. A closure argument holds the references of its environment, as each aggregate does. The body reads `*env.x` when it runs, so the value at the run node counts with no late join. A capture by value moves at creation, in the checker and in the interpreter. A capture of `s` is a reference to `s`. A clause is a closure whose environment the `handle` builds.

*Conditions.* The builder and the interpreter need one capture rule: by value if the body moves the capture, else by reference. Today a captured copy variable has a cell that outlives its scope for the closure, but not for a reference into it (ADR 0003, `kept` in ADR 0006). That split needs one decision; V125 comes from it. RR12 and F3-11 also need a must-write part in the summary of a body ("assigns `*env.x` on each path"). A closure that leaves the body needs FNVAL and STORE.

### INNER

**Inner bodies are not bodies: closures, clauses, handled and scope bodies are re-applied by hand.** Group A. Verdict: **By construction**.

- Unsound (9): RT11, RT12, F4, V006, V024, V053, RR5, V121, R3RT4.
- False positives (3): OL-R2d-clause, O3-8, O3-12.
- Secondary cause of: RT2, F3, V009, V018, V036, OL-S5c-w0312, V127, O3-2, O3-3, O3-7.

*Now.* Closure bodies, clauses, handled bodies and scope bodies are components of the CFG of the function. A node that runs one applies a hand-written list of fact kinds again. `Summary` has 39 fields, and `ContInfo` has `muts` and `frees`. Sema decides jumps (`return`, `break`) and the ends of locals for each body kind.

*Findings.* Jumps (RT11). The locals of the body (V006). Fact kinds that the summary did not carry: spawns (RT12), parameter mutations (F4), `lends_mut` (V024), frees of the handled body (RR5, V121). Values into clause parameters (V053). Results through closure parameters (R3RT4). False positives: O3-8 (the summary keeps the capability of a handler inside the closure), O3-12, OL-R2d-clause.

*Why by construction.* In the IR each inner body is a body with its own entry, `Return`, storage and drops. The interpreter has the same units (`CodeKind::Closure`, `Clause`, `HandleBody`, `ScopeBody`). A run of an inner body is a call. Two designs then need no list of fact kinds. Design (a): one summary procedure for each body, functions and inner bodies alike, so each summary has each new fact kind. Design (b): a call edge into the inner body and a return edge back, so each fact flows on the edges. Design (b) is simpler, but it merges the runs of one closure.

### SUSP

**Suspension points and their abort edges are not explicit.** Group A. Verdict: **By construction**.

- Unsound (5): RT13, V036, V074, V086, V088.
- False positives (5): V055, OL-R2c-1, OR4, V084, O3-10.
- Secondary cause of: V040, OL-1d, OL-3a, RR5, RR6, V082, V083, V089, V095, V116, V121, R3RT4, F3-7, F3-8.

*Now.* Sema marks multi and abort nodes in each form that can suspend. `multi_node` has five call sites, `abortive` and `abortive_local` have twelve, and `note_abort_ctx` has four. Sema adds the abort edges after the body (`finish_aborts`). It computes `spared_at` from `outside_vars`. A `resume` maps changes onto clause parameters with special encodings.

*Findings.* Some node kinds get no abort edge (V074, V086, V088). A call of an unknown value is not a multi point (RT13). A clause parameter across `resume` (V036). False positives: an abort edge that skips a scope end (V084), values outside the handled body (OR4, OL-R2c-1), a spawn as a multi point (O3-10), the order of `resume` and spawn (V055).

*Why by construction.* Each terminator that can suspend has an explicit abort edge. These terminators are a perform, a call of a callee whose row can perform, a resume, a scope end and a join that can fail, and the call of an `on abort` function. The edge goes to the cleanup path of the frame that the abort leaves. For a local handler that frame is the handled body. For a handler of a caller it is the function. A cleanup path goes through the scope ends and the drops of each frame that it leaves. A value outside the handled body is not on the cleanup path of a local operation. So `spared_at` is a fact of the CFG. A spawn does not suspend the task that spawns.

*Conditions.* The summary of a callee tells if it can abort or resume more than once (V040 and V082 are in SUM).

### MULTI

**The re-run of code by a multi resume is not explicit.** Group B. Verdict: **Partly**.

- Unsound (2): OL-R2a, V097.
- False positives (1): OL-NR-multi.
- Secondary cause of: FD4, V124, O3-14.

*Now.* Sema lowers the handled body of a local `multi` handler as a loop (`handled_again`). It does not model a `multi` operation of a handler of a caller. One-place instances assume one run of the code.

*Findings.* OL-R2a, V097. The false positive OL-NR-multi.

*What the IR removes.* The IR can have an explicit re-entry edge after each multi suspension point. The edge goes from the end of the continuation back to the node after the suspension point. A statement on the edge gives the copied locals the state of the suspension point. One rule covers local handlers and handlers of a caller. One-place instances, tail moves (O3-14) and liveness then see the cycle.

*What stays.* The spec decides which values a `multi` resume copies, and which values it cannot copy (FD4 and V124 are in SPEC). The re-entry edge for a handler of a caller needs the summary bit "can resume more than once" of the callee.

### LOOP

**Loops are lowered by repeated passes, not analysed by a fixpoint.** Group A. Verdict: **By construction**.

- Unsound (3): V025, V041, RR1.
- False positives (1): V101.
- Secondary cause of: none.

*Now.* `lower_loop` lowers the loop body again and again (`rewind`, keys of the carried locals) until the carried values are stable. It widens after eight passes. It reports W0707 at a bound.

*Findings.* A call comes before a new value in the loop body (V025, V041). A pass bound (RR1). The false positive V101 comes from the widening.

*Why by construction.* The IR has back edges. The analysis is a worklist fixpoint over the CFG. So a statement before a new value in the loop body sees the value of the next iteration, through the back edge. No pass bound applies to the lowering, and no state is cloned (QA7, V102).

*Conditions.* A value that goes deeper in each iteration (`cur = &cur.next[0]`) still needs widening. Its precision (V101) is a choice of the analysis.

### STATE

**The state of a local is lowering state, not a dataflow fact.** Group B. Verdict: **Partly**.

- Unsound (3): RT24b, V066, V096.
- False positives (8): V069, OL-4b, OL-6a, OL-R2b-holds, OL-NR-flow, O3-9, R3RT6, R3RT10.
- Secondary cause of: none.

*Now.* `Local` holds `uniq`, `caps`, `tasks`, `refs` and `summary` as fields. The walk over the AST changes them. After `if` and `match` the last branch wins, or a set only grows. `points_into` has no node.

*Findings.* `uniq` after a rebind or an `if` (RT24b, V066). A join of a handle that may hold one of several tasks (V096). False positives: sets that only grow (OL-6a), stale holders (V069, OL-4b, R3RT10), places with no flow (OL-NR-flow, OL-R2b-holds, R3RT6), joins that sema does not see (O3-9).

*What the IR removes.* In the IR the state of each local is a dataflow fact at each point, with a join at each merge. So the order of the lowering cannot decide a mode (V066). A must fact ("the task is joined") is a separate analysis from a may fact ("the handle can hold the task") (V096).

*What stays.* `points_into(R, Path)` has no node in the spec. So a reference keeps all its places on all paths (R3RT6, OL-NR-flow, V069). A flow-sensitive relation is a change of the spec.

### VAL

**Value propagation is written once for each surface form.** Group A. Verdict: **By construction**.

- Unsound (2): RT3a, V073.
- False positives (3): RT22, V044, OL-6b.
- Secondary cause of: V042, V047.

*Now.* Each expression gives a `Val` bundle with thirteen fields. Some fields are the type, the references, the summary, the task set, the capabilities, the `uniq` mark, the `empty` flag and the part holders. Each surface form makes a new `Val` and must copy each field.

*Findings.* Struct and array literals, value-call results and by-value bindings lose their references (RT3a). A `handle` keeps `empty` of its body (V073). False positives: a wrapper or a join drops a task set (RT22, V044); the empty value `None` (OL-6b).

*Why by construction.* In the IR an expression gives an operand. `if`, `match` and `handle` assign the value of each branch to one destination local. Struct, tuple, array and enum literals are one `Aggregate` statement. The analysis has one transfer function for each statement kind (about ten), not one for each surface form. So no form can forget a field.

### POST

**Post-passes after the body run in a fixed order.** Group A. Verdict: **By construction**.

- Unsound (5): V028, OL-1d, OL-2b, V089, V093.
- False positives (1): V079.
- Secondary cause of: V074.

*Now.* After the body, about fourteen passes run in a fixed order. Some of them are `finish_values` (with `apply_stored`), `finish_aborts`, `finish_task_ends`, `op_refs`, `finish_op_env`, `check_returns`, `check_stored_behind`, `finish_resume_runs`, `finish_spared`, `settle_moves` and `finish_via_calls`. A pass cannot see what a later pass adds.

*Findings.* A stored value is applied after the mapping of the clause parameters (V028). Operation results (OL-1d). A clause runs a parameter of a finished closure (OL-2b). Only the stored-value pass finds some abort nodes (V089). `op_refs` does not move `lent` (V093). In the false positive V079, W0204 runs before `op_refs`.

*Why by construction.* Over the IR, stored values, clause parameters, operation results and abort edges are facts of one worklist. A late fact goes to each transfer function that needs it. So there is no order to get wrong. A check reads the fixpoint, not an intermediate state.

*Conditions.* The analysis over the IR must be one fixpoint, not a new list of ordered passes.

### TWO

**Two lowerings of one AST: sema and the interpreter disagree.** Group A*. Verdict: **By construction, if the interpreter runs the IR**.

- Unsound (4): V045, OR6, RR10, IP6.
- False positives (0): none.
- Secondary cause of: RT11, V017, OR2, V136, O3-1.

*Now.* Sema lowers the AST to facts. `crates/weft-interp/src/compile.rs` lowers the same AST to stack code. Each one decides on its own: the evaluation order, the named arguments, moves, captures, tails, place statements, the resolution of effects and the shape of a `fork` result.

*Findings.* Effect resolution (V045). A place statement (OR6). Named arguments (RR10). The result of `fork` (IP6). The same cause is a part of RT11, V017, OR2, V136 and O3-1.

*Why.* With one IR, the checker and the interpreter read the same decisions. The interpreter already has the frame structure of the IR (`CodeKind`). It also has statement temporaries (`StmtBegin`, `StmtEnd`) and explicit captures (`MakeClosure` with `owned`). So the step from its stack code to the IR is small.

*Conditions.* If the interpreter keeps its own compiler, the IR is a third lowering. Then this class stays (verdict: not at all).

### TYPES

**Facts are made before the types are final.** Group A. Verdict: **By construction**.

- Unsound (0): none.
- False positives (1): V060.
- Secondary cause of: none.

*Now.* Sema chooses copy or move, and sets the flags of a variable, at its `let`. At that point inference does not know the type. `finish` sets the flags again from the resolved type.

*Findings.* In the false positive V060, a move of a local with a type variable counts as a copy.

*Why by construction.* The builder makes the IR from the typed body after inference. So it knows `copy` or `move` and the linear flags where it chooses the operand.

### FNVAL

**Function values: callee sets travel in types and side channels.** Group B. Verdict: **Partly**.

- Unsound (22): RT6, RT7, V026, V032, V033, V049, V061, OL-1a, OL-1b, OL-R2d-struct, OR1, RR2, RR6, V075, V076, V105, V107, V111, V119, V126, V133, O3-5.
- False positives (2): V029, OL-S5c-pair.
- Secondary cause of: RT3b, RT17, RT24a, F4, V011, V027, V031, V052, V053, OL-2a, RR9, V080, V081, V093, V104, V106.

*Now.* A function type carries one optional closure summary (`FnTy.summary`). Sema joins summaries only where two type variables meet. A value that leaves the body goes through a special channel: `ret`, `RetFn`, `stores`, `fn_stores`, `reaches`, stored values with reach nodes, `held_run` or `caps::MADE`.

*Findings.* Returned closures and makers (RT7, V026, V032, V033, V049, OR1, V111). One summary for each type (RR2, V107). Closures in fields, containers and tuples (OL-1a, OL-1b, V105, V126, V133, O3-5, OL-R2d-struct). Item values (RT6). Values from `resume` (RR6). Values behind references and generics (V075, V076). Modes through `fn()` places (V061). A closure in the value of an `on abort` function (V119). False positives V029, OL-S5c-pair.

*What the IR removes.* The IR removes the part for each form. A call through a local, a field or a container is one `Call` with a callee operand. A closure is one aggregate. But the analysis must still know which bodies an operand can be. Inside one body, a set-valued analysis does this by construction. Its abstract values are closure literals and items, and they flow through locals, fields, elements and tuples. Across function boundaries, the analysis needs one of two things. One is a whole-program closure analysis over the IR (0-CFA style). A package compiles its dependencies from source, so this is possible. The other is summaries for higher-order functions (SUM). Most findings are at boundaries and in data.

### STORE

**Stored references: no region for a reference behind a reference or in a function value.** Group B. Verdict: **Partly**.

- Unsound (9): V037, OL-4a, OL-R2b-res, OL-R2b-prec, OL-S5a-store, FD3, V087, V108, F3-2.
- False positives (0): none.
- Secondary cause of: V006, F3-1.

*Now.* Weft has no lifetimes. The checker mirrors the "no stored references" assumption of the borrowing proof with special forms of W0204. The forms are returns, stores behind reference parameters, stores into `rc` objects, and closures and clauses that keep a parameter.

*Findings.* A closure or a clause keeps its reference parameter (V037, OL-S5a-store, OL-R2b-res, F3-2). Stores behind references and into `rc` objects (OL-4a, FD3, V087, V108). Objects of one `rc` type (OL-R2b-prec).

*What the IR removes.* With the IR, a closure and a clause are bodies. A store behind a reference is one statement form: `(*p).f = r`, or a call that stores through `p`. So the check that covers functions also covers closures and clauses (V037, V108).

*What stays.* A function value does not state where the references that it gets live. `rc` group places do not tell objects apart (OL-R2b-res, OL-R2b-prec, F3-2). This needs a language change or a whole-program analysis. The language change is a place or a region on the parameter types of function types.

### PART

**Partial moves and partial initialization have no move paths.** Group B. Verdict: **Partly**.

- Unsound (3): V062, R3RT1, Q3-1.
- False positives (1): V023.
- Secondary cause of: R3RT10, F3-5.

*Now.* A part move is a move of the whole local for W0302 and `live_linear`. But it frees the part only. Place fields with no value get hidden variables from a walk over the type. The walk uses the ADT id as its key.

*Findings.* Unset place fields in closures, nested literals, call results and nested generics (V062, Q3-1). The rest of a linear aggregate after a part move (R3RT1). The false positive V023.

*What the IR removes.* An IR with move paths (as `MoveData` in rustc) gives a path to each projection of a local. Init state and drop elaboration then work for each path. A move of `p.a` makes the path `p.a` uninitialized. A struct that is built in place starts with the paths of its place fields uninitialized. This removes the walk over the type.

*What stays.* The spec rules (`live_linear`, the free rule, `use_after_move`) are rules for each variable. They must become rules for each path. For this reason F3-5 is in SPEC.

### GEN

**Generic flow: values of a type parameter.** Group B. Verdict: **Partly**.

- Unsound (7): RT3b, V031, V056, OL-3a, OL-NR-ptrfork, RR9, V081.
- False positives (1): OL-R2c-3.
- Secondary cause of: V054, V057, V058, V075, V085, F3-3.

*Now.* Sema lowers a generic body once. The body does not know that `T` is linear or a closure. Sema adds summary parts for `T` (`drops`, `holds`) and special cases for item values.

*Findings.* References through `id` and containers (RT3b, V031). Closures given to a `T` parameter (V056). A generic callee holds `T` across a suspension (OL-3a). Generic items as function values (RR9, V081). Modes of type parameters (OL-NR-ptrfork). The false positive OL-R2c-3.

*What the IR removes.* A value of type `T` flows in the IR as each value does. So a reference through `id(&x)` and a closure that moves into `x: T` keep their places and modes. The `holds` part is the liveness of a `T` local across a suspension terminator. The `drops` part comes from drop elaboration (DROP).

*What stays.* A caller must still instantiate the parts of a generic item where it uses the item as a value (RR9, V081). Modes have no polymorphism (OL-NR-ptrfork). Monomorphization of the IR before the check removes the class by construction. The cost is one analysis for each instance.

### CAP

**Capabilities and continuations are not values.** Group B. Verdict: **Partly**.

- Unsound (11): RT16, V046, V047, V050, V052, OL-1c, OL-S5a-w0314, OR9, RR3, V077, V120.
- False positives (2): R1-SIM, V054.
- Secondary cause of: RT12, V049, V051, OL-1a, OL-1b, RR4, V074, V075, V088, V134.

*Now.* Handler capabilities and continuations are not values in the facts. W0313 and W0314 follow a set of `caps::Held` marks through each channel. The channels are locals, parts, closures, stores, callees, clauses, resume values and tasks.

*Findings.* A closure leaves its handler (RT16, V046, V047). A continuation leaves its clause (RR3, V120). A `resume` runs in a task (OR9). A task runs a value of another stack (V050, V052, OL-S5a-w0314). A clause keeps a function value (OL-1c, V077). False positives R1-SIM, V054.

*What the IR removes.* The IR can make a capability an explicit value, as evidence passing does. `handle` binds a capability local whose storage ends with the handled body. A closure captures it in its environment. A perform takes it as an operand. A continuation is a local of the clause frame. Then "a capability leaves its body" is "a reference into a dead frame": the rules of W0204 and W0301 apply. A task that holds the capability of another task fails a mode check. The hand-written channels go away.

*What stays.* FNVAL and STORE then apply to capabilities too. The effects proof models handlers as a stack, not as values. So the proof link must change.

### SUM

**Summary parts are designed by hand for each feature.** Group B. Verdict: **Partly**.

- Unsound (13): V011, V040, V043, V051, OL-2a, OR3, OR7, V078, V080, V082, V106, V127, V132.
- False positives (3): OL-R2c-2, OR10, V115.
- Secondary cause of: RT12, RT13, V026, V050, OL-2b, OL-S5a-w0314, OR1, FD1, V126, V133, O3-5, O3-9, R3RT6.

*Now.* `EffectSig` has 24 parts. Each part answers one question about a callee. Some parts are `lent`, `ret`, `stores`, `reaches`, `reach_repeats`, `repeats`, `multi`, `fn_stores`, `group_stores`, `op_fns`, `op_effects`, `tasks`, `task_runs`, `task_effects`, `pins`, `drops`, `holds` and `raises`. Each part has its own inference and its own use at the call.

*Findings.* A callee runs a callback twice (OR3, V043, V080, V106). Function parameters run as tasks (OR7, V127, V132). Tasks perform through a handler of the caller (V051). Unknown code and handlers of a caller (V011, V078). A multi operation through an unknown value (V040, V082). A stored spawning closure (OL-2a). False positives OR10, V115, OL-R2c-2.

*What the IR removes.* Modular checking needs summaries. The IR does not change that. But the IR makes the inference of a part mechanical. A part is a query over the IR of the callee. An example: "parameter `f` is the callee operand of two `Call` terminators, or of one in a cycle". The use of a part is one substitution at the `Call`. This removes the misses where a part exists but one kind of argument does not use it. An example is a callback inside a container (V106).

*What stays.* The IR does not add a part that the summary language does not have. Two examples: what a task does with a function argument while the callee writes another argument (V132), and where the result of a handler of a caller can point (V078).

### SPEC

**A rule of the spec or a fact model is too weak or too coarse.** Group C. Verdict: **Not at all**.

- Unsound (13): RT24c, F6, V010, V016, OR5, FD4, IP1, IP3, V095, V117, V124, F3-5, F3-8.
- False positives (3): V013, QA6, V130.
- Secondary cause of: RT1, V039, OL-R2b-prec, IP8, V101, V125, R3RT1.

*Now.* The facts were correct. But a rule of the spec, or the model that a fact encodes, was too weak or too coarse.

*Findings.* Frees in the task rule (V010). Definite assignment (RT24c). Forwards (F6). Stated places (V016). The writes of a task at its end (OR5). A `fail` that resumes (IP1). Pins (IP3). Values across `multi` (FD4, V124). A failure inside `on abort` (V117). A part move (F3-5). A task that is cancelled before it starts (F3-8). The encoding of a change above a clause argument (V095). False positives V013, QA6, V130.

*Why not.* These need a new or changed rule, or a decision of the model. The IR gives cleaner inputs for some of them, for example move paths for F3-5. But the fix is the rule.

### TYPE

**Type properties, signature checks and prelude signatures.** Group C. Verdict: **Not at all**.

- Unsound (12): RT3c, RT15, RT24d, F5, QR5, QR7, V063, V067, RR8, QA3, F3-4, F3-6.
- False positives (4): RT20, OL-3b, OL-R2e-reassign, R3RT11.
- Secondary cause of: none.

*Now.* These are checks of types and declarations: `props.rs`, `!Move`, exhaustiveness, `on abort` signatures, `in` places of a signature, and the `drops` parts of the prelude.

*Findings.* Type properties (RT15, QR7, V067, F5). Checks of declarations and signatures (RT24d, V063, QA3, F3-4). A returned type that holds references (RT3c). Prelude signatures, and the effect of a drop of `Task<T>` and of `fork` values (RR8, F3-6). fip counts (QR5). False positives RT20, OL-3b, OL-R2e-reassign, R3RT11.

*Why not.* These do not come from the lowering of a body.

### INF

**Bounds of the inference over the call graph.** Group C. Verdict: **Not at all**.

- Unsound (1): QR6.
- False positives (1): V001.
- Secondary cause of: none.

*Now.* The fixpoint of effect inference over the call graph had a silent bound.

*Findings.* QR6. The false positive V001.

*Why not.* The inference over the call graph stays with or without the IR.

### NAMES

**Names and visibility.** Group C. Verdict: **Not at all**.

- Unsound (1): V003.
- False positives (2): V138, Q3-3.
- Secondary cause of: none.

*Now.* Name resolution and visibility.

*Findings.* V003. False positives V138, Q3-3.

*Why not.* These do not come from the lowering of a body.

## How the classes interact: regressions of the fixes

The stage verifiers found ten soundness regressions. In each one, a fix in one class broke an
assumption that code of another class made. With one IR, most of the pairs below are one
mechanism, so the assumption has no second copy to break.

| Regression | The fix | The assumption that broke | Classes |
| --- | --- | --- | --- |
| V045 | Sema resolves effects by identity (S3). | The interpreter resolves `handle log` with its own lookup. | TWO |
| V073 | An empty value (`None`) starts no linear value (6b). | `handle` builds its value from the body `Val` and keeps its `empty` flag. | VAL, DROP |
| V074, V088 | W0313 follows new values of a local by reachability (6a). | Each node that can abort has an abort edge, also to an outer handle end. | CAP, SUSP |
| V089 | W0313 uses the abort edges (6a). | The stored-value pass and clauses in clauses add their abort nodes before the check. | CAP, POST |
| V095 | The wildcard rules use `strict_prefix` (QA6). | `x..` at a `resume` means "a change above the argument". | SPEC, SUSP |
| V096 | A loop carries task sets of handles (RR1). | `joined_at` is a must fact; a handle holds one task. | LOOP, STATE |
| V097 | One call result is one place (QA6). | One lowering of the code is one run; a multi resume runs it again. | SPEC, MULTI |
| V116 | A local operation spares values outside the handled body (OR4). | A closure that takes an outer value by value (OR2) keeps it inside the body. | SUSP, ENV |
| V125 | A task keeps the cell of a captured copy variable (OR8 false positive). | No reference into the cell exists; the task can make one. | ENV, SPEC |

False-positive regressions of fixes: V012, V013, V023, V054, V058, V060, V069, V079, V083, V084, V085, V101, V115, V130. 8 of these 14 are in
classes of group A.

## Requirements for the IR design

The classes give these requirements. Each one names the classes that need it and the count of
unsound findings in them (primary cause only).

| Requirement | Classes | Unsound findings |
| --- | --- | --- |
| Each intermediate value is a local with `StorageLive` and `StorageDead`. Frames end their temporaries after the value leaves. | TEMP | 9 |
| Each value-giving construct ends in `dest = move p` or `dest = copy p`. A discarded value is dropped. | TAIL | 4 |
| Drop elaboration on normal and cleanup paths. A drop of a type with `on abort` on a cleanup path is a `Call`. | DROP | 8 |
| Operands are explicit reads; places have an explicit `Deref`; an index has `Len`. | ORDER, ACCESS, DEREF | 11 |
| One `Call` terminator for items, values, methods, performs and resumes. | CALLS | 8 |
| A closure is an aggregate of its environment, with one capture rule that the interpreter shares. | ENV | 15 |
| Each closure, clause, handled body and scope body is a body. A run of it is a call, with one summary procedure or with call and return edges. | INNER | 9 |
| Each terminator that can suspend has an abort edge to the cleanup path of the right frame. Multi points have re-entry edges. | SUSP, MULTI | 7 |
| One fixpoint over the IR: loops through back edges, no ordered post-passes, a dataflow fact for each local at each point. | LOOP, POST, STATE, VAL | 13 |
| The builder runs after type inference. | TYPES | 0 |
| The interpreter runs the IR, or compiles from it. | TWO | 4 |
| Move paths for init state and drops. The spec rules for moves and linear values work for each path. | PART | 3 |
| A closure analysis over the IR: set-valued in a body; whole-program or by summaries across bodies. | FNVAL | 22 |
| A summary language whose parts are queries over the IR of the callee. | SUM, GEN | 20 |
| Optional: capabilities and continuations as values with storage. | CAP | 11 |
| Outside the IR: a decision on regions for references that function values get, and on `rc` objects. | STORE | 9 |

The spec and the checker stay. The IR goes between the typed AST and the facts, so the agreement
gate between `rules.rs` and `spec/weft.dl` still holds. For the IR, the spec needs changes only
for move paths (PART) and, as an option, for a flow-sensitive `points_into` (STATE). The
findings of SPEC need their own rule changes, with or without the IR.

## What the IR does not remove

- **Function values (FNVAL)**: the IR needs a closure analysis. Inside a body a set-valued
  analysis over the IR is enough. Across bodies, choose a whole-program closure analysis or
  summaries for higher-order functions. This choice decides the largest class.
- **Summaries (SUM)**: derive each part as a query over the IR of the callee. Use it by one
  substitution at the `Call`. Design the summary language once, from the questions of the
  findings. How often and where does a callee run a function argument? What does it store?
  What does it hold across a suspension? What can code that the body cannot see do?
- **Stored references (STORE)**: a function type does not state where the references that it
  gets live, and `rc` group places do not tell objects apart. This needs a language decision
  (a place or a region on the parameters of a function type), not an IR.
- **Capabilities (CAP)**: model a capability and a continuation as values with storage. Then the
  W0313 and W0314 channels are the rules for references. The effects proof link must follow.
- **Partial moves (PART)** and **generics (GEN)**: the IR gives move paths and explicit drops of
  `T`. The spec rules must become rules for each path. Instantiation of generic items as
  values, or monomorphization, stays a decision.
- **Group C**: spec rules, type properties, inference bounds and names. The IR does not touch
  them.
- **The interpreter**: the defects of class I are in the scheduler, the unwinder and the
  oracle. An IR that the interpreter runs removes TWO, but not these.

## Excluded findings

- Duplicates (the row in Appendix A names the original): F1 (= RT1), F2 (= RT10), V019 (= V007), V021 (= V013), V022 (= V012), V030 (= V025), V034 (= V028), V038 (= V027), V048 (= V045), V065 (= V057), V068 (= V062), QA1 (= RR1), QA2 (= FD1), V090 (= V086), V091 (= V084), V092 (= V079), V094 (= V081), V099 (= V095), V100 (= V096), V109 (= V103), V110 (= V104), V112 (= V106), V113 (= V107), V114 (= V108), V122 (= V118), V131 (= V125), I3-1 (= O3-4, F3-6).
- Interpreter only: OR11, RR14, FD2, IP2, IP4, IP5, IP7, V123, V128, V129, V135, V137, O3-13, F3-9, I3-2, I3-3, I3-4.
- Not about soundness: V004, V005, V064, V070, RR11, RR13, RR15, QA7, V102, R3RT8, R3RT9.
- Rejected (not reproduced): V071.

## Appendix A: each finding

Kind, primary cause and secondary causes. Titles are short forms of the report text. For a
row of kind DUP, the column "Secondary" names the original finding.

### Round 1 reports

| Id | Kind | Primary | Secondary | Finding |
| --- | --- | --- | --- | --- |
| RT1 | U | DROP | SPEC | A move or the scope end of an owner does not invalidate references into it |
| RT2 | U | ORDER | INNER | Queued uses and reads go into the next node, which can be another component or branch |
| RT3a | U | VAL | DEREF | References lose their places through struct and array literals, value-call results and by-value match bindings |
| RT3b | U | GEN | FNVAL | References lose their places through generic callees and containers (`id(&x)`, `Box.new(&x)`, `push`) |
| RT3c | U | TYPE |  | W0204 checks only a top-level `&T` and tuples of references, not `Option<&T>` |
| RT4 | U | TEMP | ORDER | An argument reference is held only from after the later arguments run |
| RT5 | U | ENV | CALLS | A closure argument that captured a reference is not a call argument (W0312) |
| RT6 | U | FNVAL | CALLS | A call through a fn-item value ignores its mut places and aborts; `if` keeps one item |
| RT7 | U | FNVAL |  | Closure summaries are lost through returns, tuples, `if` and fields |
| RT8 | U | ENV |  | The mode of a closure (linear, once, nonportable, uniq) does not follow its captures |
| RT9 | U | DEREF |  | `c += 1` on a reference local is a rebind, not a write through it |
| RT10 | U | ACCESS |  | A use of a reference variable as a value is not a read (W0405) |
| RT11 | U | INNER | TWO | `return`/`break` in closure, handled and scope bodies go to the wrong target |
| RT12 | U | INNER | CAP SUM | A spawn in a closure is invisible at its call; W0314 misses items and parameters |
| RT13 | U | SUSP | SUM | A multi operation that a function parameter reaches is not a multi point |
| RT14 | U | DROP |  | Linear values go away silently: `let _`, wildcard part, `print`, `match _`, overwrite |
| RT15 | U | TYPE |  | `!Move` is not transitive; self-reference field stores are not checked |
| RT16 | U | CAP |  | A closure escapes its handler through a local, a tuple or a container (W0313) |
| RT17 | U | CALLS | FNVAL | `sim.run` as a value bypasses W0802 |
| RT18 | U | TEMP |  | The hidden `for` iterator does not get `uniq`, so W0503 is missed |
| RT20 | FP | TYPE |  | Integer literal elements default to i64 when indexed (W0102) |
| RT22 | FP | VAL |  | A tail spawn handle wrapped in `handle` loses its task (false W0601) |
| RT24a | U | CALLS | FNVAL | W0705 is not checked for fn items given as values |
| RT24b | U | STATE |  | `uniq` of a local stays after a rebind (sticky), W0406 missed |
| RT24c | U | SPEC |  | No definite-assignment check (`let x: u64` then use) |
| RT24d | U | TYPE |  | No exhaustiveness check for `match` |
| F1 | DUP | DROP | RT1 | Dangling references after a move or a scope end (spec has no owner rule) |
| F2 | DUP | ACCESS | RT10 | A read through a held reference is not a fact |
| F3 | U | CALLS | INNER | A perform is not checked like a call; clause reference parameters have no root |
| F4 | U | INNER | FNVAL | Mutations of a closure through its own reference parameters are lost (own_roots) |
| F5 | U | TYPE | ENV | Tuple `has_on_abort` is true for any non-ADT type (closure part = RT8) |
| F6 | U | SPEC |  | `forwards(H)` is weaker than the design: a library root handler passes |
| QR5 | U | TYPE |  | fip use counts overflow: W1002 goes away in release builds |
| QR6 | U | INF |  | Effect inference stops after 32 rounds with no diagnostic |
| QR7 | U | TYPE |  | A linear type nested 7 levels deep is not linear (depth cut-off) |
| R1-SIM | FP | CAP |  | False W0314 for a task closure that performs a standard effect inside `sim.run` |

### Round 1 stage verifiers

| Id | Kind | Primary | Secondary | Finding |
| --- | --- | --- | --- | --- |
| V001 | FP | INF |  | The round bound of inference is too small: false W0706 |
| V002 | U | DROP | ENV | An overwrite of a captured linear variable in a closure or clause is not W0601 |
| V003 | U | NAMES |  | `pub` is not enforced across units: a private dependency function is callable |
| V004 | N |  |  | Stack overflow in the derivation printer |
| V005 | N |  |  | `--workers` has no upper bound |
| V006 | U | INNER | STORE | A closure or clause stores a reference to its own local in a captured reference |
| V007 | U | TEMP |  | A temporary root has no owner and no end: a reference into it never dies |
| V008 | U | DEREF |  | An Rc result through an argument handle gets no handle dependency |
| V009 | U | ENV | INNER | A clause that moves a captured owner: the move is not applied at the perform |
| V010 | U | SPEC | DROP | A move of an owner while a task holds a reference: task_conflict ignores frees |
| V011 | U | SUM | FNVAL | The result of an unknown function value gets the argument places, not a wildcard |
| V012 | FP | ENV |  | W0204/W0301 for a closure that captures a copy value |
| V013 | FP | SPEC | ACCESS | Coarse access rules: any task that names `stats.x` reads all of `stats` |
| V014 | U | DEREF |  | A compound assignment through a reference in a field writes the field, not the target |
| V015 | U | TEMP | ENV | A closure argument is not held while later arguments run |
| V016 | U | SPEC |  | Payload instability is lost through a coarse stated place (`-> &T in m.state`) |
| V017 | U | ENV | TWO | Checker and interpreter disagree on moved captures (closure outlives the local) |
| V018 | U | ENV | INNER | A clause reads a captured reference at the perform after the body invalidated it |
| V019 | DUP | TEMP | V007 | References into temporaries never become invalid |
| V020 | U | DEREF | TEMP | A held Rc receiver loses its handle dependency while later arguments run |
| V021 | DUP | SPEC | V013 | Coarse access rules (second verifier) |
| V022 | DUP | ENV | V012 | W0204 for a returned closure that captures a copy value (second verifier) |
| V023 | FP | PART |  | A partial move counts as a move of the whole local (W0301, W0302) |
| V024 | U | INNER |  | `lends_mut` is not part of Summary: a call in a closure loses it at the run node |
| V025 | U | LOOP |  | A function-value local that a loop body reassigns later: earlier calls keep the old value |
| V026 | U | FNVAL | SUM | Returned function values are lost: joined makers, makers through parameters, nested makers |
| V027 | U | ENV | FNVAL | A stored closure that runs at a reach node does not use its captured references |
| V028 | U | POST |  | A stored closure performs a local operation: apply_stored runs after clause rebasing |
| V029 | FP | FNVAL |  | A stored closure: a mutation through its parameter counts for the whole argument |
| V030 | DUP | LOOP | V025 | Reassigned function value later in a loop body (second verifier) |
| V031 | U | GEN | FNVAL | A closure that goes into a generic container is not tracked as stored |
| V032 | U | FNVAL |  | A closure that comes back from a returned closure loses its summary (RetFn does not nest) |
| V033 | U | FNVAL |  | A callee calls a closure argument and then the closure that it returned |
| V034 | DUP | POST | V028 | Stored closure under a local handler: clause mutation lost (second verifier) |
| V035 | U | CALLS | ENV | A perform with a closure argument: only `&T` arguments are call arguments |
| V036 | U | SUSP | INNER | A clause holds a reference into its parameter across `resume`; the body frees the argument |
| V037 | U | STORE |  | An Arg-rooted place escapes a closure or clause through a captured outer local (`keep = x`) |
| V038 | DUP | ENV | V027 | A closure in a struct or tuple argument is not a call argument (second verifier) |
| V039 | U | CALLS | SPEC | Aliasing places given to one function value are never checked (W0312) |
| V040 | U | SUM | SUSP | A multi operation through an unknown value in a callee does not make the call multi |
| V041 | U | LOOP |  | A reference local that a loop body reassigns later keeps only its first value |
| V042 | U | CALLS | VAL | An argument that holds a reference in a tuple or Option is not a call argument (three call paths) |
| V043 | U | SUM |  | A spawning closure that a callee calls more than once starts one task |
| V044 | FP | VAL |  | A task handle through `if`, `match` or a closure result loses its task (false W0601) |
| V045 | U | TWO |  | The interpreter resolves `handle log` to a user effect `Log`; sema does not |
| V046 | U | CAP |  | W0313 off by one: a closure given to an operation of its own handler |
| V047 | U | CAP | VAL | A capability leaves through a `resume` argument and the operation result |
| V048 | DUP | TWO | V045 | Interpreter effect resolution (second verifier) |
| V049 | U | FNVAL | CAP | W0313 misses a closure that a callee returns inside a tuple |
| V050 | U | CAP | SUM | W0314 misses a clause that runs its function argument as a task |
| V051 | U | SUM | CAP | W0314 misses callee tasks that perform effects which a caller handles locally |
| V052 | U | CAP | FNVAL | W0314 misses a task that runs a closure from a field of a local |
| V053 | U | INNER | FNVAL | Clause values that point into clause parameters are not mapped to the perform arguments |
| V054 | FP | CAP | GEN | False W0313 for Box.new, Rc.new and generic callees |
| V055 | FP | SUSP |  | Corpus expects W0405 after `resume(); s.spawn(..)`, but resume runs the body first |
| V056 | U | GEN |  | A closure given to a type-parameter parameter skips every mode check |
| V057 | U | DROP | GEN | Generic `drops` misses a T moved into a holder that is then dropped |
| V058 | FP | TAIL | GEN | A generic function that returns T through an if/match tail gets T in `drops` |
| V059 | U | TAIL |  | A local named as an if/match arm tail is not moved |
| V060 | FP | TYPES |  | A move of a local with an inference variable type counts as a copy |
| V061 | U | FNVAL | ENV | nonportable and uniq modes are lost through fn() places and containers |
| V062 | U | PART |  | Unset place fields: closures, nested literals and call results are not tracked |
| V063 | U | TYPE |  | The W0120 budget runs out and a non-exhaustive match is accepted |
| V064 | N | LOOP |  | var_has scans all locals: quadratic finish |
| V065 | DUP | GEN | V057 | Generic `drops` (second verifier) |
| V066 | U | STATE |  | `uniq` of a local after if/else depends on the lowering order |
| V067 | U | TYPE |  | A reference to a nonportable value is portable (`&Rc`) |
| V068 | DUP | PART | V062 | Unset place fields (second verifier) |
| V069 | FP | STATE |  | Part holders never retire: stale places give false W0301 (and quadratic facts) |
| V070 | N |  | V064 | Quadratic finish (second verifier) |
| V071 | REJ | ENV |  | A once closure loses once-ness across a function boundary (not reproduced) |
| V072 | U | TEMP |  | A linear temporary held while a later operand aborts is not checked (W0602) |

### Open lists

| Id | Kind | Primary | Secondary | Finding |
| --- | --- | --- | --- | --- |
| OL-1a | U | FNVAL | CAP | A task runs a function value from a store (W0314) |
| OL-1b | U | FNVAL | CAP | A callee copies a function value out of a reference argument (W0313) |
| OL-1c | U | CAP |  | A clause keeps its function parameter (W0313) |
| OL-1d | U | POST | SUSP | An operation result that holds a reference gets no places |
| OL-2a | U | SUM | FNVAL | A stored spawning closure at a reach node starts one copy of its task |
| OL-2b | U | POST | SUM | A clause runs a parameter of a finished closure as a task: the summary is gone |
| OL-3a | U | GEN | SUSP | A generic callee aborts or resumes more than once while it holds a linear T |
| OL-3b | FP | TYPE |  | A Vec of linear values has no consumer (prelude), always W0601 |
| OL-3c | U | TEMP | DROP | A return/break in a later operand leaves a linear value on its way |
| OL-4a | U | STORE | DEREF | References stored behind a reference parameter: a read-back has no places |
| OL-4b | FP | STATE |  | A stale part holder after a join on a continue path |
| OL-5 | U | ENV |  | A closure that holds a fresh once continuation is not a once value |
| OL-6a | FP | STATE |  | Local.caps only grows: false W0313 after a reassignment |
| OL-6b | FP | VAL |  | Overwriting `None` of an inferred local is W0601 |
| OL-R2a | U | MULTI |  | A multi operation of a caller's handler re-runs the rest of the body with old locals |
| OL-R2b-res | U | STORE |  | A closure or clause stores its own reference parameter; a fn value does not state where its references live |
| OL-R2b-prec | U | STORE | SPEC | A reference stored into an rc object through a handle of the same type to another object |
| OL-R2b-holds | FP | STATE |  | A local that gets a reference from a callee through `holds` is flow-insensitive |
| OL-S5a-w0314 | U | CAP | SUM | A value the body cannot follow goes to an operation of a caller's handler (W0314) |
| OL-S5a-store | U | STORE | DEREF | A reference stored behind a closure or clause parameter is seen as the outer place |
| OL-R2c-1 | FP | SUSP |  | An operation in a closure or clause inside a handled body spares nothing |
| OL-R2c-2 | FP | SUM |  | A callee that performs the operation makes each resume free every clause reference parameter |
| OL-R2c-3 | FP | GEN |  | A generic wrapper that holds Rc<T> is never many |
| OL-R2d-box | U | ACCESS | DEREF | A borrow through a Box deref does not read the Box (W0405) |
| OL-R2d-clause | FP | INNER |  | A clause that spawns its fn parameter into an outer scope and then resumes |
| OL-R2d-struct | U | FNVAL |  | Function values in a struct that a callee returns, called later by an unknown value |
| OL-R2e-reassign | FP | TYPE |  | `let g = diff; g = rdiff` loses parameter names (one type per local) |
| OL-S5c-pair | FP | FNVAL |  | A stored callback pairs with a different known closure at parameter 0 |
| OL-S5c-w0312 | FP | CALLS | INNER | A local clause that runs its callback parameter gets W0312 |
| OL-NR-flow | FP | STATE |  | points_into is flow-insensitive: a rebind before the end is still invalid |
| OL-NR-ptrfork | U | GEN |  | A generic function that forks with its argument gets no W0401 for *T or Rc |
| OL-NR-multi | FP | MULTI |  | The multi re-run model is path-insensitive: false W0302 when runs take different branches |

### Round 2 reports

| Id | Kind | Primary | Secondary | Finding |
| --- | --- | --- | --- | --- |
| OR1 | U | FNVAL | SUM | A returned closure that captures a reference parameter does not point into the argument |
| OR2 | U | ENV | TWO | Moves of captures: the checker at creation, the interpreter at run (and a false W0302) |
| OR3 | U | SUM |  | A callee that calls a callback twice is not checked for W0301 |
| OR4 | FP | SUSP |  | W0602/W0503 for a linear value outside the `handle` |
| OR5 | U | SPEC | ACCESS | A reference made while a task runs stays valid after the join; `&v[i]` is not a read |
| OR6 | U | TWO | TAIL DROP | A variable as an expression statement: the interpreter moves and drops it, sema sees nothing |
| OR7 | U | SUM |  | Function parameters that run as tasks or fork branches: no W0405, W0401, W0403, pinning |
| OR8 | U | ACCESS |  | A use or a new value of a whole local is not an access for W0405 |
| OR9 | U | CAP |  | A `resume` inside a spawned task runs the handled body on another task |
| OR10 | FP | SUM |  | A call reads all of its reference arguments (W0405) |
| OR11 | I |  |  | The stock interpreter misses dangling references, leaks and races |
| RR1 | U | LOOP |  | The loop lowering stops after 8 passes: a chain of locals loses places, fn values, tasks |
| RR2 | U | FNVAL |  | A function type carries one closure summary: later closures in an array or Vec are lost |
| RR3 | U | CAP |  | A closure that resumes a continuation leaves its clause |
| RR4 | U | ENV | CAP | A closure that captures the scope capability `s` leaves the scope |
| RR5 | U | INNER | SUSP | `resume` carries the mutations of the handled body, not its frees |
| RR6 | U | FNVAL | SUSP | A function value that `resume` gives has no summary in the handled body |
| RR7 | U | ENV |  | A closure keeps the creation-time places, summary and modes of a captured variable |
| RR8 | U | TYPE |  | `Vec.clear` drops linear elements (prelude signature has no `drops`) |
| RR9 | U | GEN | FNVAL | A generic item given as a function value drops a linear value |
| RR10 | U | TWO | CALLS | Named arguments: sema binds by name, the interpreter by position |
| RR12 | FP | ENV |  | W0304 for a local that a closure, a clause or a task sets |
| RR11 | N | NAMES |  | An effect of another module has no name outside it |
| RR13 | N | NAMES |  | Named arguments to a constructor or closure bind by position |
| RR14 | I |  |  | The interpreter does not check integer widths of locals |
| RR15 | N | NAMES |  | An operation with the name of a prelude function is shadowed |
| FD1 | U | DROP | SUM | The effects of an `on abort` function are not checked (the unwinder call is not a call) |
| FD2 | I |  |  | Nested multi continuations share one exec record |
| FD3 | U | STORE |  | A reference stored into an rc object outlives its owner |
| FD4 | U | SPEC | MULTI | The multi rule does not count affine or `!Move` values |
| QA1 | DUP | LOOP | RR1 | Loop fixpoint stops after 8 passes |
| QA2 | DUP | DROP | FD1 | The effects of an `on abort` function do not count |
| QA3 | U | TYPE |  | An `in` place that names a later parameter gets no places (substitution order) |
| QA6 | FP | SPEC |  | A write through a wildcard reference invalidates that reference |
| QA7 | N | LOOP |  | Each loop pass clones the whole lowering state (speed) |
| IP1 | U | SPEC |  | A Fail clause can resume a failure that the runtime raises |
| IP3 | U | SPEC |  | A stealable task shares an Rc with a pinned child |
| IP6 | U | TWO |  | `fork` gives () when each branch is (): a generic caller faults |
| IP8 | H | TEMP | SPEC | Hidden part variables break `bound_before_use`; the `in` form breaks `ret_ok` |
| IP2 | I |  |  | A child failure goes to the handler at the owner's current suspension point |
| IP4 | I |  |  | A multi copy keeps the cells of a clause inside the continuation |
| IP5 | I |  |  | A with_timeout deadline is lost when the block is not on the stack |
| IP7 | I |  |  | Each HTTP request task is stealable |

### Round 2 stage verifiers (S5a, R2a-R2e)

| Id | Kind | Primary | Secondary | Finding |
| --- | --- | --- | --- | --- |
| V073 | U | VAL |  | `handle` takes `empty` from its body value: a linear clause value leaks |
| V074 | U | SUSP | POST CAP | W0313 relies on abort paths, which several node kinds do not get |
| V075 | U | FNVAL | GEN CAP | A task runs fn values through a generic T, references behind references, a copied result |
| V076 | U | FNVAL | DEREF | fn_stores ignores references stored behind references |
| V077 | U | CAP | DEREF | A clause keeps a fn value that it reads through a reference parameter |
| V078 | U | SUM |  | The result of a caller's handler operation can point outside the parameters |
| V079 | FP | POST |  | W0204 runs before op_refs moves the facts of an operation result |
| V080 | U | SUM | FNVAL | A stored spawning closure given by value to a callee that calls it twice |
| V081 | U | GEN | FNVAL | A generic function in `holds` given as a function value: no W0602 |
| V082 | U | SUM | SUSP | A once closure with a fresh continuation goes to a callee that holds it across multi |
| V083 | FP | DROP | SUSP | An abort edge does not end linear body owners: false W0601 in a retry loop |
| V084 | FP | SUSP |  | An abort edge skips the scope end: false W0405 after the handle |
| V085 | FP | DEREF | GEN | A bogus `*v..` Held root through a generic identity: false W0703 |
| V086 | U | SUSP |  | Abort paths miss a clause inside a clause and a local stored call |
| V087 | U | STORE |  | A callee stores a reference to its own local behind a reference parameter |
| V088 | U | SUSP | CAP | W0313 checks only paths to the inner handle end; an abort can leave to an outer end |
| V089 | U | POST | SUSP | Abort nodes that only the stored-value pass finds get no abort edge |
| V090 | DUP | SUSP | V086 | Abort paths miss a clause inside a clause (second verifier) |
| V091 | DUP | SUSP | V084 | Abort edge skips the scope end (second verifier) |
| V092 | DUP | POST | V079 | W0204 before op_refs (second verifier) |
| V093 | U | POST | FNVAL | op_refs does not rebase Summary.lent and op_args |
| V094 | DUP | GEN | V081 | Generic item value in `holds` (second verifier) |
| V095 | U | SPEC | SUSP | `x..` means 'something above changed' for resume; strict_prefix drops it |
| V096 | U | STATE |  | A join of a handle with a may-set of tasks ends every task in the set |
| V097 | U | MULTI |  | One-place instances assume one lowering is one run; a multi resume re-runs code |
| V098 | U | DEREF |  | A write through a tuple part reference counts as a write of the local |
| V099 | DUP | SUSP | V095 | strict_prefix and resume (second verifier) |
| V100 | DUP | STATE | V096 | Task may-sets and join (second verifier) |
| V101 | FP | LOOP | SPEC | Widening gives false W0301 for walk-then-write code |
| V102 | N | LOOP |  | Loop lowering grows exponentially with branching walks |
| V103 | U | ENV |  | The late join misses a captured closure chain and part holders (RR7 shapes) |
| V104 | U | ENV | FNVAL | A returned closure keeps creation-time places of a captured reference |
| V105 | U | FNVAL |  | A result with function values in a Vec gets no places |
| V106 | U | SUM | FNVAL | A callee that gets a callback inside a container and calls it twice |
| V107 | U | FNVAL |  | Two closures that meet in a tuple type do not join |
| V108 | U | STORE | ENV | The rc escape check misses closure, clause and closure-parameter stores |
| V109 | DUP | ENV | V103 | Late join through an inner closure (second verifier) |
| V110 | DUP | ENV | V104 | A closure that leaves keeps creation-time places (second verifier) |
| V111 | U | FNVAL |  | A closure in a returned container adds no places to `ret_refs` |
| V112 | DUP | SUM | V106 | Callbacks inside containers called twice (second verifier) |
| V113 | DUP | FNVAL | V107 | Closures in tuples do not join (second verifier) |
| V114 | DUP | STORE | V108 | rc store of closures (second verifier) |
| V115 | FP | SUM |  | `repeats` ignores the 'again' flag: a callback run once counts twice |
| V116 | U | ENV | SUSP | An outer linear value that a closure or clause took by value is 'spared' |
| V117 | U | SPEC | DROP | An `on abort` function can fail through join, fs.read, fork or a scope end |
| V118 | U | TAIL |  | A place as the tail of a discarded block moves at run time; sema sees no move |
| V119 | U | FNVAL | DROP | An `on abort` function calls a closure held in its value |
| V120 | U | CAP |  | A multi clause gives a resuming closure to the body through the resume value |
| V121 | U | INNER | SUSP | Frees in a callee of the handled body; a resume through a closure or a callee |
| V122 | DUP | TAIL | V118 | Discarded block tail place (second verifier) |
| V123 | I |  |  | A closure in an rc object shares the template cell of a multi copy |
| V124 | U | SPEC | MULTI | A `!Move` local live across multi only through a reference |
| V125 | U | ENV | SPEC | kept(T, Rt): a reference that the task makes into a kept copy variable |
| V126 | U | FNVAL | SUM | A callee keeps a fn parameter in a local container and runs it as a task |
| V127 | U | SUM | INNER | A clause runs an operation's function argument as a task: no W0405/W0403 |
| V128 | I |  |  | Interpreter crash: stale Interrupt::Fail |
| V129 | I |  |  | sim.run order depends on the worker of the entering task |
| V130 | FP | SPEC |  | The end node of a task lends the writes of a task that it started in the outer scope |
| V131 | DUP | ENV | V125 | kept(T, Rt) regression (second verifier) |
| V132 | U | SUM |  | A callee writes a non-function argument while it runs a function parameter as a task |
| V133 | U | FNVAL | SUM | A function value in a struct that a callee returns is not in held_run |
| V134 | U | ENV | CAP | The scope capability in a tuple or an Option leaves the scope |
| V135 | I |  | V128 | Interpreter crash: stale Interrupt::Fail (second verifier) |
| V136 | U | CALLS | TWO | Sema ignores the arguments of `join` and `detach`; the interpreter runs them |
| V137 | I |  |  | The oracle's portability check gives false alarms |
| V138 | FP | NAMES |  | W0107 for operation names rejects programs that perform by path |

### Round 3 reports

| Id | Kind | Primary | Secondary | Finding |
| --- | --- | --- | --- | --- |
| O3-1 | U | TAIL | TWO | A place as the tail of a `scope` body moves in the interpreter, not in the checker |
| O3-2 | U | TEMP | INNER | A reference into a temporary of a handled or scope body leaves the body |
| O3-3 | U | TEMP | INNER | A reference into a temporary of a clause leaves through the clause value or `resume` |
| O3-4 | U | DROP |  | A spawn in statement position drops a linear task result |
| O3-5 | U | FNVAL | SUM | A task or fork branch runs a closure from a struct field: no W0405, W0403 |
| O3-6 | U | DEREF | ACCESS | A task reads through an Rc handle; the parent moves the handle |
| O3-14 | U | TAIL | MULTI | A tail place of a multi handled body moves once per resume; the checker counts one |
| O3-7 | FP | CALLS | INNER | W0312 on an operation whose closure argument conflicts with itself |
| O3-8 | FP | INNER |  | A closure with its own multi handler is a multi and abort point |
| O3-9 | FP | STATE | SUM | A join through a callee, tuple, Option, `id` or closure does not end the task |
| O3-10 | FP | SUSP |  | Two spawns of function parameters get W0503 when the program has a multi op |
| O3-11 | FP | ENV |  | A move and then a new value of a captured variable invalidates the closure |
| O3-12 | FP | INNER |  | A clause conflicts with the task that it spawns |
| O3-13 | I |  |  | Oracle gaps: no read log in operands; `print` hides a moved value |
| R3RT1 | U | PART | SPEC | A move of one part of a linear aggregate ends `live_linear` for the whole local |
| R3RT2 | U | DEREF |  | A `match` through a reference loses the places of a held reference |
| R3RT3 | U | CALLS | DEREF | A call misses the references behind a reference argument (W0312, W0405) |
| R3RT4 | U | INNER | SUSP | A `resume` with a closure parameter gives the operation result no places |
| R3RT5 | FP | ENV |  | A by-value capture is still tied to the variable (W0204, W0301) |
| R3RT6 | FP | STATE | SUM | Reference arguments flow into each other against their types; points_into is flow-insensitive |
| R3RT7 | FP | CALLS |  | An `in` place on an operation parameter has no effect |
| R3RT10 | FP | STATE | PART | A new value of a part that holds a stale reference is W0301 |
| R3RT11 | FP | TYPE |  | An empty match on an empty enum is W0120 |
| R3RT8 | N | NAMES |  | `Scope` against `Scope` type message |
| R3RT9 | N | NAMES |  | The W0703 hint does not parse |
| F3-1 | U | DROP | STORE | W0118 misses an `on abort` change through a reference in the value |
| F3-2 | U | STORE |  | A closure or clause keeps its reference parameter in an outer local; a callee gives its own local |
| F3-3 | U | DROP | GEN | A generic `on abort` function drops a value of its type parameter |
| F3-4 | U | TYPE |  | The `on abort` parameter check ignores type arguments |
| F3-5 | U | SPEC | PART | A move of a part does not invalidate a reference to the whole value |
| F3-6 | U | TYPE | DROP | The runtime drops a linear task result (abort with a live handle, spawn statement, fork) |
| F3-7 | U | TEMP | SUSP | The value of a scope body is not held across the scope end; the end can abort |
| F3-8 | U | SPEC | ENV SUSP | A cancelled task that never ran drops its linear by-value capture |
| F3-11 | FP | ENV |  | A closure that rebinds a captured reference does not rebind it where it runs |
| F3-9 | I |  |  | The oracle misses a read into an unwound frame |
| I3-1 | DUP | DROP | O3-4 F3-6 | The checker loses the linear result of a task |
| I3-2 | I |  |  | The unwinder does not find linear values in closure cells or task results |
| I3-3 | I |  |  | An interrupt during an unwind cuts a running `on abort` |
| I3-4 | I |  |  | A with_timeout deadline is still lost |
| Q3-1 | U | PART |  | A place field below a second use of one generic type gets no 'unset' variable |
| Q3-3 | FP | NAMES |  | A bare variant name resolves to the first enum that has it (also in the interpreter) |

## Appendix B: the V numbers

V numbers follow the order of the `blocker` and `major` issues of the verify steps in
`round1a_results.json`, `round1b_results.json` and `round2_results.json` (dict order of the
stages, list order of the issues). Minor issues have no V number.

| V | File | Stage step | Severity | Verifier label |
| --- | --- | --- | --- | --- |
| V001 | round1a | Edge: verify probe | major | F9-fixpoint |
| V002 | round1a | Edge: verify probe | major | NEW |
| V003 | round1a | Edge: verify review | major | RT21 |
| V004 | round1a | Edge: verify review | major | RT23-limits |
| V005 | round1a | Edge: verify review | major | CLI-run-test |
| V006 | round1a | Core S1: verify probe | blocker | RT1/F1 |
| V007 | round1a | Core S1: verify probe | blocker | RT1/F1 |
| V008 | round1a | Core S1: verify probe | blocker | RT1/F1 |
| V009 | round1a | Core S1: verify probe | blocker | RT1/F1 |
| V010 | round1a | Core S1: verify probe | blocker | RT1/F1 |
| V011 | round1a | Core S1: verify probe | blocker | RT1/F1 |
| V012 | round1a | Core S1: verify probe | major | RT1/F1 |
| V013 | round1a | Core S1: verify probe | major | RT10/F2 |
| V014 | round1a | Core S1: verify probe | major | RT9 |
| V015 | round1a | Core S1: verify probe | major | RT4 |
| V016 | round1a | Core S1: verify probe | major | ProofRule3 |
| V017 | round1a | Core S1: verify probe | major | RT1/F1 |
| V018 | round1a | Core S1: verify probe | major | NEW |
| V019 | round1a | Core S1: verify review | blocker | RT1/F1 |
| V020 | round1a | Core S1: verify review | blocker | RT1/F1 + RT4 |
| V021 | round1a | Core S1: verify review | major | RT10/F2 |
| V022 | round1a | Core S1: verify review | major | RT1/F1 (W0204) |
| V023 | round1a | Core S1: verify review | major | RT1/F1 + RT4 |
| V024 | round1a | Core S2: verify review | blocker | F4 |
| V025 | round1a | Core S2: verify review | major | RT6 |
| V026 | round1a | Core S2: verify review | major | RT7 |
| V027 | round1a | Core S2: verify review | major | RT7 |
| V028 | round1a | Core S2: verify review | major | F3 |
| V029 | round1a | Core S2: verify review | major | RT7 |
| V030 | round1a | Core S2: verify probe | major | RT6 |
| V031 | round1a | Core S2: verify probe | major | RT7 |
| V032 | round1a | Core S2: verify probe | major | RT7 |
| V033 | round1a | Core S2: verify probe | major | RT7 |
| V034 | round1a | Core S2: verify probe | major | F3 |
| V035 | round1a | Core S2: verify probe | major | F3 |
| V036 | round1a | Core S2: verify probe | major | F3 |
| V037 | round1a | Core S2: verify probe | major | F4 |
| V038 | round1a | Core S2: verify probe | major | RT5 |
| V039 | round1a | Core S2: verify probe | major | F4 |
| V040 | round1a | Core S2: verify probe | major | RT13 |
| V041 | round1a | Core S2: verify probe | major | NEW |
| V042 | round1a | Core S2: verify probe | major | NEW |
| V043 | round1b | S3: verify probe | major | RT12 missed shape: a spawning closure that a callee or a function value calls mo |
| V044 | round1b | S3: verify probe | major | RT22 root cause still open for if, match and closure returns |
| V045 | round1b | S3: verify probe | major | Effect identity: the interpreter resolves `handle log` to a user effect named Lo |
| V046 | round1b | S3: verify review | blocker | W0313 misses a closure given to an operation of its own handler (rule 6: a claus |
| V047 | round1b | S3: verify review | blocker | W0313 misses a capability that leaves through a resume argument and the operatio |
| V048 | round1b | S3: verify review | blocker | Interpreter resolves `handle log` to a user effect named Log (shadowing regressi |
| V049 | round1b | S3: verify review | major | W0313 misses a closure that a callee returns inside a tuple |
| V050 | round1b | S3: verify review | major | W0314 misses a handler clause that runs its function argument as a task |
| V051 | round1b | S3: verify review | major | W0314 misses the tasks of a callee whose standard effects a caller handles with  |
| V052 | round1b | S3: verify review | major | W0314 misses a task that runs a closure from a field of a local |
| V053 | round1b | S3: verify review | major | Clause values that point into clause parameters are not mapped to the perform's  |
| V054 | round1b | S3: verify review | major | New false W0313 for Box.new / Rc.new and generic callees with no reference argum |
| V055 | round1b | S3: verify review | major | Corpus 61 spawn_in_clause marks a false W0405 as expected |
| V056 | round1b | S4: verify probe | blocker | RT8/RT14: a closure given to a type-parameter parameter skips every mode check ( |
| V057 | round1b | S4: verify probe | major | RT14: the generic `drops` part sees only direct non-moves of the parameter; a mo |
| V058 | round1b | S4: verify probe | major | New false positive: a generic function that returns T through an if/match tail g |
| V059 | round1b | S4: verify probe | major | Pre-existing, in RT14/RT15 scope: a local named as an if/match arm tail is not m |
| V060 | round1b | S4: verify probe | major | New false positive from the Lower::finish flag recompute: an untyped closure par |
| V061 | round1b | S4: verify probe | major | RT8: nonportable and not-many (uniq) modes are lost through plain-data places an |
| V062 | round1b | S4: verify probe | major | RT15: W0304 for unset place fields misses closures, nested literals and call res |
| V063 | round1b | S4: verify probe | major | RT24/W0120: when the step budget runs out, a non-exhaustive match is accepted si |
| V064 | round1b | S4: verify probe | major | Performance regression: var_has scans all locals for each query, so Lower::finis |
| V065 | round1b | S4: verify review | major | Generic `drops` only sees params that are never moved; a T moved into a value th |
| V066 | round1b | S4: verify review | major | Local.uniq after if/else or match depends on lowering order (RT24 sticky uniq st |
| V067 | round1b | S4: verify review | major | A reference to a nonportable value is portable: `&Rc` crosses fork branches (t02 |
| V068 | round1b | S4: verify review | major | Unset place fields are tracked only for a struct literal bound directly to a loc |
| V069 | round1b | S4: verify review | major | Part holders never retire: quadratic facts and false W0301 after a part or the w |
| V070 | round1b | S4: verify review | major | Quadratic Lower::finish: local_has -> var_has scans every local for every local  |
| V071 | round1b | S4: verify review | major | A once closure loses its once-ness across a function boundary: returned or passe |
| V072 | round1b | S4: verify review | major | Linear temporaries held while a later argument, part or field aborts are not che |
| V073 | round2 | S5a: verify probe | blocker | 6b regression: a handle takes `empty` from its body value, so a linear value fro |
| V074 | round2 | S5a: verify probe | blocker | 6a regression: W0313 now follows new values, but abort paths are missing for sev |
| V075 | round2 | S5a: verify probe | major | 1a missed shapes: a task still runs fn values through a generic T, through refer |
| V076 | round2 | S5a: verify probe | major | 1b missed shapes: fn_stores ignores references stored behind references |
| V077 | round2 | S5a: verify probe | major | 1c missed shape: a clause with a reference parameter keeps a fn value read throu |
| V078 | round2 | S5a: verify probe | major | 1d unsound: the result of a caller's handler operation can point outside the par |
| V079 | round2 | S5a: verify probe | major | 1d false positive: W0204 when a function returns a local-handler op result that  |
| V080 | round2 | S5a: verify probe | major | 2a missed shape: a stored spawning closure read from a field and passed by value |
| V081 | round2 | S5a: verify probe | major | 3a missed shape: a generic function in `holds` passed as a function value |
| V082 | round2 | S5a: verify probe | major | Item 5 missed shape: a once closure that holds a fresh continuation goes to a ca |
| V083 | round2 | S5a: verify probe | major | New false positive from abort edges: a linear owner of the body in a loop gets W |
| V084 | round2 | S5a: verify probe | major | New false positive from abort edges: the edge skips the scope end, so W0405 fire |
| V085 | round2 | S5a: verify probe | major | New false positive: W0703 on a bogus `*v..` place when a slice from split_at or  |
| V086 | round2 | S5a: verify probe | major | Abort paths still miss clause-in-clause and local stored calls for W0601 and W03 |
| V087 | round2 | S5a: verify probe | major | Adjacent to 4a (pre-existing): a callee can store a reference to its own local i |
| V088 | round2 | S5a: verify review | blocker | W0313 regression: a local outside an inner handle is checked only on paths to th |
| V089 | round2 | S5a: verify review | blocker | W0313 regression: abort nodes that note_abort_path does not record (a clause ins |
| V090 | round2 | S5a: verify review | major | Abort-path fix misses a clause inside a clause: a linear value or a reference ou |
| V091 | round2 | S5a: verify review | major | New W0405 false positive after a handle whose clause does not resume, around a ` |
| V092 | round2 | S5a: verify review | major | New W0204 false positive: a function that returns the result of a local handler' |
| V093 | round2 | S5a: verify review | major | Operation-result references given to a function parameter are lost: Summary.lent |
| V094 | round2 | S5a: verify review | major | 3a missed shape: a generic function item used as a function value with a linear  |
| V095 | round2 | R2a: loops, places and wildcard rules (foundation, speed,... | blocker | QA6(a) strict_prefix makes the resume miss references held by a clause parameter |
| V096 | round2 | R2a: loops, places and wildcard rules (foundation, speed,... | blocker | Task handles carried by a loop: a `join` now joins every task in the handle's ma |
| V097 | round2 | R2a: loops, places and wildcard rules (foundation, speed,... | major | One-place call instances assume one lowering is one execution, but code after a  |
| V098 | round2 | R2a: loops, places and wildcard rules (foundation, speed,... | major | Pre-existing (not from R2a): a reference in a tuple part is treated as an owned  |
| V099 | round2 | R2a: loops, places and wildcard rules (foundation, speed,... | blocker | QA6 item 8(a) (strict_prefix): a clause parameter held across `resume` is no lon |
| V100 | round2 | R2a: loops, places and wildcard rules (foundation, speed,... | blocker | RR1 task sets: a `join` of a handle that can hold several tasks records joined_a |
| V101 | round2 | R2a: loops, places and wildcard rules (foundation, speed,... | major | RR1 widening adds new false W0301 to common walk-then-write code (linked list ta |
| V102 | round2 | R2a: loops, places and wildcard rules (foundation, speed,... | major | Loop lowering grows exponentially with branching or nested deep walks: widening  |
| V103 | round2 | R2b: closures, function values and stored references: ver... | blocker | RR7 |
| V104 | round2 | R2b: closures, function values and stored references: ver... | blocker | OR1 |
| V105 | round2 | R2b: closures, function values and stored references: ver... | blocker | OR1 |
| V106 | round2 | R2b: closures, function values and stored references: ver... | blocker | OR3 |
| V107 | round2 | R2b: closures, function values and stored references: ver... | blocker | RR2 |
| V108 | round2 | R2b: closures, function values and stored references: ver... | blocker | FD3 |
| V109 | round2 | R2b: closures, function values and stored references: ver... | blocker | RR7 |
| V110 | round2 | R2b: closures, function values and stored references: ver... | blocker | RR7 |
| V111 | round2 | R2b: closures, function values and stored references: ver... | blocker | OR1 |
| V112 | round2 | R2b: closures, function values and stored references: ver... | blocker | OR3 |
| V113 | round2 | R2b: closures, function values and stored references: ver... | blocker | RR2 |
| V114 | round2 | R2b: closures, function values and stored references: ver... | blocker | FD3 |
| V115 | round2 | R2b: closures, function values and stored references: ver... | major | OR3 |
| V116 | round2 | R2c: effects, continuations, on abort and drops: verify r... | blocker | OR4 (spared_at) regression: an outer linear value that a closure or a handler cl |
| V117 | round2 | R2c: effects, continuations, on abort and drops: verify r... | major | FD1 missed shapes: an on abort function can fail at run time through join, fs.re |
| V118 | round2 | R2c: effects, continuations, on abort and drops: verify r... | major | OR6 shape left open: a place as the tail of a block whose value is discarded (bl |
| V119 | round2 | R2c: effects, continuations, on abort and drops: verify p... | blocker | FD1 missed shape: an on abort function that calls a closure held in its value |
| V120 | round2 | R2c: effects, continuations, on abort and drops: verify p... | blocker | RR3/OR9 missed shape: a multi clause gives a resuming closure to the handled bod |
| V121 | round2 | R2c: effects, continuations, on abort and drops: verify p... | blocker | RR5 missed shapes: frees and changes in a callee of the handled body, and a resu |
| V122 | round2 | R2c: effects, continuations, on abort and drops: verify p... | blocker | OR6 missed shape: a place as the tail of a block whose value is discarded |
| V123 | round2 | R2c: effects, continuations, on abort and drops: verify p... | major | IP4 missed shape: a closure in an rc object captures a local of the multi contin |
| V124 | round2 | R2c: effects, continuations, on abort and drops: verify p... | major | FD4 missed shape: a !Move local that is live across a multi operation only throu |
| V125 | round2 | R2d: tasks, scopes, fork and the scheduler: verify probe | blocker | kept(T, Rt) regression: the checker accepts a task that borrows a captured copy  |
| V126 | round2 | R2d: tasks, scopes, fork and the scheduler: verify probe | blocker | OR7 missed shape: a callee that keeps a function parameter in a local container  |
| V127 | round2 | R2d: tasks, scopes, fork and the scheduler: verify probe | blocker | OR7 missed shape: an operation's function argument that a handler clause runs as |
| V128 | round2 | R2d: tasks, scopes, fork and the scheduler: verify probe | blocker | Interpreter crash: a stale Interrupt::Fail of a scope dropped with its continuat |
| V129 | round2 | R2d: tasks, scopes, fork and the scheduler: verify probe | major | IP9 incomplete: the order inside sim.run still depends on --seed and --workers w |
| V130 | round2 | R2d: tasks, scopes, fork and the scheduler: verify probe | major | New W0405 false positive at the task-end node of a task that starts another task |
| V131 | round2 | R2d: tasks, scopes, fork and the scheduler: verify review | blocker | kept(T, Rt) regression: a reference that the task itself makes into a kept copy  |
| V132 | round2 | R2d: tasks, scopes, fork and the scheduler: verify review | blocker | OR7 missed shape: a callee writes or reads a non-function argument while it runs |
| V133 | round2 | R2d: tasks, scopes, fork and the scheduler: verify review | blocker | OR7 missed shape: a held function value in a struct that a callee returns is not |
| V134 | round2 | R2d: tasks, scopes, fork and the scheduler: verify review | blocker | RR4 missed shapes: the scope capability in a tuple or an Option |
| V135 | round2 | R2d: tasks, scopes, fork and the scheduler: verify review | blocker | IP2 regression: the interpreter fails with 'internal: the operand stack is empty |
| V136 | round2 | R2e: names, interpreter fidelity, proof claims and refact... | blocker | RR13 (missed shape, unsound): sema ignores the arguments of `t.join(...)` and `t |
| V137 | round2 | R2e: names, interpreter fidelity, proof claims and refact... | major | OR11: the oracle's stealable-portability check gives false alarms on accepted pr |
| V138 | round2 | R2e: names, interpreter fidelity, proof claims and refact... | major | RR15 fix: W0107 for operation names rejects valid programs that perform by effec |

## Files

- This report: `docs/plan/core-ir-inputs/root_causes.md`.
- The classification as data: `SCRATCH/ir/work/findings.py`.
- The text of each class: `SCRATCH/ir/work/narr.py`.
- The build script, which also checks that the text and the data agree: `SCRATCH/ir/work/build.py`.
- The extracted verifier issues: `SCRATCH/ir/work/stage_issues.txt`.
