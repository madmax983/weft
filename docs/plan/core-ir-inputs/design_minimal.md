# Core IR design: a normalizing desugaring pass ("minimal change")

Status: design proposal for the core IR (task 110). Date: 2026-10-20. Angle: minimal
change. Source: commit `b073ea7` of `/home/user/weft` (read-only for this work).

This design puts a small typed tree language, the **Core**, between the typed AST and
fact generation. The Core is the AST in A-normal form: each intermediate value is a
named local, and each move, each end of storage and each frame result is an explicit
statement. The fact generator of `crates/weft-sema/src/body/` stays. It walks the Core
in place of the AST, and most of its special cases go away.

Inputs: `docs/plan/core-ir-inputs/map_lowering.md` (the map of the current lowering, sections 2.1 to 2.34 and
the invariants A1 to G4), `docs/plan/core-ir-inputs/root_causes.md` (180 unsound findings and 53 false
positives by root cause), `docs/plan/core-ir-inputs/semantics.md` (the run-time semantics and the proof
models), the review reports of rounds 1 to 3, `round1b_tasks.md`, ADR 0002, 0003, 0005,
0006, 0007 and 0010, `spec/weft.dl`, `crates/weft-facts`, `crates/weft-sema/src/body/`,
`crates/weft-interp/src/{code,compile}.rs` and `proofs/`.

All paths in this document are relative to `/home/user/weft` unless the text says
otherwise. `ir/...` means
`SCRATCH/ir/...`.

Contents:

- Summary
- 0. Decisions
- 1. Pipeline and principles
- 2. The IR as Rust types (types, well-formedness rules, code units)
- 3. Lowering rules: typed AST to Core (general rules, then map sections 2.1 to 2.34,
  then worked examples)
- 4. Fact generation over the Core (resolver, templates, call rule, inner bodies,
  handlers, tasks, loops, worklist, signatures, diagnostics, invariants A1 to G4)
- 5. Root-cause classes: what the design kills and what stays
- 6. The interpreter (exports, the Core compiler, differential tests)
- 7. Proof alignment (B1, B3, the effects model, the B6 link)
- 8. Migration plan (stages, the diff gate, side by side, the checklist)
- 9. Risks, size and what stays out
- Appendix A: the verdict of each finding. Appendix B: the functions of `body/` and
  where they go. Appendix C: files.

---

## Summary

**What the design is.**

- A new module `crates/weft-sema/src/core/` defines the Core (section 2) and a builder
  (section 3). The builder runs once for each body, before effect inference. It does
  the type inference that the walk of `Lower` does today, and it emits the Core only
  with final types. It resolves names and methods, orders the arguments, chooses copy
  or move from the final type, makes each operand a local, and writes the ends of
  storage, the frame results, the closure environments and the unwind points.
- The fact generator (`body/`) keeps its architecture: one walk that emits CFG nodes,
  the abstract values of locals (places, function values, tasks, capability marks),
  the loop fixpoint, the order "handled body first, then clauses", the inference loop
  over signatures, and the spec and the checker with no change. It walks the Core.
  Each Core statement has one fact template (section 4).
- Four mechanisms of the fact generator become uniform: one place resolver with
  explicit `Deref` steps; one call rule for every kind of callee; one procedure that
  projects the facts of an inner body (a closure or a clause) and substitutes them at
  each node that runs it; and one worklist that replaces eleven ordered post-passes.
- The interpreter first takes its span-keyed exports (`by_value`, `arg_order`,
  `int_ops`) from the Core. Later it compiles the Core to its existing stack code, and
  `compile.rs` goes away. The machine (`machine/`) does not change (section 6).

**What it removes.** The Core has no form for these mechanisms of today. Each one had
its own call sites in many constructs (map, section 3):

| Mechanism of today | Call sites | Replaced by |
| --- | --- | --- |
| `consume` (move a value that is not plain data) | 24 | `Operand::Move`, chosen by the builder from the final type |
| `drop_value`, `discard_block_value`, `drop_linear`, `drop_linear_as` | 24 | a temporary of kind `Discard` and its `StorageDead` |
| `hold`, `hold_later`, `hold_operand`, `hold_moved`, `hold_part`, `hold_as`, `take_held` | 28 | ANF: each operand is a local that lives until its consumer |
| `temp_root`, `open_stmt`, `close_stmt`, `leave_in_flight` | 16 | `StorageLive` and `StorageDead` of temporaries, also before each jump |
| `hold_out`, `use_held`, `hand_out`, `end_frame`, `end_frames_above` | 21 | the frame epilogue: `dest = move tail`, then the ends |
| `flush`, `take_pending` (the pending queue of uses and reads) | 14 | each read is an operand of one statement |
| `late_join` and 17 other late-join functions of `late.rs` (446 lines) | 3 | substitution of the closure environment at each run node |
| `tentative`, `settle_moves`, the flag pass of `finish` | 2 | the builder runs after type inference |
| eleven ordered post-passes (`finish_values` to `finish_spared`) | 11 | one worklist (`settle`) and relation-generic rebase |

The table has 143 call sites. With the suspension helpers (`abortive`,
`abortive_local`, `multi_node`, `multi_local`, `note_abort_ctx`: 24), the read helpers
(`read`, `read_var`, `use_local`, `touch_unset`: 26) and `held_refs` (10), which each
become a part of one template, the total is about 200 call sites. After the change,
each mechanism has one caller: the template of one Core statement kind.

**What it kills** (data: `ir/work/minimal/verdicts.py`, Appendix A):

| Verdict | Unsound (180) | False positives (53) |
| --- | --- | --- |
| By construction, stages 1 to 5 | 87 (48%) | 16 (30%) |
| By construction, after the interpreter compiles the Core (stage 6) | 4 (2%) | 0 |
| Partly | 52 (29%) | 15 (28%) |
| Stays | 37 (21%) | 22 (42%) |

- 91 unsound findings go by construction. 48 of them go by **structure**: the Core has
  an explicit element with a fixed template for the value or the step that the facts
  missed. 43 go by a **single rule**: each surface form now goes through one function.
  So no form can forget the rule, but the content of that one function must be right.
- Group A of `root_causes.md` (lowering mechanics, with A*): 76 of 83 go by
  construction. The design keeps the loop fixpoint, so the class LOOP (3) is only
  partly removed. Four more stay partly or stay: `FD1`, `F3-3` and `F3-1` (`on abort`
  stays atomic) and `OL-2b` (a summary of a finished closure).
- Group B (value flow and summaries): 15 of 70 go by a single rule, for example one
  rule for the result of every call of code that the body cannot see. 46 go partly,
  9 stay.
- Group C (spec, types, inference bounds, names): 27 stay.
- By round: round 1, 59%; round 2, 47%; round 3, 55%; the open lists, 22%.
- New shapes from the mapping documents: `docs/plan/core-ir-inputs/map_lowering.md` N1 and N2, and
  `docs/plan/core-ir-inputs/semantics.md` N1 to N4. The design kills all six by construction (section 5.3).

**Size.** The fact generator has 18 415 lines in its functions today. 2 086 lines go
away, 2 286 lines move to the builder, and 14 043 lines stay. The kept functions lose
their branches for each surface form, so the fact generator ends at about 9 500 lines.
The builder has about 4 700 lines, the Core types, printer and validator about 1 500.
The new Core compiler of the interpreter (about 900 lines) replaces `compile.rs`
(1 544 lines). Section 9.2 has the table.

**Migration.** Nine stages (section 8). The old and the new fact generation run side by
side behind a switch. A diff gate compares the diagnostics and the oracle results of
both on 177 programs of the repository, about 1 570 curated probes of rounds 1 to 3
(each commit) and about 55 700 generated programs (nightly). Each difference must be in
a list of expected differences with a finding id.

**Main risks** (section 9.1): the extraction of type inference out of the walk (about
190 call sites); the precision of the generic projection of inner bodies; the period
with two fact generators while another workflow fixes bugs in the old one; and the
loop fixpoint, which stays.

---

## 0. Decisions

| Id | Decision | Why | Section |
| --- | --- | --- | --- |
| D1 | The Core is a tree, not a CFG. Blocks, `if`, `match`, loops, `handle` and `scope` stay nested. | The fact generator already walks a tree and emits a CFG. A tree keeps the walk, the frame stack, the loop fixpoint and the handler order. This is the smallest change with the largest removal of special cases. | 1.3 |
| D2 | A-normal form: each operand is a constant or a read of a place. Each intermediate value is a local with `StorageLive` and `StorageDead`. | Removes TEMP, ORDER and the hold helpers. | 3.0 |
| D3 | The builder runs after type inference. It chooses copy or move from the final type. | Removes TYPES and `tentative`. | 3.0 |
| D4 | Evaluation order and read points follow the machine of today. A late read (a binary operand, a `print` argument, an index base, a receiver) lowers to an early borrow and a late read through it when code runs in between. | Kills the three late-read shapes of `semantics.md` (N1 to N3) with no change to the interpreter. | 3.0, rule ORDER-2 |
| D5 | Each frame moves its value into a destination local, then ends its locals, then its temporaries. One rule for blocks, functions, closures, clauses, handled bodies and scope bodies. | Removes TAIL and the frame-boundary shapes of round 3. | 3.0, rule FRAME |
| D6 | A closure literal is an aggregate of its environment. One function chooses each capture mode: `Ref`, `Kept` or `Move`. The interpreter uses the same choice. | Removes ENV. | 3.21 |
| D7 | Closures and clauses are Core bodies with an environment. Handled bodies and scope bodies stay inline, with the frame rules. | The fact generator keeps them in the component of the body around them, as today. | 2.2 |
| D8 | Each statement that can abort (a call, `assert`, a scope end) has an unwind point. The builder computes the live locals on each abort path. | Removes SUSP and the abort-edge regressions. | 3.0, rule UNWIND |
| D9 | One place resolver. A place has explicit `Deref` steps. A read through a pointer reads a new stable "pointer word" step `@` of the pointer. | Removes DEREF and ACCESS. | 4.3 |
| D10 | One call rule. The callee is one enum: item, value, operation, `resume`, spawn, join, detach, fork. The result of each call of code that the body cannot see uses one rule. | Removes CALLS. Kills N1 and N2 of the map. | 4.6 |
| D11 | The summary of an inner body is its projected facts plus its context-dependent calls. One substitution maps them onto each run node. | Removes INNER and most of `late.rs`. | 4.7 |
| D12 | One worklist (`settle`) after the walk replaces the ordered post-passes. The rebase of an operation result works on every relation. | Removes POST. | 4.11 |
| D13 | The loop fixpoint of the lowering stays. Its saved state gets smaller. | A worklist over a CFG is not a minimal change. LOOP stays partly. | 4.10 |
| D14 | The unwind order is the order of the interpreter today: in a frame, the reverse order of `StorageLive`; a clause frame before its fresh continuation. The effects model changes to it. | No run-time behavior changes. No theorem depends on the order. | 7.3 |
| D15 | The temporaries of the tail of a loop body end at the end of each iteration. | The order of today piles them up (`semantics.md` N5). An earlier end is stricter for the checker. The interpreter takes the rule when it compiles the Core. | 3.13 |
| D16 | The interpreter compiles the Core to its stack code (stage 6). Before that, it takes its exports from the Core. | Removes TWO. Keeps the machine. | 6 |
| D17 | A continuation is a value that points into the root of a hidden frame local of its clause. A scope capability points into the root of its binder. Only the end of the frame ends these roots. | Their escape becomes a use of an invalid reference. Kills RR3, V120, V134. | 3.24, 3.28 |
| D18 | Out of this design: monomorphization, a CFG IR, flow-sensitive `points_into`, regions for stored references, capabilities of handlers as values, `on abort` as a call, move paths beyond `Unpack`. | Each one is a separate decision. Section 9.3. | 9.3 |

---

## 1. Pipeline and principles

### 1.1 Pipeline

Today (`crates/weft-sema/src/lib.rs:248`):

```text
parse -> collect items and signatures -> infer (loop):
                                           Lower::lower_fn(f)   // types + names + facts, one walk
                                         -> FnFacts, EffectSig
          -> checker and spec
AST -> compile.rs (+ exports by_value, arg_order, int_ops from FnFacts) -> machine
```

After the change:

```text
parse -> collect items and signatures
      -> core::build(f) for each body, once      // names, methods, types, ANF, ends, unwinds
      -> core::validate (debug builds and tests)
      -> infer (loop):
           body::Lower::lower_core(core of f)    // facts only, one walk over the Core
           -> FnFacts, EffectSig
      -> checker and spec (no change)
Core -> core_compile.rs -> machine (no change)
```

The builder does not depend on the effect signatures of callees. So the Core of a body
is built once, also when effect inference lowers the body many times. Type errors,
name errors and W0315 come from the builder once, not from the last round of the
inference.

### 1.2 Principles

1. **One form for one meaning.** Each run-time event of `semantics.md` has one Core
   form: a read is an operand, a move is `Operand::Move` or `Unpack`, a value that goes
   away is the end of a local, a frame result is an assignment to a destination, a
   suspension is a statement with an unwind point.
2. **The builder decides; the fact generator follows.** Copy or move, the read point of
   an operand, the capture mode, the end of each local and the values on each abort
   path are decisions of the builder. The fact generator never decides them again.
3. **One template for one statement kind.** Each Core statement kind has one fact
   template (section 4.5). A template does not look at the surface form that made the
   statement.
4. **Uniform, relation-generic mechanisms.** The projection and the substitution of
   inner bodies, and the rebase of operation results, work on each relation of
   `FnFacts` through one table. A new relation needs one row in that table, and a test
   checks that the table names each field (as `FnFacts::mark` does today).
5. **The machine is the reference.** The Core follows the evaluation order, the read
   points, the temporaries and the frames of the interpreter of today
   (`semantics.md`, sections 2 to 5). Only D15 changes a lifetime, and only to make it
   shorter.
6. **Validate the Core.** A validator checks the well-formedness rules of section 2.3
   on each body in debug builds and in the tests. Many hypotheses of the proof link
   become validator rules (section 7.4).

### 1.3 What this angle keeps, and why

A MIR-like CFG IR (the sibling designs `docs/plan/core-ir-inputs/design_mir.md` and `docs/plan/core-ir-inputs/design_machine.md`)
removes more classes by construction: LOOP, STATE and part of POST. It also replaces
the whole fact generator. This design keeps the parts of the fact generator that work
and that do not depend on the surface form:

| Part | Lines today | Why it stays |
| --- | --- | --- |
| CFG emission (`emit`, `start`, components) | about 100 | The tree walk emits one node for each Core statement. The CFG facts are the same. |
| Abstract values of locals (`Local`, `Val` without its per-form fields) | about 1 500 | Places, function values, tasks and capability marks are the domain of the analysis. The Core does not change the domain. |
| Places, roots, steps, wildcards, one-place instances | about 900 | The place model of ADR 0003 is the spec input. |
| Summaries of signatures (`EffectSig`, `summary_to_sig`, `infer.rs`) | about 2 500 | The summary language is a separate decision (class SUM). |
| Loop fixpoint (`lower_loop`, `next_carry`, widening) | about 1 200 | A worklist dataflow needs a CFG IR. The fixpoint works; its state gets smaller. |
| Handler order and multi re-runs (`handle`, `handled_again`) | about 600 | The order "body, then clauses" and the re-run as a loop are correct. |
| Tasks, capability marks (W0313, W0314), stored values | about 3 000 | Value-flow questions (classes FNVAL, CAP, STORE). |

The cost of this choice: LOOP (3 unsound findings, 1 false positive) stays partly, and
the state of a local stays lowering state (class STATE). The benefit: the migration
can go construct by construct, with the old generator as the reference for each step.

### 1.4 Text form

The design uses this text form for the Core. A command `weft core FILE FUNCTION` prints
it (stage 2).

```text
body#0 fn callee() -> () {
  _0: () ret
  r: &u64
  t1: Vec<u64> temp(borrowed)
  ...
  live r
  handle#0 Note -> r [scope S2] clauses [note: body#1] {
    live t1
    t1 = call mk_v() unwind(S2:1)
    live t2
    t2 = &t1
    r = call first(move t2) unwind(S2:2)
    dead t2
    dead t1
  }
  ...
  return
}
```

- `live x`, `dead x`: `StorageLive`, `StorageDead`.
- `x = copy p`, `x = move p`, `x = &p`, `x = &p[]`: `Assign` with `Use` and `Ref`.
- `x = Add(copy a, const 1): u64`: `Bin` with its integer type.
- `x = call f(move a, copy b) unwind(S:n)`: `Call` with its unwind point (scope `S`, `n`
  live locals of `S`).
- `x = closure#3 { ref a, kept b, move c }`: `Rvalue::Closure`.
- `unpack t => (a, b)`: `Unpack`.
- Places: `x`, `(*x).hp`, `v[i]`, `v[]`, `(o as Some).0`, `up.x` (field `x` of the
  environment).

---

## 2. The IR as Rust types

### 2.1 Where the code goes

| Path | Content | Lines (estimate) |
| --- | --- | --- |
| `crates/weft-sema/src/core/mod.rs` | The types of section 2.2 | 700 |
| `crates/weft-sema/src/core/build/` | The builder: `names.rs`, `types.rs` (the unification of `Lower` today), `expr.rs` (ANF), `stmt.rs`, `pat.rs` (patterns and W0120), `call.rs` (method resolution, argument order), `closure.rs` (environments, capture modes), `elab.rs` (ends, frames, jumps, unwind points) | 4 700 |
| `crates/weft-sema/src/core/print.rs` | The text form of section 1.4 | 300 |
| `crates/weft-sema/src/core/validate.rs` | The rules of section 2.3 | 450 |
| `crates/weft-sema/src/body/` | The fact generator over the Core | 9 500 (from 18 415) |
| `crates/weft-interp/src/core_compile.rs` | Core to `code::Op` (stage 6) | 900 (replaces `compile.rs`, 1 544) |
| `crates/weft-check/tests/ir_gate.rs`, `tests/ir_gate/` | The diff gate of section 8.2 | 600 |

`weft-facts`, `weft-check`, `weft-datalog`, `weft-verified`, `spec/weft.dl` and
`machine/` do not change, except for one constant in `weft-facts` (the pointer-word
step, D9) and one line of `FnFacts` for the switch of section 8.3.

### 2.2 The types

The listing below compiles with `rustc -W missing_docs` (file
`ir/work/minimal/core_sketch.rs`, with stubs for `Ty`, `FnId`, `AdtId`, `EffectId`,
`IntTy`, `BinOp`, `UnOp` and `Span`). In `weft-sema` these are the existing types. One
change to `Ty`: `FnTy::summary: Option<usize>` (an index of a closure summary of the
walk) becomes `FnTy::closures: ClosureSet` (the closure literals that the value can
be). The builder joins the sets where two function types unify, as `fn_joins` joins
summaries today (`body/mod.rs:1611`).

```rust
//! The core IR ("Core") of Weft: a small typed tree language between the typed
//! AST and fact generation.
//!
//! The Core keeps the tree shape of the AST: blocks, `if`, `match`, loops,
//! `handle` and `scope` stay nested. It removes everything else that made the
//! old lowering special-case each surface form:
//!
//! - Each operand is a constant or a read of a place (`copy` or `move`). An
//!   operand is never an expression.
//! - Each value that an expression makes goes into a local. A temporary is a
//!   local of kind [`LocalKind::Temp`].
//! - Each local starts with [`StmtKind::StorageLive`] and ends with
//!   [`StmtKind::StorageDead`] on each path, also on the path of a `break`,
//!   a `continue` and a `return`.
//! - Each move is explicit: an operand [`Operand::Move`], or [`StmtKind::Unpack`].
//! - A value goes away only at the end of its local, or when an
//!   [`StmtKind::Assign`] replaces it.
//! - Each frame (a function, a closure, a clause, a handled body, a scope body)
//!   moves its value into a destination local first. Then it ends its locals
//!   and its temporaries.
//! - A closure literal is an aggregate of its environment ([`Rvalue::Closure`]).
//! - Each statement that can suspend or abort names its unwind point
//!   ([`UnwindPoint`]).
//!
//! The builder makes the Core after type inference. So each local has its
//! final type, and the builder chooses `copy` or `move` from that type.
//!
//! `Ty`, `FnId`, `AdtId`, `EffectId`, `IntTy`, `BinOp`, `UnOp` and `Span` are
//! the existing types of `weft-sema` and `weft-syntax`.

// ---------------------------------------------------------------------------
// Ids
// ---------------------------------------------------------------------------

/// The index of a body in [`CoreProgram::bodies`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BodyId(pub u32);

/// The index of a local in [`CoreBody::locals`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(pub u32);

/// The index of an unwind scope in [`CoreBody::scopes`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ScopeId(pub u32);

/// A loop of a body. [`StmtKind::Break`] and [`StmtKind::Continue`] name it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LoopId(pub u32);

/// A `handle` expression. All bodies of one function share these ids. The
/// fact generator uses the id as the capability (`CapId`) of the handler.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct HandleId(pub u32);

/// A closure literal. All bodies of one function share these ids. A function
/// type carries a set of them ([`ClosureSet`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ClosureId(pub u32);

/// The index of an environment field of a closure or a clause
/// ([`CoreBody::env`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EnvIdx(pub u32);

// ---------------------------------------------------------------------------
// Program and bodies
// ---------------------------------------------------------------------------

/// The Core of a program: one tree of bodies for each function and each test.
#[derive(Clone, Debug, Default)]
pub struct CoreProgram {
    /// All bodies. An inner body (a closure or a clause) comes after its parent.
    pub bodies: Vec<CoreBody>,
    /// The body of each function with a body, by function index.
    pub fn_body: Vec<Option<BodyId>>,
    /// The body of each test, with the name of the test.
    pub tests: Vec<(String, BodyId)>,
}

/// One body: a function, a test, a closure or a handler clause.
///
/// A handled body and a scope body are not bodies. They stay inline in the
/// body around them ([`Handle::body`], [`ScopeStmt::body`]), with the same
/// frame rules. The fact generator writes them into the component of the body
/// around them, as the old lowering does.
#[derive(Clone, Debug)]
pub struct CoreBody {
    /// What the body is.
    pub kind: BodyKind,
    /// The source location of the body.
    pub span: Span,
    /// The source unit. The spans are byte offsets in this unit.
    pub unit: usize,
    /// The locals: parameters, the return slot, user locals and temporaries.
    pub locals: Vec<LocalDecl>,
    /// The parameters, in the order of the signature. A clause has the
    /// arguments of its operation here.
    pub params: Vec<LocalId>,
    /// The environment of a closure or a clause: one field for each captured
    /// local of the parent body. Empty for a function and a test.
    pub env: Vec<EnvField>,
    /// The local that holds the value of the body when it returns.
    pub ret: LocalId,
    /// The statements of the body. The last statement is [`StmtKind::Return`].
    pub block: Block,
    /// The unwind scopes. Scope 0 is the scope of the whole body.
    pub scopes: Vec<UnwindScope>,
    /// The inner bodies that this body makes: its closures and its clauses.
    pub inner: Vec<BodyId>,
}

/// What a body is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BodyKind {
    /// The body of a function.
    Fn(FnId),
    /// The body of a test block.
    Test,
    /// The body of a closure literal.
    Closure {
        /// The body that makes the closure.
        parent: BodyId,
        /// The closure literal.
        id: ClosureId,
    },
    /// A clause of a `handle` expression.
    Clause {
        /// The body that has the `handle` expression.
        parent: BodyId,
        /// The `handle` expression.
        handle: HandleId,
        /// The index of the operation in the effect.
        op: usize,
        /// The local of the continuation (`resume`).
        cont: LocalId,
        /// The hidden local of kind [`LocalKind::ClauseFrame`]. The value of
        /// the continuation points into its root.
        frame: LocalId,
    },
}

/// A local of a body.
#[derive(Clone, Debug)]
pub struct LocalDecl {
    /// The name in diagnostics: the source name, or a description such as
    /// `argument 2 of push`.
    pub name: String,
    /// What the local is.
    pub kind: LocalKind,
    /// The final type. It has no inference variable.
    pub ty: Ty,
    /// The properties of the type that the fact generator and the
    /// interpreter need.
    pub props: LocalProps,
    /// The source location of the declaration, or of the expression for a
    /// temporary.
    pub span: Span,
    /// The unwind scope that ends the local.
    pub scope: ScopeId,
    /// The source declares the local with no value (`let x: T`). The fact
    /// generator gives it `unset_at` at its `StorageLive` (W0304).
    pub unset: bool,
}

/// What a local is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LocalKind {
    /// A local that the source declares with `let`, a pattern or a loop.
    User,
    /// A parameter.
    Param,
    /// The return slot of the body.
    Ret,
    /// A value that the builder makes. It has no name in the source.
    Temp(TempKind),
    /// The continuation of a clause (`resume`).
    Cont,
    /// A hidden local that stands for the frame of a clause. A continuation
    /// value points into its root. Only the end of the clause ends it, and
    /// nothing moves it. So a closure that keeps the continuation after the
    /// clause ends holds an invalid reference.
    ClauseFrame,
    /// The binder of a `scope` (`s`).
    ScopeBinder,
    /// The hidden iterator of a `for` loop.
    Iterator,
    /// The result of a task that a spawn in statement position gives to its
    /// scope. The end of the scope drops it ([`StmtKind::ScopeEnd`]).
    TaskResult,
}

/// Why the builder made a temporary. Diagnostics use it for their text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TempKind {
    /// The value of an operand or an argument.
    Operand,
    /// A reference to a place that the machine reads later than the builder
    /// forms it (rule ORDER-2 of the design: a late read).
    EarlyBorrow,
    /// A value that `&e` borrows.
    Borrowed,
    /// A receiver that is not a place.
    Receiver,
    /// The value that a `match` tests.
    Scrutinee,
    /// The value of a block, an `if`, a `match`, a `handle` or a `scope`.
    Value,
    /// A value that nothing uses: an expression statement, `_`, a loop body.
    Discard,
    /// A part of a value that a pattern takes.
    Part,
    /// The result of a call.
    CallResult,
}

/// The properties of the final type of a local.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LocalProps {
    /// A read copies the value (plain data). Else a read moves it.
    pub copy: bool,
    /// The value is linear.
    pub linear: bool,
    /// Each linear part of the value has `on abort`.
    pub has_on_abort: bool,
    /// The type is `!Move`.
    pub immovable: bool,
    /// The value cannot cross threads.
    pub nonportable: bool,
    /// The value is not `many`: a `multi` resume cannot copy it.
    pub once: bool,
    /// The type mentions a type parameter that a caller can make linear.
    pub maybe_linear: bool,
    /// The value can hold a function value.
    pub holds_fn: bool,
    /// The value can hold a reference.
    pub holds_refs: bool,
}

/// A field of the environment of a closure or a clause.
#[derive(Clone, Debug)]
pub struct EnvField {
    /// The captured local of the parent body.
    pub outer: LocalId,
    /// How the closure holds the local.
    pub capture: Capture,
    /// The type of the captured local.
    pub ty: Ty,
}

/// How a closure or a clause holds a captured local.
///
/// One function of the builder chooses the mode (`capture_mode`). The
/// interpreter uses the same choice: [`Capture::Move`] is an owned cell of the
/// closure, the other two are the cell of the local.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Capture {
    /// The closure refers to the cell of the local. The closure value points
    /// into the root of the local.
    Ref,
    /// The closure refers to the cell of a local of plain data, and the body
    /// never borrows it. The cell stays readable after the local ends, so the
    /// closure value points only where the value of the local points.
    Kept,
    /// The closure takes the value when it is made (a by-value capture). Only
    /// a closure can do this. A clause never does.
    Move,
}

/// A sequence of statements.
#[derive(Clone, Debug, Default)]
pub struct Block {
    /// The statements, in the order that they run.
    pub stmts: Vec<Stmt>,
}

/// A statement and its source location.
#[derive(Clone, Debug)]
pub struct Stmt {
    /// What the statement does.
    pub kind: StmtKind,
    /// The source location. Diagnostics use it.
    pub span: Span,
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

/// What a statement does.
#[derive(Clone, Debug)]
pub enum StmtKind {
    /// The local starts. It has no value yet.
    StorageLive(LocalId),
    /// The local ends. The value that it still holds, or the parts of the
    /// value that did not move, go away here.
    StorageDead(LocalId),
    /// Computes the value and puts it into the place. If the place has a
    /// value, that value goes away first. `init` is true if the place is a
    /// whole local that has no value yet (the first value after
    /// `StorageLive`): then no old value goes away and the cell is not
    /// written.
    Assign {
        /// The place that gets the value.
        place: Place,
        /// The value.
        value: Rvalue,
        /// The place is a whole local with no value yet.
        init: bool,
    },
    /// Moves the whole value out of `src` and puts its parts into new locals.
    /// A destructuring `let`, a by-value `match` binding and a tuple pattern
    /// lower to it. A part that a pattern does not name (`_`) goes into a
    /// local of kind [`TempKind::Part`] that ends at once.
    Unpack {
        /// The place of the value. It moves as a whole.
        src: Place,
        /// Each part: the projection from `src`, and the local that gets it.
        parts: Vec<(Vec<Proj>, LocalId)>,
        /// The value is a linear struct: the unpack consumes its record.
        consume: bool,
    },
    /// A place in statement position, such as `v` or `v[i]` on its own line.
    /// It names the place. It reads nothing and moves nothing.
    Mention(Place),
    /// A call of any kind: a function item, a function value, an operation,
    /// a `resume`, or a built-in of tasks.
    Call(Box<Call>),
    /// `print(args)`. It reads each argument here.
    Print {
        /// The arguments.
        args: Vec<Operand>,
    },
    /// `assert cond`. If the condition is false, the task aborts and unwinds.
    Assert {
        /// The condition.
        cond: Operand,
        /// The values that the abort unwinds.
        unwind: UnwindPoint,
    },
    /// `if`. The condition is a local or a constant.
    If {
        /// The condition.
        cond: Operand,
        /// The branch for `true`.
        then: Block,
        /// The branch for `false`. It can be empty.
        else_: Block,
    },
    /// `match`. The arms test the place in order. The first arm that matches
    /// binds and runs.
    Match {
        /// The place that the arms test.
        scrut: Place,
        /// The arms.
        arms: Vec<Arm>,
    },
    /// A loop. `while` and `for` lower to it.
    Loop {
        /// The id that `break` and `continue` name.
        id: LoopId,
        /// The source form, for diagnostics.
        kind: LoopKind,
        /// The body. Control goes back to its start at its end.
        body: Block,
    },
    /// Takes the next element from an iterator. If there is one, `dest` starts
    /// here and gets it. If there is none, `dest` does not start, and control
    /// leaves the loop `exit`.
    IterNext {
        /// The iterator local.
        iter: LocalId,
        /// The local that gets the element. It starts here.
        dest: LocalId,
        /// The loop to leave at the end.
        exit: LoopId,
    },
    /// Leaves the loop. The builder ends the locals of the loop before it.
    Break(LoopId),
    /// Goes to the start of the loop body. The builder ends the locals of the
    /// iteration before it.
    Continue(LoopId),
    /// Leaves the body. The value is in [`CoreBody::ret`]. The builder ends
    /// the locals of the body before it.
    Return,
    /// `handle E { clauses } in body`.
    Handle(Box<Handle>),
    /// `scope { s => body }`.
    Scope(Box<ScopeStmt>),
    /// The end of a scope body: wait for the tasks of the scope. This can
    /// abort if a task failed.
    ScopeEnd {
        /// The binder of the scope.
        binder: LocalId,
        /// The task results that spawns in statement position gave to the
        /// scope. They go away here.
        given: Vec<LocalId>,
        /// The values that an abort here unwinds.
        unwind: UnwindPoint,
    },
    /// A spawn in statement position gives its task handle to the scope. The
    /// handle moves. The end of the scope puts the result into `result`.
    Give {
        /// The task handle. It moves here.
        handle: LocalId,
        /// The binder of the scope.
        scope: LocalId,
        /// The local of kind [`LocalKind::TaskResult`] that gets the result at
        /// the end of the scope.
        result: LocalId,
    },
    /// A compile error that becomes a fault at run time. Control does not go
    /// on.
    Unreachable(String),
}

/// The source form of a loop.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LoopKind {
    /// `loop { ... }`.
    Loop,
    /// `while cond { ... }`.
    While,
    /// `for pat in iter { ... }`.
    For,
}

/// An arm of a `match`.
#[derive(Clone, Debug)]
pub struct Arm {
    /// The test of the pattern. The test reads the place and binds nothing.
    pub test: PatTest,
    /// The bindings of the pattern, in the order of the pattern.
    pub binds: Vec<Bind>,
    /// The body of the arm. It ends with the value of the arm in the
    /// destination of the `match`, and then the ends of the bindings.
    pub body: Block,
    /// The source location of the arm.
    pub span: Span,
}

/// The test part of a pattern.
#[derive(Clone, Debug, PartialEq)]
pub enum PatTest {
    /// Matches each value: `_` or a binding.
    Any,
    /// Matches a literal.
    Lit(Const),
    /// Matches the parts of a tuple.
    Tuple(Vec<PatTest>),
    /// Matches a variant and its payload.
    Variant {
        /// The index of the variant.
        variant: u32,
        /// The tests of the payload fields.
        fields: Vec<PatTest>,
    },
}

/// A binding of a pattern.
#[derive(Clone, Debug)]
pub struct Bind {
    /// The local that gets the value.
    pub local: LocalId,
    /// The place of the bound part: the scrutinee and projections.
    pub from: Place,
    /// How the local gets the part.
    pub mode: BindMode,
}

/// How a binding gets its part.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindMode {
    /// The local gets a copy of the part.
    Copy,
    /// The part moves into the local. The scrutinee moves as a whole (ADR 0003).
    Move,
    /// The local gets a reference to the part. A scrutinee behind a reference
    /// binds so.
    Ref,
}

/// A call. The arguments are already evaluated, in the order of evaluation.
/// The call reads them here.
#[derive(Clone, Debug)]
pub struct Call {
    /// What the call runs.
    pub callee: Callee,
    /// The arguments, in the order of the parameters. The receiver of a method
    /// is the first argument.
    pub args: Vec<CallArg>,
    /// The local that gets the result. `None` for a call whose result is `()`
    /// and that nothing uses.
    pub dest: Option<LocalId>,
    /// The values that an abort at the call unwinds.
    pub unwind: UnwindPoint,
}

/// What a call runs.
#[derive(Clone, Debug)]
pub enum Callee {
    /// A function item, with the type arguments of this call. A method that
    /// the builder resolves is a function item too.
    Item {
        /// The function.
        f: FnId,
        /// The type arguments.
        targs: Vec<Ty>,
    },
    /// A function value in a place: a closure, a function item, a function
    /// parameter or a value that the body does not know.
    Value(Place),
    /// An operation of an effect.
    Op {
        /// The handler that the operation reaches.
        cap: CapRef,
        /// The effect.
        effect: EffectId,
        /// The index of the operation in the effect.
        op: usize,
    },
    /// `resume(arg)`: a call of a continuation in a place.
    Resume(Place),
    /// `s.spawn(f)`: starts a task in the scope of the binder in the place.
    Spawn(Place),
    /// `t.join()`.
    Join,
    /// `t.detach()`.
    Detach,
    /// `fork(f, g, ...)`.
    Fork,
}

/// The handler that an operation reaches. The builder finds it by the lexical
/// rule (ADR 0005).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CapRef {
    /// A `handle` of this function, also from inside a closure or a clause of
    /// the function.
    Local(HandleId),
    /// A handler of a caller: the effect row of the function.
    Caller,
}

/// An argument of a call.
#[derive(Clone, Debug)]
pub struct CallArg {
    /// The value.
    pub op: Operand,
    /// The callee builds the value in place: a `!Move` value for a parameter
    /// of its own type, or the argument of `Box.new` and `Rc.new` (ADR 0007).
    /// A move of such an operand is not a move of a `!Move` value (W0604).
    pub in_place: bool,
}

/// `handle E { clauses } in body`.
#[derive(Clone, Debug)]
pub struct Handle {
    /// The handler.
    pub id: HandleId,
    /// The handled effect.
    pub effect: EffectId,
    /// The clauses. Each clause is an inner body of kind
    /// [`BodyKind::Clause`]. Its environment holds the cells of the locals
    /// that it captures.
    pub clauses: Vec<BodyId>,
    /// The handled body, inline. Its last statements move its value into
    /// `dest` and then end its locals and temporaries (rule FRAME).
    pub body: Block,
    /// The local that gets the value of the `handle`.
    pub dest: LocalId,
    /// The unwind scope of the handled body. An abort to this handler unwinds
    /// the values of this scope and of the scopes inside it.
    pub scope: ScopeId,
    /// The handled body can run again after a `multi` resume: the effect has a
    /// `multi` operation, and a clause can name `resume` more than once or in
    /// a loop, a closure or another clause (ADR 0005).
    pub rerun: bool,
}

/// `scope { s => body }`.
#[derive(Clone, Debug)]
pub struct ScopeStmt {
    /// The binder `s`. It starts before the body and ends after the statement.
    pub binder: LocalId,
    /// The scope body, inline. Its last statements move its value into
    /// `dest`, then [`StmtKind::ScopeEnd`], then the ends of its locals and
    /// temporaries.
    pub body: Block,
    /// The local that gets the value of the scope.
    pub dest: LocalId,
    /// The unwind scope of the scope body.
    pub scope: ScopeId,
}

// ---------------------------------------------------------------------------
// Unwinding
// ---------------------------------------------------------------------------

/// A lexical scope of locals, for the ends on abort paths.
#[derive(Clone, Debug)]
pub struct UnwindScope {
    /// The scope around this one. `None` for scope 0.
    pub parent: Option<ScopeId>,
    /// The number of locals of the parent that are live where this scope
    /// starts.
    pub parent_live: u32,
    /// What ends at the end of this scope.
    pub kind: ScopeKind,
    /// The locals of the scope, in the order of `StorageLive`. An unwinding
    /// ends them in the reverse order.
    pub locals: Vec<LocalId>,
}

/// What a scope is. An abort goes to the end of a scope of the kind
/// [`ScopeKind::HandledBody`], or out of the body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScopeKind {
    /// The whole body.
    Body,
    /// A block.
    Block,
    /// The temporaries of one statement.
    Statement,
    /// The handled body of a `handle`.
    HandledBody(HandleId),
    /// The body of a `scope`. An abort through it cancels and waits for the
    /// tasks of the scope.
    ScopeBody(LocalId),
    /// One iteration of a loop body.
    Iteration(LoopId),
}

/// The point of a statement that can abort: the innermost unwind scope and
/// the number of its locals that are live there.
///
/// The values that an abort to handler `h` unwinds are the live locals of
/// this scope and of each scope around it, up to and with the scope
/// [`ScopeKind::HandledBody`] of `h`. An abort of the whole task (a failed
/// `assert`, an operation of a handler of a caller that does not resume, a
/// cancellation) unwinds the live locals of each scope of the body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UnwindPoint {
    /// The innermost scope.
    pub scope: ScopeId,
    /// The number of its locals that are live.
    pub live: u32,
}

// ---------------------------------------------------------------------------
// Values, operands and places
// ---------------------------------------------------------------------------

/// A value that an assignment computes.
#[derive(Clone, Debug)]
pub enum Rvalue {
    /// The value of an operand.
    Use(Operand),
    /// A reference to a place. `all` is true for `&p[]`: a slice of all the
    /// elements.
    Ref {
        /// The place.
        place: Place,
        /// The reference is a slice of all the elements of the place.
        all: bool,
    },
    /// An arithmetic operator or a comparison of two copy values. `ty` is the
    /// integer type of an arithmetic result: the machine checks that the
    /// result fits it.
    Bin {
        /// The operator. It is not `&&` or `||`: these lower to `if`.
        op: BinOp,
        /// The left operand.
        lhs: Operand,
        /// The right operand.
        rhs: Operand,
        /// The integer type of the result, for arithmetic.
        ty: Option<IntTy>,
    },
    /// A comparison of two values that are not plain data. It reads both
    /// places and moves neither.
    Compare {
        /// The operator: `==`, `!=`, `<`, `<=`, `>` or `>=`.
        op: BinOp,
        /// The left place.
        lhs: Place,
        /// The right place.
        rhs: Place,
    },
    /// `-x` or `!x`.
    Un {
        /// The operator. It is not `&`: a borrow is [`Rvalue::Ref`].
        op: UnOp,
        /// The operand.
        arg: Operand,
        /// The integer type of the result of `-x`.
        ty: Option<IntTy>,
    },
    /// A tuple, an array, a struct, or a variant of an enum.
    Aggregate {
        /// What the aggregate is.
        kind: AggKind,
        /// The value of each field, in the order of the fields of the type.
        fields: Vec<FieldValue>,
    },
    /// A closure literal: its body and its environment.
    Closure {
        /// The closure literal.
        id: ClosureId,
        /// The body of the closure.
        body: BodyId,
        /// One operand for each field of [`CoreBody::env`] of the body.
        env: Vec<EnvOperand>,
    },
    /// A function item as a value.
    FnItem {
        /// The function.
        f: FnId,
        /// The type arguments.
        targs: Vec<Ty>,
    },
    /// A string with interpolated parts. Each part is converted to a string
    /// where it is evaluated (the machine reads it at once).
    Str(Vec<StrPiece>),
    /// An iterator over the elements of a place (`for x in v[]`). Each step
    /// reads the length of the place.
    Elems(Place),
    /// An iterator over a range `lo..hi`.
    Range {
        /// The start.
        lo: Operand,
        /// The end, not included.
        hi: Operand,
    },
    /// The result of a task that a scope gave back at its end
    /// ([`StmtKind::Give`]).
    TaskResult(LocalId),
}

/// The kind of an aggregate.
#[derive(Clone, Debug, PartialEq)]
pub enum AggKind {
    /// A tuple.
    Tuple,
    /// An array or a `Vec` literal.
    Array,
    /// A struct.
    Struct(AdtId),
    /// A variant of an enum.
    Variant(AdtId, u32),
}

/// The value of one field of an aggregate.
#[derive(Clone, Debug)]
pub enum FieldValue {
    /// The field gets the value of the operand.
    Value(Operand),
    /// A place field of a `!Move` struct gets no value here (W0304 until the
    /// body sets it, ADR 0007).
    Unset,
}

/// A part of a string with interpolated parts.
#[derive(Clone, Debug)]
pub enum StrPiece {
    /// Plain text.
    Text(String),
    /// A local that holds the string form of an interpolated value.
    Value(LocalId),
}

/// An operand of a closure environment.
#[derive(Clone, Debug)]
pub enum EnvOperand {
    /// The cell of the local ([`Capture::Ref`]).
    Ref(Place),
    /// The cell of a local of plain data that the body never borrows
    /// ([`Capture::Kept`]).
    Kept(Place),
    /// The value of the local. It moves here ([`Capture::Move`]).
    Move(Place),
}

/// An operand: a constant or a read of a place.
#[derive(Clone, Debug)]
pub enum Operand {
    /// Reads the value and keeps it in the place. The type is plain data.
    Copy(Place),
    /// Reads the value and moves it out of the place.
    Move(Place),
    /// A constant.
    Const(Const),
}

/// A constant.
#[derive(Clone, Debug, PartialEq)]
pub enum Const {
    /// An integer of an integer type.
    Int(i128, IntTy),
    /// `true` or `false`.
    Bool(bool),
    /// A string with no interpolated part.
    Str(String),
    /// `()`.
    Unit,
    /// A duration in milliseconds (`2.s`).
    Duration(u64),
    /// A variant of an enum with no payload, such as `None`.
    Variant(AdtId, u32),
}

/// A place: a base and a list of projections.
#[derive(Clone, Debug, PartialEq)]
pub struct Place {
    /// The local or the captured local where the place starts.
    pub base: PlaceBase,
    /// The steps from the base, in order.
    pub proj: Vec<Proj>,
}

/// Where a place starts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlaceBase {
    /// A local of this body.
    Local(LocalId),
    /// A captured local, through field `i` of the environment of this body.
    /// Only a closure body or a clause body has it.
    Upvar(EnvIdx),
}

/// One step of a place.
#[derive(Clone, Debug, PartialEq)]
pub enum Proj {
    /// A field of a struct or a part of a tuple: a stable step.
    Field(u32),
    /// The payload of a variant: an unstable step. A `match` arm that tests
    /// the variant uses it.
    Variant(u32),
    /// An element at the index in the local. The step reads the length of the
    /// place before it (a bounds check).
    Index(LocalId),
    /// All the elements (`v[]`): the element step of the type.
    Elems,
    /// The target of a pointer. The kind tells how the facts resolve it.
    Deref(DerefKind),
}

/// The pointer that a [`Proj::Deref`] follows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DerefKind {
    /// A reference. The place goes to the places that the reference points
    /// into.
    Ref,
    /// A `Box`. The place goes to the unstable target step of the box.
    Box,
    /// An `Rc`. The place goes to the group root of the type. The place
    /// depends on the handle.
    Rc,
}


/// A set of closure literals that a function value can be. The builder joins
/// the sets where two function types unify. It replaces `FnTy::summary`.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct ClosureSet(pub Vec<ClosureId>);
```

### 2.3 Well-formedness rules (the validator)

`core::validate` checks these rules on each body. A violation is a bug of the builder,
not an error of the program. The tests run the validator on each program of the diff
gate (section 8.2), and debug builds run it on each body.

| Rule | Statement |
| --- | --- |
| V1 Types | Each local has a type with no inference variable. An operand `Copy(p)` has a type with `props.copy`. An `Index(i)` local has an integer type. |
| V2 Storage | On each path through a body, each local that is not a parameter, the return slot or an environment field gets `StorageLive` before its first use and `StorageDead` once after its last use. No local gets `StorageLive` while it is live. |
| V3 Values of temporaries | Each read of a local of kind `Temp`, `Ret`, `Iterator` or `TaskResult` comes after an assignment to it on each path (a definite-assignment check over the tree). User locals are not checked here: a use of `let x: T` before a value is W0304, and the spec reports it. |
| V4 Single use of temporaries | A temporary of kind `Operand`, `EarlyBorrow`, `Receiver` or `CallResult` is read by one statement only. |
| V5 Frames | The body of a `handle` and of a `scope` ends with the frame epilogue of rule FRAME: an assignment to `dest`, then (for a scope) `ScopeEnd`, then `StorageDead` of each local of its unwind scope. A body block ends with the same epilogue for `ret`, then `Return`. |
| V6 Jumps | Before `Break(l)`, `Continue(l)` and `Return`, each local of each unwind scope between the jump and its target is dead. |
| V7 Unwind points | Each `Call`, `Assert` and `ScopeEnd` names the innermost unwind scope at its position, and the number of locals of that scope that are live there. |
| V8 ANF | Each operand of a statement or an rvalue is a constant, or a `Copy` or a `Move` of a place. No place has an `Index` of a local that is not live. |
| V9 Late reads | A temporary of kind `EarlyBorrow` is used only under a `Deref` in one statement of the same source statement. |
| V10 Captures | A `Move` field exists only in a closure. A `Kept` field has a copy type, and no statement of the body (or of an inner body) borrows a place at or below it. The rule recomputes the capture mode and compares. |
| V11 Lexical effects | `Callee::Op` with `CapRef::Local(h)` occurs only in the body of `h` or in an inner body that the body of `h` makes. `Callee::Resume` occurs only in a clause or in an inner body of a clause. `Callee::Spawn` names a local of kind `ScopeBinder` or an environment field of one. |
| V12 Dead code | No statement follows `Return`, `Break`, `Continue` or `Unreachable` in its block. |
| V13 Bodies | Each inner body has one maker: one `Rvalue::Closure` or one entry of `Handle::clauses`. |

### 2.4 The Core and the code units of the interpreter

The Core has the frame structure of the interpreter (`semantics.md`, section 1.1):

| Interpreter code unit (`CodeKind`) | Core |
| --- | --- |
| `Fn(f)` | a body of kind `BodyKind::Fn(f)` |
| `Test` | a body of kind `BodyKind::Test` |
| `Closure` | a body of kind `BodyKind::Closure`; its environment is `MakeClosure { caps, owned }`: a `Ref` or `Kept` field is a captured cell, a `Move` field is an index in `owned` |
| `Clause` | a body of kind `BodyKind::Clause`; its environment is `ClauseSpec::caps` |
| `HandleBody` | `Handle::body`, inline. The Core compiler of stage 6 moves it into a code unit of its own; its captured cells are the outer locals that it names. |
| `ScopeBody` | `ScopeStmt::body`, inline, moved into a code unit in the same way |
| a slot | a local of kind `User`, `Param`, `Iterator`, `ScopeBinder` |
| a temporary cell (`ToTemp`) or a value on the operand stack | a local of kind `Temp` |
| `StmtBegin` and `StmtEnd` | an unwind scope of kind `Statement` and the `StorageDead` of its temporaries |
| `DropSlots` | `StorageDead` of the locals of a block |


---

## 3. Lowering rules: typed AST to Core

### 3.0 General rules

The builder has three passes over one body:

1. **Walk.** It walks the AST once, in the order of evaluation. It resolves names and
   methods, infers types by unification (the code of `Lower::unify` today), and emits
   Core statements. For each expression it returns a list of statements and one of
   three results: an operand, a place, or "the value is already in the destination". A
   read whose type is not known yet is an operand "copy or move". The walk puts each
   operand that has a later sibling into a temporary.
2. **Finalize.** It resolves the types, sets `LocalProps`, turns each "copy or move"
   into `Copy` or `Move`, chooses the capture modes (rule CAPTURE, innermost closure
   first), and collapses a temporary into a direct operand where rule ORDER-2 allows
   it.
3. **Elaborate.** It writes `StorageDead` (rules TEMP, FRAME, DISCARD, JUMP), the unwind
   scopes and the unwind points (rule UNWIND). Then the validator runs.

The rules below hold for each construct. Sections 3.1 to 3.34 give only what is
special to a construct.

**Rule ANF (operands).** An operand is a constant or a read of a place. An expression
that is not a place and not a constant lowers to statements that put its value into a
local, and the operand reads that local. The builder writes `StorageLive` of a
temporary directly before the statement that gives it its value. So no temporary is
live with no value, except a destination that a nested frame fills.

**Rule ORDER-1 (order of evaluation).** The builder emits the statements of the parts
of an expression in the order of the machine (`semantics.md`, section 2.1): left to
right, with five exceptions.

1. A call of a function item, of a method of a value with named arguments, or of an
   operation evaluates its arguments in the order of the parameters. The builder
   computes this order once (today `order_args`, `body/args.rs`, and the span-keyed
   `FnFacts::arg_order`).
2. An assignment evaluates the value first, then the index operands of the target.
3. A place operand of a binary operator, an argument of `print` and the base of an
   index are read at the operator, not where they are written.
4. A method receiver is a place first. The call reads it, and moves it if `self` is
   by value, after the arguments.
5. A positional struct evaluates its arguments in the order of the fields.

**Rule ORDER-2 (where a read happens).** A place operand has a formation point and an
access point. The formation point is where the machine follows the `Field` and `Deref`
steps of the place: at the place expression itself. An `Index` step comes after its
index operand. The access point is where the machine reads, moves or borrows the
place: at the consumer for exceptions 3 and 4 of ORDER-1, else at the place
expression. Let `S` be the parts of the expression that the machine evaluates between
the two points. A part is **inert** if it is a constant, a read of a local, or a place
with inert index operands. A call, an operation, an assignment, a block with
statements and a closure literal with a `Move` field are not inert.

- If `S` is empty or each part of `S` is inert, the place goes directly into the
  consumer: `copy p`, `move p`, `&p`.
- Else, if the access point is the place expression (a call argument, a part of a
  literal, a value of `let`), the builder writes `t = copy p` or `t = move p` at the
  place expression, and the consumer reads `t`.
- Else (a late read), the builder writes `t = &p` (a temporary of kind
  `EarlyBorrow`) at the formation point, and the consumer reads `*t`.
- A `move` operand always goes into a temporary at its place expression if a later
  part of `S` reads or writes any place. So `f(v, v.len())` moves `v` before the
  second argument reads it (W0302, as the machine faults).

So the Core has the exact read points of the machine of today. The second and third
cases make the late-read shapes N1 to N3 of `semantics.md` into uses of a temporary
reference after an invalidation (W0301), with no change to the interpreter. Example in
section 3.35.

**Rule COPY-MOVE.** An operand is `Copy` if the final type is plain data (`props.rs`,
not `NotCopy`), else `Move`. A value of a type parameter and a closure are not plain
data. A move out of a place behind a reference is W0303: the builder reports it and
writes `Copy` to go on.

**Rule TEMP (lifetimes of temporaries).** Each source statement opens an unwind scope
of kind `Statement`. The temporaries that the builder makes for the statement belong
to that scope. At the end of the statement the builder ends them in the reverse order
of their `StorageLive`. The rules of the machine (`semantics.md`, section 4.2) decide
the statement:

| Code | The temporaries end at |
| --- | --- |
| a statement that is not a tail | the end of that statement |
| the tail of a block | the end of the statement around the block |
| the condition of `while` | the end of the condition (a statement of its own) |
| the tail of a loop body | the end of the iteration (D15; the machine of today keeps them to the end of the loop) |
| the tail of a frame (function, closure, clause, handled body, scope body) | the frame epilogue, after the value moved into the destination |

**Rule FRAME (the end of a frame).** A frame `F` with destination `d` ends with these
statements, in this order:

1. `d = move t` or `d = copy t`, where `t` is the value of the tail (or `d = const ()`).
   If the tail is a call, the call writes into `d` directly.
2. For a scope body: `ScopeEnd` (section 3.28).
3. `StorageDead` of the locals of `F`, in the reverse order of `StorageLive`.
4. `StorageDead` of the temporaries of the tail.
5. For a function, a closure and a clause: `StorageDead` of the parameters (a
   reference parameter ends its own cell, not what it points into), then `Return`.

The destination is `CoreBody::ret` for a body, `Handle::dest` for a handled body,
`ScopeStmt::dest` for a scope body, and a temporary of kind `Value` (or the binder of a
`let`) for a block, an `if` arm and a `match` arm. The machine has the same order
(`semantics.md`, section 5.3). Because `d` is live across steps 2 to 5, each free there
reaches each later use of `d`. This is the rule that the old lowering wrote by hand for
blocks (`hold_out`, `use_held`) and forgot for handled bodies, clauses, `resume`
arguments and scope bodies (O3-2, O3-3, F3-7).

**Rule DISCARD.** A value that nothing uses goes into a temporary of kind `Discard`,
and the end of the statement ends it. This holds for an expression statement, `let _ =
e`, a part `_` of a pattern, the tail of a block statement, the tail of a loop body and
the tail of an `if` with no `else`. A place of a local in statement position is not a
value: it lowers to `Mention(p)` (ADR 0003).

**Rule JUMP.** Before `break l`, `continue l` and `return`, the builder writes
`StorageDead` of each local of each unwind scope between the jump and its target,
innermost first, each scope in the reverse order of `StorageLive`. This includes the
temporaries of the statements around the jump, so a value on its way to a call ends at
a `return` in a later argument (OL-3c). For `return e`, the builder first writes
`ret = move t`.

**Rule UNWIND.** Each `Call`, `Assert` and `ScopeEnd` gets the unwind point of its
position: the innermost unwind scope and the number of its locals that are live. The
locals that an abort to handler `h` unwinds are the live locals of each scope from that
point out to the scope `HandledBody(h)`, innermost first. An abort of the whole task
unwinds the live locals of each scope of the body. The builder computes the points; the
fact generator only reads them (section 4.8).

**Rule CAPTURE.** The environment of a closure is the list of the locals of an outer
body that its body, or a body inside it, names. One function `capture_mode` chooses the
mode of each field:

1. `Move` if the body moves the captured local or a place below it (an operand
   `Move`, an `Unpack`, or an inner closure with a `Move` field for it). An inner
   closure that moves a capture makes each closure around it move it (ADR 0003).
2. Else `Kept` if the type is plain data and no statement of the body, or of a body
   inside it, borrows a place at or below the field (`Rvalue::Ref`, `BindMode::Ref`, a
   by-reference receiver or argument).
3. Else `Ref`.

A clause gets `Ref` or `Kept` only: the machine captures cells for a clause and moves a
value out of the cell when the clause runs (`semantics.md`, section 3.1). The
interpreter gets the same choice (section 6).

**Rule NAMES.** The builder resolves names with the rules of today (ADR 0005): a local,
then `print` and `fork`, then an item (the prelude last), then a variant, then an
operation. It resolves a method by the final type of the receiver. It reports the
W01xx diagnostics, W0120, W0303, W0315 and W0504 once.

### 3.1 Function body, parameters and the exit (map 2.1)

```text
body#B fn f(p1: &World, p2: Vec<u64>) -> &u64 {
  _0: &u64 ret
  <statements of the body>
  _0 = <tail>                      // FRAME 1
  dead <locals of the body>        // FRAME 3
  dead <temporaries of the tail>   // FRAME 4
  dead p2; dead p1                 // FRAME 5: the parameters
  return
}
```

- The parameters are locals of kind `Param`. They are live and have a value at the
  entry.
- `return e` lowers by rule JUMP.
- **Removes:** `finish_return`, the special exit rule of tail temporaries
  (`stmt.rs:110`), and the local forms of W0204 in `check_returned_refs` (a returned
  reference into a local, a by-value parameter or a temporary). The `Return` template
  uses `_0` after the ends (section 4.5), so these forms become `error(_0, exit)`.
  `diagnose.rs` reports an error of a return slot as W0204, so the code stays. The
  forms move from sema into the spec (they were the "S5b F8 partial" open item).
- **Stays:** the stated-place check of returned references (`ref_at`, `ref_in` on an
  edge-less node), the substitution of `in` places in the order of their roots
  (`in_place_order`), the `Param` roots and the held roots `*rs`.

### 3.2 `let` and patterns (map 2.2)

| Source | Core |
| --- | --- |
| `let x = e` | the statements of `e`, then `live x` directly before the statement that gives `x` its value (`x = rvalue`, or `x = call ...`) |
| `let x: T` | `live x` with `unset` set (the template emits `unset_at`, section 4.5) |
| `let _ = e` | `live t; t = e; dead t` (DISCARD) |
| `let (a, _) = e` | `live t; t = e; live a; live w; unpack t => (.0: a, .1: w); dead w` and `dead t` at the end of the statement |
| `let S(a, b) = s` | `live a; live b; unpack s => (.0: a, .1: b) consume` |
| `let x = y` (a place) | `live x; x = move y` or `x = copy y` |

- `Unpack` moves the whole source (ADR 0003: a destructuring consumes the value). A
  part `_` goes into a temporary of kind `Part` that ends at once, so a linear part
  that a pattern drops is `unconsumed` (W0601).
- **Removes:** `consume` in `let`, `wild_drops`, `wild_drops_into`,
  `pattern_holds_linear`, `drop_linear` for `_`, the special case of a fresh task
  handle under `_` (O3-4: section 3.28), and the "let" node that `rebound_at` needed
  for `no_gen_kill` (the call template has a separate bind node, section 4.6).
- O3-2 goes by FRAME: the handled body moves its value into `x` before the ends of
  its temporaries, so the free reaches `x` (section 3.35).

### 3.3 Expression statements and place statements (map 2.3)

- `e;` with `e` a place of a local (`v`, `p.tx`, `v[i]`): the statements of the index
  operands, then `Mention(p)`.
- Any other `e;`: DISCARD. A block statement `{ ...; v }` moves `v` into a temporary
  of kind `Discard` (V118, OR6). A `scope` statement with a tail place moves it the
  same way (O3-1). A spawn in statement position lowers to `Give` (section 3.28,
  O3-4).
- **Removes:** `drop_value`, `discard_block_value`, `local_place`, and their early
  returns for a value with a variable or with tasks (the cause of O3-1 and O3-4).

### 3.4 Assignment to a local (map 2.4)

`x = v` lowers to the statements of `v` with destination `x` (`init: false`). The value
runs first (ORDER-1, exception 2). The template writes the cell of `x` (W0405) and
rebinds `x` (section 4.5).

- **Removes:** `assign_name`, and the order hazard of `drop_replaced_uses`.
- **Stays:** a local of a function type joins the old and the new function value
  (ADR 0005); the places of `x` only grow (`points_into` is flow-insensitive).

### 3.5 Assignment to a place (map 2.5)

`p.f[i] = v` lowers to: the statements of `v` into a temporary `tv` (or a direct
operand by ORDER-2), then the index operands of the target, then
`(place) = move tv` with explicit `Deref` steps in `place`.

| Target | Place |
| --- | --- |
| `p.f = v`, `p` owned | `p.f` |
| `r.f = v`, `r: &S` | `(*r).f` |
| `b.f = v`, `b: Box<S>` | `(*b).f` (a `Box` deref) |
| `h.f = v`, `h: Rc<S>` | `(*h).f` (an `Rc` deref) |
| `t.0.hp = v`, `t: (&E, &E)` | `(*t.0).hp` |

- The template has three cases by the shape of the place: a whole local, a part of a
  local (no `Deref`), and a place through a `Deref` (section 4.5). Each case is one
  rule for each surface form.
- **Removes:** `assigned_places`, `drop_replaced_uses`, the pending queue of the target
  uses, the separate rule for a write through a tuple part (V098) and through a field
  that holds a reference (V014).
- **Stays:** part holders (`part_holder`, `retire_holders`, `retire_stale`, a
  precision mechanism for `points_into`), `writes_via`, the self-reference check of
  W0605 (`check_self_ref`), the store records for W0204 (`note_stored_behind`) and for
  stored function values (`escape`).

### 3.6 Compound assignment (map 2.6)

`x op= v` lowers to `tv = v; x = Op(copy x, copy tv): T` for a local `x` that is not a
reference. For a place, or a reference local `c`, the machine follows references
(`CompoundStore`): `(*c) = Op(copy *c, copy tv): T`.

- **Removes:** the rebind of RT9 (`c += 1` on a reference local is now a write through
  `*c`), and the special path of `assign_name` for compound operators.

### 3.7 Names, fields, indexes and slices (map 2.7)

The builder makes each implicit dereference of the machine an explicit `Deref` step
(`semantics.md`, section 2.4):

| Point | `Deref` steps that the builder inserts |
| --- | --- |
| `Field`, `Index`, `&x[]`, a `for` source, a pattern test | references, `Box` and `Rc`, as many as the type needs |
| a method receiver | references, `Box` and `Rc`, until the type has the method |
| a compound assignment | references only |
| an operand of an operator, a condition | references only |
| an argument of a non-reference parameter that is a reference to a copy value | one reference (`coerce_args`, `exec.rs:975`) |

- An index `v[i]` is `v[t_i]` with `t_i` an integer local. The template reads the
  pointer word of the place before the `Index` step (section 4.3).
- **Removes:** `place_expr`, `field_of`, `deref_lval`, `place_value`,
  `field_referents`, `held_refs` as a per-form rule, and `LVal::through_ref`. One
  resolver (section 4.3) replaces them.

### 3.8 Borrows (map 2.8)

- `&p` is `Rvalue::Ref { place: p, all: false }`; `&p[]` is `all: true`.
- `&e` for a value `e`: `live tv; tv = e; t = &tv`, with `tv` of kind `Borrowed`. The
  end of the statement ends `tv` (TEMP), so a reference into it is invalid after the
  statement (S007, V007).
- **Removes:** `borrow`, the temporary root of `temp_root`, and `temp_refs`.

### 3.9 Temporaries (map 2.9)

Rule TEMP gives each temporary its end. The table of the map (section 2.9) becomes
the table of rule TEMP. The rows that sema had wrong (O3-2 for the handled body and
the scope body, O3-3 for a clause and a `resume` argument) follow from FRAME with no
special case.

- **Removes:** `temp_root`, `open_stmt`, `close_stmt`, `stmt_temps`,
  `Summary::dropped`, and the statement record of the handled body (R2c).

### 3.10 Blocks and tails (map 2.10)

A block with a value lowers to its statements, then FRAME steps 1, 3 and 4 with a
destination: the binder of a `let`, a temporary of kind `Value`, or the destination of
an outer frame. A block with no value has `d = const ()` or nothing.

- A tail that names a local of the block moves it into `d` (S059). A value that points
  into a local of the block is in `d` when the local ends, so a later use of `d` is
  W0301 (RT1, F1).
- **Removes:** `block_with`, `hold_out`, `use_held`, `hand_out`, `end_frame`,
  `block_inner`, `push_frame` and `pop_frame` as rules (the walk still keeps a stack
  of unwind scopes).

### 3.11 `if`, `&&`, `||` (map 2.11)

```text
live tc; tc = <cond>
live d
if copy tc { <then>; d = move ta } else { <else>; d = move tb }
```

- `a && b` lowers to `live d; ta = a; if copy ta { tb = b; d = copy tb } else { d =
  const false }`, and `||` to the mirror form.
- An `if` with no `else` in statement position has no destination; its tail is
  DISCARD.
- **Removes:** the move of the branch value (`consume`, S059, V058), the drop of a
  missing `else` (`discard_block_value`), and the separate short-circuit nodes.
- **Stays:** `branch_state`, `set_branch` and `joined` (the join of `@ uniq`, task sets
  and part holders) and `retire_stale`. They are lowering state of the domain
  (class STATE).

### 3.12 `match` and patterns (map 2.12)

```text
live ts; ts = <scrutinee>            // only if the scrutinee is not a place
live d
match p {
  Some(x) [bind x <- move (p as Some).0] => { <body>; d = move ta; dead x }
  None                                   => { <body>; d = move tb }
}
```

- The builder splits each pattern into a test (`PatTest`) and bindings (`Bind`). A
  by-value binding of a part that is not plain data moves the scrutinee as a whole
  (`BindMode::Move`, ADR 0003). A scrutinee behind a reference binds by reference
  (`BindMode::Ref`): `x = &(*p as Some).0`.
- A binding through a reference to a payload that is itself a reference is
  `x = &(*p as Some).0` with type `&&T`, and a later `x.hp` is `(**x).hp`. The
  resolver follows the second `Deref` to where the stored reference points (R3RT2).
- A part `_` of an arm that takes the value by value is a binding into a temporary of
  kind `Part` that ends at once (ADR 0007).
- W0120 (exhaustiveness) moves to the builder with `exhaust.rs`.
- **Removes:** `match_pattern`, `match_drops`, `match_deps`, the `sval` rule of RT3, and
  the move of the arm value.

### 3.13 Loops (map 2.13)

```text
// while c { b }
loop L1 {
  live tc; tc = <c>; dead <temporaries of c>
  if copy tc { } else { dead tc; break L1 }
  dead tc
  <b>; dead <temporaries of the tail of b>     // D15
}

// for x in v[] { b }
live src; src = &v                 // or a temporary for a value
live it; it = Elems(*src)          // each step reads the length
loop L2 {
  iter_next it -> x else L2        // x starts here; at the end, control leaves L2
  <b>
  dead x
}
dead it; dead src
```

- `break` and `continue` lower by rule JUMP.
- **Removes:** `loop_body`, `end_frames_above`, `leave_in_flight`, the "end of
  statement" rule of the condition, and the iterator rules of `elem_iter` and
  `for_loop` (the iterator is a local with a type; its `@ uniq` mode comes from its
  operand by the assignment template: RT18).
- **Stays:** `lower_loop` and its widening (D13). `LoopHead` loses the fields of the
  removed mechanisms: `pend_uses`, `pend_reads`, `stmt_temps`, `tentative`,
  `late_vars`, and the frame and in-flight stacks.

### 3.14 `return` (map 2.14)

Rule JUMP, then `Return`. W0315 (a `return` inside a handled body, a clause or a scope
body) is a builder error. **Removes:** `closure_return`, `closure_ret_refs` (a closure
that returns a reference into its own local is `error(_0, exit)` by the `Return`
template).

### 3.15 Operators and literals (map 2.15)

- `a op b`: the operands by ORDER-2, then `t = Bin { op, lhs, rhs, ty }`. `ty` is the
  integer type of the result: the interpreter export `int_ops` comes from it.
- A comparison of two values that are not plain data is `Rvalue::Compare` of two
  places: it reads both and moves neither.
- `-128` is one constant (W0102 range, from the builder).
- `"{a} and {b}"`: each part is converted where it is evaluated
  (`t1 = Str([Value(a)])`), then `Str([...])`.
- **Removes:** `binary`, `hold_later` for operands, `arith`, `check_int_lits` (moves to
  the builder), `finish_int_ops`.

### 3.16 Aggregates (map 2.16)

`(a, b)`, `[a, b]`, `S { f: a, g: b }`, `S(a, b)` and `Some(a)` lower to the operands
in the order of ORDER-1, then one `Rvalue::Aggregate` with the fields in the order of
the type. A place field of a `!Move` struct with no value is `FieldValue::Unset`.

- **Removes:** the five copies of the "consume, hold, take" loop (`elements`,
  `struct_lit`, `positional_struct`, `variant_ctor`, `hold_part`, `take_held_here`)
  and the "value" node.
- **Stays:** the type variable of a tuple part that can hold a function value (RR2) is
  now a `ClosureSet` in the type; `keep_modes` (W0502 in sema) stays a builder check at
  the unification.

### 3.17 Calls of function items (map 2.17)

```text
live t1; t1 = <arg 1>          // in the order of the parameters, by ORDER-2
live t2; t2 = &<place>         // a reference argument
live d
d = call f<targs>(move t1, move t2, copy x) unwind(S:n)
dead t2; dead t1               // at the end of the statement
```

- Phase 1 (`item_arg_slots`) and phase 2 (`eval_item_args`) of today go to the
  builder: the order of the arguments and their evaluation are statements before the
  call.
- An argument that the callee builds in place has `CallArg::in_place` (ADR 0007).
- A generic callee in `holds` is a fact-generator rule at the call (section 4.6). It
  needs no node of its own in the Core.
- **Removes:** `eval_item_args`, `item_arg_slots`, `order_args`, `item_call_types`,
  `unify_arg`, `hold_operand`, `move_temp`, and the eight-phase structure as separate
  code paths (phases 3 to 8 become the template of `Callee::Item`).

### 3.18 Method calls (map 2.18)

The builder resolves the method from the final type of the receiver. A by-reference
`self` gets `&place` (with the `Deref` steps of section 3.7), formed by ORDER-2. A
by-value `self` gets `move place` at the call. Built-in methods map to callees:
`s.spawn(f)` is `Callee::Spawn(s)`, `t.join()` is `Callee::Join`, `t.detach()` is
`Callee::Detach`, an effect path `E.op(...)` is `Callee::Op`, `sim.run(...)` is
`Callee::Item` of the prelude function with its flag.

- **Removes:** `method_call`, `method_on_path`, `no_method`, `no_self`,
  `check_visible` (they move to the builder), and the separate argument code of
  `join` and `detach` (V136).
- **Stays:** `note_via_call` and `finish_via_calls` (`writes_via` for a method call
  through a one-reference local).

### 3.19 Generic calls and type parameters (map 2.19)

- The Core keeps generic bodies. A value of a type parameter has
  `props.maybe_linear` and `copy: false`, so each read of it is a `Move`.
- **Removes:** `tentative`, `settle_moves` (S4 "Ty::Var move"), the flag pass of
  `finish` (V060), `hold_generic` and `release_generic` as separate nodes (the call
  template keeps the holder rule, section 4.6).
- **Stays:** `dropped_params` and `held_params` (the `drops` and `holds` parts), now
  over facts in which each value of `T` is a typed local (V057), and
  `check_item_value` for a generic item used as a value.

### 3.20 Calls of function values (map 2.20)

`v(a, b)` lowers to `live ta; ta = a; live tb; tb = b; d = call (v)(move ta, move tb)`
with `Callee::Value(v)`. The machine reads the callee value before the arguments
(ORDER-1). So, by ORDER-2, if an argument is not inert, the builder first writes
`tf = copy v` and the call is `call (tf)(...)`: a new value of `v` in an argument does
not change the callee. A function item in a local is the same form.

- **Removes:** `call_value`, `eval_value_args`, the separate result rules
  `value_call_result` and `value_call_refs` (one result rule, section 4.6).

### 3.21 Closures (map 2.21)

```text
// let f = |r: &E| { keep = r; print(x.hp); take(y) }      (x: &E, y: Lk)
live f
f = closure#4 { ref keep, kept x, move y }     // body#7
...
body#7 closure(r: &E) -> () {
  up.keep = copy r                // writes the cell of the outer `keep`
  live t1; t1 = copy (*up.x).hp
  print(copy t1); dead t1
  call take(move up.y) unwind(S0:0)
  _0 = const ()
  dead r
  return
}
```

- The closure body is a Core body of kind `Closure`. Its parameters are locals of kind
  `Param`. Its captured locals are environment fields, named `up.x` in places.
- The literal is one `Rvalue::Closure`. A `Move` field moves the local at the literal
  (OR2: the machine and the facts agree, because the interpreter takes the same
  choice). The modes of the closure come from the type properties of its
  environment fields (RT8, OL-5). The closure is linear if a `Move` field is linear. It
  is `once` if the body moves out of a field or calls a `once` value. It is nonportable
  if a field is nonportable.
- **Removes:** `closure`, `closure_value`, `bind_closure_params` as a special path,
  `captures_live_at` as a separate rule (section 4.7), `note_capture`, `move_var` for
  captures, `closure_call_refs`, the export `FnFacts::by_value`, and all of
  `late.rs` except the task parts.
- **Stays:** the separate CFG component of the closure body, and its lowering at the
  literal in the walk.

### 3.22 Function items as values (map 2.22)

`f` as a value is `Rvalue::FnItem { f, targs }`. Its type has the item in the
`ClosureSet` field (an item is one member of the set). `sim.run` as a value keeps its
`sim_run_at` fact by the template of `FnItem` (RT17).

### 3.23 Stored function values (map 2.23)

The Core has no special form. A function value that an `Assign` puts into a place that
is not a whole local, or that a call argument gives to a parameter that stores it, is
a stored value. The fact generator keeps the store records (`escape`, `reach`) and runs
the stored values in the `settle` worklist (section 4.11).

### 3.24 `handle` and clauses (map 2.24)

```text
live d
handle#2 Ask -> d [scope S5] rerun=false clauses [ask: body#9] {
  <statements of the handled body>
  d = move t_tail                 // FRAME 1
  dead <locals>; dead <temps>     // FRAME 3, 4
}

body#9 clause Ask.ask() -> u64 [handle#2, cont k] {
  // env: the cells of the outer locals that the clause names (Ref or Kept)
  live t; t = const 1
  _0 = call resume[k](move t) unwind(S0:1)   // the value of the clause
  dead t
  return
}
```

- The handled body is inline in the parent body, with its own unwind scope of kind
  `HandledBody(h)`. Each clause is a Core body of kind `Clause`. Its parameters are the
  operation arguments; its `cont` local is the continuation (type `Cont`, `once` or
  `multi`).
- The value of the `handle` is `d`. The handled body writes it (FRAME). A clause that
  ends with no `resume`, or that returns after `resume`, gives its `_0`. The fact
  template of `Handle` joins the two at the end node (section 4.8).
- A continuation value points into the root of the hidden `frame` local of its clause
  (kind `ClauseFrame`, D17). The clause epilogue ends that local, and nothing moves it.
  A closure captures the continuation as `Kept` (a continuation is plain data, and a
  closure does not borrow it), so the closure points where the continuation points:
  into the frame root, not into the `cont` local. So the move of a `once` continuation
  at `resume` does not invalidate the closure, but the end of the clause does. A
  closure that holds the continuation and leaves the clause, also through the `resume`
  value into the handled body, is then a use of an invalid reference (RR3, V120).
  `diagnose.rs` reports an error of this kind as W0313, so the code stays.
- **Removes:** `lower_clause` as a special path, `bind_clause_params`,
  `bind_clause_cont`, `end_clause_locals`, `join_clause_vals`, `body_frees`,
  `inner_frees`, `clause_refs_onto_args`, the statement record of the handled body.
- **Stays:** the order "handled body, then clauses", `HandlerInfo`, the footprint,
  `clause_multi`, `body_multi`, `reaches_without` (can a clause end with no `resume`)
  and the W0313 marks of handler capabilities (`caps.rs`).

### 3.25 A `multi` handled body (map 2.25)

The builder sets `Handle::rerun` with the rule of today (`resumes_at_most_once`, a count
of `resume` in the syntax). The fact generator lowers the handled body as a loop when
`rerun` is true (`handled_again`, D13). Because the tail move is a statement of the
body (FRAME 1), each pass moves the tail place again (O3-14).

### 3.26 Perform (map 2.26)

`op(a)` and `E.op(a)` lower to the arguments in the order of the parameters, then
`d = call op[cap](...)` with `Callee::Op { cap, effect, op }`. The builder finds `cap` by
the lexical rule: the innermost `handle` of the effect around the expression in this
function (also around the closure or the clause that has the expression), else
`CapRef::Caller`.

- **Removes:** `perform_op`, `eval_op_args`, `op_slots`, `op_arg_places` as a separate
  argument path (F3, V035, R3RT7: the `in` places of an operation are the `in` places of
  a call).

### 3.27 `resume` (map 2.27)

`resume(e)` lowers to `t = e; d = call resume[k](move t)` with `Callee::Resume(k)`, `k`
the `cont` local of the clause or an environment field of a closure inside the clause.
The argument goes through the operand rules, so a `resume` argument that points into a
temporary of the clause is in `t` when the temporary ends (O3-3).

### 3.28 `scope`, `spawn`, `join`, `detach`, `fork` (map 2.28)

```text
live s; live d
scope s -> d [scope S7] {
  live tf; tf = closure#5 { ... }
  live h; h = call spawn[s](move tf) unwind(S7:2)
  live r1                                  // kind TaskResult, in the scope of the body
  give h to s -> r1                        // a spawn in statement position
  dead h; dead tf
  ...
  d = move t_tail                          // FRAME 1
  scope_end s given [r1] unwind(S7:k)      // waits; can abort while d is live
  dead r1                                  // the result goes away: W0601 if linear
  dead <locals>; dead <temps>
}
dead s
```

- A scope capability is a value that points into the root of its binder (D17). Each
  copy of `s` (in a tuple, an `Option`, a closure) points there, and `dead s` frees it
  (RR4, V134).
- `t.join()` is `r = call join(move t)`; `t.detach()` is `call detach(move t)`;
  `fork(f, g)` is `r = call fork(move tf, move tg)`.
- **Removes:** the early return of `drop_value` for a task handle (O3-4), the special
  "scope end" node and its separate `may_abort` (F3-7), the separate argument code of
  `join` and `detach` (V136).
- **Stays:** `start_task`, `task_captures`, the task sets of locals, `finish_task_ends`,
  `finish_task_marks`, `arg_tasks` (now items of the `settle` worklist where they run
  after the walk).

### 3.29 `sim.run` (map 2.29)

`sim.run(seed: 1) { body }` is a call of the prelude item with a closure argument. The
template of `Callee::Item` keeps `sim_run_at`, the root handlers and `root_caps` for
this item.

### 3.30 `with_timeout` (map 2.30)

A call of the prelude item. The rules "runs its argument once" (`item_runs_once`) and
"does not run it twice" (`item_repeats`) stay in the call template.

### 3.31 `on abort` (map 2.31)

The Core does not call `on abort`. The unwind points name the values that an abort
unwinds; `LocalProps::has_on_abort` gives the flag. W0118 stays a program-level check
(D18). Section 9.3 describes the later step that makes the call explicit.

### 3.32 `Rc`, `Box`, `Weak` (map 2.32)

A place through a handle has a `Deref(Rc)` step; through a box a `Deref(Box)` step. The
resolver gives the group root, the handle dependency and the read of the pointer word
(section 4.3). So a task that reads through `h` reads the pointer word of `h`, and a move
of `h` in the parent conflicts with it (O3-6).

### 3.33 `print` and `assert` (map 2.33)

- `print(a, b)` is `StmtKind::Print` with operands by ORDER-2: the machine reads each
  argument at `Print`, so an argument place before a later argument that runs code
  gets an early borrow (`semantics.md` N2, p9).
- `assert e` is `tc = e; assert copy tc unwind(S:n)`. The template marks the node
  `may_abort` (`semantics.md` N4, p25). A callee that can fail an `assert` gets a new
  signature bit `unwinds` (section 4.12), so its callers mark the call `may_abort`
  (p27).

### 3.34 Effects at calls (map 2.34)

The builder resolves the handler of each operation (`CapRef`). The fact generator
decides the effects of a call from its callee kind (section 4.6). Effects need no Core
form beyond `Callee` and `CapRef`.

### 3.35 Worked examples

**O3-2 (a temporary of a handled body).** Source (`r3/oracle/repro/O3-2_*.wf`,
function `callee`):

```weft
let r = handle Note { fn note(x) { resume(()) } } in { first(&mk_v()) }
print(r + 1)
```

Core:

```text
live r
handle#0 Note -> r [scope S2] clauses [note: body#1] {
  live t1; t1 = call mk_v() unwind(S2:1)       // t1: Vec<u64>, kind Borrowed
  live t2; t2 = &t1
  r = call first(move t2) unwind(S2:2)         // the tail call writes the destination
  dead t2
  dead t1                                      // FRAME 4: the tail temporary ends
}
live t3; t3 = Add(copy *r, const 1): u64
print(copy t3)
dead t3
```

Facts: the bind node of `first` gives `points_into(r, t1[])` (the stated place `in v[]`
with `v := t1`). `dead t1` gives `scope_end(t1, n)` and `owner(t1, t1)`, so
`frees_at(n, t1)` and `invalidated_at(r, n)`. The `Add` node uses `r`: W0301. The old
lowering freed `t1` before the "let" node rebound `r`, so the free did not reach `r`.

**`semantics.md` N1 (a late read, probe p2).** Source:

```weft
let r = &v[0]
let x = r.hp + { v.push(E { hp: 2 }); 1 }
```

The machine follows `r` at the left operand and reads `hp` at `+`. The right operand
calls `push`. ORDER-2, third case:

```text
live t1; t1 = &(*r).hp                          // EarlyBorrow at the formation point
live t2
  live t3; t3 = E { hp: const 2 }
  live t4; t4 = &v
  call Vec.push(move t4, move t3) unwind(S3:4)
  dead t4; dead t3
  t2 = const 1
live x; x = Add(copy *t1, copy t2): u64          // the late read through t1
dead t2; dead t1
```

`t1` points into `v[].hp`. `push` mutates `v` (`mut(self)`), an unstable strict prefix,
so `t1` is invalid at the `Add` node: W0301. The checker of today accepts the program
and the oracle faults.

**RR7 (a captured variable gets a new value after the closure is made).**

```weft
let r = &a[0]
let f = || print(r.hp)
r = &b[0]
b.clear()
f()
```

`f = closure#1 { kept r }`. In body#1, `(*up.r).hp` resolves `up.r` to the variable `r`
and the `Deref` to the root `ArgUp(1, 0)` (section 4.7). The projection of body#1 has
`uses(r, ·)` and `reads_at(·, ArgUp(1, 0).hp)`. At the node of `f()`, the substitution
maps `ArgUp(1, 0)` to the places of `r` there: `a[]` and `b[]`. So the node uses `r`,
which `b.clear()` invalidated: W0301. No late join is needed.

**O3-4 (a spawn statement drops a linear result).** Section 3.28: `give h to s -> r1`,
then `scope_end` gives `r1` its value, then `dead r1` is `unconsumed(r1)`: W0601.

**`map_lowering.md` N1 (the result of an operation of a handler of a caller).**

```weft
let r = pick(&v)        // Pick.pick(v: &Vec<u64>) -> &u64, a handler of a caller
v.clear()
print(r)
```

`live t1; t1 = &v; live r; r = call pick[Caller](move t1)`. The result rule for code that
the body cannot see (section 4.6, rule OPAQUE) gives `r` the wildcard place of each
reference argument (`v..`) and the root "a place of a caller". `v.clear()` overlaps
`v..`: W0301.

---

## 4. Fact generation over the Core

The fact generator keeps its outputs: one `FnFacts` for each function and test, with
the same relations, and one `EffectSig`. The spec, the checker, the bridge and the
diagnostics read the same facts. Only the producer changes.

### 4.1 The mechanisms

Section 5 and Appendix A name these mechanisms by their tags.

| Tag | Mechanism | Where |
| --- | --- | --- |
| M1 | Each value is a local with explicit `StorageLive` and `StorageDead`; ANF operands | 3.0 ANF, TEMP; 4.5 |
| M2 | The frame epilogue: `dest = move tail`, then the ends | 3.0 FRAME |
| M3 | Explicit moves after type inference; `Unpack`; one assignment template for each value kind | 3.0 COPY-MOVE; 4.4, 4.5 |
| M4 | Discarded values end; `Give` for a spawn in statement position | 3.0 DISCARD; 3.28 |
| M5 | Places with explicit `Deref`; one resolver; the pointer word `@` | 3.7; 4.3 |
| M6 | One `Call` statement and one call rule, with rule OPAQUE | 3.17 to 3.20, 3.26; 4.6 |
| M7 | The closure environment and one capture rule | 3.0 CAPTURE; 3.21 |
| M8 | Inner bodies: projection, substitution, replay | 4.7 |
| M9 | Unwind points on each statement that can abort | 3.0 UNWIND; 4.8 |
| M10 | The late-read rule | 3.0 ORDER-2 |
| M11 | One worklist after the walk; relation-generic rebase | 4.11 |
| M12 | The builder runs after type inference | 1.1; 3.0 |
| M13 | The interpreter compiles the Core | 6 |
| M14 | Continuations point into the root of a hidden frame local of their clause; scope capabilities into the root of their binder | 3.24, 3.28 |

### 4.2 The state of the walk

`Lower` has 105 fields today (`body/mod.rs:1160`) and `LoopHead` has 61. These groups
of fields go away, because the Core holds the information or no rule needs it:

- the pending queue: `pend_uses`, `pend_reads`;
- the statement and frame stacks: `stmt_temps`, `frames` as a rule source, the
  in-flight values, `temp_refs`;
- the type state: `inf`, `late_vars`, `tentative`, `int_lits`, `int_ops`,
  `maybe_linear` as a separate set (it is `LocalProps::maybe_linear`);
- the late joins: `holder_log` as a source for `cap_refs_now`, the late-join records;
- the match state: `match_moves`, `match_deps`;
- the post-pass tables that only carry facts to a later pass: `resume_refs_pending`,
  `op_results` as a special root (it is one item of the worklist), `out_suspends`
  (it comes from the unwind points).

These stay: the CFG cursor (`cur`), the abstract value of each local (places,
function values, tasks, capability marks, `@ uniq`, part holders), the tables of
function values (`closures` becomes the table of `Σ(B)`, `escaped`, `reaches`), the
handler and task tables, the store records for W0204, and the loop stack. The walk
also keeps the stack of unwind scopes of the Core, for the node ranges of handled
bodies and for `outside_vars`.

### 4.3 The place resolver

`resolve(place)` gives the places of a Core place, and the variables and places that a
step through it uses or reads:

```text
resolve(place) -> Resolved {
    places: Vec<PlaceId>,   // the places that the Core place names
    uses:   Vec<VarId>,     // the variables that the steps use
    reads:  Vec<PlaceId>,   // the reads of the steps (pointer words, reference cells, lengths)
    deps:   Vec<PlaceId>,   // the handle places of `Rc` steps (ADR 0003)
}
```

| Step | Places | Uses and reads |
| --- | --- | --- |
| base `Local(x)` | the root of `x` | uses `x`, and each live part holder of `x` below the place |
| base `Upvar(i)`, field `Ref` or `Kept` of outer `x` | the root of `x` (the same root and variable as in the outer body) | uses `x` |
| base `Upvar(i)`, field `Move` | the root of the copy that the closure owns | uses that variable |
| `Field(f)` | the field step (stable) | — |
| `Variant(v)` | the variant step (unstable) | — |
| `Index(t)` | the element step of the type (`elem_step`) | uses `t`; reads the pointer word `p.@` |
| `Elems` | the element step | — |
| `Deref(Ref)` | if `p` is the root of a local `x`: the places of `x` (in an inner body for an upvar: the root `ArgUp(B, i)`, section 4.7); if `p` is a part of a local: the places that the references there point to (the part holders, else the places of the local, as `held_refs` today); if `p` is below a `Param`, `Arg` or `Group` root: the held root `*rs..` of ADR 0003 | uses the variable that holds the reference; reads `p` |
| `Deref(Box)` | the unstable deref step `p.*` | reads `p.@` |
| `Deref(Rc)` | the group root of the inner type | reads `p.@`; deps `p.*` (the handle place) |

The **pointer word** `p.@` is a new stable step with a reserved field id in
`weft-facts` (as `WILD` is a reserved id). It names the pointer of a `Box`, a `Vec` or
an `Rc` handle, and the length of a `Vec`. It is disjoint from each other child of `p`,
and a change of `p` as a whole overlaps it. So:

- a read through a `Box` reads the box pointer, and a task that replaces the box
  conflicts with it, but a task that writes inside the box does not (OL-R2d-box, with
  no false positive of the kind that ADR 0006 feared);
- a task that reads through an `Rc` handle reads its pointer word, so a move of the
  handle in the parent conflicts (O3-6);
- an index reads the length (`v.@`), as ADR 0006 asks, and a write of an element does
  not conflict with it.

The verified place algebra needs no change: the step is a `Field` step.

This one function replaces `place_expr`, `field_of`, `deref_lval`, `place_value`,
`field_referents`, `held_refs` at its ten call sites, `handle_deps` at its call sites,
and `LVal`.

### 4.4 Operand and rvalue templates

An operand or an rvalue has no node of its own. Its facts go to the node of the
statement that reads it.

| Element | Facts at the node `n` of the statement | Abstract value |
| --- | --- | --- |
| `Copy(p)` | `R = resolve(p)`; `uses(v, n)` for `R.uses`; `reads_at(n, a)` for `R.places` and `R.reads`; `uses` of the unset field variables at or below `p` | the value at `p`: of the local, of a part holder, or the held places of a part |
| `Move(p)` | as `Copy`; and `moved_at(x, n)` for the base local `x`; if `p` has projections, also `moved_part(m, n)` for each place of `p` (ADR 0003) | the value at `p`; the local loses its task set |
| `Const(c)` | none | empty for a variant with no payload |
| `Use(op)` | the facts of `op` | the value of `op` |
| `Ref { place, all }` | `R = resolve(place)`; `uses` of `R.uses`; `reads_at` of `R.reads` only; `uses` of the unset field variables below | places `R.places` and `R.deps`; with `all`, the element step |
| `Bin`, `Un` | the facts of the operands | a scalar; the integer type goes to the interpreter export |
| `Compare { lhs, rhs }` | `reads_at` and `uses` of both resolved places; no move | `bool` |
| `Aggregate` | the facts of each operand | the join of the operand values: places, function values, task sets, capability marks; empty if each part is empty; `Unset` fields go to the unset table of the destination |
| `Closure { id, body, env }` | `Ref(x)`: `uses(x, n)`; `Kept(x)`: `uses(x, n)`; `Move(x)`: the `Move` template | places: the root of `x` for `Ref`, the cell indirection `PlacesOf(x)` for `Kept` (section 4.11), the held places of the value for `Move`; function values: `{id}` with the environment; the modes and marks of `Σ(body)` |
| `FnItem { f }` | `check_item_value` for a generic item; `sim_run_at` on an edge-less node for `sim.run` | function values: `{f}` |
| `Str` | the facts of the piece locals | a string |
| `Elems(p)` | `reads_at(n, p.@)`; `uses` of `R.uses` | places: the element places of `p`; `@ uniq` of the source (RT18) |
| `Range` | the facts of the operands | a scalar range |
| `TaskResult(h)` | `uses(h, n)` | the result places of the tasks of `h` |

### 4.5 Statement templates

Each Core statement gives the nodes and the facts of this table. The table is the whole
fact generation for a body with no call, no closure, no handler and no task.

| Statement | Nodes | Facts |
| --- | --- | --- |
| `StorageLive(x)` | one node if `x.unset`, else none | `unset_at(x, n)` if `x.unset` (W0304); `owner(root(x), x)` once for each local |
| `StorageDead(x)` | one node | `scope_end(x, n)` |
| `Assign` to a whole local `x` | one node | the rvalue facts; `rebound_at(x, n)`; `points_into(x, P)` for the places of the value (with the one-place rules of `point_local`); `empty_at(x, n)` for an empty value; if not `init`: `mutates_at(n, root(x))` (the write of the variable, W0405) |
| `Assign` to a part of a local `x` (no `Deref`) | one node | the rvalue facts; `mutates_at(n, m)` for the resolved places; `overwrites(x, n)` if `x` can hold a linear value; the part holder of the part: `rebound_at(h, n)`, `points_into(h, P)`; `rebound_at` of the unset field variables below; a store record if the value holds a function value |
| `Assign` through a `Deref` | one node | the rvalue facts; `mutates_at(n, m)` for the resolved places; `writes_via(n, r)` if `r` is a one-reference local and each place is at or below its place; a drop pair if the old value can be linear (W0601: a borrowed place always has a value); a store record for W0204 if the value holds references and the place is below a `Param` or `Group` root; a store record for a function value |
| `Unpack { src, parts }` | one node | the `Move` template of `src`; for each part local `a`: `rebound_at(a, n)`, `points_into(a, P)` with the places that the part holds, `empty_at` for an empty part |
| `Mention(p)` | one node | `uses` of `resolve(p).uses` only |
| `Call` | section 4.6 | section 4.6 |
| `Print { args }` | one node | the operand facts; the `uses` of the unset field variables of each whole value |
| `Assert { cond }` | one node | the operand facts; `may_abort(n)` |
| `If` | a branch node, the two blocks, a join node | the operand facts at the branch node; the branch state of the domain (`branch_state`, `joined`) |
| `Match` | a match node, an arm node for each arm, an end node | `reads_at` of the scrutinee places at the match node; at each arm node the bindings: `Move` is the `Move` template of the scrutinee (once for the arm), `Copy` and `Ref` the `Copy` and `Ref` templates; `rebound_at` and `points_into` of each binding |
| `Loop` | a head node, the body, a back edge, an exit node | none of its own; `lower_loop` (section 4.10) |
| `IterNext { iter, dest }` | one node with an edge to the exit | `uses(iter, n)`; `reads_at(n, src.@)`; `rebound_at(dest, n)`; `points_into(dest, P)` for the element places |
| `Break`, `Continue` | one node with an edge to the exit or the head | none (the ends are statements before it) |
| `Return` | the exit node | `uses(ret, n)`; the stated-place check of the function (`ref_at`, `ref_in` on an edge-less node) |
| `Handle` | section 4.8 | section 4.8 |
| `Scope` | a scope node, the body | `rebound_at(binder, n)`; `performs_at` or `escapes_at` of `Async`; `may_abort(n)` |
| `ScopeEnd { binder, given }` | a scope-end node, then a task-end node | `joined_at(t, n)` for each task of the scope; `may_abort(n)`; for each given result `r`: `rebound_at(r, n)` and `points_into(r, P)` with the result places of its task; at the task-end node: `lends_mut` of the writes of the tasks (ADR 0006) |
| `Give { handle, scope, result }` | one node | `uses` and `moved_at` of `handle`; the tasks of `handle` go to the given list of the scope |
| `Unreachable` | one node with no successor | none |

Each local owns its root, also a reference local. Today the cell of a reference local
has no owner (ADR 0003, `Local::cell`); in the Core an early borrow of a cell (rule
ORDER-2) must die with the local, so the cell gets an owner. No other reference points
into the cell of a reference local, so this adds no other invalidation.

The `uses(ret, exit)` of `Return` is new. It makes the local forms of W0204 (a
returned reference into a local, a by-value parameter or a temporary of the body)
derivations of the spec: the frame epilogue frees the root before the exit node uses
the return slot (section 4.13).

### 4.6 The call rule

A `Call` statement gives a call node `N` and, if the call has a destination, a bind node
`B` after it. Some callees add nodes around `N`. A generic callee in `holds` adds a
"held by the callee" node before `N`. A callee that can run a function argument or a
stored value twice adds a "call again" node between `N` and `B`. A callee that runs a
function argument as a task adds the "task of the callee" chain there too.
The template always emits the "call again" node for a call that can run stored values,
so the worklist never needs to insert a node between two nodes.

At `N`, in this order:

1. The operand facts of the callee place (for `Value`, `Resume`, `Spawn`) and of each
   argument (section 4.4).
2. The call arguments: for each argument `i` with a reference type, `reads_at(N, a)`
   and `call_arg(N, a, root_of(i))` for each place that the operand reaches through the
   `Deref` steps of its type. So a reference argument whose pointee holds references
   gives the places of these references too (R3RT3). For a by-value argument that holds
   references, `call_arg(N, a, fn_arg(i))` or `STORED` for its held places (the root
   kinds of `body/roots.rs` stay).
3. The facts of the callee kind (table below).
4. `may_abort(N)` and `multi_at(N)` from the callee kind.
5. The abort edges to local handlers: items of the worklist (section 4.8).

At `B`: `rebound_at(dest, B)`, `points_into(dest, P)` for the result places, `empty_at`
for an empty result, and the abstract value of the result (function values, tasks,
marks). The binding at a separate node keeps `no_gen_kill` (A5) for each call.

| Callee | Mutations and lends | Effects | `may_abort` | `multi_at` | Result |
| --- | --- | --- | --- | --- | --- |
| `Item f` | `mutates_at` and `call_mut` of the `mut` places of the signature, substituted with the argument places; function arguments run with the `lent` places (`apply_value`); a callee task run (`task_runs`) adds the "task of the callee" chain | for each named effect: `performs_at` through a local handler, else `escapes_at`; `raises` | a named effect, or the bit `unwinds` (section 4.12) | the `multi` part | the stated places; the flow places of an unstated reference (`flow_refs`, one-place instances); the `ret` part for a function value; the handle places of the arguments for a group place; rule OPAQUE for an extern function with no stated place |
| `Value`, a closure | the projection `Σ(B)` with the substitution (section 4.7); `moved_at` of the callee local if a member of the closure set is `once` (W0502) | from `Σ(B)` | from `Σ(B)` | from `Σ(B)` | `σ(ret of B)` |
| `Value`, an item | as `Item f` | as `Item f` | as `Item f` | as `Item f` | as `Item f` |
| `Value`, a function parameter | `lends_mut` and `call_mut` of the given places; a `caller_runs` record | the row of the parameter type, or pass-through | yes | `may_be_multi` | rule OPAQUE |
| `Value`, unknown | `lends_mut` of the given places; stored values can run here (`reach`) | the row of the type | yes | the row | rule OPAQUE |
| `Op`, `CapRef::Local(h)` | `give_op` of the reference arguments (the clause parameters point there); the clauses run here (worklist) | `performs_at(N, h)` | `abortive_local` | `clause_multi(h)` | the operation-result root of `h`, rebased by the worklist |
| `Op`, `CapRef::Caller` | `lends_mut` and `call_mut` of the reference arguments; function arguments run in the worst way (`worst_runs`) | `escapes_at(N, E)` | yes | the effect has a `multi` operation | rule OPAQUE |
| `Resume(k)` | the projection `Π(h)` of the handled body (section 4.8) | `resumes_at(N, h)` | `abortive_local` | `body_multi`, `clause_multi` | the value of the handled body |
| `Spawn(s)` | the task footprint: `Σ` of the task closure with the task sink (section 4.9) | `Async` | yes | — | a task handle with task set `{t}` |
| `Join` | `joined_at(t, N)` for each task that no other local can hold; a task-end node with the writes of the task | `Async` | yes | — | the result places of the task |
| `Detach` | the signature of `Task.detach` (its `drops` part) | — | — | — | `()` |
| `Fork` | one fork task for each branch; a fork-join node with `joined_at` | `Par` | yes | — | the tuple of the branch results |

**Rule OPAQUE.** Some calls run code that the body cannot see: a call of a function
parameter, of an unknown function value, of an operation of a handler of a caller, and
of an extern function with no stated place. The result of such a call points into two
kinds of places. The first kind is the wildcard place of each place that an argument
reaches: each reference argument, and each by-value argument with references. (A
one-place instance replaces the wildcard place under the rules of ADR 0003.) The second
kind is the root "a place of a caller" (`env_ref`). The node lends that root
(`finish_op_env`). One function computes this for the four callee kinds. Today `op_result_refs` and `value_call_refs` compute it twice,
and each one misses a part: the operation arguments (map N1) and the root of the caller
(map N2). V011 and V078 had the same cause.

### 4.7 Inner bodies: projection, substitution, replay

A closure body and a clause body are **inner bodies**. The fact generator lowers each
one into a CFG component of its own, as today: a closure body at its literal in the
walk, a clause after the handled body of its `handle`.

**Resolution inside an inner body `B`.** An environment field `i` of kind `Ref` or `Kept`
for the outer local `x` resolves to the variable and the root of `x` (the variable
tables are shared by all components). A `Deref` through such a field resolves to a root
`ArgUp(B, i)` of kind `Arg`: "the places that `x` points into where `B` runs". The
places of `ArgUp(B, i)` are in `points_into(x, ·)` too; no node of another component
changes that root, so this adds no invalidation outside `B`. A field of kind `Move`
resolves to a variable and a root that the closure owns. A reference parameter
resolves to an `Arg` root, as today.

**The summary `Σ(B)`** has three parts:

- **Projected facts.** Each fact of the component of `B` whose subjects are visible
  outside `B`, with its node replaced by a hole. Visible: a place under a `Param`,
  `Group` or `env_ref` root, under an `Arg` root of `B`, or under the root of an outer
  local; a variable of an outer local; the capability of a handler outside `B`; a task
  that starts in a scope outside `B`. Not visible: the locals and temporaries of `B`,
  its continuation, the handlers inside `B` (so a closure with its own `multi` handler
  is not a `multi` node where it runs: O3-8).
- **Replays.** Each call of `B` whose meaning depends on where `B` runs: a callee
  `Value(up.i)` or `Value(param)`, an operation through a handler outside `B`, a
  `resume` of a continuation outside `B`, a spawn into a scope outside `B`, and a call
  that can run stored values. A replay keeps its callee and its argument places, in
  the places of `B`.
- **The result.** `points_into` of the return slot of `B`, restricted to visible places.

**Gen and kill.** A relation that only adds to a derived relation of the spec (for
example `mutates_at`, `reads_at`, `lends_mut`, `releases_at`, `uses`, `call_arg`,
`call_mut`, `escapes_at`, `performs_at`, `may_abort`, `multi_at`, `spawned_at`,
`points_into`) projects as it is. A relation that stops a derived relation
(`rebound_at`, `joined_at`, `writes_via`, `spared_at`, `empty_at`, `unwound_at`)
projects for an outer variable only if each path of `B` from its entry to its exit has
the fact (a must check on the component of `B`). `moved_at` both adds (`moved`) and
stops (`live_linear`). It projects as it is. And `B` gets one more check: a move of a linear
outer variable on some paths of `B`, but not on each path, is W0601 in `B`. Else the
value can stay live where no owner knows it. This rule is stricter than today for a
clause that moves a captured linear local on one branch only.

**The substitution `σ`** at a run node `N`, for one member `c` of the closure set of the
callee (or for a clause):

| Root of `B` | Maps to |
| --- | --- |
| `ArgUp(B, i)`, field `Ref` or `Kept` of `x` | the places of `x` at `N`: the current value in the walk, or the final value in the worklist |
| `Arg` of parameter `j` | the places of argument `j` at `N`, or each place inside each reference argument for a run through a callee (the `lent` part) |
| the owned root of a `Move` field `i` | the place of the closure value at `N`, field `i` of its environment |

**Apply.** At `N`: each projected fact under `σ`; then each replay under `σ`, through the
call template of section 4.6 with `N` as its node; then the result places under `σ`.
The same function applies a summary with one of two sinks: "the node" (a call, a
perform, a stored-value run) or "the task" (a spawn: mutations and lends become
`task_writes`, reads become `task_reads`).

**One table of relations.** The projection, the substitution and the rebase of section
4.11 go through one table `RELS` in `body/inner.rs`: for each relation of `FnFacts`,
the kind of each argument (node, place, variable, capability, task, number) and its
role (gen, kill, both, static). A unit test destructures `FnFacts` field by field, as
`FnFacts::mark` does, so a new relation cannot miss a row. Today each new kind of fact
needed a new field in `Summary` (42 fields) and a mapping at each run site; V024
(`lends_mut`), F4, RR5 and V093 were such misses.

**What this replaces.** `Summary` as a hand-written list, `apply_summary`, the mapping
parts of `run_handler` (`clause_through_params`, `run_clause_caps`), `late.rs` except
the task parts, `closure_call_refs`, `late_ret_refs`, `resume_through_params`,
`onto_param`, `finish_resume_runs` as a separate pass, and `captures_live_at`.

### 4.8 Handlers

The order of today stays:

1. The `handle` node: `handler(h, E)`.
2. The handled body, inline in the parent component. If `Handle::rerun`, the body is
   lowered as a loop (`handled_again`), and the "resume again" node rebinds the locals
   of the scope `HandledBody(h)` (from the unwind scopes, not from a list of the walk).
3. Each clause, lowered as an inner body; its summary `Σ(clause)`; `footprint(h, m)` for
   each visible place that a clause mutates; `clause_multi`, `body_multi`,
   `clause_performs`.
4. The end node of the `handle`, with an edge from the end of the handled body.
5. A "handle value" node: `uses(dest, n)`, then `rebound_at(dest, n)` and
   `points_into(dest, P)` for the places of the body value and of `σ(ret)` of each
   clause (a clause that resumes returns its own value after the body ends). The use
   comes first, so a free in the frame epilogue of the handled body reaches it. The
   value is empty only if the body value and each clause value are empty (V073). On an
   abort path the abort node gives `dest` its value (below), so `dest` has a value on
   each path into this node.

**Clause runs.** Each node of the body that performs through `h` (an `Op` call, or a
replay of an inner body that performs through `h`) applies `Σ(clause of op)` with the
parameters mapped to the arguments. These are items of the worklist, because the
clauses come after the body.

**Resume.** A `Resume(k)` call in a clause of `h` at node `N` applies `Π(h)`: the
projection of the facts of the handled body (its node range from step 2) that the
clause can see. The clause sees the outer locals and the places that a perform gave to
its parameters. Let a perform give the place `P` to parameter `j`. Then a place `q` of
the body below `P` maps to `Arg(j)` with the steps of `q` below `P`. A free of a local of the
body that a parameter points into gives `releases_at(N, Arg(j))`. This is the inverse of
`σ`, through the same table `RELS`, so the frees and the changes of a callee of the
handled body (RR5, V121) and of a closure that resumes go through the same rule.

**Abort edges.** For each node `N` that can run a clause of `h`, where a clause of `h` can
end with no `resume` (`reaches_without` on the clause component), the worklist adds a
node `A` with the edges `N -> A -> end of h`, and:

- `unwound_at(v, A)` for each local that is live at the unwind point of `N`, in each
  unwind scope from the scope of `N` out to `HandledBody(h)`;
- `rebound_at(dest, A)` and `points_into(dest, P)` for `σ(ret)` of each clause of `h`
  that can end with no `resume`: on this path the clause value is the value of the
  `handle`;
- `joined_at(t, A)` for each task of each `ScopeBody` scope on that way (the
  cancellation waits for them), and a task-end node.

Each kind of node that can run a clause has an unwind point in the Core. So each kind
gets the same edge: a perform, a call of a closure, a stored-value run, and a clause in
a clause (V074, V086, V088, V089). An abort edge never skips the end of a scope body,
because the scope is on the way (V084).

**`spared_at`.** For an operation of a local handler `h` at `N`, a variable `v` is spared
if it is declared outside `HandledBody(h)` (from the unwind scopes) and no inner body
that runs at `N` holds it by a `Move` field. The rule of `outside_vars` stays, with its
input from the Core.

### 4.9 Tasks and scopes

- A spawn applies `Σ` of the task closure with the task sink. `captures(t, x)` for each
  `Ref` and `Kept` field, `mut_through(t, x)` for a field that the task writes
  through, `kept(t, root(x))` for each `Kept` field. Rule CAPTURE gives `Kept` only to a
  local that the task never borrows, so the regression V125 (a reference that the task
  makes into a kept variable) has no form.
- A task that runs a stored closure (O3-5, V052) replays the call of the unknown value
  with the task sink, so the stored values that can run there add to the footprint of
  the task.
- `finish_task_values`, `finish_task_ends` and `arg_tasks` become items of the
  worklist. `finish_task_marks` (pins, `opaque`, `spawns_in`) runs after the worklist.

### 4.10 Loops

`lower_loop` stays, with its widening and W0707. A pass lowers the Core body of the
loop again from the head state. The head state is the abstract value of each local that
is live at the head (from the unwind scopes) and the domain tables. The removed fields
of section 4.2 leave `LoopHead`. The rewind of facts stays.

### 4.11 The worklist `settle`

After the walk, one worklist replaces the ordered post-passes 1 to 6, 10 and 11 of the
map (section 1.4). Its items:

| Item | What it does | Today |
| --- | --- | --- |
| `RunClause(N, h)` | applies the clause summary at a node that performs through `h` | `run_handler`, `finish_values` |
| `RunStored(N, value)` | applies a stored value at a node that can reach it | `apply_stored` |
| `RunResume(N, k)` | applies `Π(h)` at a node that runs a closure that resumes | `finish_resume_runs` |
| `AbortEdge(N, h)` | adds the abort node of section 4.8 | `finish_aborts` |
| `TaskValues(t)`, `TaskEnd(t, e)` | the late values of task captures; the lends at task ends | `finish_task_values`, `finish_task_ends` |
| `OpResult(h)` | moves each fact below the operation-result root of `h` onto the places that the `resume`s give, in each relation of `RELS` | `op_refs` |
| `EnvLend(N)` | lends `env_ref` at a node that runs code of a caller | `finish_op_env` |
| `Cells(x)` | expands the cell indirection `PlacesOf(x)` of the closure values with the final places of `x` | the late joins of returned and stored closures |

An item can add facts and new items: a stored value can perform through a local
handler, a clause can run a stored value, an operation result can reach a stored
value. The worklist runs to a fixpoint. Facts only grow, and each item is a pair from a
finite set (nodes and values), so it ends. Then the checks run once, on the final
facts: `check_returns` (stated places), `check_stored_behind` (W0204 for stores),
`finish_spared`, `finish_via_calls` (`writes_via`), `summary_to_sig`, `dropped_params`
and `held_params`, `finish_task_marks`, and `normalize`.

So no pass can read a fact that a later pass changes (V028, V089, V093, OL-1d, V079).
The worklist adds a node only with an edge from an existing node (an abort node, a
task-end node), never between two nodes. It gives the new node the node ranges of its
anchor, so the ranges of inner bodies and handled bodies stay right (map, section 1.4).

### 4.12 Signatures

- `summary_to_sig` stays. It reads the final facts.
- New bit `EffectSig::unwinds`: the body can abort the task with no effect (a failed
  `assert`, or a call of a callee with `unwinds`). It only grows, so it joins the row
  lattice of `infer.rs`. A call of a callee with `unwinds` is `may_abort` (p27).
- `drops` and `holds` keep their analysis (`dropped_params`, `held_params`). Each value
  of a type parameter is now a typed local with an end, so the analysis sees each value
  that goes away (V057, V058).
- The other parts (`lent`, `ret`, `stores`, `reaches`, `tasks`, `task_runs`, `op_fns`,
  `fn_stores`, `ret_refs`, `group_stores`, `fn_store_refs`) stay as they are. Their
  redesign is the class SUM (section 9.3).

### 4.13 Diagnostics

The codes do not change. `diagnose.rs` gets three mappings for facts that the Core
makes in a new way:

| Violation | Code and text |
| --- | --- |
| `error(R, P)` where `R` is a return slot and `P` an exit node | W0204, "returns a reference into `x`", with `x` from the free that invalidates `R` |
| `error(R, P)` where the free comes from the end of a `ClauseFrame` local | W0313, "the continuation leaves its clause" |
| `unconsumed(r, P)` where `r` is a `TaskResult` local | W0601, "the scope drops the linear result of a task that a spawn in statement position started" |

A diagnostic names a temporary by its `TempKind` and its span ("argument 2 of `push`",
"the value of the block"), as the hidden variables of today do.

### 4.14 The invariants of `map_lowering.md`, section 5

"Structure": the Core has an explicit element with a fixed template for it. "Rule": one
function covers each form. "Same": the design keeps the mechanism of today.

| Invariant | Status | How |
| --- | --- | --- |
| A1 Path cover | structure, except one open case | each construct has fixed edges; abort edges come from unwind points; re-runs for local handlers from `rerun`. Open: the re-run after a `multi` operation of a handler of a caller (OL-R2a) |
| A2 Components | structure | one component for each Core body; handled and scope bodies inline |
| A3 Run-node cover | rule | `Σ(B)` is relation-generic, with replays; open: a place in a local of a callee (F3-2) |
| A4 Order inside a node | structure | one node for each statement; a call has a separate bind node; uses before changes in each template |
| A5 `no_gen_kill` | structure | only a call or an `Assign` through a `Deref` invalidates; a call binds at a separate node; a borrow does not invalidate |
| A6 `bound_before_use` | structure | validator rules V2 and V3 for each body, also inner bodies (today the lint covers only the function component) |
| B1 Interned tree | same | the place table of `weft-facts` |
| B2 Typed stability | structure | each step comes from a typed `Proj` (`field_step`, `elem_step`, the `Deref` kind) |
| B3 Root truth | rule | one resolver; `Arg` roots of inner bodies are substituted at each run node |
| B4 Wildcards | same | the one-place rules of ADR 0003 stay |
| B5 Split ids | same | `seg_split` |
| B6 Handle places | rule | `Deref(Rc)` gives the handle place and reads the pointer word (O3-6) |
| C1 Points-into cover | rule | one transfer function for each rvalue; rule OPAQUE (N1, N2); the second `Deref` of a binding (R3RT2) |
| C2 Holder cover | structure | each value in transit is a local until its consumer |
| C3 Rebind hygiene | structure | an assignment uses its source operand at its own node |
| C4 Free cover | structure | `StorageDead` of each local on each path, also before jumps and on abort paths; open: callee locals (F3-2) |
| C5 Change cover | rule | rule OPAQUE lends `env_ref` (N2) |
| C6 `writes_via` exactness | same | `writes_through`, `finish_via_calls` |
| C7 Part moves | same (spec) | `moved_part`; F3-5 is a spec rule |
| C8 References behind references | rule | the call rule gives the places reachable through the `Deref` steps of the type (R3RT3); bindings (R3RT2) |
| D1 Move cover | structure | `Operand::Move`, `Unpack`, tails by FRAME, re-runs by `rerun` (O3-14); part moves stay with the spec rules of R3a |
| D2 New values | structure | the three `Assign` templates |
| D3 Normal ends | structure | `StorageDead` |
| D4 Suspension cover | structure | `may_abort` at each `Call`, `Assert` and `ScopeEnd` by callee kind; open: F3-8 (spec) |
| D5 Linear holders | structure | each linear value is in a local with flags from the final type; `Give` and `TaskResult` (O3-4) |
| D6 Flags | structure for the flags | `LocalProps` from the final type; open: `on abort` correctness (W0118, I3-1) |
| D7 Unset values | structure | `StorageLive` with no value; `FieldValue::Unset`; open: nested literals (Q3-1 needs move paths) |
| E1 to E4 `multi` | same | `rerun`, `spared_at` from unwind scopes |
| F1 to F6 Tasks | rule | the task sink of `Σ`; replays for stored closures (O3-5); the pointer word (O3-6); open: callee summaries (V132) |
| G1 Effects | rule | `CapRef` from the builder; the effect facts by callee kind |
| G2 Call roots | rule | one call rule (R3RT3, O3-7) |
| G3 Changes of caller memory | same | `needs_decl` in the spec |
| G4 Argument checks | rule | the call rule checks `in` places and `@ uniq` for each callee kind, also an operation (R3RT7) |


---

## 5. Root-cause classes: what the design kills and what stays

The verdicts come from the data file `ir/work/minimal/verdicts.py`. It imports the
rows of `ir/work/findings.py` (the classification of `root_causes.md`) and gives each
unsound finding and each false positive one verdict:

- **K**: by construction in stages 1 to 5. The tag "st" (structure) or "ru" (single
  rule) says how (Summary).
- **KI**: by construction after the interpreter compiles the Core (stage 6).
- **P**: partly. The Core removes the part that came from one surface form. A decision
  about the domain, the summaries, the spec or the language stays.
- **S**: stays. The cause is outside the lowering of a body, or this design keeps the
  mechanism as it is.

Appendix A has the verdict, the mechanism and the reason for each finding.

### 5.1 By class

| Class | Group | U | K | KI | P | S | FP | FP K | FP P or S |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| TEMP | A | 9 | 9 | 0 | 0 | 0 | 0 | 0 | 0 |
| TAIL | A | 4 | 4 | 0 | 0 | 0 | 1 | 1 | 0 |
| DROP | A | 8 | 5 | 0 | 2 | 1 | 1 | 1 | 0 |
| ORDER | A | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| ACCESS | A | 3 | 3 | 0 | 0 | 0 | 0 | 0 | 0 |
| DEREF | A | 7 | 7 | 0 | 0 | 0 | 1 | 1 | 0 |
| CALLS | A | 8 | 8 | 0 | 0 | 0 | 3 | 2 | 1 |
| ENV | A | 15 | 15 | 0 | 0 | 0 | 5 | 2 | 3 |
| INNER | A | 9 | 9 | 0 | 0 | 0 | 3 | 1 | 2 |
| SUSP | A | 5 | 5 | 0 | 0 | 0 | 5 | 3 | 2 |
| LOOP | A | 3 | 0 | 0 | 3 | 0 | 1 | 0 | 1 |
| VAL | A | 2 | 2 | 0 | 0 | 0 | 3 | 3 | 0 |
| POST | A | 5 | 4 | 0 | 1 | 0 | 1 | 1 | 0 |
| TYPES | A | 0 | 0 | 0 | 0 | 0 | 1 | 1 | 0 |
| TWO | A* | 4 | 0 | 4 | 0 | 0 | 0 | 0 | 0 |
| MULTI | B | 2 | 0 | 0 | 1 | 1 | 1 | 0 | 1 |
| STATE | B | 3 | 0 | 0 | 3 | 0 | 8 | 0 | 8 |
| FNVAL | B | 22 | 4 | 0 | 16 | 2 | 2 | 0 | 2 |
| STORE | B | 9 | 1 | 0 | 5 | 3 | 0 | 0 | 0 |
| PART | B | 3 | 0 | 0 | 3 | 0 | 1 | 0 | 1 |
| GEN | B | 7 | 3 | 0 | 3 | 1 | 1 | 0 | 1 |
| CAP | B | 11 | 4 | 0 | 6 | 1 | 2 | 0 | 2 |
| SUM | B | 13 | 3 | 0 | 9 | 1 | 3 | 0 | 3 |
| SPEC | C | 13 | 0 | 0 | 0 | 13 | 3 | 0 | 3 |
| TYPE | C | 12 | 0 | 0 | 0 | 12 | 4 | 0 | 4 |
| INF | C | 1 | 0 | 0 | 0 | 1 | 1 | 0 | 1 |
| NAMES | C | 1 | 0 | 0 | 0 | 1 | 2 | 0 | 2 |
| **Total** | | **180** | **87** | **4** | **52** | **37** | **53** | **16** | **37** |

Comparison with the baseline of `root_causes.md` (a full MIR-like IR, verdicts by
class): the baseline puts 83 unsound findings (46%) by construction. This design puts
91 (51%). It loses LOOP (3) and the four `on abort` and closure-summary findings of
group A. It gains 15 findings of group B that one rule of section 4 covers: rule
OPAQUE (V011, V078), the closure sets in types (RR2, V107, RT6), the replays of inner
bodies with the task sink (O3-5, V052, V127), the uniform store and argument rules
(V108, RT3b, V031, V056), the uniform flow of capability marks (RT16) and the frame
roots of continuations (RR3, V120).

### 5.2 The ids by verdict

- **K, unsound (87):** RT1, RT2, RT3a, RT3b, RT4, RT5, RT6, RT8, RT9, RT10, RT11, RT12,
  RT13, RT14, RT16, RT17, RT18, RT24a, F3, F4, V002, V006, V007, V008, V009, V011, V014,
  V015, V017, V018, V020, V024, V027, V028, V031, V035, V036, V039, V042, V052, V053,
  V056, V057, V059, V072, OL-1d, OL-3c, OL-5, OL-R2d-box, OR2, OR8, RR2, RR3, RR4, RR5,
  RR7, V073, V074, V078, V086, V088, V089, V093, V098, V103, V104, V107, V108, V116,
  V118, V120, V121, V125, V127, V134, V136, O3-1, O3-2, O3-3, O3-4, O3-5, O3-6, O3-14,
  R3RT2, R3RT3, R3RT4, F3-7.
- **KI, unsound (4):** V045, OR6, RR10, IP6.
- **K, false positives (16):** RT22, V012, V044, V058, V060, OL-6b, OL-R2c-1, OR4, V079,
  V083, V084, V085, O3-7, O3-8, R3RT5, R3RT7.
- **P, unsound (52):** RT7, RT24b, V025, V026, V032, V033, V037, V040, V041, V043, V046,
  V047, V049, V050, V051, V061, V062, V066, OL-1a, OL-1b, OL-1c, OL-2a, OL-2b, OL-3a,
  OL-4a, OL-S5a-store, OR1, OR3, OR7, OR9, RR1, RR6, RR9, FD1, FD3, V075, V076, V077,
  V080, V081, V082, V087, V096, V097, V105, V106, V111, V126, V133, R3RT1, F3-3, Q3-1.
- **P, false positives (15):** V029, V054, V055, V069, OL-4b, OL-6a, OL-R2c-2,
  OL-R2d-clause, OL-S5c-pair, OL-S5c-w0312, V115, O3-9, O3-10, O3-12, R3RT10.
- **S, unsound (37):** RT3c, RT15, RT24c, RT24d, F5, F6, QR5, QR6, QR7, V003, V010,
  V016, V063, V067, OL-R2a, OL-R2b-res, OL-R2b-prec, OL-S5a-w0314, OL-R2d-struct,
  OL-NR-ptrfork, OR5, RR8, FD4, QA3, IP1, IP3, V095, V117, V119, V124, V132, F3-1, F3-2,
  F3-4, F3-5, F3-6, F3-8.
- **S, false positives (22):** RT20, R1-SIM, V001, V013, V023, OL-3b, OL-R2b-holds,
  OL-R2c-3, OL-R2e-reassign, OL-NR-flow, OL-NR-multi, OR10, RR12, QA6, V101, V130,
  V138, O3-11, R3RT6, R3RT11, F3-11, Q3-3.
- **The hypothesis IP8** (hidden part variables break `bound_before_use`): K for that
  part (validator rules V2 and V3 for each component). Its second part (`ret_ok` for
  the `in` form) stays.

By round: round 1, 46 of 78 (59%); round 2, 30 of 64 (47%); round 3, 11 of 20 (55%);
the open lists, 4 of 18 (22%). Round 3 found frame-boundary shapes, and the Core kills
them by FRAME. The open lists are value-flow questions, and most of them stay partly.

### 5.3 New shapes from the mapping documents

| Id | Shape | Verdict | Mechanism |
| --- | --- | --- | --- |
| map N1 (`ir/work/map/opres.wf`) | the result of an operation of a handler of a caller does not point into the reference arguments of the operation | K (ru) | rule OPAQUE (4.6) |
| map N2 (`ir/work/map/fnres2.wf`) | the result of a call of a function parameter with no reference argument has no place | K (ru) | rule OPAQUE lends and points into `env_ref` |
| sem N1 (`ir/probes/p2_*.wf`) | a place operand of a binary operator is read at the operator | K (st) | rule ORDER-2, early borrow |
| sem N2 (`p9`) | the same for an argument of `print` | K (st) | rule ORDER-2 |
| sem N3 (`p10`) | the base of an index is followed after the index operand | K (st) | the `Index` step is in the consumer place, after the index statements |
| sem N4 (`p25`, `p27`) | a failed `assert` unwinds the task, and it is not `may_abort` | K (st) | the `Assert` template and the bit `EffectSig::unwinds` |

### 5.4 Regressions of fixes

`root_causes.md` lists ten soundness regressions where a fix in one class broke an
assumption of another class. With the Core:

| Regression | Classes | After |
| --- | --- | --- |
| V045 (effect resolution) | TWO | KI: the interpreter compiles the Core, which has `CapRef` |
| V073 (`handle` keeps `empty`) | VAL, DROP | K: the "handle value" node joins `empty` of each source |
| V074, V088 (abort paths missing) | SUSP, CAP | K: each statement that can abort has an unwind point |
| V089 (abort nodes of the stored-value pass) | CAP, POST | K: the worklist adds abort edges for its own run nodes |
| V095 (`strict_prefix` and `resume`) | SPEC, SUSP | S: a spec encoding |
| V096 (task sets and `join`) | LOOP, STATE | P: the task sets stay lowering state |
| V097 (one-place instances and re-runs) | SPEC, MULTI | P: the re-run rule stays |
| V116 (`spared_at` and by-value captures) | SUSP, ENV | K: `spared_at` reads the unwind scopes and the `Move` fields |
| V125 (`kept` and a task-made reference) | ENV, SPEC | K: rule CAPTURE gives `Kept` only with no borrow |

Six of the nine rows are now one mechanism. The three that stay are value-flow or spec
questions.

### 5.5 What stays, and why

- **LOOP (3 U, 1 FP).** The loop fixpoint stays (D13). Its saved state gets smaller, but
  a missed field in `LoopHead` is still possible. A worklist dataflow needs a CFG IR.
- **STATE (3 U, 8 FP).** `points_into` is not flow-sensitive, and `@ uniq`, task sets and
  part holders are lowering state. The Core gives the joins one place (the `If`,
  `Match` and `Loop` templates), but the domain does not change.
- **FNVAL (16 P, 2 S).** Function values that cross a function boundary: returned
  closures, closures in returned containers, closures that a callee stores. The Core
  gives one callee operand and one closure aggregate, but the summary of the callee
  (`ret`, `ret_refs`, `fn_stores`) decides the result.
- **SUM (9 P, 1 S).** The parts of `EffectSig` stay as they are. The Core makes a part
  easier to compute as a query over the Core of the callee, but the summary language is
  a separate design.
- **STORE (5 P, 3 S).** A function type does not state where the references that it gets
  live, and `rc` group places do not tell objects apart. This needs a language decision.
- **PART (3 P), GEN (3 P, 1 S).** `Unpack` removes the partial moves of patterns. A move
  of a part (`take(p.a)`) keeps `moved_part` and the spec rules of R3a. Nested literals
  with unset place fields need move paths. Generic items as values and the modes of type
  parameters stay.
- **CAP (6 P, 1 S).** W0313 and W0314 for the capabilities of handlers keep their marks
  (`caps.rs`). The marks now flow through one assignment template, so a form cannot
  forget them inside a body. Across bodies and tasks they stay summary questions.
- **MULTI (1 P, 1 S).** The re-run after a `multi` operation of a handler of a caller
  (OL-R2a) has no edge.
- **DROP (2 P, 1 S).** `on abort` stays atomic, and W0118 stays (D18).
- **Group C (27 U, 10 FP).** Spec rules, type properties, inference bounds and names.

---

## 6. The interpreter

### 6.1 Stage 3: exports from the Core

Today the interpreter compiles the AST (`compile.rs`, 1 544 lines) and reads three
span-keyed tables from the facts: `by_value` (the captures that each closure moves),
`arg_order` (the order of named arguments for a callee that the compiler does not
know) and `int_ops` (the integer type of each arithmetic result). At stage 3 these
tables come from the Core:

- `by_value`: the `Move` fields of each closure body, by the span of the literal;
- `arg_order`: from the `Call` statements with named arguments of a value receiver;
- `int_ops`: from `Bin` and `Un` with an integer type.

Test D1 compares these tables with the tables from `FnFacts` on each program of the
gate, before the switch. After the switch the facts do not carry them.

### 6.2 Stage 6: the interpreter compiles the Core

A new `crates/weft-interp/src/core_compile.rs` compiles the Core to the existing
`code::Op` stack code. `machine/` gets one new instruction, `Op::Deref` (place to
place through one reference), for an explicit `Deref` with no `Field` or `Index` after
it. The rest of the machine does not change.

| Core | Stack code |
| --- | --- |
| a body | a code unit (`CodeKind::Fn`, `Test`, `Closure`, `Clause`) |
| `Handle::body`, `ScopeStmt::body` | a code unit `HandleBody` or `ScopeBody`; its captured cells are the outer locals that the block names; the destination is a slot of the unit, and the unit returns it |
| a local | a slot; the temporaries are slots too (the compiler does not use `ToTemp`, `StmtBegin` or `StmtEnd`) |
| `StorageLive` | nothing; `BindEmpty` for a local with no value |
| `StorageDead` | `DropSlots` (consecutive ends merge) |
| `Assign` with `init` | the rvalue, then `Bind(slot)` |
| `Assign` | the rvalue, the place, `Store`; `CompoundStore` is not needed |
| `Copy(p)`, `Move(p)` | the place (`Var`, `Field`, `Index`, `Deref`), then `Read` |
| `Ref { place, all }` | the place, then `Borrow` or `BorrowAll` |
| `Bin`, `Un` | the operands, the operator, then `CheckInt(ty)` |
| `Aggregate` | `Tuple`, `MakeVec`, `MakeStruct`, `MakeEnum` |
| `Closure` | `MakeClosure { caps, owned }`: `Ref` and `Kept` fields are cells, `Move` fields are in `owned` |
| `Unpack` | `Untuple` or `Unstruct`, then `Bind` for each part |
| `Match` | `Match { pat, fail }` for each arm, from `PatTest` and the bindings |
| `Call` | `Call`, `CallValue`, `Perform`, `CallMethod` (spawn, join, detach), `Fork` |
| `Handle` | `Handle(spec)`, then `Bind(dest)` |
| `Scope`, `ScopeEnd` | `Scope`, `ScopeWait` |
| `Give` | `Pop` of the handle (the scope keeps the task) |
| `If`, `Loop`, `Break`, `Continue`, `IterNext` | jumps, `LoopEnter`, `BackEdge`, `Break`, `IterNext` |
| `Elems`, `Range` | `ElemIter`, `RangeIter` |
| `Print`, `Assert`, `Unreachable` | `Print`, `Assert`, `Fault` |

The slots of a code unit are in the order of `StorageLive`, so the unwinder of today
(the highest slot first) takes the reverse order of `StorageLive` (D14). The Core
removes the operand stack as a place for values on their way, so the unwinder finds
these values in slots. Then `compile.rs` and the three span-keyed tables go away
(RR10, V045, IP6, OR6: class TWO).

### 6.3 Differential tests

| Test | Stage | What it compares |
| --- | --- | --- |
| D0 types | 2 | for each expression span, the final type of the builder and the type of the old walk (a debug table of `Lower`) |
| D1 exports | 3 | `by_value`, `arg_order`, `int_ops` from the Core and from the facts |
| D2 facts | 4, 5 | the diff gate of section 8.2 |
| D3 runs | 6 | for each program of the gate with `main` or tests: the old compiler and the Core compiler, with `--oracle`, seeds 1 to 3, workers 1 and 4: the output, the exit code, the kind and the place of each fault, and the oracle events (dangling reads, leaks, races) |
| D4 traces (optional) | 3 to 5 | the machine logs the span of each read, move, store and end of a cell; a replay of the Core on the same path checks that each event comes from a Core statement with that span, in the same order |

D4 checks the Core as a description of the old compiler before stage 6. D3 checks that
the switch changes no run, except the expected differences below.

### 6.4 What changes in a run

- D15: the temporaries of the tail of a loop body end at the end of each iteration. Only
  `Weak.upgrade` and the oracle can see it (`semantics.md`, p24).
- Nothing else. The evaluation order, the read points, the capture choice and the unwind
  order are the ones of today.

---

## 7. Proof alignment

### 7.1 B1 (the CFG model)

The reference fragment of the Core maps to the instructions of
`proofs/borrowing/src/model.rs`, one statement to one node:

| Core | B1 |
| --- | --- |
| `t = &x` | `Borrow { dst: t, x }` |
| `t = &(*s).l[i]` (an unstable step) | `Child { dst: t, src: s, label: l }` |
| `t = copy s` (a reference) | `Copy { dst: t, src: s }` |
| a read or a write of a scalar through `*r` | `Read`, `Write` |
| `Call` (call node) | `Call { args, ret: None }`, with the mutable arguments of the callee footprint |
| `Call` (bind node) | `Copy` of the result into `dest` (the result binds at its own node) |
| `t = closure#k { ... }` | `MkClosure { clo: t, caps }` |
| a call of a closure, an operation, a `resume` | `Invoke` |
| `StorageDead(x)`, a move of `x` | `Free { x }`: a proposed B1 extension (`semantics.md`, section 13.7, step 3) |

The link proves `thm_dataflow_exact` under `no_gen_kill`. A call binds its result at
its own node in the Core, so each Core call has `no_gen_kill`. Today only the "let"
node of sema gives it.

### 7.2 B3 (the layout model)

`Proj::Field` maps to `Field`; `Proj::Variant` after a `match` test maps to the B3
instruction `Variant` on the edge of the arm; `Deref(Box)`, `Index` and `Elems` of a
`Vec` map to `Kid`; the pointer word `@` is a stable `Field` of the pointer cell. B3 is
straight-line and needs the CFG lift of B1 before it covers a Core body with branches.
The Core does not change that.

### 7.3 The effects model

| Core | `proofs/effects/src/model.rs` |
| --- | --- |
| `Handle { clauses, body }` | `Handle { eff, clauses, body }` |
| `Callee::Op { cap: Local(h) }` | `Perform { cap, op }` with the capability of `h` |
| a closure body that performs through `h` | a block with `h` in its capability parameters: the Core gives the set of `CapRef`s of each inner body, so the capability passing of the model is explicit |
| `Callee::Resume` | `Resume` |
| a linear local and its `StorageDead` | `Acquire`, `Consume` |
| an unwind point | the frames that the unwinder takes |

D14 fixes the unwind order of the interpreter of today. The model changes two steps to
it: `step_unwind_abort` takes the resource with the highest slot (the latest
`StorageLive`), not the newest resource; and `step_unwind_drop` unwinds a clause frame
before its fresh continuation (`semantics.md` N6, N7). No theorem depends on the order
(`semantics.md`, section 7.3). The blocks of the model are straight-line; the CFG lift
is the same work for each IR design.

### 7.4 The B6 link and its hypotheses

| Hypothesis (`proofs/link/README.md`) | Today | After |
| --- | --- | --- |
| `facts_ok`: `cfg_wf` | tested | structure: one component for each Core body; edges from the templates; checked by the validator and the gate |
| `facts_ok`: `instr_groups_ok` | tested; closures out | a template for each statement kind; a test compares the facts of the reference fragment with `link_facts(embed(core))` on the corpus |
| `facts_ok`: `fits`, borrowed locals exist | tested | validator V2 |
| `bound_before_use` | a lint on the function component only | validator V2 and V3 on each component |
| `no_gen_kill` | a lint | structure (A5) |
| `typed_by`, `alias_exact` | a round-3 lint | structure: each step comes from a typed projection |
| `ret_ok` | false for the `in` form | no change |
| no `MkClosure` or `Invoke` in the link | not proved | the closure aggregate is `MkClosure`; the link can take it with the B2 lemmas (`lemma_perform_is_call`) |
| no stored references | W0204 | no change (class STORE) |
| B4 is reference-based | documented | no change |
| `on abort` is atomic | W0118 | no change (D18) |

Stage 8 (optional) adds `proofs/link/src/core_link.rs`: an `IrStmt` type for the
reference fragment, `embed` to B1, and a Rust test that checks the template equality on
each corpus function. A Verus proof of the fact generator itself stays out of scope:
the templates are Rust code of `weft-sema`, not of `weft-verified`.

---

## 8. Migration plan

### 8.1 Stages

| Stage | Content | Exit criteria | Size |
| --- | --- | --- | --- |
| S0 | The gate: the manifest, the baseline of today, the harness (section 8.2) | the gate runs on the repository and the curated probes; the nightly job runs on the generated programs; the baseline is in `tests/ir_gate/baseline.jsonl` | 600 lines; 2 days |
| S1 | `core/mod.rs`, `print.rs`, `validate.rs` | unit tests on hand-written Core; the printer round-trips the examples of this document | 1 450 lines; 2 days |
| S2 | Builder part 1: names, methods, types (the unification moves out of `Lower`, which keeps a copy until S5), ANF, ORDER-1, ORDER-2; the command `weft core FILE FN` | D0 holds on the gate; the validator holds rules V1, V4, V8, V9, V11 | 3 000 lines; 6 days |
| S3 | Builder part 2: TEMP, FRAME, DISCARD, JUMP, UNWIND, CAPTURE; the exports of section 6.1 | the validator holds each rule on the gate; D1 holds; the interpreter takes its exports from the Core | 1 700 lines; 5 days |
| S4 | The fact generator over the Core, next to the old one, in six groups (section 8.3) | for each group: the gate has no unexpected difference; `weft agree` holds on the new facts; the hypothesis lints hold on each component | 9 500 lines (mostly moved and cut); 12 to 15 days |
| S5 | The new generator is the default; the old one stays behind the switch for one review round; then the old code, `Summary`, `late.rs` and the span-keyed fields of `FnFacts` go away | one review round with no regression that the old generator does not have | minus 19 000 lines; 2 days |
| S6 | `core_compile.rs`; `Op::Deref` | D3 holds on the gate; `compile.rs` goes away | 900 lines; 5 days |
| S7 | ADR 0012 (the Core); edits of ADR 0002 (the checklist), 0003, 0005, 0006, 0007, 0010; `docs/architecture.md`; `docs/traceability.md`; `CLAUDE.md` | `docs` tests hold | 2 days |
| S8 (optional) | `proofs/link/src/core_link.rs` and its test; the unwind order of the effects model | `proofs/verify-all.sh` holds | 3 days |

The days are days of one agent stream: about 40 days in total. S4 can split into
parallel streams by group after group 4a; with three streams the total is about 30
days.

### 8.2 The diff gate

**Inputs.**

- The repository: `tests/programs` (129), `crates/weft-interp/tests/programs` (42),
  `examples` (4), `tests/packages` (2): 177 programs.
- The curated probes of rounds 1 to 3 and of the IR mapping, without copies of the
  source tree and with one copy of each text (by its hash): about 1 570 programs. They
  come from `redteam/`, `specreview/`, `s2/`, `edge/`, `edgefix/`, `s1fix/`, `s2fix/`,
  `s5r/`, `fix/`, `p/`, `core/`, `verify/` (curated parts), `r2/{oracle,redteam,
  fidelity,interp,quality}` (probes, repro, fp, min), `r3/{oracle,redteam,fidelity,
  interp,quality}` (probes, repro, r2probes), and `ir/{probes,work/map,work/machine,
  work/mir}`. Stage S0 copies them into `tests/ir_gate/probes/` with a manifest that
  names the source of each file.
- The generated programs (nightly only): the runs, seeds and sweeps of `r2/oracle` and
  `r3/oracle`, the fuzz and generator corpora of `r3/quality`, and the generated parts
  of `verify/`: about 55 700 programs. They stay outside the repository, in an archive
  that the nightly job reads.

**What the gate compares**, for each program, with `Options::facts` set to `Old` and to
`New`:

1. the multiset of diagnostics: code, file, line;
2. `weft agree` on the new facts (the checker equals the spec);
3. the hypothesis lints (`gen_kill.dl`, `unbound_use.dl`) on each component of the new
   facts;
4. for a program with `main` or tests that the checker accepts with the new facts: `weft
   run --oracle` and `weft test --oracle`, seeds 1 to 3.

The gate does not compare raw facts: node and variable ids differ by construction.

**Classification of a difference.** The harness puts each difference in one class:

| Class | Condition | Action |
| --- | --- | --- |
| fixed | the old facts accept, the new reject, and the oracle faults on the program | expected; the entry names the finding id |
| precision gain | the old facts reject, the new accept, and the oracle does not fault | expected; the entry names the finding id or the reason |
| new false positive | the old facts accept, the new reject, and the oracle does not fault | blocks, unless an entry justifies it (for example a stricter rule of D15 or of section 4.7) |
| regression | the old facts reject, the new accept, and the oracle faults; or the new facts accept a program that the oracle faults on and that the old facts reject | blocks always |
| code change | the same lines, other codes | blocks, unless an entry gives the mapping of section 4.13 |

**The file of expected differences** is `tests/ir_gate/expected.toml`:

```toml
[[diff]]
file = "probes/r3/oracle/repro/O3-2_handled_body_temporary.wf"
old = ["W0301@77"]                       # with_local: correct today
new = ["W0301@24", "W0301@29", "W0301@34", "W0301@39", "W0301@44", "W0301@50",
       "W0301@56", "W0301@60", "W0301@66", "W0301@77"]   # example lines of the expected result
class = "fixed"
finding = "O3-2"
reason = "FRAME: the handled body moves its value before its temporaries end"
```

**Commands.** `cargo test -p weft-check --test ir_gate` (each commit: the repository and
the curated probes, about 1 750 programs); `scripts/ir_gate_full.sh ARCHIVE` (nightly:
the generated programs, with a report of new differences). At each commit the
CLAUDE.md gates run too: `cargo fmt --all`, `cargo clippy --workspace --all-targets --
-D warnings`, `cargo test --workspace`, and `proofs/verify-all.sh` where a proof file
changes.

### 8.3 Side by side

- `Options` gets `facts: FactGen` with the values `Old`, `New` and `Both`. `Both` runs the
  two generators and the checker on each, and writes the differences (the gate uses it).
- The new generator returns `Unsupported(construct)` for a body with a construct of a
  group that is not on yet. The old generator then lowers that body. The gate reports
  the coverage of each group.
- The groups, in this order:
  - 4a: straight-line code, blocks, `if`, `match`, `return`, calls of items, aggregates,
    borrows, `print`, `assert`;
  - 4b: loops;
  - 4c: closures, function values, stored values;
  - 4d: `handle`, clauses, `resume`, `multi` re-runs;
  - 4e: `scope`, `spawn`, `join`, `detach`, `fork`, `sim.run`, `with_timeout`;
  - 4f: generic bodies, `drops`, `holds`, generic items as values.
- The inference loop (`infer.rs`) calls the generator of the body. A body and its
  callees can use different generators while the groups come in; the signatures are
  the same type, so the inference does not care.

### 8.4 The other workflow

Another workflow fixes round-3 items in `/home/user/wt-core` now (R3a). This plan
starts from the commit that merges R3a. Rules for the time of S4 and S5:

- A soundness fix in the old generator gets a probe in `tests/ir_gate/probes/`. The new
  generator must pass the probe; the gate makes that visible.
- After S4 starts, a fix goes into the old generator only if the baseline of the gate
  needs it. Each other fix goes into the new generator.
- The R3a fixes for frames (O3-1, O3-14, O3-2, O3-3, F3-7) and for unset fields (Q3-1,
  Q3-4) are special cases that the Core replaces; S5 deletes them with the old code.

### 8.5 The checklist for a rule change after the migration

The list of ADR 0002 and `CLAUDE.md` stays, with two changes:

- Step "fact generation" names the place: the template of a Core statement kind
  (section 4.5), the call rule (4.6), or a row of `RELS` for a new relation (4.7).
- A new surface construct needs a builder rule (section 3) and no new fact template if
  it lowers to existing Core statements. The gate shows if it does not.

---

## 9. Risks, size and what stays out

### 9.1 Risks

| Risk | Likelihood | Impact | Mitigation |
| --- | --- | --- | --- |
| R1. The extraction of type inference from the walk changes types. About 190 call sites of `unify` and `inf` are in `body/`. `Ty::Fn` carries value flow today. | high | wrong copy or move, wrong method, wrong flags | D0 type parity before any fact changes; `ClosureSet` replaces `FnTy::summary` with the same join points as `fn_joins`; S2 keeps the old inference in `Lower` until S5 |
| R2. The projection of inner bodies is too wide or too narrow | medium | false positives (too wide) or missed facts (too narrow) | the gen and kill roles of `RELS`; the gate on the 1 570 probes, many of them from round 2 on closures and clauses; the must check for kill facts |
| R3. The must check of moves in inner bodies (section 4.7) rejects programs that the old lowering accepts | medium | new false positives | the gate classifies them; the rule is sound and matches the machine; an entry can justify it |
| R4. Two generators at one time, while R3a and later fixes land in the old one | high | double work; drift | the freeze rules of 8.4; the gate shows each drift |
| R5. Fact volume: one node for each Core statement, early borrows, `StorageLive` nodes | medium | slower checker | no node for `StorageLive` that a value follows; ORDER-2 makes an early borrow only when code runs in between; `scale.rs` counts parts; consecutive `StorageDead` of one scope can share a node if the spec result does not change (it does not: each end is a free with no use between) |
| R6. The loop fixpoint stays | certain | LOOP (3 U, 1 FP) stays partly | the smaller `LoopHead`; a later CFG IR can replace `lower_loop` |
| R7. The pointer word `@` is a new step | low | a missed overlap in the checker | it is a `Field` step: the verified algebra handles it; the gate and the corpus test of W0405 |
| R8. Outlining handled and scope bodies in `core_compile.rs` changes captured cells | medium | run differences at S6 | D3 and D4; the outline uses the free locals of the block, as the AST compiler does |
| R9. Diagnostics move from sema to the spec (W0204 local forms) | low | other text, other notes | the mapping of 4.13; the corpus markers keep their codes |
| R10. The design keeps `points_into` flow-insensitive and the summary language | certain | classes STATE, SUM, FNVAL, STORE stay partly | out of scope (9.3); the Core makes a later change smaller |

### 9.2 Size

| Part | Today | After | Note |
| --- | --- | --- | --- |
| `body/` (the fact generator), lines in functions | 18 415 | about 9 500 | 2 086 deleted, 2 286 moved to the builder, 14 043 kept and cut by about a third (Appendix B) |
| `core/mod.rs`, `print.rs`, `validate.rs` | 0 | about 1 450 | new |
| `core/build/` | 0 | about 4 700 | 2 286 moved (names, types, methods, patterns, W0120, arguments) and about 2 400 new (ANF, ORDER-2, TEMP, FRAME, JUMP, UNWIND, CAPTURE) |
| `weft-interp`: `compile.rs` / `core_compile.rs` | 1 544 | about 900 | stage 6 |
| the gate | 0 | about 600 | harness and scripts; the probes are data |
| `weft-facts`, `weft-check`, spec | — | + about 60 | the pointer-word step, the switch, three diagnostic mappings |
| cross-cutting call sites in the fact generator | about 200 | about 20 | Summary |

The total number of lines goes down by about 3 500 (from about 20 000 to about 16 500 in
sema and the compiler of the interpreter). The main gain is not the number of lines:
each mechanism has one caller.

### 9.3 What stays out

| Out of scope | Classes that stay | A later step |
| --- | --- | --- |
| A CFG IR and a worklist dataflow for loops | LOOP, part of STATE | replace `lower_loop` with a fixpoint over the CFG of the facts; the Core can lower to a CFG with one more pass |
| Flow-sensitive `points_into` | STATE | a spec change (`points_into_at`) |
| A summary language with parts as queries over the Core | SUM, part of FNVAL | compute each part of `EffectSig` from the Core of the callee |
| A closure analysis across functions | FNVAL | 0-CFA over the Core of the program, or summaries |
| Regions for the references that a function value gets | STORE | a language decision |
| Capabilities of handlers as values | CAP | `handle` binds a local of the capability; W0313 becomes W0301 as for continuations (M14) |
| `on abort` as a call on abort paths | DROP (FD1, F3-1, F3-3) | the unwind point names the function; the abort node gets its call facts; the effects model changes |
| Move paths for each projection | PART | `MoveData` over the Core; spec rules for each path |
| Monomorphization | GEN | instantiate generic bodies at each use |
| The re-run after a `multi` operation of a handler of a caller | MULTI (OL-R2a) | a re-entry edge from the bit "can resume more than once" of the callee |

### 9.4 Open choices for ADR 0012

1. D15: the temporaries of the tail of a loop body end at the end of each iteration
   (proposed), or at the end of the loop (the machine of today; not expressible as a
   static end in the Core without a special case).
2. The pointer word `@` (proposed), or the read of the whole pointer place (today, with
   the false positives that ADR 0006 avoids by reading nothing).
3. The must check of moves of linear outer variables in inner bodies (proposed), or the
   rule of today (sound only if each path moves).
4. `Kept` captures (proposed: the cell outlives the local for plain data with no
   borrow), or `Ref` for each capture (simpler, with the false positives V012 and RR12).
5. Handled bodies and scope bodies inline (proposed), or as Core bodies (closer to the
   machine; each run of a handled body then needs a summary, and the abort edges and
   the re-run loop cross components).
6. The codes of the facts that move into the spec (W0204 for a return slot, W0313 for a
   continuation): keep the codes by a mapping in `diagnose.rs` (proposed), or report
   W0301.

---

## Appendix A. The verdict of each finding

Generated by `work/minimal/appendix.py` from `work/minimal/verdicts.py`. "st": structure, "ru": single rule (Summary). The mechanism tags are in section 4.1.

| Id | Kind | Class | Verdict | How | Finding |
| --- | --- | --- | --- | --- | --- |
| F3-7 | U | TEMP | K (st) | M2 M9 | The value of a scope body is not held across the scope end; the end can abort |
| O3-2 | U | TEMP | K (st) | M1 M2 | A reference into a temporary of a handled or scope body leaves the body |
| O3-3 | U | TEMP | K (st) | M1 M2 | A reference into a temporary of a clause leaves through the clause value or `resume` |
| OL-3c | U | TEMP | K (st) | M1 (jump ends in-flight temps) | A return/break in a later operand leaves a linear value on its way |
| RT18 | U | TEMP | K (st) | M1 M2 | The hidden `for` iterator does not get `uniq`, so W0503 is missed |
| RT4 | U | TEMP | K (st) | M1 M2 | An argument reference is held only from after the later arguments run |
| V007 | U | TEMP | K (st) | M1 M2 | A temporary root has no owner and no end: a reference into it never dies |
| V015 | U | TEMP | K (st) | M1 M2 | A closure argument is not held while later arguments run |
| V072 | U | TEMP | K (st) | M1 M9 | A linear temporary held while a later operand aborts is not checked (W0602) |
| O3-1 | U | TAIL | K (st) | M2 | A place as the tail of a `scope` body moves in the interpreter, not in the checker |
| O3-14 | U | TAIL | K (st) | M2 | A tail place of a multi handled body moves once per resume; the checker counts one |
| V059 | U | TAIL | K (st) | M2 | A local named as an if/match arm tail is not moved |
| V118 | U | TAIL | K (st) | M2 | A place as the tail of a discarded block moves at run time; sema sees no move |
| V058 | FP | TAIL | K (st) | M2 | A generic function that returns T through an if/match tail gets T in `drops` |
| F3-1 | U | DROP | S | W0118 signature check | W0118 misses an `on abort` change through a reference in the value |
| F3-3 | U | DROP | P | drops part is uniform; W0118 must read it | A generic `on abort` function drops a value of its type parameter |
| FD1 | U | DROP | P | on abort stays atomic (W0118); unwind point names the function | The effects of an `on abort` function are not checked (the unwinder call is not a call) |
| O3-4 | U | DROP | K (st) | M4 (Give; ScopeEnd drops the result) | A spawn in statement position drops a linear task result |
| RT1 | U | DROP | K (st) | M1 M4 | A move or the scope end of an owner does not invalidate references into it |
| RT14 | U | DROP | K (st) | M1 M4 | Linear values go away silently: `let _`, wildcard part, `print`, `match _`, overwrite |
| V002 | U | DROP | K (st) | M7 (upvar is the outer variable) | An overwrite of a captured linear variable in a closure or clause is not W0601 |
| V057 | U | DROP | K (st) | M1 M3 (T values in typed locals) | Generic `drops` misses a T moved into a holder that is then dropped |
| V083 | FP | DROP | K (st) | M9 | An abort edge does not end linear body owners: false W0601 in a retry loop |
| RT2 | U | ORDER | K (st) | M1 | Queued uses and reads go into the next node, which can be another component or branch |
| OL-R2d-box | U | ACCESS | K (st) | M5 (PTR word of the Box) | A borrow through a Box deref does not read the Box (W0405) |
| OR8 | U | ACCESS | K (st) | M5 | A use or a new value of a whole local is not an access for W0405 |
| RT10 | U | ACCESS | K (st) | M5 | A use of a reference variable as a value is not a read (W0405) |
| O3-6 | U | DEREF | K (st) | M5 (PTR word of the handle) | A task reads through an Rc handle; the parent moves the handle |
| R3RT2 | U | DEREF | K (st) | M5 | A `match` through a reference loses the places of a held reference |
| RT9 | U | DEREF | K (st) | M5 | `c += 1` on a reference local is a rebind, not a write through it |
| V008 | U | DEREF | K (ru) | M6 (handle places of every argument) | An Rc result through an argument handle gets no handle dependency |
| V014 | U | DEREF | K (st) | M5 | A compound assignment through a reference in a field writes the field, not the target |
| V020 | U | DEREF | K (st) | M1 M5 | A held Rc receiver loses its handle dependency while later arguments run |
| V098 | U | DEREF | K (st) | M5 | A write through a tuple part reference counts as a write of the local |
| V085 | FP | DEREF | K (st) | M5 | A bogus `*v..` Held root through a generic identity: false W0703 |
| F3 | U | CALLS | K (ru) | M6 | A perform is not checked like a call; clause reference parameters have no root |
| R3RT3 | U | CALLS | K (ru) | M6 | A call misses the references behind a reference argument (W0312, W0405) |
| RT17 | U | CALLS | K (ru) | M6 | `sim.run` as a value bypasses W0802 |
| RT24a | U | CALLS | K (ru) | M6 | W0705 is not checked for fn items given as values |
| V035 | U | CALLS | K (ru) | M6 | A perform with a closure argument: only `&T` arguments are call arguments |
| V039 | U | CALLS | K (ru) | M6 | Aliasing places given to one function value are never checked (W0312) |
| V042 | U | CALLS | K (ru) | M6 | An argument that holds a reference in a tuple or Option is not a call argument (three call paths) |
| V136 | U | CALLS | K (ru) | M6 | Sema ignores the arguments of `join` and `detach`; the interpreter runs them |
| O3-7 | FP | CALLS | K (ru) | M8 (one root for one value) | W0312 on an operation whose closure argument conflicts with itself |
| OL-S5c-w0312 | FP | CALLS | P | root choice for a clause callback | A local clause that runs its callback parameter gets W0312 |
| R3RT7 | FP | CALLS | K (ru) | M6 | An `in` place on an operation parameter has no effect |
| OL-5 | U | ENV | K (st) | M7 M8 | A closure that holds a fresh once continuation is not a once value |
| OR2 | U | ENV | K (st) | M7 M8 | Moves of captures: the checker at creation, the interpreter at run (and a false W0302) |
| RR4 | U | ENV | K (st) | M7 M14 | A closure that captures the scope capability `s` leaves the scope |
| RR7 | U | ENV | K (ru) | M7 M8 | A closure keeps the creation-time places, summary and modes of a captured variable |
| RT5 | U | ENV | K (st) | M7 M8 | A closure argument that captured a reference is not a call argument (W0312) |
| RT8 | U | ENV | K (st) | M7 M8 | The mode of a closure (linear, once, nonportable, uniq) does not follow its captures |
| V009 | U | ENV | K (ru) | M7 M8 | A clause that moves a captured owner: the move is not applied at the perform |
| V017 | U | ENV | K (st) | M7 (export from the Core; KI with M13) | Checker and interpreter disagree on moved captures (closure outlives the local) |
| V018 | U | ENV | K (ru) | M7 M8 | A clause reads a captured reference at the perform after the body invalidated it |
| V027 | U | ENV | K (ru) | M7 M8 | A stored closure that runs at a reach node does not use its captured references |
| V103 | U | ENV | K (ru) | M7 M8 | The late join misses a captured closure chain and part holders (RR7 shapes) |
| V104 | U | ENV | K (ru) | M7 (cell indirection) | A returned closure keeps creation-time places of a captured reference |
| V116 | U | ENV | K (ru) | M7 M9 | An outer linear value that a closure or clause took by value is 'spared' |
| V125 | U | ENV | K (st) | M7 M8 | kept(T, Rt): a reference that the task makes into a kept copy variable |
| V134 | U | ENV | K (st) | M14 | The scope capability in a tuple or an Option leaves the scope |
| F3-11 | FP | ENV | S | precision of a rebind through a cell | A closure that rebinds a captured reference does not rebind it where it runs |
| O3-11 | FP | ENV | S | cell and value share one root | A move and then a new value of a captured variable invalidates the closure |
| R3RT5 | FP | ENV | K (st) | M7 M8 | A by-value capture is still tied to the variable (W0204, W0301) |
| RR12 | FP | ENV | S | needs a must-write summary | W0304 for a local that a closure, a clause or a task sets |
| V012 | FP | ENV | K (st) | M7 M8 | W0204/W0301 for a closure that captures a copy value |
| F4 | U | INNER | K (ru) | M8 | Mutations of a closure through its own reference parameters are lost (own_roots) |
| R3RT4 | U | INNER | K (ru) | M8 | A `resume` with a closure parameter gives the operation result no places |
| RR5 | U | INNER | K (ru) | M8 | `resume` carries the mutations of the handled body, not its frees |
| RT11 | U | INNER | K (st) | M2 (jumps elaborated per body) | `return`/`break` in closure, handled and scope bodies go to the wrong target |
| RT12 | U | INNER | K (ru) | M8 | A spawn in a closure is invisible at its call; W0314 misses items and parameters |
| V006 | U | INNER | K (ru) | M8 | A closure or clause stores a reference to its own local in a captured reference |
| V024 | U | INNER | K (ru) | M8 | `lends_mut` is not part of Summary: a call in a closure loses it at the run node |
| V053 | U | INNER | K (ru) | M8 | Clause values that point into clause parameters are not mapped to the perform arguments |
| V121 | U | INNER | K (ru) | M8 | Frees in a callee of the handled body; a resume through a closure or a callee |
| O3-12 | FP | INNER | P | replay of the clause spawn at the perform | A clause conflicts with the task that it spawns |
| O3-8 | FP | INNER | K (ru) | M8 | A closure with its own multi handler is a multi and abort point |
| OL-R2d-clause | FP | INNER | P | replay order in a clause | A clause that spawns its fn parameter into an outer scope and then resumes |
| RT13 | U | SUSP | K (ru) | M6 (one opaque-callee rule) | A multi operation that a function parameter reaches is not a multi point |
| V036 | U | SUSP | K (ru) | M8 (handled-body projection at resume) | A clause holds a reference into its parameter across `resume`; the body frees the argument |
| V074 | U | SUSP | K (st) | M9 | W0313 relies on abort paths, which several node kinds do not get |
| V086 | U | SUSP | K (st) | M9 | Abort paths miss a clause inside a clause and a local stored call |
| V088 | U | SUSP | K (st) | M9 | W0313 checks only paths to the inner handle end; an abort can leave to an outer end |
| O3-10 | FP | SUSP | P | summary of parameter spawns | Two spawns of function parameters get W0503 when the program has a multi op |
| OL-R2c-1 | FP | SUSP | K (ru) | M9 (spared from unwind levels) | An operation in a closure or clause inside a handled body spares nothing |
| OR4 | FP | SUSP | K (ru) | M9 | W0602/W0503 for a linear value outside the `handle` |
| V055 | FP | SUSP | P | replay order of resume and spawn | Corpus expects W0405 after `resume(); s.spawn(..)`, but resume runs the body first |
| V084 | FP | SUSP | K (st) | M9 | An abort edge skips the scope end: false W0405 after the handle |
| OL-R2a | U | MULTI | S | re-run after a caller multi operation | A multi operation of a caller's handler re-runs the rest of the body with old locals |
| V097 | U | MULTI | P |  | One-place instances assume one lowering is one run; a multi resume re-runs code |
| OL-NR-multi | FP | MULTI | S | path-insensitive re-run | The multi re-run model is path-insensitive: false W0302 when runs take different branches |
| RR1 | U | LOOP | P |  | The loop lowering stops after 8 passes: a chain of locals loses places, fn values, tasks |
| V025 | U | LOOP | P |  | A function-value local that a loop body reassigns later: earlier calls keep the old value |
| V041 | U | LOOP | P |  | A reference local that a loop body reassigns later keeps only its first value |
| V101 | FP | LOOP | S | widening choice | Widening gives false W0301 for walk-then-write code |
| RT24b | U | STATE | P |  | `uniq` of a local stays after a rebind (sticky), W0406 missed |
| V066 | U | STATE | P |  | `uniq` of a local after if/else depends on the lowering order |
| V096 | U | STATE | P |  | A join of a handle with a may-set of tasks ends every task in the set |
| O3-9 | FP | STATE | P |  | A join through a callee, tuple, Option, `id` or closure does not end the task |
| OL-4b | FP | STATE | P |  | A stale part holder after a join on a continue path |
| OL-6a | FP | STATE | P |  | Local.caps only grows: false W0313 after a reassignment |
| OL-NR-flow | FP | STATE | S | points_into is not flow-sensitive | points_into is flow-insensitive: a rebind before the end is still invalid |
| OL-R2b-holds | FP | STATE | S | points_into is not flow-sensitive | A local that gets a reference from a callee through `holds` is flow-insensitive |
| R3RT10 | FP | STATE | P |  | A new value of a part that holds a stale reference is W0301 |
| R3RT6 | FP | STATE | S | points_into is not flow-sensitive | Reference arguments flow into each other against their types; points_into is flow-insensitive |
| V069 | FP | STATE | P |  | Part holders never retire: stale places give false W0301 (and quadratic facts) |
| RT3a | U | VAL | K (st) | M3 | References lose their places through struct and array literals, value-call results and by-value match bindings |
| V073 | U | VAL | K (st) | M3 | `handle` takes `empty` from its body value: a linear clause value leaks |
| OL-6b | FP | VAL | K (st) | M3 | Overwriting `None` of an inferred local is W0601 |
| RT22 | FP | VAL | K (st) | M3 | A tail spawn handle wrapped in `handle` loses its task (false W0601) |
| V044 | FP | VAL | K (st) | M3 | A task handle through `if`, `match` or a closure result loses its task (false W0601) |
| OL-1d | U | POST | K (ru) | M11 | An operation result that holds a reference gets no places |
| OL-2b | U | POST | P | summary of a finished closure | A clause runs a parameter of a finished closure as a task: the summary is gone |
| V028 | U | POST | K (ru) | M11 | A stored closure performs a local operation: apply_stored runs after clause rebasing |
| V089 | U | POST | K (ru) | M9 M11 | Abort nodes that only the stored-value pass finds get no abort edge |
| V093 | U | POST | K (ru) | M11 | op_refs does not rebase Summary.lent and op_args |
| V079 | FP | POST | K (st) | M11 | W0204 runs before op_refs moves the facts of an operation result |
| IP6 | U | TWO | KI (st) | M13 | `fork` gives () when each branch is (): a generic caller faults |
| OR6 | U | TWO | KI (st) | M13 | A variable as an expression statement: the interpreter moves and drops it, sema sees nothing |
| RR10 | U | TWO | KI (st) | M13 | Named arguments: sema binds by name, the interpreter by position |
| V045 | U | TWO | KI (st) | M13 | The interpreter resolves `handle log` to a user effect `Log`; sema does not |
| V060 | FP | TYPES | K (st) | M12 | A move of a local with an inference variable type counts as a copy |
| O3-5 | U | FNVAL | K (ru) | M8 (task replays the unknown call) | A task or fork branch runs a closure from a struct field: no W0405, W0403 |
| OL-1a | U | FNVAL | P |  | A task runs a function value from a store (W0314) |
| OL-1b | U | FNVAL | P |  | A callee copies a function value out of a reference argument (W0313) |
| OL-R2d-struct | U | FNVAL | S | values a callee makes and returns | Function values in a struct that a callee returns, called later by an unknown value |
| OR1 | U | FNVAL | P |  | A returned closure that captures a reference parameter does not point into the argument |
| RR2 | U | FNVAL | K (ru) | closure sets in types | A function type carries one closure summary: later closures in an array or Vec are lost |
| RR6 | U | FNVAL | P |  | A function value that `resume` gives has no summary in the handled body |
| RT6 | U | FNVAL | K (ru) | M6 (one value-call rule, value sets join) | A call through a fn-item value ignores its mut places and aborts; `if` keeps one item |
| RT7 | U | FNVAL | P |  | Closure summaries are lost through returns, tuples, `if` and fields |
| V026 | U | FNVAL | P |  | Returned function values are lost: joined makers, makers through parameters, nested makers |
| V032 | U | FNVAL | P |  | A closure that comes back from a returned closure loses its summary (RetFn does not nest) |
| V033 | U | FNVAL | P |  | A callee calls a closure argument and then the closure that it returned |
| V049 | U | FNVAL | P |  | W0313 misses a closure that a callee returns inside a tuple |
| V061 | U | FNVAL | P |  | nonportable and uniq modes are lost through fn() places and containers |
| V075 | U | FNVAL | P |  | A task runs fn values through a generic T, references behind references, a copied result |
| V076 | U | FNVAL | P |  | fn_stores ignores references stored behind references |
| V105 | U | FNVAL | P |  | A result with function values in a Vec gets no places |
| V107 | U | FNVAL | K (ru) | closure sets in types | Two closures that meet in a tuple type do not join |
| V111 | U | FNVAL | P |  | A closure in a returned container adds no places to `ret_refs` |
| V119 | U | FNVAL | S | on abort stays atomic | An `on abort` function calls a closure held in its value |
| V126 | U | FNVAL | P |  | A callee keeps a fn parameter in a local container and runs it as a task |
| V133 | U | FNVAL | P |  | A function value in a struct that a callee returns is not in held_run |
| OL-S5c-pair | FP | FNVAL | P |  | A stored callback pairs with a different known closure at parameter 0 |
| V029 | FP | FNVAL | P |  | A stored closure: a mutation through its parameter counts for the whole argument |
| F3-2 | U | STORE | S | callee locals have no name | A closure or clause keeps its reference parameter in an outer local; a callee gives its own local |
| FD3 | U | STORE | P |  | A reference stored into an rc object outlives its owner |
| OL-4a | U | STORE | P |  | References stored behind a reference parameter: a read-back has no places |
| OL-R2b-prec | U | STORE | S | rc group places | A reference stored into an rc object through a handle of the same type to another object |
| OL-R2b-res | U | STORE | S | function types state no region | A closure or clause stores its own reference parameter; a fn value does not state where its references live |
| OL-S5a-store | U | STORE | P |  | A reference stored behind a closure or clause parameter is seen as the outer place |
| V037 | U | STORE | P |  | An Arg-rooted place escapes a closure or clause through a captured outer local (`keep = x`) |
| V087 | U | STORE | P |  | A callee stores a reference to its own local behind a reference parameter |
| V108 | U | STORE | K (ru) | M8 (one store check in each body) | The rc escape check misses closure, clause and closure-parameter stores |
| Q3-1 | U | PART | P |  | A place field below a second use of one generic type gets no 'unset' variable |
| R3RT1 | U | PART | P |  | A move of one part of a linear aggregate ends `live_linear` for the whole local |
| V062 | U | PART | P |  | Unset place fields: closures, nested literals and call results are not tracked |
| V023 | FP | PART | S | spec: a part move is a move of the whole local | A partial move counts as a move of the whole local (W0301, W0302) |
| OL-3a | U | GEN | P |  | A generic callee aborts or resumes more than once while it holds a linear T |
| OL-NR-ptrfork | U | GEN | S | no mode polymorphism | A generic function that forks with its argument gets no W0401 for *T or Rc |
| RR9 | U | GEN | P |  | A generic item given as a function value drops a linear value |
| RT3b | U | GEN | K (ru) | M6 (type-parameter arguments pass places) | References lose their places through generic callees and containers (`id(&x)`, `Box.new(&x)`, `push`) |
| V031 | U | GEN | K (ru) | M6 (one store rule) | A closure that goes into a generic container is not tracked as stored |
| V056 | U | GEN | K (ru) | M6 M7 (modes from the environment) | A closure given to a type-parameter parameter skips every mode check |
| V081 | U | GEN | P |  | A generic function in `holds` given as a function value: no W0602 |
| OL-R2c-3 | FP | GEN | S | generic Rc wrapper | A generic wrapper that holds Rc<T> is never many |
| OL-1c | U | CAP | P |  | A clause keeps its function parameter (W0313) |
| OL-S5a-w0314 | U | CAP | S | value of a caller operation | A value the body cannot follow goes to an operation of a caller's handler (W0314) |
| OR9 | U | CAP | P |  | A `resume` inside a spawned task runs the handled body on another task |
| RR3 | U | CAP | K (st) | M14 | A closure that resumes a continuation leaves its clause |
| RT16 | U | CAP | K (ru) | M3 (marks flow through Assign and Aggregate) | A closure escapes its handler through a local, a tuple or a container (W0313) |
| V046 | U | CAP | P |  | W0313 off by one: a closure given to an operation of its own handler |
| V047 | U | CAP | P |  | A capability leaves through a `resume` argument and the operation result |
| V050 | U | CAP | P |  | W0314 misses a clause that runs its function argument as a task |
| V052 | U | CAP | K (ru) | M8 (task replay) | W0314 misses a task that runs a closure from a field of a local |
| V077 | U | CAP | P |  | A clause keeps a fn value that it reads through a reference parameter |
| V120 | U | CAP | K (st) | M14 | A multi clause gives a resuming closure to the body through the resume value |
| R1-SIM | FP | CAP | S | root handler marks | False W0314 for a task closure that performs a standard effect inside `sim.run` |
| V054 | FP | CAP | P |  | False W0313 for Box.new, Rc.new and generic callees |
| OL-2a | U | SUM | P |  | A stored spawning closure at a reach node starts one copy of its task |
| OR3 | U | SUM | P |  | A callee that calls a callback twice is not checked for W0301 |
| OR7 | U | SUM | P |  | Function parameters that run as tasks or fork branches: no W0405, W0401, W0403, pinning |
| V011 | U | SUM | K (ru) | M6 (one opaque-result rule) | The result of an unknown function value gets the argument places, not a wildcard |
| V040 | U | SUM | P |  | A multi operation through an unknown value in a callee does not make the call multi |
| V043 | U | SUM | P |  | A spawning closure that a callee calls more than once starts one task |
| V051 | U | SUM | P |  | W0314 misses callee tasks that perform effects which a caller handles locally |
| V078 | U | SUM | K (ru) | M6 (one opaque-result rule) | The result of a caller's handler operation can point outside the parameters |
| V080 | U | SUM | P |  | A stored spawning closure given by value to a callee that calls it twice |
| V082 | U | SUM | P |  | A once closure with a fresh continuation goes to a callee that holds it across multi |
| V106 | U | SUM | P |  | A callee that gets a callback inside a container and calls it twice |
| V127 | U | SUM | K (ru) | M8 (clause replays the argument run) | A clause runs an operation's function argument as a task: no W0405/W0403 |
| V132 | U | SUM | S | needs a new summary part | A callee writes a non-function argument while it runs a function parameter as a task |
| OL-R2c-2 | FP | SUM | P |  | A callee that performs the operation makes each resume free every clause reference parameter |
| OR10 | FP | SUM | S | read part in signatures | A call reads all of its reference arguments (W0405) |
| V115 | FP | SUM | P |  | `repeats` ignores the 'again' flag: a callback run once counts twice |
| F3-5 | U | SPEC | S |  | A move of a part does not invalidate a reference to the whole value |
| F3-8 | U | SPEC | S |  | A cancelled task that never ran drops its linear by-value capture |
| F6 | U | SPEC | S |  | `forwards(H)` is weaker than the design: a library root handler passes |
| FD4 | U | SPEC | S |  | The multi rule does not count affine or `!Move` values |
| IP1 | U | SPEC | S |  | A Fail clause can resume a failure that the runtime raises |
| IP3 | U | SPEC | S |  | A stealable task shares an Rc with a pinned child |
| OR5 | U | SPEC | S |  | A reference made while a task runs stays valid after the join; `&v[i]` is not a read |
| RT24c | U | SPEC | S |  | No definite-assignment check (`let x: u64` then use) |
| V010 | U | SPEC | S |  | A move of an owner while a task holds a reference: task_conflict ignores frees |
| V016 | U | SPEC | S |  | Payload instability is lost through a coarse stated place (`-> &T in m.state`) |
| V095 | U | SPEC | S |  | `x..` means 'something above changed' for resume; strict_prefix drops it |
| V117 | U | SPEC | S |  | An `on abort` function can fail through join, fs.read, fork or a scope end |
| V124 | U | SPEC | S |  | A `!Move` local live across multi only through a reference |
| QA6 | FP | SPEC | S |  | A write through a wildcard reference invalidates that reference |
| V013 | FP | SPEC | S |  | Coarse access rules: any task that names `stats.x` reads all of `stats` |
| V130 | FP | SPEC | S |  | The end node of a task lends the writes of a task that it started in the outer scope |
| F3-4 | U | TYPE | S |  | The `on abort` parameter check ignores type arguments |
| F3-6 | U | TYPE | S |  | The runtime drops a linear task result (abort with a live handle, spawn statement, fork) |
| F5 | U | TYPE | S |  | Tuple `has_on_abort` is true for any non-ADT type (closure part = RT8) |
| QA3 | U | TYPE | S |  | An `in` place that names a later parameter gets no places (substitution order) |
| QR5 | U | TYPE | S |  | fip use counts overflow: W1002 goes away in release builds |
| QR7 | U | TYPE | S |  | A linear type nested 7 levels deep is not linear (depth cut-off) |
| RR8 | U | TYPE | S |  | `Vec.clear` drops linear elements (prelude signature has no `drops`) |
| RT15 | U | TYPE | S |  | `!Move` is not transitive; self-reference field stores are not checked |
| RT24d | U | TYPE | S |  | No exhaustiveness check for `match` |
| RT3c | U | TYPE | S |  | W0204 checks only a top-level `&T` and tuples of references, not `Option<&T>` |
| V063 | U | TYPE | S |  | The W0120 budget runs out and a non-exhaustive match is accepted |
| V067 | U | TYPE | S |  | A reference to a nonportable value is portable (`&Rc`) |
| OL-3b | FP | TYPE | S |  | A Vec of linear values has no consumer (prelude), always W0601 |
| OL-R2e-reassign | FP | TYPE | S |  | `let g = diff; g = rdiff` loses parameter names (one type per local) |
| R3RT11 | FP | TYPE | S |  | An empty match on an empty enum is W0120 |
| RT20 | FP | TYPE | S |  | Integer literal elements default to i64 when indexed (W0102) |
| QR6 | U | INF | S |  | Effect inference stops after 32 rounds with no diagnostic |
| V001 | FP | INF | S |  | The round bound of inference is too small: false W0706 |
| V003 | U | NAMES | S |  | `pub` is not enforced across units: a private dependency function is callable |
| Q3-3 | FP | NAMES | S |  | A bare variant name resolves to the first enum that has it (also in the interpreter) |
| V138 | FP | NAMES | S |  | W0107 for operation names rejects programs that perform by path |

## Appendix B. The functions of `body/` and where they go

Generated from `work/minimal/fnsizes.tsv` (the lines of each function, up to the next function) and `work/minimal/classify.py`. "Kept" functions lose their branches for each surface form; section 9.2 estimates that they shrink by about a third.

| File | Deleted (lines) | Moved to the builder (lines) | Kept in the fact generator (lines) |
| --- | --- | --- | --- |
| `aborts.rs` | 82: `finish_aborts` | 0 | 33 |
| `args.rs` | 0 | 101: `order_args`, `no_names`, `slot_exprs` | 0 |
| `call.rs` | 332: `eval_item_args`, `eval_value_args`, `cont_to_body`, `eval_op_args`, `closure_arg` | 545: `callback`, `call`, `ambiguous_op`, `method_call`, `no_method`, `method_on_path`, `check_visible`, `call_fn`, `no_self`, `item_call_types`, `item_arg_slots`, `unify_arg`, `print`, `positional_struct`, `variant_ctor`, `op_slots` | 2470 |
| `caps.rs` | 0 | 0 | 1023 |
| `drops.rs` | 151: `drop_linear`, `drop_linear_as`, `move_temp`, `val_name`, `match_drops`, `wild_drops`, `wild_drops_into`, `pattern_holds_linear`, `payload_tys` | 0 | 259 |
| `exhaust.rs` | 0 | 169: `check_exhaustive`, `covers`, `specialize`, `rows_by_variant`, `is_wild` | 0 |
| `expr.rs` | 362: `deref_lval`, `place_value`, `captures_live_at`, `closure_return`, `closure_ret_refs`, `closure_call_refs`, `root_place`, `rebase`, `end_clause_locals`, `join_clause_vals`, `body_frees`, `inner_frees`, `free_kills`, `change_kills`, `v_refs_result` | 1013: `expr`, `expr_with`, `elements`, `path_member`, `lit`, `name`, `is_sim_run`, `unit_variant`, `path_ref`, `binary`, `struct_lit`, `adt_by_path`, `if_expr`, `match_pattern`, `handled_effect`, `neg_literal`, `stmt`, `block`, `expr` | 1711 |
| `flow.rs` | 0 | 0 | 196 |
| `fnval.rs` | 0 | 0 | 1576 |
| `late.rs` | 446: `note_cap_values`, `cap_refs_now`, `note_cap_run`, `capturing`, `at_or_below`, `rebased`, `late_join`, `map_given`, `late_inner`, `late_changes`, `late_refs`, `val_late_refs`, `with_fn_refs`, `held_fn_refs`, `late_refs_into`, `late_ret_refs`, `closure_once_now`, `late_once` | 0 | 181 |
| `loops.rs` | 0 | 0 | 1183 |
| `mod.rs` | 297: `block_tail`, `flush`, `take_pending`, `restore_pending`, `hold`, `hold_later`, `hold_operand`, `hold_moved`, `take_held`, `leave_in_flight`, `take_held_here`, `hold_part`, `moves_value`, `hold_as`, `local_frame`, `pop_frame`, `push_frame`, `temp_root`, `open_stmt`, `close_stmt`, `closure_has`, `var_has`, `local_has`, `local_has_strict`, `may_be_linear` | 249: `err`, `show`, `unify`, `fn_joins`, `fn_covers`, `lookup_local`, `ty_has`, `ty_has_strict`, `has`, `ty_has_in`, `holds_refs`, `is_linear`, `has_unknown`, `has_on_abort`, `is_immovable`, `is_nonportable`, `is_copy`, `may_free`, `is_scalar`, `deref_ty` | 2589 |
| `oprefs.rs` | 39: `op_targets`, `resolve_op_refs` | 0 | 463 |
| `repeat.rs` | 0 | 0 | 440 |
| `roots.rs` | 0 | 0 | 62 |
| `stmt.rs` | 377: `settle_moves`, `finish_return`, `block`, `block_with`, `hold_out`, `use_held`, `hand_out`, `block_inner`, `end_frame`, `end_frames_above`, `local_place`, `drop_value`, `discard_block_value`, `loop_body`, `drop_replaced_uses`, `place_or_temp`, `consume` | 209: `check_int_lits`, `finish_int_ops`, `arith`, `bind_pattern`, `check_binders`, `walk`, `local_ty`, `base_name` | 1096 |
| `tasks.rs` | 0 | 0 | 761 |
| total | 2086 | 2286 | 14043 |

## Appendix C. Files

All paths are in
`SCRATCH/ir/`.

| File | Content |
| --- | --- |
| `design_minimal.md` | this document |
| `work/minimal/core_sketch.rs` | the Rust types of section 2.2, with stubs; `rustc --edition 2021 -W missing_docs core_sketch.rs` compiles it with no warning |
| `work/minimal/verdicts.py` | the verdict of each finding (imports `work/findings.py`); `python3 verdicts.py ..` prints the tables of section 5 |
| `work/minimal/appendix.py` | makes Appendix A and Appendix B from the data |
| `work/minimal/fnsizes.py`, `fnsizes.tsv` | the size of each function of `crates/weft-sema/src/body/` at `b073ea7` |
| `work/minimal/classify.py` | the disposition of each function (deleted, moved to the builder, kept) |
| `work/minimal/part*.md`, `appendix_*.md` | the parts of this document |
