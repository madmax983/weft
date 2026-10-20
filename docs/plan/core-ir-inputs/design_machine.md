# Core IR design: the machine IR

Status: design proposal (angle "machine"). Date: 2026-10-20. Source: commit `b073ea7`
of `/home/user/weft`, and commit `616f99c` of `/home/user/wt-core` (R3a fixes) for the
probes. Inputs: `docs/plan/core-ir-inputs/map_lowering.md`, `docs/plan/core-ir-inputs/root_causes.md`, `docs/plan/core-ir-inputs/semantics.md`, the
review reports of rounds 1 to 3, the spec, the facts schema, the ADRs and the proof
models.

The angle of this design: the IR copies the proof models. A body of the IR is a frame
of the interpreter and a block of the effects model. A statement of the IR is a node of
the B1 CFG model. Capabilities, continuations, frames and unwinding are explicit IR
forms. So the B6 link can later prove "IR to facts", not only "exec core to model".

All paths in this document are relative to `/home/user/weft` unless the text says
otherwise. `SCRATCH` is
`SCRATCH`.

## Contents

0. Summary
1. Principles, terms and pipeline
2. The IR as Rust types (task item 1)
3. Lowering rules: typed tree to IR, for each construct (task item 2)
4. Fact generation: the templates, the analysis, the invariants (task item 3)
5. Root-cause classes: what the design removes and what stays (task item 4)
6. The interpreter runs the IR; differential tests (task item 5)
7. Proof alignment: B1, B3, B4, the effects model, the B6 link (task item 6)
8. Migration plan and the diff gate (task item 7)
9. Risks, size and what stays out (task item 8)
- Appendix A: four new unsound findings (M1 to M4) from this design work
- Appendix B: files

---

## 0. Summary

**The problem.** Fact generation lowers the surface AST straight to facts. Each surface
form needs its own special case, and the special cases meet. Three review rounds found
about 20 soundness blockers each, almost all in fact generation (`docs/plan/core-ir-inputs/root_causes.md`:
180 unsound findings, 53 false positives).

**The proposal.** A core IR, `weft-ir`, between the typed tree and fact generation. Its
form copies the machines that the proofs and the interpreter use:

| Machine object | Interpreter | Proof model | IR form |
| --- | --- | --- | --- |
| frame | `CodeFrame`, one `Code` unit | effects `CFrame`, one `Block` | `Body` (function, test, closure, clause, handled body, scope body) |
| instruction | `Op` | B1 `Node { instr, succs }` | one `Stmt` or one `Term` = one fact node |
| local cell | slot cell, temporary cell | B1 local, effects slot | `LocalDecl` with `Live` and `Dead` |
| capability | handler id in `HEnv` | effects `env: Seq<HId>`, `Perform { cap }`, `Call { caps }` | `CapOperand`, `CapArgs`, a capability local of a handled body |
| continuation | `Clause { cont }` frame | effects `CFrame::k`, `Resume` | `LocalKind::Kont`, `TermKind::Resume` |
| unwinder | `unwind_frame`, `frame_values` | `step_unwind_abort`, `step_unwind_drop`, `step_unwind_pop` | cleanup blocks: `UnwindValue`, `UnwindKont`, `UnwindExit` |
| suspension point | `Perform`, `Call`, `Join`, `ScopeWait`, `Fork` | `is_susp`: `Call`, `Handle`, `Resume`, `Perform` | a terminator with an `unwind` block |
| `multi` copy | `copy_frames` | `Resume` of a `multi` `Kont` | a re-entry edge with a `Copy` node in the facts |

**The facts become a function of the IR.** Each IR instruction has one fact template
(section 4.1, generated from the sketch crate). A small analysis over the IR (one
fixpoint for each body and one over the call graph) gives the places, the function
values, the task sets and the summaries. Then one pass emits the facts. There are no
post-passes, no pending queue, no hidden variables and no re-lowering of loops.

**What it removes.** Of the 180 unsound findings of `docs/plan/core-ir-inputs/root_causes.md` (primary
cause only):

| Verdict | Unsound | False positives |
| --- | --- | --- |
| by construction: the IR has no form for the defect | 87 (48%) | 25 (47%) |
| by one rule: one function of the analysis or of the summary procedure gives it, so no construct can forget it | 64 (36%) | 14 (26%) |
| stays: spec, types, names, inference bounds, `rc` identity | 29 (16%) | 14 (26%) |

"By construction" holds the lowering-mechanics classes of `docs/plan/core-ir-inputs/root_causes.md` (TEMP,
TAIL, DROP, ORDER, ACCESS, DEREF, CALLS, ENV, INNER, SUSP, LOOP, VAL, POST, TYPES, and
TWO because the interpreter runs the IR: 83), plus MULTI (re-entry edges, 2) and two
PART findings (`Uninit` from the full type). "By one rule" holds most of the classes
that `docs/plan/core-ir-inputs/root_causes.md` calls "partly" (FNVAL, SUM, STORE, GEN, STATE, CAP): this
design takes the decisions that they need (a set-valued closure analysis with heap
slots, summary parts as queries, caller and callee frame roots, capabilities and
continuations as values). Section 5 lists each finding id with its verdict.

**New findings.** The machine view predicted four new unsound shapes. I wrote a probe
for each one. The checker accepts each probe at `b073ea7` and at `616f99c` (R3a), and
`weft run --oracle` faults on each one (Appendix A):

- M1: the code of a clause after `resume` runs after the handled body ends. The checker
  puts its changes at the perform node, before the body makes its value.
- M2: the result of `resume` does not point where the value of the handled body points.
- M3: a clause that does not resume returns a reference into an operation argument. The
  argument points into a local of the handled body. The unwinding frees that local
  before the `handle` gives the value.
- M4: the same as M3, with a local of a callee that performs the operation.

The design also removes the open findings of the sibling maps: N1 and N2 of
`docs/plan/core-ir-inputs/map_lowering.md` (results of code of a caller), and N1 to N4 of `docs/plan/core-ir-inputs/semantics.md`
(late reads of operands, `assert` with no abort edge). All of them are still open at
`616f99c` (I re-ran them).

**Decisions that this design takes** (the open choices of `docs/plan/core-ir-inputs/semantics.md`, section 12):

| Choice | Decision | Cost |
| --- | --- | --- |
| Read point of a place operand | at the operand (choice A, the MIR order) | `x + { x = 5; 1 }` gives 2, not 6 (p1); `design.md` states the order |
| Tail temporaries of a loop body | end at the end of each iteration | the interpreter frees them earlier (p24) |
| Unwind order in a frame | reverse declaration order (the interpreter today) | the effects model changes `max_slot` (section 7.4) |
| Clause frame and its fresh continuation | the clause frame first (the interpreter today) | the effects model changes `step_unwind_drop` (section 7.4) |
| Copy captures | `KeptCell`: the cell stays readable for the closure (the interpreter today) | stated in the IR, not a side table |
| Who runs the IR | the interpreter, through a new `compile_ir` to the existing stack code | `compile.rs` and the span-keyed exports go away |

**Size.** About 23 500 new lines of code (typed tree, IR types, builder, analysis,
summaries, fact generator, interpreter back end) and 3 000 lines of tests. About 21 000
lines go away (`body/`, `compile.rs`, the re-lowering loop of `infer.rs`). Section 9 has
the table and the risks.

**Migration.** Stages S0 to S8. The old and the new fact generation run side by side
(`--facts=old|ir|both`) from stage 4. A diff gate runs both on the corpus (129 files),
the examples (4), and 57 247 distinct probe files of rounds 1 to 3 and the oracle
sweeps. Each verdict that differs must have an oracle verdict or a reviewed reason
(section 8).

**A sketch that compiles.** The IR types, the verifier, the fact templates and a
worked example are a small Rust crate in
`SCRATCH/ir/work/machine/weft_ir_sketch/` (2 078 lines, `cargo test` and
`cargo clippy -D warnings` pass). Section 2 copies the types from it. Section 4.1
copies the template table that its test prints. Its test `each_relation_has_a_source`
checks that each of the 73 input relations of the spec has a source.

---

## 1. Principles, terms and pipeline

### 1.1 Principles

1. **One body is one frame.** The interpreter runs each function, test, closure, clause,
   handled body and scope body in a frame of its own (`CodeKind`). The IR has one body
   for each. A body has its own locals, its own storage, its own return slot `_0`, and
   its own cleanup chain. The rules of a frame end (the value leaves, then the locals
   end, then the tail temporaries end) are in one place: the builder of the body end.
2. **One instruction is one node.** Each statement and each terminator is one node of
   the facts, as each B1 node has one instruction. A terminator that hands control to
   another frame and back has a fixed list of extra nodes (`Phase`). So the order inside
   a node is the order of one instruction, and nothing else.
3. **Explicit machine objects.** A capability is a value: the handled body gets it as a
   parameter, a perform names it, a call passes the lexical environment. A
   continuation is a local of the clause frame. Unwinding is code: cleanup blocks. A
   `multi` copy is an edge with a copy node.
4. **The facts are a function of the IR.** One template for each instruction kind. One
   analysis gives the abstract values. One pass writes the facts. A new spec relation
   needs one new template entry, not a new call at 20 sites.
5. **The interpreter runs the IR.** The checker and the interpreter read the same
   decisions: order, moves, captures, temporaries, drops, unwind order.
6. **The IR does not decide what the analysis decides.** The IR holds what the source
   says after type inference and name resolution. It does not hold places, effect rows,
   or function value sets. So the IR is built once, before effect inference.

### 1.2 Terms

| Term | Meaning |
| --- | --- |
| typed tree (THIR) | the AST after name resolution and type inference: each expression has its final type, each call its callee, each name its binding |
| body | one frame: a function, a test, a closure, a clause, a handled body or a scope body |
| inner body | a closure, a clause, a handled body or a scope body |
| once-run frame | a handled body or a scope body: it runs exactly once each time its terminator runs |
| splice | the fact generator puts the nodes of a once-run frame into the component of its parent, with a call edge and return edges |
| run node | a node that runs another body through its summary: a call, a perform, a resume, a spawn, a cleanup node with `on abort` |
| summary | the effects of a body on what it can name from outside: its parameters, its environment, its capabilities, its result |
| cleanup chain | the cleanup blocks of a frame: they finish the values of the frame on an abort path and end at `UnwindExit` |
| abort destination | where an abort stops: the `handle` of a local handler, or the caller of the function (a caller's handler, a cancel, a timeout, a failed `assert`) |
| move path | a local or a part of a local with no `Deref` and no `Index`: the unit of moves, drops and fact variables |
| α | the place abstraction: it maps an IR place to the fact places (section 4.3) |

### 1.3 Pipeline

```text
source ──parse──► AST (with ExprId)
        ──resolve + typeck──► THIR: final types, callees, effect identities, argument order, integer types
        ──build──► IR: bodies, blocks, locals, cleanup chains (no effect rows, no places)
        ──verify──► IR well-formed (V1 to V12)
        ──analyze──► per body: abstract states (places, function values, tasks, init);
                     per call-graph SCC: summaries and effect rows (one monotone fixpoint)
        ──emit──► FnFacts (schema unchanged) ──► checker and spec (unchanged) ──► diagnostics
        ──compile_ir──► stack code ──► machine (frames, effects, unwinder, scheduler)
```

What changes and what stays:

| Part | Today | After |
| --- | --- | --- |
| `weft-syntax` | AST with spans | the AST gets an `ExprId` on each `Expr` (a counter in the parser) |
| `weft-sema` | `Lower` does inference and facts in one walk (`body/`, 19 097 lines) | `typeck` (inference only, from `Lower`) gives the THIR; `body/` goes away |
| `weft-sema::infer` | re-lowers bodies until signatures stop changing | runs the summary fixpoint over the IR; no re-lowering |
| `weft-ir` (new) | none | types, builder, verifier, printer, analysis, summaries, fact generator |
| `weft-facts` | schema | unchanged at first; stage 7 adds relations through ADR 0002 |
| `spec/weft.dl`, `weft-check` | rules | unchanged at first; stage 7 changes |
| `weft-interp` | `compile.rs` from the AST, span-keyed tables from sema (`by_value`, `arg_order`, `int_ops`) | `compile_ir` from the IR; `machine/` keeps its frames, effects and scheduler; the unwinder runs cleanup blocks (stage 3b) |
| proofs | link exec core to models | stage 8: the link includes the IR types and proves the embedding |

### 1.4 What the angle "machine" adds to a plain MIR

A MIR-like IR (the IR that `docs/plan/core-ir-inputs/root_causes.md` assumes) already gives explicit
temporaries, moves, drops and one call terminator. This design adds:

- **Frames as bodies with splices.** A handled body and a scope body are bodies, not
  blocks of the parent. The fact generator splices them back into the parent component,
  with the frame-end order of the machine. A plain MIR would inline them and copy the
  frame-end rules by hand, as `body/` does today.
- **Capability values.** A handled body gets its capability as a parameter. A closure
  records the capability environment where it is made. So "a closure leaves its
  handler" is "a value points into a dead frame" (W0301 and W0204 machinery).
- **Continuations as values and as calls.** `Resume` is a call of the continuation, with
  a summary of the rest of the handled body. The end of a `handle` runs the code of the
  clauses after their `resume`. This fixes M1 and M2.
- **The unwinder as code.** Each terminator that can abort names a cleanup block. The
  fact generator copies a cleanup chain for each abort destination. So `spared_at`,
  `unwound_at`, the abort value of a clause (M3, M4) and the unwind order follow from
  the CFG.
- **Re-entry edges for `multi`.** A `multi` suspension point gets an edge from the end of
  each copied frame back to its successor, through a copy node. This holds for a local
  handler and for a handler of a caller (OL-R2a).

The cost is more IR forms (17 terminators, 11 statements) and a summary for each
continuation. Section 9 weighs it.

---

## 2. The IR as Rust types

The types below are the crate `weft-ir` of the design. They are copied from the sketch
crate `SCRATCH/ir/work/machine/weft_ir_sketch/src/lib.rs`, which compiles with no
warnings under `cargo clippy -D warnings`. The ids are `u32` newtypes made by one macro:
`BodyId`, `BlockId`, `LocalId`, `FnId`, `ClosureId`, `HandlerId`, `ScopeId`, `TestId`,
`SpawnId`, `TyId`, `EffectId`, `OpIdx`, `FieldIdx`, `VariantIdx`, `SplitId`,
`CapEnvId`, `ExprId`. `Span`, `Origin` and `IntTy` are plain data. In the real crate,
`TyId` points into the type table of `typeck` (types with no inference variables and
no closure summaries), and the ids of items are the ids of `weft-sema`.

### 2.1 Design rules of the types

- **No right side can change memory or suspend.** `Rvalue` reads and builds values
  only. Each change of memory is an `Assign` destination, a `Drop`, a `Dead`, or a
  terminator. Each suspension is a terminator. So the order "uses, then changes" of a
  node (ADR 0002, `mod.rs:1` of `body/`) is the order of one instruction.
- **Each read of a place is an `Operand`** at exactly one statement or terminator. A
  read of a length is `Rvalue::Len` or `StmtKind::Bounds`. There is no pending queue.
- **`Deref` is a projection of its own.** A place through a reference, a `Box` or an
  `Rc` names the pointer local in its path. So a read of `(*r).f` uses `r`, and a place
  through `(*h)` of an `Rc` handle depends on `h`.
- **Moves are `Operand::Move`.** A move of a part is a `Move` of a projection. A
  closure takes a by-value capture with a `Move` operand in its environment aggregate.
- **Storage is explicit.** Each local except the parameters and `_0` gets `Live` before
  its first use and `Dead` on each path out of its scope, on normal paths and on
  cleanup paths. The verifier checks it (V4 to V6).
- **Drops are explicit.** `Drop(p)` drops the value at `p` on a normal path. A cleanup
  path has `UnwindValue(p, action)`, where the action is the `on abort` function, a
  drop, or a fault. The builder writes these from the types, after type inference.
- **Frames are bodies.** A `Handle` terminator names the handled body and the clause
  bodies. A `Scope` terminator names the scope body. A closure aggregate names the
  closure body. Each body has its own `_0`, its own storage and its own cleanup chain.
- **Capabilities.** `CapOperand::Local` is a capability value in a local: only a handled
  body has one (its parameter). `CapOperand::Row(E)` is the capability that the caller
  gives for effect `E`. `CapOperand::Root(E)` is a root handler. A call passes
  `CapArgs::Lexical(env)`: the callee takes the capability of each effect of its row
  from that static environment, as `Call { block, caps }` of the effects model. An
  `on abort` call passes `CapArgs::Root`.
- **The IR has no places, no rows and no function value sets.** These are results of the
  analysis (section 4.2). So the IR does not change while effect inference runs.

### 2.2 The types

```rust
// ---------------------------------------------------------------------------
// The program
// ---------------------------------------------------------------------------

/// A whole program: each body of each unit, and the declarations.
#[derive(Clone, Debug, Default)]
pub struct Program {
    /// The bodies. The index is the [`BodyId`].
    pub bodies: Vec<Body>,
    /// The function items. The index is the [`FnId`].
    pub fns: Vec<FnDecl>,
    /// The closure literals. The index is the [`ClosureId`].
    pub closures: Vec<ClosureDecl>,
    /// The `handle` expressions. The index is the [`HandlerId`].
    pub handlers: Vec<HandlerDecl>,
    /// The `scope` expressions. The index is the [`ScopeId`].
    pub scopes: Vec<ScopeDecl>,
    /// The spawn sites. The index is the [`SpawnId`].
    pub spawns: Vec<SpawnDecl>,
    /// The static capability environments. The index is the [`CapEnvId`].
    pub cap_envs: Vec<CapEnv>,
}

/// A function item.
#[derive(Clone, Debug)]
pub struct FnDecl {
    /// The path, for diagnostics.
    pub name: String,
    /// The body. `None` for an extern function.
    pub body: Option<BodyId>,
    /// The parameter types, in order.
    pub params: Vec<TyId>,
    /// The result type.
    pub ret: TyId,
    /// The number of type parameters.
    pub generics: u32,
    /// The stated row, if the signature states one. Inference adds the rest.
    pub stated_row: Option<Vec<EffectId>>,
    /// A function that the runtime gives a special meaning.
    pub intrinsic: Option<Intrinsic>,
}

/// A function with a run-time meaning that its signature does not show.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Intrinsic {
    /// `sim.run`: runs its block with the root handlers of a simulation.
    SimRun,
    /// `with_timeout`: runs its block once, and can fail at a deadline.
    WithTimeout,
}

/// A closure literal.
#[derive(Clone, Debug)]
pub struct ClosureDecl {
    /// The body of the closure.
    pub body: BodyId,
    /// The body that makes the closure.
    pub maker: BodyId,
    /// The captures, in the order of the fields of the environment.
    pub captures: Vec<Capture>,
    /// The closure is `once`: it moves a capture that is not plain data.
    pub once: bool,
    /// The capability environment where the closure is made. The closure performs
    /// through it (handlers are lexical). The analysis puts the capabilities that the
    /// closure can use into the abstract value of the closure, so a closure that
    /// leaves the body of its handler holds a dead capability (W0313).
    pub cap_env: CapEnvId,
}

/// One capture: one field of an environment.
#[derive(Clone, Debug)]
pub struct Capture {
    /// The captured place, in the maker body.
    pub source: Place,
    /// How the environment holds it.
    pub mode: CaptureMode,
}

/// How an environment holds a capture. The builder and the interpreter use one rule
/// (`capture_mode`), so they cannot disagree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CaptureMode {
    /// A reference to the cell of the variable. The end of the variable frees the cell.
    ByRef,
    /// The value moves into the environment when the closure is made.
    ByMove,
    /// A reference to the cell of a copy variable. The cell stays readable for the
    /// closure after the end of the variable (ADR 0003, `kept` in ADR 0006).
    KeptCell,
    /// A copy of a capability value.
    Cap,
    /// A copy of a continuation value.
    Kont,
}

/// A `handle` expression.
#[derive(Clone, Debug)]
pub struct HandlerDecl {
    /// The handled effect.
    pub effect: EffectId,
    /// The clause of each operation.
    pub clauses: Vec<(OpIdx, BodyId)>,
    /// The handled body.
    pub handled: BodyId,
    /// The body that holds the `handle` terminator.
    pub site: BodyId,
    /// The effect has a `multi` operation.
    pub multi: bool,
}

/// A `scope` expression.
#[derive(Clone, Debug)]
pub struct ScopeDecl {
    /// The scope body. Its first parameter is the scope capability.
    pub body: BodyId,
    /// The body that holds the `scope` terminator.
    pub site: BodyId,
}

/// A spawn site.
#[derive(Clone, Debug)]
pub struct SpawnDecl {
    /// The scope that joins the task.
    pub scope: Option<ScopeId>,
    /// The task is a branch of a `fork`: it runs on another thread.
    pub fork: bool,
    /// Where the task starts.
    pub origin: Origin,
}

/// A static capability environment. Handlers are lexical, so the builder knows the
/// capability of each effect at each point.
#[derive(Clone, Debug)]
pub struct CapEnv {
    /// The environment around this one.
    pub parent: Option<CapEnvId>,
    /// The capabilities that this environment adds.
    pub adds: Vec<(EffectId, CapOperand)>,
}

// ---------------------------------------------------------------------------
// Bodies
// ---------------------------------------------------------------------------

/// What a body is. Each kind is one `CodeKind` of the interpreter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BodyKind {
    /// A function body.
    Fn(FnId),
    /// A test body.
    Test(TestId),
    /// A closure body. Its first parameter is the environment.
    Closure(ClosureId),
    /// A handler clause. Its parameters are the environment, the operation
    /// arguments and the continuation.
    Clause(HandlerId, OpIdx),
    /// A handled body. Its first parameter is the environment.
    Handled(HandlerId),
    /// A scope body. Its parameters are the environment and the scope capability.
    Scope(ScopeId),
}

/// One body: one frame.
#[derive(Clone, Debug)]
pub struct Body {
    /// What the body is.
    pub kind: BodyKind,
    /// The lexical parent: the body that makes this body.
    pub parent: Option<BodyId>,
    /// The locals. The index is the [`LocalId`].
    pub locals: Vec<LocalDecl>,
    /// The return slot `_0`.
    pub ret: LocalId,
    /// The parameters, in order. An inner body has its environment first.
    pub params: Vec<LocalId>,
    /// The capability values that the frame gets as parameters. In Phase 1 only a
    /// handled body has one: the capability that its `handle` makes. The row
    /// capabilities of a function are [`CapOperand::Row`].
    pub caps: Vec<(EffectId, LocalId)>,
    /// The continuation of a clause and its mode (`multi`).
    pub kont: Option<(LocalId, bool)>,
    /// The blocks. The index is the [`BlockId`].
    pub blocks: Vec<Block>,
    /// The first block.
    pub entry: BlockId,
    /// The block that ends the unwinding of this frame ([`TermKind::UnwindExit`]).
    pub unwind_exit: BlockId,
    /// The capability environment at the entry.
    pub cap_env: CapEnvId,
    /// Where the body comes from.
    pub origin: Origin,
}

/// A local.
#[derive(Clone, Debug)]
pub struct LocalDecl {
    /// The final type.
    pub ty: TyId,
    /// What the local is.
    pub kind: LocalKind,
    /// The source name, if one exists.
    pub name: Option<String>,
    /// The properties of the type. The builder computes them once, from the final type.
    pub props: Props,
    /// The value of the local is built for one call, in place (`Box.new(S { .. })`).
    /// A move of it into that call is not a move of a `!Move` value (W0604).
    pub in_place: bool,
    /// Where the local comes from.
    pub origin: Origin,
}

/// What a local is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LocalKind {
    /// The return slot `_0`.
    Return,
    /// A parameter of a function or a clause.
    Param(u32),
    /// The environment of an inner body.
    Env,
    /// A variable of the source.
    User,
    /// A temporary.
    Temp(TempKind),
    /// The iterator of a `for` loop.
    Iterator,
    /// A capability value of an effect. A handled body gets the new one as a parameter.
    Cap(EffectId),
    /// A continuation (`resume`). The flag is `multi`.
    Kont(bool),
    /// The capability of a scope (`s` in `scope { s => .. }`).
    ScopeCap,
    /// The result of a task that has no handle. The end of its scope drops it.
    TaskResult(SpawnId),
}

/// Why a temporary exists. Diagnostics use it to name the value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TempKind {
    /// An operand of a call, an operator or an aggregate.
    Operand,
    /// The callee of a call of a function value.
    Callee,
    /// A method receiver.
    Receiver,
    /// The scrutinee of a `match`.
    Scrutinee,
    /// A value that a borrow (`&e`) puts into a cell.
    Borrowed,
    /// A value that nothing keeps: the builder drops it.
    Discarded,
    /// The value of a branch, an arm, a block or a frame body.
    Value,
}

/// The properties of a type that the facts need. One function computes them
/// (`props.rs`), from the final type.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Props {
    /// The value is copied when it is read.
    pub copy: bool,
    /// The value is linear.
    pub linear: bool,
    /// The type declares `on abort` for each linear part.
    pub on_abort: bool,
    /// The value is not `many`.
    pub once: bool,
    /// The type is `!Move`.
    pub immovable: bool,
    /// The value cannot cross threads.
    pub nonportable: bool,
    /// The value is `@ uniq`.
    pub uniq: bool,
    /// The value can be a function value.
    pub callable: bool,
    /// The type mentions a type parameter.
    pub generic: bool,
}

// ---------------------------------------------------------------------------
// Places and operands
// ---------------------------------------------------------------------------

/// A place: a local and projections.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Place {
    /// The local.
    pub local: LocalId,
    /// The projections, from the local outwards.
    pub proj: Vec<Proj>,
}

/// One projection. Each one is one step of the place model (ADR 0003), except
/// [`Proj::Deref`] of a reference, which goes to the places that the reference
/// points into.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Proj {
    /// Follow a pointer.
    Deref(DerefKind),
    /// A field of a struct or a part of a tuple. A stable step.
    Field(FieldIdx),
    /// The payload of a variant. An unstable step. Valid only after a test of the variant.
    Variant(VariantIdx),
    /// An element. The stability comes from the type (`Vec`: unstable; array: stable).
    /// The bounds check is a statement before it ([`StmtKind::Bounds`]).
    Index(LocalId),
    /// All elements (`&v[]`).
    Elems,
    /// One side of a split.
    Split(SplitId, Side),
}

/// A pointer kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DerefKind {
    /// A reference: the place moves to the places that the reference points into.
    Ref,
    /// A `Box`: an unstable step below the owner.
    Box,
    /// An `Rc`: the `rc` group root of the inner type. The handle stays a dependence.
    Rc,
}

/// A side of a split.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Side {
    /// `[..k]`.
    Left,
    /// `[k..]`.
    Right,
}

/// An operand. Each read of a place is an operand at one statement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operand {
    /// Read and copy. Only for a type with [`Props::copy`].
    Copy(Place),
    /// Read and move. The place has no value after it.
    Move(Place),
    /// A constant.
    Const(Const),
}

/// A constant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Const {
    /// `()`.
    Unit,
    /// A boolean.
    Bool(bool),
    /// An integer with its type.
    Int(i128, IntTy),
    /// A string.
    Str(String),
    /// A duration in milliseconds.
    Duration(u64),
    /// A function item as a value, with its type arguments.
    Fn(FnId, Vec<TyId>),
}

/// The right side of an assignment. No right side can change memory or suspend.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rvalue {
    /// An operand.
    Use(Operand),
    /// A reference to a place.
    Ref(Place),
    /// A binary operator. An integer result is checked against its type: a fault
    /// stops the run.
    Binary(BinOp, Option<IntTy>, Operand, Operand),
    /// A unary operator.
    Unary(UnOp, Option<IntTy>, Operand),
    /// A tuple, an array, a struct, a variant or a closure.
    Aggregate(AggKind, Vec<Operand>),
    /// The length of a buffer. It reads the buffer.
    Len(Place),
    /// The variant of an enum value. It reads the tag.
    Discriminant(Place),
    /// A string interpolation: the text of each operand, joined.
    Concat(Vec<Operand>),
    /// A new iterator over the elements of a place, or over a range.
    Iter(IterSource),
}

/// A binary operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    /// `+`.
    Add,
    /// `-`.
    Sub,
    /// `*`.
    Mul,
    /// `/`.
    Div,
    /// `%`.
    Rem,
    /// `==`.
    Eq,
    /// `!=`.
    Ne,
    /// `<`.
    Lt,
    /// `<=`.
    Le,
    /// `>`.
    Gt,
    /// `>=`.
    Ge,
}

/// A unary operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    /// `-x`.
    Neg,
    /// `!x`.
    Not,
}

/// What an aggregate builds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AggKind {
    /// A tuple.
    Tuple,
    /// A fixed array.
    Array,
    /// A new `Vec` with these elements.
    Vec,
    /// A struct. The operands are in the order of the fields of the struct.
    Struct(TyId),
    /// A variant.
    Variant(TyId, VariantIdx),
    /// A closure. The operands are the fields of its environment.
    Closure(ClosureId),
}

/// The source of an iterator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IterSource {
    /// The elements of a place. A scalar element is a copy; another element is a
    /// reference into the buffer.
    Elems(Place),
    /// A range `lo..hi`.
    Range(Operand, Operand),
}

// ---------------------------------------------------------------------------
// Capabilities
// ---------------------------------------------------------------------------

/// The capability of a perform or of a call.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CapOperand {
    /// A capability value in a local: the parameter that a handled body gets.
    Local(Place),
    /// The capability of the effect that the caller of the function gives: a
    /// parameter of the row. The row is inferred, so these parameters are not
    /// locals. The effects model numbers them (`Sig::caps`).
    Row(EffectId),
    /// A root handler of the runtime, or of `sim.run`.
    Root(EffectId),
}

/// The capabilities that a call gives to its callee.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CapArgs {
    /// The lexical environment at the call. The callee gets the capability of each
    /// effect of its row from it.
    Lexical(CapEnvId),
    /// The root handlers only. An `on abort` function gets these.
    Root,
}

// ---------------------------------------------------------------------------
// Statements and terminators
// ---------------------------------------------------------------------------

/// A basic block.
#[derive(Clone, Debug)]
pub struct Block {
    /// The statements.
    pub stmts: Vec<Stmt>,
    /// The terminator.
    pub term: Term,
    /// The block is on a cleanup path. Only an abort edge enters a cleanup block.
    pub cleanup: bool,
}

/// A statement. It cannot suspend and has one successor.
#[derive(Clone, Debug)]
pub struct Stmt {
    /// What the statement does.
    pub kind: StmtKind,
    /// Where it comes from.
    pub origin: Origin,
}

/// What a statement does.
#[derive(Clone, Debug)]
pub enum StmtKind {
    /// The local gets a new cell. It has no value yet.
    Live(LocalId),
    /// The cell of the local ends. A value that is still in it goes away.
    Dead(LocalId),
    /// The place gets a value. The old value has no drop to do: the builder writes a
    /// [`StmtKind::Drop`] before it if the old value needs one.
    Assign(Place, Rvalue),
    /// The value at the place goes away on a normal path. A part that a move took
    /// has nothing to drop.
    Drop(Place),
    /// A linear value is finished: a destructuring of a linear struct.
    Consume(Place),
    /// The place has no value from here (`let x: T`, a place field of a value
    /// that is built in place).
    Uninit(Place),
    /// A check of an index against the length of a buffer. A failure is a fault.
    Bounds(Place, Operand),
    /// A place in statement position: the place is named and not read.
    Mention(Place),
    /// `print`: reads each operand.
    Print(Vec<Operand>),
    /// The unwinder finishes the value at the place: it runs its `on abort`, or drops
    /// it. Only on a cleanup path.
    UnwindValue(Place, UnwindAction),
    /// The unwinder aborts a fresh continuation that the frame holds. Its frames
    /// unwind next. Only on a cleanup path.
    UnwindKont(LocalId),
}

/// What the unwinder does with one value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnwindAction {
    /// Run this `on abort` function with the root handlers.
    OnAbort(FnId),
    /// Drop the value: it has no linear part.
    Drop,
    /// The value is linear and has no `on abort`: a fault. W0602 rejects each program
    /// that can reach it.
    Fault,
}

/// A terminator.
#[derive(Clone, Debug)]
pub struct Term {
    /// What the terminator does.
    pub kind: TermKind,
    /// Where it comes from.
    pub origin: Origin,
}

/// What a terminator does. A terminator with an `unwind` block can abort its frame.
#[derive(Clone, Debug)]
pub enum TermKind {
    /// Go to a block.
    Goto(BlockId),
    /// Go to the block of the value of the operand.
    Switch {
        /// The tested value: a `bool`, an integer or a discriminant.
        on: Operand,
        /// The block for each value.
        arms: Vec<(u128, BlockId)>,
        /// The block for each other value.
        otherwise: BlockId,
    },
    /// The frame ends normally. `_0` holds the value.
    Return,
    /// The unwinding leaves this frame. Only in [`Body::unwind_exit`].
    UnwindExit,
    /// Control cannot come here.
    Unreachable,
    /// A call of a function item or of a function value.
    Call {
        /// What the call runs.
        callee: Callee,
        /// The arguments, in the order of the parameters.
        args: Vec<Operand>,
        /// The place that gets the result.
        dest: Place,
        /// The capabilities that the callee gets.
        caps: CapArgs,
        /// The next block. `None` if the callee never returns.
        next: Option<BlockId>,
        /// The cleanup block of an abort.
        unwind: Option<BlockId>,
    },
    /// A perform of an operation.
    Perform {
        /// The capability.
        cap: CapOperand,
        /// The operation.
        op: OpIdx,
        /// The arguments, in the order of the parameters.
        args: Vec<Operand>,
        /// The place that gets the result: the value of a `resume`.
        dest: Place,
        /// The next block.
        next: BlockId,
        /// The cleanup block of an abort.
        unwind: Option<BlockId>,
    },
    /// A `resume`: a call of the continuation. It runs the rest of the handled body.
    Resume {
        /// The continuation.
        kont: Place,
        /// The value for the perform.
        arg: Operand,
        /// The place that gets the value of the handled body.
        dest: Place,
        /// The next block.
        next: BlockId,
        /// The cleanup block of an abort.
        unwind: Option<BlockId>,
    },
    /// A `handle`: make the capability, run the handled body in a new frame.
    Handle {
        /// The handler.
        handler: HandlerId,
        /// The environment of the clauses.
        clause_env: Operand,
        /// The environment of the handled body.
        body_env: Operand,
        /// The place that gets the value of the `handle`.
        dest: Place,
        /// The next block: after the body or after a clause that did not resume.
        next: BlockId,
        /// The cleanup block of an abort that goes past this handler.
        unwind: Option<BlockId>,
    },
    /// A `scope`: run the scope body in a new frame.
    Scope {
        /// The scope.
        scope: ScopeId,
        /// The environment of the body.
        env: Operand,
        /// The place that gets the value.
        dest: Place,
        /// The next block.
        next: BlockId,
        /// The cleanup block of an abort.
        unwind: Option<BlockId>,
    },
    /// Wait for the tasks of a scope. Then raise the failure of a task, once.
    /// The last terminator of a scope body before its drops.
    ScopeWait {
        /// The scope capability.
        scope: Place,
        /// The results of the tasks with no handle. The wait drops them.
        orphans: Vec<LocalId>,
        /// The next block.
        next: BlockId,
        /// The cleanup block of an abort.
        unwind: Option<BlockId>,
    },
    /// Start a task in a scope. A spawn does not suspend the task that spawns.
    Spawn {
        /// The spawn site.
        site: SpawnId,
        /// The scope capability.
        scope: Operand,
        /// The closure or function value that the task runs. It moves into the task.
        task: Operand,
        /// The place that gets the task handle. `None`: the scope keeps the task.
        dest: Option<Place>,
        /// The next block.
        next: BlockId,
    },
    /// Wait for a task and take its result. It consumes the handle.
    Join {
        /// The handle.
        task: Operand,
        /// The place that gets the result.
        dest: Place,
        /// The next block.
        next: BlockId,
        /// The cleanup block of an abort.
        unwind: Option<BlockId>,
    },
    /// Let a task run on. It consumes the handle and drops the result.
    Detach {
        /// The handle.
        task: Operand,
        /// The next block.
        next: BlockId,
    },
    /// Run the branches as tasks on other threads and wait for all of them.
    Fork {
        /// The spawn site of each branch.
        sites: Vec<SpawnId>,
        /// The branch values. Each one moves into its task.
        branches: Vec<Operand>,
        /// The place that gets the tuple of the results.
        dest: Place,
        /// The next block.
        next: BlockId,
        /// The cleanup block of an abort.
        unwind: Option<BlockId>,
    },
    /// `assert`: a false condition aborts the task.
    Assert {
        /// The condition.
        cond: Operand,
        /// The next block.
        next: BlockId,
        /// The cleanup block of the abort.
        unwind: Option<BlockId>,
    },
    /// Advance an iterator: the next element, or the exit.
    IterNext {
        /// The iterator.
        iter: Place,
        /// The place that gets the element.
        dest: Place,
        /// The block for an element.
        next: BlockId,
        /// The block after the last element.
        done: BlockId,
    },
}

/// What a call runs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Callee {
    /// A function item with type arguments.
    Fn(FnId, Vec<TyId>),
    /// A function value: a closure, a function item, a function parameter, or a
    /// value that the body does not follow.
    Value(Operand),
}

impl TermKind {
    /// Returns the blocks of the normal successors: not the cleanup block.
    pub fn normal_successors(&self) -> Vec<BlockId> {
        match self {
            Self::Goto(b) => vec![*b],
            Self::Switch { arms, otherwise, .. } => {
                let mut v: Vec<BlockId> = arms.iter().map(|(_, b)| *b).collect();
                v.push(*otherwise);
                v
            }
            Self::Return | Self::UnwindExit | Self::Unreachable => Vec::new(),
            Self::Call { next, .. } => next.iter().copied().collect(),
            Self::Perform { next, .. }
            | Self::Resume { next, .. }
            | Self::Handle { next, .. }
            | Self::Scope { next, .. }
            | Self::ScopeWait { next, .. }
            | Self::Spawn { next, .. }
            | Self::Join { next, .. }
            | Self::Detach { next, .. }
            | Self::Fork { next, .. }
            | Self::Assert { next, .. } => vec![*next],
            Self::IterNext { next, done, .. } => vec![*next, *done],
        }
    }

    /// Returns the cleanup block of an abort, if the terminator can abort.
    pub const fn unwind(&self) -> Option<BlockId> {
        match self {
            Self::Call { unwind, .. }
            | Self::Perform { unwind, .. }
            | Self::Resume { unwind, .. }
            | Self::Handle { unwind, .. }
            | Self::Scope { unwind, .. }
            | Self::ScopeWait { unwind, .. }
            | Self::Join { unwind, .. }
            | Self::Fork { unwind, .. }
            | Self::Assert { unwind, .. } => *unwind,
            Self::Goto(_)
            | Self::Switch { .. }
            | Self::Return
            | Self::UnwindExit
            | Self::Unreachable
            | Self::Spawn { .. }
            | Self::Detach { .. }
            | Self::IterNext { .. } => None,
        }
    }

    /// Returns true if the terminator can suspend the frame: another frame runs
    /// before it goes on. These are the suspension points of the effects model.
    pub const fn suspends(&self) -> bool {
        matches!(
            self,
            Self::Call { .. }
                | Self::Perform { .. }
                | Self::Resume { .. }
                | Self::Handle { .. }
                | Self::Scope { .. }
                | Self::ScopeWait { .. }
                | Self::Join { .. }
                | Self::Fork { .. }
        )
    }
}
```

### 2.3 Well-formedness rules

The builder makes bodies that obey these rules. `weft_ir::verify` checks them in each
test and in debug builds, and the diff gate runs it on each input (section 8). The
sketch implements V1 to V7 (`verify.rs`, 291 lines); three tests show that it finds a
missing `Dead` and a normal edge into a cleanup block.

| Rule | Statement | Why the facts need it |
| --- | --- | --- |
| V1 | Each successor is a block of the body. | A1 (path cover) |
| V2 | A normal edge goes from a normal block to a normal block. An `unwind` edge goes to a cleanup block. A cleanup block goes only to cleanup blocks. | the abort paths are separate from the normal paths (D3 versus `unwound_at`) |
| V3 | A cleanup block ends with `Goto` to a cleanup block or with `UnwindExit`. No `Return` is on a cleanup path. | each abort path ends at the frame boundary of the unwinder |
| V4 | Each use of a local is on a path where the local has a cell on each path from the entry (`Live` before the use, no `Dead` between). | A6 (`bound_before_use`) for each component, not only the function component |
| V5 | No `Live` of a local that has a cell. | one binding for each cell (B1 `locals`) |
| V6 | At `Return` and at `UnwindExit`, only the parameters, `_0`, the capability parameters and the continuation have a cell. | D3 (each normal end has `scope_end`), C4 (each free has a node) |
| V7 | `UnwindExit` is the only terminator of `Body::unwind_exit`, and only there. | one frame boundary for the unwinder |
| V8 | Each projection fits the type: `Deref` only on a reference, a `Box` or an `Rc`; `Field` in range; `Variant` only in a block that a `Switch` on the discriminant of the same place dominates; `Index` with a `usize` local; `Split` only on a slice. | B2 (typed stability), B3 (variant steps) |
| V9 | `Copy` only for a type with `Props::copy`; `Move` only for other types; no `Move` through `Deref(Ref)` (W0303 is a builder diagnostic). | D1 (each move is a `moved_at`), C4 |
| V10 | Each terminator that can suspend has an `unwind` block, except a `Call` of a callee that the builder knows cannot abort (an extern function with no row, a function item whose stated row is empty and that has no `assert`); the analysis checks the last case after inference. | A1 for abort paths, D4 |
| V11 | A `CapOperand::Local` names a capability local of the body. `Resume` names a continuation local of a clause, or a continuation field of an environment. `Row(E)` appears only in a function, a test or a closure. | the capability and the continuation are values of one frame |
| V12 | A temporary has its `Live` and its `Dead` in one statement scope, except a temporary of the tail of a frame body: it ends after `_0` gets the value. | C2 (holder cover), the frame-end order |

### 2.4 Text form

`weft ir FILE [FUNCTION]` prints the IR in this form. Each local is `_n`. A block is
`bbN`, and `(cleanup)` marks a cleanup block. Each terminator shows its normal successor
and its cleanup block.

### 2.5 Worked example: probe M3

Probe `SCRATCH/ir/work/machine/m8_abort_value_into_body.wf` (finding M3, Appendix A):

```weft
effect Pick { fn pick(v: &Vec<u64>) -> &u64 }

fn main() {
    let r = handle Pick {
        fn pick(v) { &v[0] }
    } in {
        let w = Vec.new()
        w.push(3)
        pick(&w)
    }
    print(r)
}
```

The IR, built by hand in `example.rs` of the sketch and printed by its printer. The
verifier accepts the three bodies (test `the_example_verifies`):

```text
body main (Fn(FnId(0)))
    let _0: Return
    let _1: User `r`
    let _2: Temp(Operand) `body env`
    let _3: Temp(Operand) `clause env`
  bb0:
    Live(_1)
    Live(_2)
    _2 = Tuple()
    Live(_3)
    _3 = Tuple()
    _1 = handle h0(clauses: move _3, body: move _2) -> [next: bb1, unwind: Some(2)]
  bb1:
    Dead(_3)
    Dead(_2)
    Print(copy _1)
    Dead(_1)
    _0 = const Unit
    Return
  bb2 (cleanup):
    Dead(_3)
    Dead(_2)
    Dead(_1)
    Goto(BlockId(3))
  bb3 (cleanup):
    UnwindExit
body handled (Handled(HandlerId(0)))
    let _0: Return
    let _1: Env
    let _2: Cap(EffectId(0)) `Pick`
    let _3: User `w`
    let _4: Temp(Receiver)
    let _5: Temp(Discarded)
    let _6: Temp(Operand)
  bb0:
    Live(_3)
    _3 = call Fn(FnId(1), [TyId(1)])() -> [next: Some(1), unwind: None]
  bb1:
    Live(_4)
    _4 = &_3
    Live(_5)
    _5 = call Fn(FnId(2), [TyId(1)])(move _4, const Int(3, U64)) -> [next: Some(2), unwind: None]
  bb2:
    Dead(_5)
    Dead(_4)
    Live(_6)
    _6 = &_3
    _0 = perform Local(Place { local: LocalId(2), proj: [] }).0(move _6) -> [next: bb3, unwind: Some(4)]
  bb3:
    Drop(_3)
    Dead(_3)
    Dead(_6)
    Return
  bb4 (cleanup):
    Dead(_6)
    UnwindValue(_3, Drop)
    Dead(_3)
    Goto(BlockId(5))
  bb5 (cleanup):
    UnwindExit
body clause (Clause(HandlerId(0), OpIdx(0)))
    let _0: Return
    let _1: Env
    let _2: Param(0) `v`
    let _3: Kont(false) `resume`
    let _4: Temp(Operand)
  bb0:
    Live(_4)
    _4 = const Int(0, Usize)
    Bounds((*_2), copy _4)
    _0 = &(*_2)[_4]
    Dead(_4)
    Return
  bb1 (cleanup):
    UnwindKont(_3)
    UnwindExit
.
```

Three points of the machine view show in this example:

- The handled body is a body of its own. The tail `pick(&w)` writes `_0`. Then the
  local `w` ends, and then the tail temporary `_6` (`bb3`): the order of `DropSlots` and
  `Return` in the interpreter. The cleanup block `bb4` uses the order of the unwinder:
  the temporaries first, then the locals.
- The perform names its capability: `Local(_2)`, the parameter that the `handle` gives
  to the handled body.
- The perform has a cleanup block `bb4`. On an abort, the unwinder finishes `w`
  (`UnwindValue(_3, Drop)`) and leaves the frame (`bb5`). Section 4.6 shows how the
  facts of this abort path give W0301 at `print(r)`.

---

## 3. Lowering rules: typed tree to IR

The builder `weft_ir::build` lowers the THIR of one item (a function or a test, with
the closures, clauses, handled bodies and scope bodies inside it) to bodies. It runs
once, after type inference, before effect inference. Section 3.1 gives the general
rules. Sections 3.2 to 3.34 give the rule for each construct of `docs/plan/core-ir-inputs/map_lowering.md`,
section 2 (the map number is in brackets). Section 3.35 lists the diagnostics of the
builder. Each rule names the special cases of the current lowering that go away, with
the review ids that made them.

Notation: `t`, `t1` are new temporaries. `Live(t); t = rv` is written `t := rv`. A
terminator is written `dest = kind(args) -> [next, unwind: cleanup]`. `C(scope)` is the
cleanup block of the current scope stack (section 3.1.6).

### 3.1 General rules

#### 3.1.1 Destinations and operands

The builder has three entry points for an expression `e`:

- `into(e, dest)`: write the value of `e` into the place `dest`. Each construct that
  gives a value (a block tail, a branch, an arm, a `handle`, a `scope`, a call) uses it.
  So the tail value of each frame and each branch is an assignment of an operand: a
  move if the type is not plain data, a copy else (class TAIL).
- `operand(e)`: evaluate `e` now and give an `Operand`. **Choice A of
  `docs/plan/core-ir-inputs/semantics.md` 2.2: an operand is read where it is written.** A place of a copy
  type gives `t := copy p`. A place of another type gives `t := move p` in a move
  position (an argument, a field value, a `let` value), and `t := &p` in a read
  position (a comparison, `print`). A value gives a temporary. A constant stays a
  constant. A place operand may skip the temporary only if no later operand of the
  same construct can run code (a later operand is a constant or a plain local): then
  the order cannot show.
- `place(e)`: evaluate a place expression and give a `Place`. The index expressions
  run now, in order, into temporaries (`Index(t)`). A value that is not a place goes
  into a temporary of the current statement (`place_or_temp`, as `compile.rs:1115`).

The order inside one construct is the order of `docs/plan/core-ir-inputs/semantics.md`, section 2.1, with
three changes that choice A makes: a place operand of a binary operator, of `print`
and the base of an index are read where they are written (N1 to N3 of the semantics
map go away). The other exceptions stay and are now written once in the builder:
named arguments in parameter order (ADR 0009), the value before the target in an
assignment, a positional struct in field order, and a method receiver read at the
call.

#### 3.1.2 Scopes

The builder keeps a stack of scopes:

| Scope | Opened by | Holds | Closed by |
| --- | --- | --- | --- |
| `Frame` | each body | the tail temporaries of the body, the parameters | the frame end (3.1.4) |
| `Block` | each block `{ }` | its `let` locals and the patterns of `match` arms | the end of the block, or a jump out of it |
| `Stmt` | each statement that is not a tail; the condition of `while`; each loop body tail | the temporaries of the statement | the end of the statement |
| `Loop` | `while`, `loop`, `for` | the iterator of `for`; the `break` and `continue` targets | the end of the loop |
| `Fence` | a handled body, a clause, a scope body | nothing; `break`, `continue` and `return` cannot cross it (W0315) | the end of the body |

A temporary goes into the innermost `Stmt` scope. A block tail is not a statement, so
its temporaries go into the scope around the block (the semantics of the interpreter,
`docs/plan/core-ir-inputs/semantics.md` 4.2). The temporaries of the tail of a loop body go into a `Stmt` scope
of their own: they end at the end of each iteration (decision N5).

#### 3.1.3 Drop elaboration

At each exit of a scope, on each path, the builder writes for each local of the scope,
in reverse declaration order: `Drop(l)` if the type of `l` is not plain data, then
`Dead(l)`. A local whose value moved has nothing to drop: the interpreter skips a moved
value, and the facts see the move (`moved_at`) before the end (`scope_end`). The
builder does not need an init analysis for this.

The builder also writes a `Drop` at these points:

- before an `Assign` that replaces a value that is not plain data (`Drop(p); p = v`: the
  old value of a place goes away);
- for a value that nothing keeps: an expression statement, `let _ = e`, a `_` pattern
  over a part, a discarded block tail, the branch of an `if` with no `else`;
- for the results of tasks with no handle, at the end of their scope
  (`ScopeWait::orphans`).

A linear value at a `Drop` is the error that W0601 reports: the facts see it as
`scope_end` of a live linear value. So the forms of RT14 (`let _`, a wildcard part,
`print`, `match _`, an overwrite) and V057 (a `T` moved into a holder that goes away)
are one rule.

#### 3.1.4 The end of a frame

Each body ends in the order of the machine (`docs/plan/core-ir-inputs/semantics.md` 5.3):

```text
_0 = <tail operand>            // the value leaves into the return slot
ScopeWait(s) -> [next, C]      // only a scope body: wait for the tasks
Drop/Dead of the block locals  // reverse declaration order
Dead of the tail temporaries   // they end after the value left
Return
```

A reference in `_0` into a local or a tail temporary of the frame is therefore a
reference into a dead cell at the node that receives the value (`Ret` of a call, or
`Exit` of a spliced frame, section 4.4). This is the rule that O3-2, O3-3 and F3-7 needed, written once for
each frame kind.

#### 3.1.5 Jumps

`break`, `continue` and `return` exit each scope between the jump and its target, in
order from the innermost: the drops and `Dead` of 3.1.3 for each one, then `Goto`. A
value on its way (an operand in a temporary of an open statement) is a temporary of an
exited `Stmt` scope, so it gets its `Drop` and `Dead` there (ADR 0007: "a `return` in a
later operand leaves the value"; OL-3c). A `Fence` scope stops the search: W0315 for a
jump out of a handled body, a clause or a scope body. The builder reports W0315 (today
sema reports it).

#### 3.1.6 Cleanup chains

Each terminator that can abort gets `unwind: C`. `C` is the cleanup chain of the frame
at that point. It finishes each value that has a cell there:

```text
cleanup:     UnwindValue(t_newest, action) ; Dead(t_newest) ; ...   // live temporaries, newest first
             UnwindValue(l_highest, action) ; Dead(l_highest) ; ... // live locals, highest index first
             Goto(unwind_exit)
unwind_exit: UnwindExit
```

This is the order of the unwinder of the interpreter (`frame_values`, `effects.rs:424`):
the operand stack and the temporaries newest first, then the slots from the highest,
across all scopes of the frame. The IR states it, so the interpreter, the facts and the
effects model use one order (decisions N6, N7 of the semantics map). Two chains with the
same suffix share the blocks of the suffix, as the drop trees of MIR do.

`action(l)` comes from the type:

| Type of `l` | Action |
| --- | --- |
| no linear part | `Drop` |
| linear, and the type declares `on abort = f` | `OnAbort(f)` |
| linear, no `on abort` on the type, each linear part has one | one `UnwindValue` for each linear part, in field order (`extract_linear`, `effects.rs:455`) |
| a linear part with no `on abort` | `Fault`: W0602 rejects each program that reaches it |

A clause body has `UnwindKont(k)` at the end of its chain: if the clause aborts while
its continuation is fresh, the frames of the continuation unwind next (`do_drop` of the
effects model). The chain of a handled body and of a scope body ends at their own
`UnwindExit`; the fact generator connects it to the parent (section 4.4).

#### 3.1.7 Captures

One function, `capture_mode(var, body)`, decides how a closure holds each captured
variable. The interpreter uses the same function through the IR (no `by_value` side
table):

- `ByMove` if the body (or an inner closure of it) moves the variable, or moves a part
  of it (ADR 0003, R2b OR2).
- `KeptCell` if the variable is plain data and the body does not move it.
- `ByRef` else.
- `Cap` and `Kont` for capability and continuation values.

A clause, a handled body and a scope body capture by reference only (`ByRef` or
`KeptCell`), as the interpreter does (`Handle`, `Scope` in `exec.rs`). Their environment
aggregate is built at their terminator.

### 3.2 Function body, parameters, exit [2.1]

```text
body f (Fn):  params _1.._n (Live at entry), _0
  bb0: <body block into _0>; <frame end>; Return
  unwind_exit: UnwindExit
```

- A by-value parameter is a local of the frame. A reference parameter is a local of
  reference type: a place through it is `(*_i).proj`.
- The row capabilities are `CapOperand::Row(E)`. The effects model numbers them in the
  order of the inferred row (section 7.4).
- **Goes away:** the second `Param` root for a by-value parameter that holds references
  (`stmt.rs:47`) becomes α of `Deref` (section 4.3); "the temporaries of the tail of the
  body get no `scope_end`" (`stmt.rs:110`) becomes the frame end of 3.1.4;
  `check_returned_refs` after `op_refs` (S5a 1d, S079, S092) has no order to respect
  (section 4.2: no post-passes).
- A test body is a `Test` body with no parameters.

### 3.3 `let` and patterns [2.2]

```text
let x = e        =>  Live(x); <into(e, x)>
let x: T         =>  Live(x); Uninit(x)
let (a, b) = e   =>  t := <e>; Live(a); a = move t.0; Live(b); b = move t.1   (copy for plain data)
let S(a, b) = s  =>  Live(a); a = move s.0; Live(b); b = move s.1; Consume(s)  (a linear struct)
let _ = e        =>  t := <e>; Drop(t); Dead(t)
```

- The binding is one `Assign` node, after the nodes of the value. A call result binds at
  the return node of the call (section 4.1), so no node both invalidates and rebinds (A5).
- A part that holds references gets its places from α of the part (section 4.3), not
  from `held_refs` (`stmt.rs:1496`).
- **Goes away:** `assign_local` (a function that does eight things, map 2.2), the cell
  root of a reference local, the one-place instance logic at the binding
  (`point_local`), `wild_drops` and `drop_linear` (3.1.3).
- **Gap closed:** O3-2 (`let r = handle … in { first(&mk_v()) }`): the temporary of the
  handled body ends before `Return` of that body; `_0` of the handled body holds the
  value across that free, and `Exit` of the `Handle` uses `_0`: W0301 (section 4.8,
  invariant C2).
- A fresh task handle under `_` is a `Spawn` with `dest: None` (3.28), not a drop.

### 3.4 Expression statements and place statements [2.3]

```text
e;  (a value)           =>  Stmt scope { t := <e>; Drop(t); Dead(t) }
p;  (a place of a local) =>  Stmt scope { <index temporaries>; Bounds(..); Mention(p) }
{ ... v };  (a block)   =>  Stmt scope { t := <block>; Drop(t); Dead(t) }
```

- A place in statement position names the place. It reads only the lengths of its
  indexes (`Bounds`), as `compile.rs:473` does. It moves nothing (OR6).
- A discarded value always gets a destination and a `Drop`: a scope statement (O3-1), a
  spawn statement with a handle type (O3-4: the handle is linear, the `Drop` is W0601,
  unless it is the `dest: None` form of 3.28), a block statement (V118).
- **Goes away:** `drop_value` and its early returns for values with a variable or a
  task set (map 2.3), `discard_block_value`, `local_place`.

### 3.5 Assignment to a local: `x = v` [2.4]

```text
x = v   =>  t := <v>; Drop(x); x = move t        (Drop only if the type is not plain data)
```

- The value runs first, then the target, then the store (`compile.rs:481`).
- A local of a function type gets the new value. The abstract value of `x` is the join
  of its values on the paths into each use (section 4.2): the flow-insensitive join of
  ADR 0005 becomes a flow-sensitive state.
- `x = v` on a reference local `x` gives `x` a new reference. `x += v` on a reference
  local writes through it: `(*x) = (*x) + v` (RT9).

### 3.6 Assignment to a place: `p.f = v`, `v[i] = x`, through a reference [2.5]

```text
p.f = v       =>  t := <v>; <place p>; Drop(p.f); p.f = move t
(*r).f = v    =>  t := <v>; Drop((*r).f); (*r).f = move t
v[i] = x      =>  t := <x>; ti := <i>; Bounds((*v), copy ti); Drop((*v)[ti]); (*v)[ti] = move t
```

- The target place runs after the value (its index expressions too).
- A new value of a part of a local is an assignment to a move path (`p.f`). The fact
  generator gives each move path that the body assigns a fact variable of its own
  (section 4.3): the part holders of today (`part_holder`, `retire_holders`,
  `retire_stale`, S069) are this rule.
- A linear old value behind a reference is a `Drop` of a linear value: W0601, as ADR
  0007 says ("behind a reference the old value is always there").
- A self-reference field of a `!Move` struct: the `Assign` node emits `ref_at` and
  `ref_in` (W0605).
- **Goes away:** `drop_replaced_uses`, `assigned_places` with `field_referents`,
  `writes_through` as a special path (it is one rule of the template, section 4.1).

### 3.7 Compound assignment: `x += v` [2.6]

```text
x += v   (x a local)          =>  t := <v>; t2 := Add(copy x, move t) as T; x = move t2
p += v   (p through a ref)    =>  t := <v>; t2 := Add(copy p, move t) as T; p = move t2
```

- The integer type is in the `Binary` right side (`Option<IntTy>`). The span-keyed
  `int_ops` table goes away (RR14).
- `CompoundStore` of the interpreter follows references only (`docs/plan/core-ir-inputs/semantics.md` 2.4).
  The builder writes the `Deref` that the type asks for (RT9, V014, V098).

### 3.8 Names, field places, index places, slices [2.7]

| Source | IR place |
| --- | --- |
| `x` (a local) | `x` |
| `x` (a capture of a closure, `ByRef`) | `(*env.k)` |
| `x` (a capture, `ByMove`) | `env.k` |
| `r.f` with `r: &S` | `(*r).f` |
| `b.f` with `b: Box<S>` | `(*b).f` (`Deref(Box)`) |
| `h.f` with `h: Rc<S>` | `(*h).f` (`Deref(Rc)`) |
| `v[i]` with `v: Vec<T>` | `ti := <i>; Bounds(v, copy ti); v[ti]` (`Index`, unstable element step) |
| `a[i]` with `a: [T; n]` | `a[ti]` (stable element step) |
| `t.0` | `t.0` (`Field`) |
| `o.Some` | `(o as Some).0` (`Variant`, after a test) |
| `&v[]` | `&v[]` (`Elems`) |

- The builder writes each implicit dereference that the interpreter does
  (`docs/plan/core-ir-inputs/semantics.md` 2.4). So `held_refs` (`flow.rs:60`), `deref_lval`, `through_ref`,
  the `*rs` roots of `held_root` and the handle dependencies `handle_deps` become α of
  one projection (section 4.3). A read through `(*h).f` names `h`, so a task that reads
  it reads the handle (O3-6).
- A reference parameter whose pointee holds references: `(*(*p).f)` is a place through
  a second `Deref`. α gives the `Held` interface root (section 4.3), as ADR 0003 asks.

### 3.9 Borrow: `&p`, `&p[]`, `&value` [2.8]

```text
&p        =>  t := &<place p>
&p[]      =>  t := &<place p>[]
&value    =>  tv := <value>; t := &tv          (tv in the current Stmt scope)
&b.items  =>  t := &(*b).items                 (names b: a read of the Box, OL-R2d-box)
```

- A borrow is `Rvalue::Ref`: no read of the value. A borrow of a place field with no
  value is a use of it (W0304): the template emits `uses` of the move path.
- **Goes away:** `temp_root` (S007): `tv` is a temporary with storage.

### 3.10 Temporaries and statements [2.9]

The table of `docs/plan/core-ir-inputs/map_lowering.md` 2.9 becomes one rule: a temporary ends at the end of
its `Stmt` scope, or at the frame end for a tail temporary of a frame body. Each frame
kind (function, closure, clause, handled body, scope body) uses 3.1.4, so the rows
"handled body: its own statement record", "closure body: each run node (`dropped`)" and
"scope body: the enclosing statement" go away. The summary of a closure or a clause
(section 4.5) reports the frees of its own temporaries at its run nodes as frees of
the callee frame root, not as `scope_end` of hidden variables (`Summary::dropped`).

### 3.11 Blocks and tails [2.10]

```text
into({ s1; ...; sn; e }, dest)  =>  Block scope { Stmt scope {s1} ... Stmt scope {sn}; into(e, dest) }; <drops of the block locals>
```

- The value moves into `dest` before the block locals end. A reference in the value
  into a block local is invalid after the end (`hold_out` and `use_held` of RT1/F1 go
  away: `dest` is the holder).
- A closure body is a frame: its tail goes into `_0` (3.1.4). A returned reference into
  a closure local is invalid at the return node of each call (W0301), or W0204 for a
  stated place.

### 3.12 `if`, `&&`, `||` [2.11]

```text
into(if c { a } else { b }, dest)  =>  tc := <c>; Switch(move tc) [true: bbA, false: bbB]
  bbA: into(a, dest); Goto(join)      bbB: into(b, dest); Goto(join)
a && b  =>  t := <a>; Switch(copy t) [false: done, true: bbB];  bbB: t = <b>; Goto(done)
```

- The temporaries of the condition belong to the statement around the `if`
  (`docs/plan/core-ir-inputs/semantics.md` 4.2): they end after both branches.
- The value of each branch moves into `dest` (S059, V059). A branch of type `Never`
  ends in `Unreachable` or in a jump.
- **Goes away:** `branch_state`, `set_branch`, `joined`, `join_uniq` (the join of the
  analysis does it), `retire_stale` on the edges, `join_val` for function values.

### 3.13 `match` and its patterns [2.12]

```text
into(match e { P1 => a1, P2 => a2 }, dest)
  =>  s := <place_or_temp e>
      td := Discriminant(s); Switch(move td) [v1: bbA1, v2: bbA2, otherwise: Unreachable]
  bbA1: Block scope { <bind P1 from s>; into(a1, dest) }; Goto(end)
```

- A binding by value: `x = move (s as V).0` (a part move, or the whole move of the
  scrutinee when the arm takes all of it). A binding through a reference (the scrutinee
  is `(*r)`): `x = &(*r as V).0`. A binding of a reference payload by value copies the
  reference: `x = copy (*r as V).0`, and α of a copy of a reference is the places that
  the stored reference points into (R3RT2).
- A pattern `_` over a linear part of a value that the arm takes: `Drop((s as V).k)`.
- An arm that matches a variant with no payload consumes a linear local scrutinee:
  `Consume(s)` (ADR 0007 `empty`).
- The temporaries of the scrutinee belong to the statement around the `match`.
- W0120 (exhaustiveness) stays in `typeck`, before the builder.

### 3.14 Loops: `while`, `loop`, `for`, `break`, `continue` [2.13]

```text
while c { b }    =>  head: Stmt scope { tc := <c> }; Switch(move tc) [true: body, false: exit]
                     body: Block scope { b (tail in its own Stmt scope, then Drop) }; Goto(head)
loop { b }       =>  head: Block scope { b }; Goto(head)
for p in e { b } =>  it := Iter(Elems(<place_or_temp e>));   (or Range(lo, hi))
                     head: Live(x); IterNext(it, x) -> [next: body, done: exit]
                     body: Block scope { <bind p from x>; b }; Goto(head)
break / continue =>  <exit scopes up to the loop>; Goto(exit / head)
```

- The loop is a cycle in the CFG. The analysis iterates to a fixpoint with widening at
  the loop head (section 4.2). **Goes away:** `lower_loop`, `LoopHead` (61 fields),
  `FnFacts::rewind`, `Locals::restore`, `next_carry`, `retire_loop_stale`, the pass
  bound W0707 (the analysis cannot fail to converge: its lattice has a finite height
  after widening). V025, V041 and RR1 come from the passes.
- An element of scalar type is a copy. Another element is a reference into the buffer
  (`&(*src)[elem]`). The iterator is `@ uniq` if its source is: the flags of the local
  come from its type (RT18).
- `IterNext` reads the length at each step (the interpreter does, `docs/plan/core-ir-inputs/semantics.md` 10).

### 3.15 `return` [2.14]

```text
return e  =>  into(e, _0); <exit all scopes of the frame>; Goto(return block)
```

- In a closure, `return` leaves the closure frame (its `Fence` is the closure body).
  W0315 for a handled body, a clause or a scope body (3.1.5).

### 3.16 Operators and literals [2.15]

```text
a + b    =>  ta := <operand a>; tb := <operand b>; t := Add(move ta, move tb) as T
a == b   =>  ta := &<place a>; tb := &<place b>; t := Eq(move ta, move tb)   (not plain data)
-a, !a   =>  ta := <operand a>; t := Neg(move ta) as T
"{a}{b}" =>  ta := <operand a>; tb := <operand b>; t := Concat(...)
```

- Choice A: each operand is read where it is written (N1 of the semantics map, p2:
  `r.hp + { v.push(..); 1 }` copies `r.hp` before the push, so it is safe, and a
  comparison of two `Vec`s borrows each one where it is written, so a push in a later
  operand invalidates the borrow: W0301).
- `-128` is one literal. A literal that does not fit is W0102 in `typeck`.

### 3.17 Aggregates [2.16]

```text
(a, b)           =>  ta := <a>; tb := <b>; t := Tuple(move ta, move tb)
[a, b]           =>  ... t := Array(...)            Vec literal: t := Vec(...)
S { b: x, a: y } =>  tx := <x>; ty := <y>; t := Struct(S)(move ty, move tx)  (written order, field order in the aggregate)
S(x, y)          =>  in the order of the fields of S
Some(a)          =>  ta := <a>; t := Variant(Option, Some)(move ta)
```

- A part that moves is a temporary that lives until the aggregate: it is held while the
  later parts run, and a jump or an abort in a later part finishes it (its `Stmt` scope
  and the cleanup chain). **Goes away:** `hold_moved`, `hold_later`, `hold_part`,
  `take_held_here`, and the "consume, hold, take" loop that `docs/plan/core-ir-inputs/map_lowering.md` 2.16
  counts at ten sites (RT4, V015, V072, OL-3c, S072).
- A struct with a place field that the literal does not give: `Uninit(t.f)` after the
  aggregate, for each place field at each depth of the final type (Q3-1, V062: the walk
  uses the full type, not the ADT id).
- A struct literal that gives a place field a reference: `ref_at` with no `ref_in`
  (W0605).

### 3.18 Calls of function items [2.17]

```text
f(x, y)   =>  tx := <operand x>; ty := <operand y>;           (parameter order, ADR 0009)
              Live(t); t = call f<T..>(move tx, move ty) caps Lexical(env)
                 -> [next: bb, unwind: C]
```

- One terminator for each call form. The eight phases of `call_fn_as` become: the
  builder evaluates the arguments in parameter order; the fact generator applies the
  template of `Call` (section 4.1) with the summary of `f` (section 4.5).
- A by-value argument moves where it is evaluated (`move tx` is a temporary that the
  move filled). A closure argument at a parameter of function type is a temporary that
  holds the closure value; the callee borrows or takes it as its type says.
- A `!Move` value built for a parameter of its own type, or for `Box.new` and `Rc.new`,
  has `in_place: true` (W0604 skips it).
- `unwind` is present if the callee can abort (V10); the analysis drops the edge when
  the summary says it cannot.
- **Goes away:** `item_arg_slots`, `eval_item_args`, `arg_order` export (RR10),
  `hold_operand`, `hold_generic` and `release_generic` (the return node moves a held
  argument, section 4.1), `callee_drops` (the summary has `drops`), `item_fn_args`,
  `arg_tasks` chains of "task of the callee" nodes (the summary of the callee has its
  tasks), "call again" nodes (`repeats` gives a second application of a callback's
  summary at the return node, section 4.5).

### 3.19 Method calls [2.18]

```text
x.m(a)  (self by reference)  =>  ta := <a>; tr := &<place x>; t = call m(move tr, move ta)
x.m(a)  (self by value)      =>  ta := <a>; t = call m(move <place x>, move ta)
T.f(a), module.f(a)          =>  a function item call
```

- The receiver is a place first; the call reads it after the arguments (p7, p8).
- `s.spawn(..)`, `t.join()`, `t.detach()` are `Spawn`, `Join`, `Detach` terminators
  (3.28). Their arguments are operands, so their moves are in the IR (V136).
- **Goes away:** `note_via_call` and `finish_via_calls` (QA6): `writes_via` at a call
  is one rule of the template (each change of the summary is below the one place of the
  receiver reference).

### 3.20 Generic calls and type parameters [2.19]

- The IR is generic: a value of type `T` is a local of type `Param(i)`. Its props are
  "maybe linear, maybe not plain data" (`Props::generic`). The builder writes `Drop` and
  `UnwindValue` for it as for a value that is not plain data.
- The `drops` and `holds` parts of the summary are queries over the IR of the body
  (section 4.5): `drops(T)` if a `Drop` or a `Dead` of a maybe-initialized `T` value is
  reachable; `holds(T)` if a `T` value is live across a node that can abort or resume more
  than once. No hand-written W0601 analysis (`dropped_params`, `held_params`).
- The types are final when the builder runs, so a move of a value whose type was an
  inference variable is a move or a copy for sure (`tentative`, `settle_moves`, V060 go
  away).
- A generic function item as a value (`check_item_value`) is a `Const::Fn(f, tys)`
  operand. A call of it applies the summary of `f` with those type arguments; a value
  that code outside the body can run gets the same check where it is made (3.23).

### 3.21 Calls of function values [2.20]

```text
v(a)  =>  tv := copy v; ta := <a>; t = call (copy tv)(move ta) caps Lexical(env) -> [bb, C]
```

- The callee is an operand, read before the arguments (`docs/plan/core-ir-inputs/semantics.md` 2.3).
- The analysis gives the set of values the callee can be: closures (with their
  environment), items, function parameters, values that the body does not know. The
  template applies the summary of each one (section 4.5).
- For a function parameter or an unknown value, the summary is "code of a caller". It
  can change each place that the arguments reach (`lends_mut`). Its result points into
  the argument places and into the root of the caller frame (this rule fixes finding N2
  of `docs/plan/core-ir-inputs/map_lowering.md`). It can abort, and resume more than once, if its row allows.
- A `once` closure moves at the call: the callee operand is `move v` (W0502).

### 3.22 Closures [2.21]

```text
|p| body  =>  te := Aggregate(Closure(c))(<one operand for each capture>)
              where the operand is &x (ByRef, KeptCell), move x (ByMove), copy cap, copy kont
body c (Closure):  params _1 = env, _2 = p; _0
  bb0: <body into _0>; <frame end>; Return
```

- The closure value is the aggregate. Its abstract value holds the places of its
  captures (by reference: the captured variable; by move: what the moved value holds),
  the capabilities of its `cap_env` that its row uses, and its body.
- In the closure body, a capture is a place through the environment: `(*env.k)` for
  `ByRef`, `env.k` for `ByMove`.
- **Goes away:** `{closure}` hidden variables, `note_capture`, `moved_captures`,
  `captures_live_at` (the environment is a parameter that has its value at the entry),
  the `closure end` node, `late_join` and its nine functions (RR7, V103, V104, O3-11,
  F3-11: the run node applies the summary to the current value of the captured
  variable, section 4.5), `union_ret`, the `by_value` export (OR2, V017).
- The modes of the closure are the props of its environment fields: linear if a field
  is linear, `once` if a `ByMove` field is not plain data, nonportable if a field is
  (RT8, OL-5, V061).
- **Decision needed (V125):** `KeptCell` keeps the semantics of today. A reference into
  the cell (not the capture) still dies at the end of the variable.

### 3.23 Function items as values, joins [2.22] and stored function values [2.23]

```text
f (an item as a value)   =>  t := Use(Const::Fn(f, tys))
store into a field       =>  (*r).f = move tclosure      (an Assign of a place through a Deref)
```

- A function value is a value. It flows through locals, fields, elements and tuples as
  other values do. The analysis (section 4.2) keeps the set of closures and items that
  each place can hold, including the abstract heap behind references. **Goes away:**
  `FnTy::summary`, `fn_joins` (RR2, V107: the type table is not a value-flow table),
  `join_val`, `escape`, `escape_all`, `keep`, `store_into`, `apply_stored` with
  `insert_after`, `reach` and `known_at` (V027, V028, V089, QA17). A `{stored closure}`
  variable becomes the variable of a heap slot (section 4.3).
- A call of a value that the analysis loads from the heap applies the summaries of the
  values that the heap slot can hold. A call of unknown code (an extern function, a
  function parameter) can run each value stored in a place that its arguments reach:
  the analysis applies those summaries at that node (the `reaches` rule of ADR 0005,
  as one transfer function).
- `sim.run` as a value emits `sim_run_at` at the `Assign` (RT17).

### 3.24 `handle`, clauses and the handled body [2.24]

```text
dest = handle E { op_i(params) { clause_i } } in body
  =>  tc := Aggregate(Tuple)(&x, ...)     (the captures of the clauses, by reference)
      tb := Aggregate(Tuple)(&y, ...)     (the captures of the handled body, by reference)
      dest = handle h(clauses: move tc, body: move tb) -> [next, unwind: C]
body H (Handled h):  params _1 = env; cap _2 = the new capability of E; _0
body K_i (Clause h, op_i):  params _1 = env, op arguments; kont = resume; _0
```

- The `Handle` terminator makes the capability, runs the handled body, and gives
  `dest` the value of the body or the value of a clause. Its `unwind` is for an abort
  that goes past the handler (a caller's handler, a cancel).
- The clauses run in the capability environment of the `handle` (rule 6 of the effects
  proof): their `cap_env` is the environment of the site, without the new capability.
- The handled body and each clause are bodies. **Goes away:** the inline lowering of the
  handled body in the parent (map 4.3), its own statement record (R2c), `body_frees`,
  `inner_frees`, `merge_summary`, `run_handler` and `run_clause_caps` (section 4.5 applies
  the clause summary at each perform), `end_clause_locals`, `join_clause_vals`,
  `clause_refs_onto_args` (the substitution of section 4.5 maps a clause parameter onto
  the argument places), `finish_aborts` (the abort edges are in the IR), `finish_spared`
  (section 4.4), `op_refs` and `resume_refs_pending` (section 4.2: one fixpoint for the
  handled body and its clauses), `check_cont_escape` and `check_cap_escape` (W0313 by the
  reference rules, section 4.7).
- The fact generator splices the handled body into the component of the site, with the
  phases `Exit`, `Post`, `Landing` and `Copy`, and each perform that aborts to the
  handler gets an `AbortValue` node (section 4.4). This is where M1 and M3 are
  fixed.

### 3.25 A `multi` handled body (re-runs) [2.25]

- No special lowering. The IR is the same as 3.24. The fact generator adds the re-entry
  edges (section 4.4) for each `multi` suspension point: from the `Post` node of the
  `handle` back to the successor of the point, through a `Copy` node. **Goes away:**
  `handled_again`, `again_node`, `resumes_at_most_once` (a syntax count; the analysis
  asks whether the clause can reach two `Resume` nodes, or one in a cycle or in a closure
  that runs more than once).
- O3-14 (a tail place of a `multi` body moves once for each resume): the move of the tail
  `_0 = move x` of a local `x` from outside the body is on the cycle, so the second run
  sees `moved` (W0302). One-place instances are off on the cycle (V097), as the analysis
  sees it.

### 3.26 Perform [2.26]

```text
op(a, b)  =>  ta := <a>; tb := <b>;                         (parameter order)
              t = perform cap.op(move ta, move tb) -> [next, unwind: C]
```

- `cap` is `Local(_2)` of the innermost handled body of `E` in the same function,
  `Row(E)` if a caller handles `E`, or `Root(E)` inside an `on abort` function. The
  builder resolves it from the static capability environment (handlers are lexical).
- A perform inside a closure names the capability of the closure's `cap_env`: the
  builder writes `Row(E)` or the place of the capability through the environment; the
  analysis adds the capability to the abstract value of the closure.
- The result `t`: the analysis gives it the places of the values that the clauses of a
  local handler give to `resume` (section 4.5), or, for `Row(E)`, the places of the
  reference arguments of the operation and the root of the caller frame (finding N1 of
  `docs/plan/core-ir-inputs/map_lowering.md`, fixed by the rule).
- **Goes away:** `perform_op`, `op_slots`, `eval_op_args`, `perform_effect`,
  `note_abort_ctx`, `note_op_fn`, `give_held_to_op`, `op_arg_places`, `op_fn_values`,
  `op_suspends`, `op_result` (map 2.26): one terminator, one template.

### 3.27 `resume` [2.27]

```text
resume(v)  =>  tv := <v>; t = resume(kont, move tv) -> [next, unwind: C]
```

- In a clause body `kont` is the local `resume`. In a closure inside the clause it is a
  `Kont` field of the environment (the closure captures the continuation by copy; it
  moves it if the continuation is `once`, so the closure is `once`).
- The analysis gives `t` the abstract value of `_0` of the handled body: what the body
  gives back when it ends (M2). The summary of the continuation (section 4.5) gives the
  changes, frees and aborts of the rest of the body at the `Resume` node: RR5, V121, V036
  and R3RT4 are this one rule.
- **Goes away:** `ContInfo::muts`, `ContInfo::frees`, `resume_through_params`,
  `onto_param`, `finish_resume_runs` (map 2.27).

### 3.28 `scope`, `spawn`, `join`, `detach`, `fork` [2.28]

```text
dest = scope { s => body }  =>  te := Aggregate(Tuple)(&x, ...);
                                dest = scope k(env: move te) -> [next, unwind: C]
body S (Scope k): params _1 = env, _2 = s (ScopeCap)
  ... <body into _0>; ScopeWait(_2, orphans) -> [bb, unwind: C]; <frame end>; Return

h = s.spawn(f)              =>  tf := <f>; Live(h); spawn site_i(copy s, move tf) -> h, [next]
s.spawn(f);                 =>  tf := <f>; Live(r); spawn site_i(copy s, move tf) -> None, [next]
                                (r is a TaskResult local of the scope body: ScopeWait drops it)
x = h.join()                =>  join(move h) -> x, [next, unwind: C]
h.detach()                  =>  detach(move h) -> [next]
dest = fork(f, g)           =>  tf := <f>; tg := <g>; dest = fork(move tf, move tg) -> [next, unwind: C]
```

- The scope body waits for its tasks before its locals end (ADR 0006), and `ScopeWait`
  can abort (F3-7).
- A spawn in statement position gives the result to the scope. The result is a local
  (`TaskResult`) that `ScopeWait` drops: a linear result is W0601 (O3-4, I3-1).
- The spawn does not suspend the parent. A task that a callee or a closure starts comes
  from its summary at the run node (section 4.5).
- **Goes away:** `start_task`, `task_captures`, `task_ret`, `end_tasks`,
  `finish_task_values`, `finish_task_ends`, `finish_task_marks`, "task end" nodes and
  `restart_after` (map 2.28): the templates of `Spawn`, `Join`, `ScopeWait` and `Fork`, and
  the task part of the summaries.
- **Stays (TYPE):** the type rule of `Task<T>` and `on abort` for a linear `T` (F3-6), and
  the unwinder gap for closure cells (I3-2) and cancelled tasks (F3-8).

### 3.29 `sim.run` [2.29]

```text
sim.run(seed, workers) { body }  =>  t = call sim.run(seed, workers, move tclosure) caps Lexical(env)
```

- `Intrinsic::SimRun`: the fact generator emits `sim_run_at`, the `handler` and
  `sim_root` facts of the root handlers, and applies the summary of the closure with the
  capabilities of the simulation (`CapOperand::Root` for each standard effect).
- `workers = 4` when the call leaves it out is a constant argument in the IR.

### 3.30 `with_timeout` [2.30]

- `Intrinsic::WithTimeout`: a call. Its summary runs the closure exactly once, and the call
  can abort and perform `fail` through the capabilities at the call. The
  `item_runs_once` and `item_repeats` special cases are two bits of its summary.

### 3.31 `on abort` [2.31]

- An `on abort` function is a function item with a body. The cleanup chain of each frame
  names it (`UnwindAction::OnAbort(f)`). The fact generator applies the summary of `f` at
  the `UnwindValue` node, with `CapArgs::Root`.
- W0118 becomes a query over the summary of `f`:
  - its changes must be below its parameter value (F3-1: a change through a reference
    in the value is a change outside it);
  - its row may hold only effects that the root handlers serve;
  - its `raises` part must be empty;
  - its `drops` part must not hold a type parameter of its parameter type (F3-3, F3-4,
    with the substitution of the type arguments).
- FD1, V117 and V119 (the effects and the changes of an `on abort` function, a closure
  that it calls) come from the summary of `f`.

### 3.32 `Rc`, `Box`, `Weak` [2.32]

- `Deref(Rc)` goes to the group root of the inner type, and α adds the handle place
  (`h.*`) to the places of each reference through it (section 4.3). A read through the
  handle reads `h` (O3-6).
- `Deref(Box)` is an unstable step below the owner. `Box.new` builds its argument in
  place.
- `Weak` has no `Deref`.

### 3.33 `print` and `assert` [2.33]

```text
print(a, b)  =>  ta := <operand a>; tb := <operand b>; Print(copy ta, copy tb); Drop and Dead of the temporaries
assert(c)    =>  tc := <c>; Assert(move tc) -> [next, unwind: C]
```

- `print` reads its operands where they are written (choice A; N2 of the semantics map).
  A value that is not plain data is borrowed, not moved.
- `assert` can abort the task. Its cleanup edge and `may_abort` (N4 of the semantics
  map, probes p25 and p27) come from the terminator. The summary of a body with an
  `Assert` can abort, so its callers get `may_abort` too.

### 3.34 Effects at calls and at handlers of a caller [2.34]

- A call passes `CapArgs::Lexical(env)`. For each effect `E` of the callee's row, the
  analysis resolves `E` in `env` to a local handler capability (then `performs_at` with
  the footprint of its clauses), to `Row(E)` (then `escapes_at`), or to a root handler.
  This is the elaborated capability passing of the effects model (`Call { caps }`).
- **Goes away:** `perform_at`, `effect_lends`, `raise_here` (the `raises` part is a
  query), `callee_ops`, `may_run_again` (one-place instances are off on cycles of the
  CFG, re-entry edges included).

### 3.35 What the builder reports

The builder reports the diagnostics that need the structure of the IR and not the
analysis: W0315 (a jump out of a fence), W0303 (a move through a reference), W0604 for a
move of a named `!Move` value that is not `in_place`. Type errors, names, W0120, W0102
and W0107 stay in `typeck`.

---

## 4. Fact generation

The fact generator `weft_ir::facts` reads the IR, the results of the analysis
(section 4.2) and the summaries (section 4.5). It writes one `FnFacts` for each function
and each test, with the schema of `crates/weft-facts` as it is today. So the checker,
the spec, the agreement tests and the bridge do not change in stages 1 to 6.

### 4.1 Nodes and templates

**Nodes.** Each statement is one node. Each terminator is one node (`Phase::Main`), and
some terminators have more nodes, always in this order on the CFG (`facts.rs` of the
sketch, `NodeKey`):

| Terminator | Nodes in order | Why |
| --- | --- | --- |
| `Call`, `Resume` | `Main` → `Ret` → `FrameEnd` (→ `Copy` on a re-entry edge); on an abort to a local handler `h`: `Main` → `AbortValue(h)` → the cleanup chain | the result binds after the call (A5, `no_gen_kill`); a held argument moves at `Ret`; the frame that gave the result ends after the result binds (C3); the value of a clause that does not resume binds before the unwinding |
| `Perform` | `Main` → `Ret` (→ `Copy` on a re-entry edge); on an abort: `Main` → `AbortValue(h)` → the cleanup chain | the same; the frames of the clauses end at `Post` or `Landing` of the `handle` |
| `Join`, `Fork` | `Main` → `Ret` | the same; they lend the writes of the task at `Ret` (the task end) |
| `Handle` | `Main` → (spliced handled body) → `Exit` → `Post`; the end of an abort to this handler: `Landing`; `Copy` on a re-entry edge | the frame order of the machine (section 4.4) |
| `Scope` | `Main` → (spliced scope body) → `Exit` → `FrameEnd` | the same |
| a cleanup block | one copy of each node for each abort destination (`NodeKey::dest`) | section 4.4 |

The relation `cfg_edge` links the nodes in this order, the blocks by their successors,
the `unwind` edges, the splice edges and the re-entry edges (section 4.4).

**Templates.** Each instruction has one template: the input relations of
`spec/weft.dl` that it can emit at its nodes. The table below is the output of the test
`print_table` of the sketch (`facts.rs`). The test `each_relation_has_a_source` checks
that each of the 73 input relations of the spec has a source: the place interner
(`place`, `parent`, `unstable`, `wildcard`, `one_place`, `step_alias`, `step_within`,
`param_rooted`), the declarations (`owner`, `linear`, `has_on_abort`, `once_var`,
`immovable`, `nonportable`, `uniq`, `has_signature`, `declared_mut`, `declared_effect`,
`shared_root`, `task`, `fork_task`, `library`, `std_effect`, `started`,
`no_runtime`), or a template.

Statements (third column: what a cleanup path adds):

| Statement | Relations | On a cleanup path |
| --- | --- | --- |
| `Live` | cfg_edge | - |
| `Dead` | cfg_edge, scope_end | unwound_at |
| `Assign` | cfg_edge, points_into, mutates_at, reads_at, rebound_at, uses, moved_at, overwrites, empty_at, moved_part, writes_via, sim_run_at, ref_at, ref_in | - |
| `Drop` | cfg_edge, rebound_at, scope_end | - |
| `Consume` | cfg_edge, uses, moved_at | - |
| `Uninit` | cfg_edge, unset_at | - |
| `Bounds` | cfg_edge, reads_at, uses | - |
| `Mention` | cfg_edge, uses | - |
| `Print` | cfg_edge, reads_at, uses | - |
| `UnwindValue` | cfg_edge, mutates_at, reads_at, unwound_at, lends_mut | - |
| `UnwindKont` | cfg_edge | - |

Terminators:

| Terminator | Phase | Relations |
| --- | --- | --- |
| `Goto` | Main | cfg_edge |
| `Switch` | Main | cfg_edge, reads_at, uses |
| `Return` | Main | cfg_edge, ref_at, ref_in |
| `UnwindExit` | Main | cfg_edge |
| `Unreachable` | Main | cfg_edge |
| `Call` | Main | cfg_edge, points_into, mutates_at, reads_at, performs_at, uses, moved_at, moved_part, releases_at, may_abort, multi_at, spared_at, resumes_at, escapes_at, spawned_at, task_reads, task_writes, captures, mut_through, kept, spawns_in, opaque, call_mut, call_arg, lends_mut, handler, sim_root, sim_run_at, arg_at, param_in, uniq_param, arg_aliased, fn_arg_effect, param_effect |
| `Call` | Ret | cfg_edge, points_into, rebound_at, moved_at, empty_at |
| `Call` | FrameEnd | cfg_edge, scope_end |
| `Call` | AbortValue | cfg_edge, points_into, rebound_at, empty_at |
| `Call` | Copy | cfg_edge, rebound_at, empty_at |
| `Perform` | Main | cfg_edge, points_into, mutates_at, reads_at, performs_at, uses, moved_at, moved_part, releases_at, may_abort, multi_at, spared_at, resumes_at, escapes_at, spawned_at, task_reads, task_writes, captures, mut_through, kept, spawns_in, opaque, call_mut, call_arg, lends_mut, arg_at, param_in, uniq_param, arg_aliased, fn_arg_effect, param_effect |
| `Perform` | Ret | cfg_edge, points_into, rebound_at, empty_at |
| `Perform` | AbortValue | cfg_edge, points_into, rebound_at, empty_at |
| `Perform` | Copy | cfg_edge, rebound_at, empty_at |
| `Resume` | Main | cfg_edge, points_into, mutates_at, reads_at, performs_at, uses, moved_at, moved_part, releases_at, may_abort, multi_at, spared_at, resumes_at, escapes_at, spawned_at, task_reads, task_writes, captures, mut_through, kept, spawns_in, opaque, call_mut, call_arg, lends_mut |
| `Resume` | Ret | cfg_edge, points_into, rebound_at, empty_at |
| `Resume` | FrameEnd | cfg_edge, scope_end |
| `Resume` | AbortValue | cfg_edge, points_into, rebound_at, empty_at |
| `Handle` | Main | cfg_edge, points_into, reads_at, footprint, rebound_at, uses, clause_multi, body_multi, handler, clause_performs |
| `Handle` | Exit | cfg_edge, points_into, rebound_at, uses, empty_at |
| `Handle` | Post | cfg_edge, points_into, mutates_at, reads_at, performs_at, uses, moved_at, scope_end, releases_at, may_abort, multi_at, spared_at, resumes_at, escapes_at, spawned_at, task_reads, task_writes, captures, mut_through, kept, spawns_in, opaque, call_mut, call_arg, lends_mut |
| `Handle` | Landing | cfg_edge, scope_end |
| `Handle` | Copy | cfg_edge, rebound_at, empty_at |
| `Scope` | Main | cfg_edge, points_into, performs_at, rebound_at, uses, may_abort, escapes_at |
| `Scope` | Exit | cfg_edge, points_into, rebound_at, uses, empty_at |
| `Scope` | FrameEnd | cfg_edge, scope_end |
| `ScopeWait` | Main | cfg_edge, performs_at, rebound_at, uses, scope_end, may_abort, spared_at, escapes_at, joined_at, lends_mut |
| `Spawn` | Main | cfg_edge, points_into, mutates_at, reads_at, performs_at, rebound_at, uses, moved_at, moved_part, escapes_at, spawned_at, task_reads, task_writes, captures, mut_through, kept, spawns_in, opaque, call_mut, call_arg |
| `Join` | Main | cfg_edge, performs_at, uses, moved_at, may_abort, spared_at, escapes_at, joined_at |
| `Join` | Ret | cfg_edge, points_into, rebound_at, empty_at, lends_mut |
| `Detach` | Main | cfg_edge, rebound_at, uses, moved_at, scope_end |
| `Fork` | Main | cfg_edge, mutates_at, reads_at, performs_at, uses, moved_at, moved_part, may_abort, spared_at, escapes_at, spawned_at, task_reads, task_writes, captures, mut_through, kept, spawns_in, opaque, call_mut, call_arg |
| `Fork` | Ret | cfg_edge, points_into, rebound_at, empty_at, joined_at, lends_mut |
| `Assert` | Main | cfg_edge, reads_at, uses, may_abort, spared_at |
| `IterNext` | Main | cfg_edge, points_into, reads_at, rebound_at, uses, empty_at |

**The rules of the templates.** Notation: `n` is the node; `v(p)` is the fact
variable of the move path of `p` (section 4.3); `α(p)` is the set of fact places of an
IR place (section 4.3); `refs(o)` is the set of places that the value of an operand
holds (the analysis, section 4.2); `Σ` is a summary and `σ` its substitution at `n`
(section 4.5).

*Operands.* Each operand `copy q` or `move q` at `n` emits:
`uses(v, n)` for the move path of `q`, for each move path above it and each assigned
move path below it, and for each pointer local on the path of `q` (a read through `r`
uses `r`); `reads_at(n, α(q))`; `reads_at(n, cell(x))` if the base `x` is a source
local (a use of a variable reads it, OR8); `uses(u, n)` for each unset place field
variable at or below `q` (W0304). A `move q` also emits `moved_at(v(q), n)` if `q` is a
whole local, or `moved_part(α(q), n)` and `moved_at` of the move path of the part if
`q` is a part.

*Statements.*

- `Live(l)`: no fact but the edge.
- `Dead(l)`: `scope_end(v, n)` for each variable of `l`, but only if `l` is plain data.
  A local that is not plain data got its `scope_end` at its `Drop`. So each local has
  exactly one `scope_end` on each normal path. On a cleanup path `Dead` emits nothing:
  the `UnwindValue` before it emitted `unwound_at`.
- `Assign(p, rv)`: the operands of `rv`. Then, for the destination:
  - `p` is a whole local `l`: `rebound_at(v(l), n)` and `rebound_at` of each move path
    variable below `l`; `points_into(v(l), A)` for each `A` in `refs(rv)`;
    `empty_at(v(l), n)` if `rv` has no linear part (a variant with no payload);
    `mutates_at(n, cell(l))` if `l` is a source local (a new value writes the variable,
    W0405).
  - `p` is a part of `l` (no `Deref`): `rebound_at(v(p), n)`; `points_into(v(p), A)`;
    `mutates_at(n, α(p))`; `overwrites(v(l), n)` if the part can hold a linear value.
  - `p` goes through `Deref` of `r`: `mutates_at(n, α(p))`; `uses(v(r), n)`;
    `reads_at(n, cell(r))`; `writes_via(n, v(r))` if the analysis says `r` holds one
    reference to one place (not a wildcard) and `p` is at or below it (C6).
  - `rv = Ref(q)` into a place field of a `!Move` struct: `ref_at` and `ref_in` (W0605).
  - `rv` holds `Const::Fn(sim.run)`: `sim_run_at(n)` (RT17).
- `Drop(p)`: `scope_end(v(p), n)` (the value goes away; with `owner`, the free). For a
  place through a `Deref` with a linear type: a drop pair, a fresh variable with
  `rebound_at` at `n` and `scope_end` at the next node (W0601: a borrowed place always
  has a value). For a part of a local, nothing: the `overwrites` of the next `Assign`
  covers it (the rule of today).
- `Consume(p)`: `uses` and `moved_at(v(p), n)`: the linear value is finished.
- `Uninit(p)`: `unset_at(v(p), n)`.
- `Bounds(q, i)`: `reads_at(n, α(q))` (the length and the buffer, OR5), and the
  operand `i`.
- `Mention(q)`: `uses` of the pointer locals on the path of `q`.
- `Print(ops)`: the operands; each operand that holds a reference reads through it
  (`reads_at` of `refs`), and the whole value is read (W0304).
- `UnwindValue(p, a)`: `unwound_at(v(p), n)` and of each variable below `p`. If `a` is
  `OnAbort(f)`: the summary of `f` at `n` with its parameter mapped onto `α(p)` and
  `CapArgs::Root` (FD1, F3-1).

*Terminators.*

- `Switch`: its operand. `Return`: `ref_at(n, A)` for `A` in `refs(_0)` and
  `ref_in(n, D)` for each stated returned place (W0204).
- `Call`, `Perform`, `Resume` (`Main`): the operands; `call_arg(n, A, root)` for each
  place `A` that an argument reaches, also through stored references (R3RT3), with one
  root for each kind of `body/roots.rs`; the summary of each body that the callee can be
  (section 4.5); `arg_at`, `param_in`, `uniq_param`, `arg_aliased`, `fn_arg_effect`,
  `param_effect` from the signature of the callee; `spared_at(V, n)` (section 4.4).
  `Ret`: `rebound_at(v(dest), r)`, `points_into(v(dest), σ(Σ.ret))`, `empty_at`;
  `moved_at` of each argument that the callee holds (the `holds` part). `FrameEnd`:
  `scope_end` of the callee frame variable of a call, or of the continuation frame
  variable of a `resume` (section 4.3). A result that points into that frame is then
  invalid at its next use.
- `Handle` (`Main`): `handler(h, E)`; `footprint(cap(h), M)` for each place that a
  clause changes outside itself (the clause summaries); `clause_multi(cap(h))` if a
  clause can resume twice; `body_multi(cap(h))` if the handled body can;
  `clause_performs(h, E')`; `rebound_at` of the capability variable. `Exit`: `uses` of
  `_0` of the handled body, and its value into `dest`. `Post`: the summary of the clauses
  after their `resume` (M1), then `scope_end` of the capability variable and of the
  clause frame variable. `Landing`: the same two `scope_end` facts. (The `AbortValue(h)` node of a suspending node `P` binds `dest` of
  the `Handle` of `h` with `rebound_at` and `points_into` the value of the clause.)
- `Scope`: `rebound_at` of the scope capability variable; `escapes_at` or `performs_at`
  of `Async`; `may_abort`. `Exit`: `uses` of `_0` of the scope body, and its value into
  `dest`. `FrameEnd`: `scope_end` of the scope capability variable.
- `ScopeWait`: `joined_at(T, n)` for each task of the scope; `lends_mut(n, M)` for each
  place `M` that such a task writes (the end of a task, ADR 0006); `may_abort`; the
  orphan results get `rebound_at` here (they arrive), and their `Drop` follows.
- `Spawn`: `spawned_at(T, n)`; `task_reads`, `task_writes`, `captures`, `mut_through`,
  `kept`, `spawns_in`, `opaque` from the summary of the task body and its environment;
  `mutates_at`, `call_mut`, `call_arg` (a spawn is a change at the spawn node);
  `rebound_at` and `points_into` of the handle.
- `Join`: `moved_at` of the handle; `joined_at(T, n)` for each task of the must-set of
  the handle (section 4.2); `may_abort`. `Ret`: the result; `lends_mut` of the writes of
  the task.
- `Detach`: `moved_at` of the handle; a drop pair for a linear result (ADR 0007).
- `Fork`: `spawned_at` and the task facts of each branch; `may_abort`. `Ret`:
  `joined_at` of each branch, `lends_mut`, the result.
- `Assert`: its operand; `may_abort(n)`; `spared_at`.
- `IterNext`: `uses` of the iterator; `reads_at` of the elements and the length;
  `rebound_at` and `points_into` of the element.

`may_abort(n)` holds at each `Main` node of a terminator whose `unwind` edge the fact
generator keeps: a perform (each named effect can abort, ADR 0005), a call or a resume
whose summary can abort, `Join`, `ScopeWait`, `Fork`, `Assert`, and `Scope` (it performs
`Async`). `multi_at(n)` holds where the operation, the summary or the clause can resume
more than once.

### 4.2 The analysis: one fixpoint

The analysis gives the abstract values that the templates read. It replaces the
abstract values that `Lower` computes during its walk (`Val`, `LVal`, `Local`), the loop
passes, and the post-passes.

**Domain.** At each point of a body, the state maps:

| Key | Abstract value |
| --- | --- |
| each move path | `AbsVal { refs, fns, caps, tasks, linear, empty }`: the places that the value can point into; the closures (with a snapshot of their environment), items, function parameters and unknown values that it can be; the capabilities that it holds; the tasks that it can be a handle of; whether it can hold a linear value; whether it holds nothing linear (`None`) |
| each heap slot | the same, for values stored behind a reference, in a `Box`, in a `Vec` or in an `rc` object: the slot is the fact place of the storage, cut at a fixed depth |
| each move path (must) | initialized or not (for `drops` and `holds`, and for W0304 diagnostics) |
| each task | the move paths that can hold its handle (a may-set) and whether the task is joined (a must fact) |

**Transfer functions.** One for each statement kind and each terminator kind: 28
functions. A right side has one transfer: `Ref(q)` gives `refs = α(q)` and the handle
places of each `Deref(Rc)` on `q`; `Use(copy q)` gives the value at `q`; an aggregate
gives the union of its operands with the structure of the move paths; a closure
aggregate gives `fns = {Closure(c, snapshot of the operands)}` and the union of the
`refs` of its environment. A terminator that runs another body applies its summary
(section 4.5).

**Joins and widening.** A join is a union of the may-parts and an intersection of the
must-parts. At a loop head (the target of a back edge), the analysis widens. A place
that goes deeper than the places at the head by more than 8 steps becomes the wildcard
place of the outermost new place. More than 16 places in one root become the wildcard
place of their common prefix. These are the rules of `loops.rs` (RR1, QA4, QA7, S101,
S102), applied to a state, not to a re-lowering. The lattice is finite after widening,
so the fixpoint exists. W0707 (the loop pass bound) goes away.

**Interprocedural order.** The analysis of a body reads the summaries of the bodies
that it runs. It builds a graph: a body points to each body whose summary it reads
(a callee item, a closure body, a clause, the continuation of a handled body, a task
body). It runs each strongly connected component of this graph to a fixpoint, callees
first. A handled body and its clauses are always in one component: the result of a
perform comes from the `resume` values of the clauses, and the result of a `resume`
comes from `_0` of the handled body. Each summary starts empty and only grows; summary
places are cut at 8 steps (`SIG_PLACE_STEPS`). So the iteration is monotone and ends.

**Effect rows** are a part of the summaries: the effects that a body performs through
`Row` capabilities, directly or through a callee whose capability resolves to `Row` at
the call. The inference of `infer.rs` becomes this fixpoint. It needs no re-lowering of
a body. The parts of `EffectSig` that do not only grow today (`parts_limit`, W0704) only
grow here, because the analysis starts from bottom and is monotone. W0706 stays as a
guard: a row that grows past the height of its lattice shows a bug.

**No post-passes.** The fact generator runs after all summaries are final. It is a pure
function `emit(ir, states, summaries) -> FnFacts`. So no fact depends on the order of
passes: the 17 post-passes of `docs/plan/core-ir-inputs/map_lowering.md` 1.4 have no place to go. Each of
them is one of these:

| Post-pass today | In this design |
| --- | --- |
| `finish_values` (`apply_stored`, `finish_task_values`) | the heap slots of the analysis; the run node applies the summary of each stored value |
| `finish_aborts` | the `unwind` edges of the IR and the copies of the cleanup chains (section 4.4) |
| `finish_task_ends`, `finish_task_marks` | the templates of `Join`, `ScopeWait`, `Fork`, `Spawn` and the task part of the summaries |
| `op_refs`, `finish_op_env` | the fixpoint of a handled body and its clauses; the caller frame root (section 4.3) |
| `check_returns`, `check_stored_behind` | checks over `refs(_0)` at `Return` and over the `stores` part of the summary |
| `summary_to_sig` | the summary is the signature part |
| `finish_resume_runs` | the continuation summary at each node that runs a `Resume` (section 4.5) |
| `finish_spared` | `spared_at` from the abort destinations (section 4.4) |
| `check_int_lits`, `finish_int_ops` | `typeck` and the integer type of `Binary` |
| `settle_moves` | final types: no tentative move |
| `finish_via_calls` | the `writes_via` rule of the `Call` template |
| the flag pass | the props of each `LocalDecl` |
| `dropped_params`, `held_params` | the `drops` and `holds` queries |

### 4.3 Places, roots and variables

**Roots.** The fact generator makes these roots for one component:

| IR object | Root kind | Shown as | Owner variable |
| --- | --- | --- | --- |
| a local of a body of the component (also a temporary, the environment of a closure value, a by-value parameter) | `Local` | its name or its temporary kind | the local |
| the pointee of reference parameter `i` of the function | `Param` | `*p` | none |
| the pointees of the references inside parameter `i` (by value or behind a reference) | `Param` | `*p..` (wildcard) | none |
| the `rc` group of a type | `Group` | the type | none |
| the pointee of an environment field or of a reference parameter of a closure or a clause | `Arg` | the capture or the parameter | none |
| the capability of a `handle` | `Local` | `capability of handle E` | the capability variable; it ends at `Post` and at `Landing` |
| the continuation of a clause | `Local` | `resume` | the continuation variable; it ends at the clause `Return` |
| the scope capability | `Local` | `s` | it ends at the `FrameEnd` of the scope |
| a place of a caller that the body cannot name | `Arg` | `a place of a caller` | none; `lends_mut` at each node that runs code of a caller |
| a local of the callee of call node `n` that the callee gives back | `Local` | `a local of f` | a variable of `n`; `scope_end` at `FrameEnd` of `n` and on its abort paths |
| a local of a clause of handler `h` that a clause gives back (to `resume`, or as its value) | `Local` | `a local of the clause` | a variable of the `Handle`; `scope_end` at `Post` and `Landing` |
| in a clause component: a place of the handled body that the clause cannot name | `Local` | `a local of the handled body` | a variable of each `Resume`; `scope_end` at its `FrameEnd` |

The last five rows are the frames of the machine that the body cannot see. The caller
frame root fixes N1 and N2 of `docs/plan/core-ir-inputs/map_lowering.md` by one rule: the result of code of a
caller (a perform through `Row`, a call of a function parameter or of an unknown value)
points into the argument places and into the caller frame root. The callee frame root
fixes M4 and F3-2: a callee that gives back a place in its own frame (an operation
argument, a reference that a closure parameter keeps) gives a place that dies at `Ret`.

**α: from an IR place to fact places.** α walks the projections:

| Projection | Fact step |
| --- | --- |
| the base local `l` (owned) | the root of `l` |
| `Field(f)` | the field step (stable) |
| `Variant(v)` | the variant step (unstable) |
| `Index(_)`, `Elems` | the element step; its stability comes from the type (`elem_step`) |
| `Split(s, side)` | the split step of split `s` (one split for each call and parameter, QA17) |
| `Deref(Box)` | the deref step (unstable) |
| `Deref(Rc)` | the group root of the inner type; the handle place `h.*` joins the places of each reference made through it (ADR 0003) |
| `Deref(Ref)` of a move path `p` of the body | the places in `refs` of `p` in the state at the node |
| `Deref(Ref)` of an interface place (a parameter, an environment field) | the interface root of that place, or its `Held` wildcard root for a second `Deref` |

So the stability of each step comes from the type of the projection (B2), and a place
through a reference names the reference (B6, C8).

**Variables.** The fact variables are move paths: each local, and each part of a local
that the body assigns, moves or leaves unset on its own. There is also one variable for
each heap slot that can hold a function value or a capability. The flags of a variable
come from the props of the type of its move path, joined with the modes of the closures
that the analysis says it can hold (V061). The hidden variables of
`docs/plan/core-ir-inputs/map_lowering.md` 1.6 map to IR locals:

| Hidden variable today | In the IR |
| --- | --- |
| held operand (`argument`, `receiver`, `operand`, `tuple part`, `element`, `field`) | a temporary of kind `Operand` or `Receiver` |
| value on its way (`hold_moved`) | the same temporary; a move fills it |
| block value (`hold_out`) | the destination of the block (a local or `_0`) |
| temporary owner (`temp_root`) | a temporary of kind `Borrowed` |
| part holder `value in p`, stale part holder | the move path variable of the part |
| unset place field | the move path variable of the field, with `Uninit` |
| `{iterator}` | the `Iterator` local |
| `{closure}` | the local that holds the closure aggregate |
| `{stored closure}` | the variable of the heap slot that holds the value: `points_into` the places that the environments of its values hold; `uses` at each node that runs a value from the slot (a store into a slot is a weak update, so it does not rebind) |
| continuation `resume` | the `Kont` local of the clause |
| dropped linear value (`drop_linear_as`) | the temporary of kind `Discarded`, with `Drop` |
| value that a generic callee holds | the argument temporary; it moves at `Ret` (the `holds` part) |
| moved temporary (`move_temp`) | the temporary; a `Move` of a `!Move` value that is not `in_place` |
| task handle | a local of type `Task<T>` |

### 4.4 Frames in the facts

**Components.** One `FnFacts` for each function and each test. Its components are the
body of the function, each closure body and each clause body inside it. A handled body
and a scope body are spliced into the component of the body that runs them. A closure
and a clause are components of their own: they can run at many nodes, so their effects
reach a run node through their summary (section 4.5).

**The splice of a once-run frame.** For a `Handle` of handler `h` at node `n` in body
`B`, with handled body `H`, and a suspending node `P` inside `H` (or inside a frame that
`H` splices):

```text
n.Main ──► entry of H
Return of H ──► n.Exit ──► n.Post ──► first node of next            (normal end)
P.Main ──► P.AbortValue(h) ──► cleanup chains from P up to H (copies for h) ──► n.Landing ──► next
P.Main ──► cleanup chains from P up to H (copies for "past h") ──► unwind block of n in B
```

- At `n.Exit`, `dest` binds (the value of the body exists; `_0` of `H` is used there, so
  a reference in it into a local or a temporary of `H` is W0301: O3-2). At `n.Post` the
  clauses run their code after `resume` (the `post` part of their summary), and then the
  capability and the clause frames end. A change of a clause after its `resume`
  therefore invalidates a reference in the value (M1). At `n.Landing`, the capability
  and the clause frames end.
- At `P.AbortValue(h)`, `dest` binds to the value of the clause, with σ of `P` (a clause
  parameter maps onto the argument places at `P`), before the unwinding. There is one
  such node for each suspending node and each local handler that it can abort to, because
  the cleanup chain that follows depends on `P`.
  The cleanup chain of `H` then frees the locals of `H`. A reference in the value of the
  clause into a local of `H` (through an operation argument) is invalid after the
  landing (M3). This is the order of the machine: the clause returns, `drop_now`
  unwinds the continuation, then `deliver` gives the value to the frame below
  (`effects.rs:132`).
- A `Scope` is the same with no `AbortValue` and no `Landing`: no clause stops an abort
  there. `ScopeWait` and the scope body locals end before `Exit`.

**Abort destinations.** Each suspending node `P` has a set of destinations. A perform
through `Local(cap of h)` aborts to `h`. A call or a resume aborts to each `h` that its
summary performs through (after the capability resolution), and to "past the
function" if it performs through `Row`, can fail, can be cancelled, or has an `assert`.
The fact generator instantiates the cleanup chain of each frame between `P` and a
destination once for that destination (`NodeKey::dest`). So an abort to `h` never
reaches the cleanup of the frames outside the handled body of `h`. Then:

- `unwound_at(V, Q)` holds exactly on the cleanup nodes of the frames that the abort
  leaves.
- `spared_at(V, P)` holds for each variable `V` that is live at `P` and that no cleanup
  chain of a destination of `P` finishes. This is the meaning that ADR 0005 states, as a
  fact of the CFG. OR4, OL-R2c-1 and V116 are about this set; V074, V084, V086, V088
  and V089 are about the abort edges. Here neither has a special case.

**Re-entry edges (`multi`).** Let `P` be a node with `multi_at(P)`. Its continuation
holds the frames from `P` up to its destination: the handled body of `h` and the frames
inside it, or, for a capability of a caller, the whole frame of the function. For each
such `P`, the fact generator adds:

```text
end of the copied region ──► Copy(P) ──► P.Ret
```

The end of the copied region is `n.Post` of the `Handle` of `h` (after the clause code
that runs between two resumes), or the `Return` of the function for a capability of a
caller. `Copy(P)` emits `rebound_at` and `empty_at` for each variable of the copied
frames whose places are all in the roots of the copied frames: the copy of the machine
(`copy_frames`). A variable that points outside keeps its state, so a reference that the
first run invalidates is invalid in the second run (ADR 0005). This one rule covers a
local handler (`handled_again`) and a handler of a caller (OL-R2a, which has no edge
today). A tail move of a value from outside the body is on the cycle (O3-14). A
one-place instance is off on each node of the cycle (V097).

**The entry of a component.** A closure or a clause component starts at the entry node
of its body. Its parameters, its environment and its continuation bind there
(`rebound_at`). A linear capture by move is a field of the environment, so a new value
of it inside the closure is `overwritten` (S002) with no special case.

### 4.5 Summaries

One procedure `summarize(body)` computes the summary of each body from the states of
the analysis at its nodes. One procedure `apply(Σ, σ, n)` emits the facts of a summary
at a run node. Each part is a projection of the effects of the nodes of the body onto
its interface. A new relation of the spec needs one new part, which each run node then
gets (INNER: today a new `Summary` field needs a mapping at each of six sites).

**Interface roots.** The parameters (`Param(i)`, and `Held(i)` for what references in
the parameter point to), the environment fields (`Env(k)`), the capability operands
(`Row(E)` and capability fields of the environment), the continuation, the caller
frame, and `_0`.

**Parts.**

| Part | Content (in interface places) | Replaces today |
| --- | --- | --- |
| `muts` | places that the body changes, with the unstable steps | `Summary::muts`, `mut` places of an inferred row, `footprint` sources |
| `reads` | places that the body reads | `Summary::reads` (OR10: a call reads only what the callee reads) |
| `frees` | places that the body frees: moves out of a by-move environment field, frees through code of a caller, frees of a continuation | `Summary::dropped`, `ContInfo::frees`, `releases_at` sources |
| `lends` | places that the body gives to code that it does not know | `Summary::lends`, `lent` |
| `performs` | the operations and their capability interface | `performs`, `op_args`, `cap_runs`, `callee_ops` |
| `aborts` | the abort destinations (by capability interface), `assert`, failures | `abortive`, `abortive_local`, `raises` |
| `multi` | the capability interfaces through which the body can resume more than once | `multi`, `reach_repeats` |
| `runs` | each function value of the interface (a parameter, an environment field) that the body runs: how many times (one, many), at which order, as a task or not, with which places | `lent`, `repeats`, `task_runs`, `op_fns`, `held_run` |
| `tasks` | the footprints of the tasks that the body starts in a scope that it does not own; the capabilities that its tasks hold | `spawns`, `tasks`, `task_effects`, `pins` |
| `ret` | the abstract value of `_0`: places, closures (their environment in interface terms), capabilities, tasks, results of code of a caller | `ret`, `RetFn`, `ret_refs`, `stores` of a returned value |
| `stores` | the values that the body writes behind a reference parameter or into an `rc` object | `stores`, `fn_stores`, `group_stores`, `stored_behind` |
| `drops`, `holds` | type parameters (section 3.20) | `drops`, `holds` |
| `uses`, `moves` | the environment fields that the body uses or moves when it runs | `late_join` uses, `moved_captures` |
| `pre`, `post` (clauses only) | the parts above, split at the `Resume` nodes: before them, and after them | `run_handler` (whole clause at the perform) |

**The kinds of run node**, all with `apply`:

| Run node | Summary | σ maps |
| --- | --- | --- |
| `Call` of an item | the item | parameters to the argument places; `Row(E)` through `CapArgs` |
| `Call` of a closure value | the closure body | parameters to the arguments; `Env(k)` to the place of the capture (the variable itself for `ByRef`, so the current value of the variable counts: RR7 and V103 by construction) |
| `Call` of a parameter or an unknown value | "code of a caller": `lends` of all reachable places, `ret` into the arguments and the caller frame, `aborts` and `multi` by its row | the same |
| `Perform` through a local handler | the `pre` part of each clause of the operation | clause parameters to the argument places (S053, F3, V035); the clause environment to the site places |
| `Perform` through `Row(E)` | "code of a caller", with the effect `E` | the same |
| `Handle` at `Post` | the `post` part of each clause | the same as the perform; the `resume` result to `_0` of the body |
| `Resume` | the continuation of the handler: the effects from each suspension node of the handler to the `Return` of the handled body, and `ret` = `_0` of the handled body | the places of the handled body that the clause can name (its parameters and environment); the places it cannot name to the caller frame root |
| `Spawn`, `Fork` branch | the task body; its effects become `task_reads` and `task_writes`, not `mutates_at` of the parent after the spawn node | as a closure call |
| `UnwindValue` with `OnAbort(f)` | `f` | the parameter to the value; `CapArgs::Root` |
| a node of code that can run stored values (unknown code, an item with no body) | the summary of each function value in a heap slot that the arguments reach | as a closure call |

A callee that runs a function argument more than once (`runs` says "many") gets the
summary of that argument applied twice: at `Main` and again at `Ret`, so that a change of
the first run invalidates what the second run uses (OR3, V043, V106; today a "call
again" node). A function argument that runs as a task gets `spawned_at` at `Main` and
`joined_at` at `Ret` (OR7, V126, V127, V132).

**Soundness of a summary** is a hypothesis of the design, not a theorem: each part must
contain each effect of the body on its interface. The design reduces it to one
procedure, and tests it at run time (section 6.3, the summary oracle).

### 4.6 Worked examples

**M3** (`m8_abort_value_into_body.wf`, IR in section 2.5). The perform `P` in `bb2` of
the handled body aborts to `h`, because the clause of `pick` returns with no `resume`.
The facts of the abort path:

```text
P.Main      performs_at(P, cap_h); call_arg(P, w, param0); may_abort(P)
            (clause summary pre: reads (*v)[] -> reads_at(P, w[]))
P ──► P.AbortValue(h) = a
            rebound_at(r, a); points_into(r, w[])      (the clause value &v[0], v -> &w)
a ──► cleanup copy for h:  Dead(_6) ; UnwindValue(_3 = w, Drop) ; Dead(w)
            unwound_at(w, c); owner(w, w) -> frees_at(c, w) -> invalidated_at(r, c)
c ──► n.Landing ──► main.bb1:  Print(copy r)   uses(r, q)  -> error(r, q): W0301
```

Today the checker accepts this program, and the oracle faults (Appendix A).

**M1** (`m1_post_resume.wf`). The clause is `let x = resume(()); v.clear(); x`. The
handled body ends with `&v[0]` in `_0`. At the `Exit` node of the `Handle`, `r` binds
to `v[]`. At the next node, `Post`, the `post` part of the clause applies: `v.clear()`
changes `v` below an unstable step, so `mutates_at(post, v)` invalidates `r`. The use
`print(r)` is W0301.
Today the change of `v` is at the perform node, before `&v[0]` exists.

**M2** (`m6b_resume_result_ref.wf`). In the clause component, `x = resume(())` binds at
`Ret` of the `Resume` node to the `ret` of the continuation: `_0` of the handled body,
`&v[0]`, which the clause names as `(*env.v)[]`. Then `v.clear()` in the clause changes
`(*env.v)`, and `print(x)` is W0301.

**O3-14** (a tail place of a `multi` body). The handled body ends with
`_0 = move x`, `x` a local of the parent. The re-entry edge goes from `Post` through
`Copy` back to `P.Ret`. `x` is outside the copied frame, so `Copy` does not rebind it,
and the second `move x` sees `moved(x)`: W0302.

### 4.7 W0313 and W0314: capabilities as values

- The capability of a `handle` is a value: a variable with a root that ends at the
  `Post` and the `Landing` of the `Handle`. A closure value holds the capabilities of
  its `cap_env` that its row uses (the analysis puts them into `AbsVal::caps`, and the
  closure variable `points_into` their roots). A continuation is a `Kont` local with a
  root that ends at the clause `Return`.
- So "a closure that performs through `h` is used after the `handle`" is W0301 on a
  capability root. Stage 4 keeps the code W0313: `diagnose.rs` reports an `error(R, P)`
  whose invalidating free is a capability root as W0313, with the text of today. A
  closure returned, stored behind a parameter, or put into an `rc` object, with a
  capability root among its places, is the W0204 check on that root, reported as W0313.
  RT16, V046, V047, OL-1c, RR3, V077, V120 and V049 become these two rules.
- W0314 (a task reaches a handler on the stack of another task) is a check over the
  `tasks` part of the summaries: the capabilities that a task holds or uses. Stage 4 runs
  it in Rust over the analysis (as sema does today). Stage 7 moves it into the spec:
  an input relation `stack_cap(Rt)` and a rule `foreign_cap(T, V) :- captures(T, V),
  points_into(V, Path), stack_cap(Rt), prefix(Rt, Path)`, through the checklist of
  ADR 0002.

### 4.8 The invariants of `docs/plan/core-ir-inputs/map_lowering.md` section 5

"Construction" means: the IR has no form for the violation; the verifier (V1 to V12)
and one template give it. "One rule" means: one function of the analysis or of the
summaries gives it, so no construct can forget it; its soundness is still a property of
that function.

| Invariant | Status | How |
| --- | --- | --- |
| A1 path cover | construction | the CFG of the IR is the code that the interpreter runs (section 6); `unwind` edges, splices and re-entry edges are explicit; abort and re-run edges of a call depend on its summary (one rule) |
| A2 components | construction | one component for each body that can run at many nodes; once-run frames are spliced |
| A3 run-node cover | one rule | `apply` of section 4.5 at each run node; each part is a projection of all effect kinds |
| A4 order inside a node | construction | one instruction for each node; `Ret`, `FrameEnd`, `AbortValue`, `Exit`, `Post`, `Landing`, `Copy` nodes in a fixed order |
| A5 `no_gen_kill` | construction | a right side cannot change memory; a call result binds at `Ret`, and the frame that gave it ends at `FrameEnd`; `Exit` binds and `Post` changes |
| A6 `bound_before_use` | construction | V4: each use has a cell on each path; each component binds its parameters at its entry |
| B1 interned tree | construction | the place interner (unchanged) |
| B2 typed stability | construction | α takes the stability from the type of each projection |
| B3 root truth | construction | the roots of section 4.3; the caller and callee frame roots name the frames that the body cannot see |
| B4 wildcards | one rule | the widening of the analysis and the cut of summary places |
| B5 split ids | construction | `SplitId` in the projection |
| B6 handle places | construction | `Deref(Rc)` in the path; α adds `h.*` |
| C1 points-into cover | one rule | the transfer functions; the summaries `ret`; the caller frame rule (N1, N2) |
| C2 holder cover | construction | each value in transit is in a local with storage; a frame value is in `_0` until `Ret` or `Exit` |
| C3 rebind hygiene | construction | the value binds where it exists: `Ret` before `FrameEnd`, `AbortValue` before the cleanup, `Exit` before `Post` (M1, M3, M4, O3-2, O3-3) |
| C4 free cover | construction | each free is a `Drop`, `Dead`, `Move`, `Consume`, `UnwindValue`, or a summary `frees` part; the callee frame root (F3-2, M4) |
| C5 change cover | one rule | `Assign` through `Deref`; summaries; `lends_mut` of code of a caller |
| C6 `writes_via` | one rule | the `Assign` and `Call` rule of section 4.1 |
| C7 part moves | not by the IR | a spec rule (F3-5; R3a has a rule change) |
| C8 references behind references | construction | a second `Deref` in the place; `call_arg` of each place that an argument reaches (R3RT2, R3RT3) |
| D1 move cover | construction | `Move` operands; tails are moves; `Consume` |
| D2 new values | construction | `Assign`, `Ret`, `Exit`, `AbortValue`, `Copy` |
| D3 normal ends | construction | drop elaboration on each normal path (V6) |
| D4 suspension cover | construction | each suspending terminator has its `unwind`; `Assert`, `ScopeWait`, `Join`, `Fork` included (N4, F3-7) |
| D5 linear holders | construction | each linear value is in a local with the `linear` flag; task results with no handle are `TaskResult` locals (O3-4) |
| D6 flags | construction for the IR; not for type rules | props from the final type; `Task<T>` and `on abort` (I3-1, F3-6) stay a type rule |
| D7 unset values | construction | `Uninit` of each place field from the full type (Q3-1, V062) |
| E1 `multi` cover | one rule | `multi_at` from the operation, the summary and the clauses |
| E2 re-runs | construction | the re-entry edges for each `multi` node, local and caller handlers (OL-R2a) |
| E3 `spared_at` | construction | the abort destinations and the copies of the cleanup chains |
| E4 `once_var` | construction | props |
| F1 `spawned_at` | construction | `Spawn`, `Fork`, the `tasks` and `runs` parts at run nodes |
| F2 `joined_at` must | one rule | the must-set of the task part of the state |
| F3 task footprints | one rule | the task body summary; heap slots for stored values (O3-5); the handle in the path (O3-6) |
| F4 parent accesses | construction | operands and destinations |
| F5 `kept` | construction | `KeptCell` captures only |
| F6 pinning facts | one rule | the env fields and the `tasks` part |
| G1 effects | one rule | capability resolution through `CapArgs` |
| G2 call roots | construction | one `call_arg` rule for every call form |
| G3 caller changes | construction | α roots `Param` and `Group` |
| G4 call checks | construction | the `Call` and `Perform` templates (R3RT7: an operation parameter with `in` gets `param_in`) |

---

## 5. Root-cause classes: what the design removes and what stays

This section uses the 290 classified findings of `docs/plan/core-ir-inputs/root_causes.md` (data:
`SCRATCH/ir/work/findings.py`). The tables are generated from that file and from the
verdicts of this design by `SCRATCH/ir/work/machine/tools/section5.py`, which also
checks the totals (180 unsound findings, 53 false positives).

### 5.1 Counts

The counts use the primary cause of each finding, as `docs/plan/core-ir-inputs/root_causes.md` does. Three
verdicts:

- **Construction**: the IR has no form for the defect; the verifier and one template
  give it.
- **One rule**: one function of the analysis or of the summary procedure gives it.
  No construct can forget the case. The function itself can still be wrong, so the
  risk moves into one place that tests can aim at (section 6.3).
- **Stays**: a decision of the spec, of the types or of the language, or a cause
  outside the lowering.

| Verdict | Unsound | Share | False positives | Share |
| --- | --- | --- | --- | --- |
| Construction | 87 | 48% | 25 | 47% |
| One rule | 64 | 36% | 14 | 26% |
| Stays | 29 | 16% | 14 | 26% |
| Total | 180 | | 53 | |

The difference to `docs/plan/core-ir-inputs/root_causes.md` (83 by construction, 70 partly, 27 not at all):
the machine design adds MULTI and two PART findings to "construction" (re-entry
edges; `Uninit` from the full type). It moves most of the "partly" classes to "one
rule", because it takes the decisions that `docs/plan/core-ir-inputs/root_causes.md` leaves open: a set-valued
closure analysis with heap slots, summary parts as queries (with `runs`, `holds` for
each parameter, task accesses), the caller and callee frame roots, and capabilities
and continuations as values.

### 5.2 Classes by construction

These are the classes of group A and A* of `docs/plan/core-ir-inputs/root_causes.md`. TWO needs stage 3 (the
interpreter runs the IR). The mechanism column names the section of this design.

| Class | Unsound | False positives | Mechanism |
| --- | --- | --- | --- |
| TEMP | 9: RT4, RT18, V007, V015, V072, OL-3c, O3-2, O3-3, F3-7 | 0: - | temporaries are locals with `Live` and `Dead`; the frame end of 3.1.4; values bind where they exist (4.4) |
| TAIL | 4: V059, V118, O3-1, O3-14 | 1: V058 | `into(e, dest)`: each tail is an `Assign` of a move or a copy; a discarded value gets a `Drop` (3.1.1, 3.4) |
| DROP | 8: RT1, RT14, V002, V057, FD1, O3-4, F3-1, F3-3 | 1: V083 | drop elaboration (3.1.3); `UnwindValue` with the `on abort` summary (3.1.6, 3.31) |
| ORDER | 1: RT2 | 0: - | each read is an operand of one statement; no pending queue (2.1) |
| ACCESS | 3: RT10, OL-R2d-box, OR8 | 0: - | operands, destinations, `Len`, `Bounds`, `Deref` in the path (4.1) |
| DEREF | 7: RT9, V008, V014, V020, V098, O3-6, R3RT2 | 1: V085 | `Deref` as a projection; α of section 4.3 |
| CALLS | 8: RT17, RT24a, F3, V035, V039, V042, V136, R3RT3 | 3: OL-S5c-w0312, O3-7, R3RT7 | one `Call`, one `Perform`, one `Resume` template; `call_arg` of each reachable place (4.1) |
| ENV | 15: RT5, RT8, V009, V017, V018, V027, OL-5, OR2, RR4, RR7, V103, V104, V116, V125, V134 | 5: V012, RR12, O3-11, R3RT5, F3-11 | the closure aggregate and the environment parameter; one `capture_mode` (3.1.7, 3.22) |
| INNER | 9: RT11, RT12, F4, V006, V024, V053, RR5, V121, R3RT4 | 3: OL-R2d-clause, O3-8, O3-12 | one body for each frame; splices and summaries (4.4, 4.5) |
| SUSP | 5: RT13, V036, V074, V086, V088 | 5: V055, OL-R2c-1, OR4, V084, O3-10 | `unwind` edges; copies of the cleanup chains for each destination; `spared_at` from the CFG (4.4) |
| LOOP | 3: V025, V041, RR1 | 1: V101 | back edges and one fixpoint with widening (3.14, 4.2) |
| VAL | 2: RT3a, V073 | 3: RT22, V044, OL-6b | one transfer function for each right side (4.2) |
| POST | 5: V028, OL-1d, OL-2b, V089, V093 | 1: V079 | facts are a pure function of the final analysis (4.2) |
| TYPES | 0: - | 1: V060 | the builder runs after type inference (1.3) |
| TWO | 4: V045, OR6, RR10, IP6 | 0: - | the interpreter runs the IR (section 6) |

### 5.3 Classes that root_causes.md calls "partly": each finding

| Id | Kind | Class | Verdict | Mechanism or reason |
| --- | --- | --- | --- | --- |
| RT6 | U | FNVAL | one rule | the callee operand has a set of values; each item applies its summary |
| RT7 | U | FNVAL | one rule | closure values flow through returns, tuples, `if` and fields as abstract values |
| V026 | U | FNVAL | one rule | `ret` holds closures with their environment in interface terms; a maker through a parameter is code of a caller |
| V029 | FP | FNVAL | one rule | σ maps the parameter of a stored closure onto the places that the run node gives |
| V032 | U | FNVAL | one rule | an abstract closure value nests (cut at a fixed depth to an unknown value) |
| V033 | U | FNVAL | one rule | the callee summary has `runs` and `ret`; both apply at the call |
| V049 | U | FNVAL | one rule | capabilities are in the abstract value, also inside a tuple |
| V061 | U | FNVAL | one rule | the flags of a variable join the modes of the closures that it can hold |
| OL-1a | U | FNVAL | one rule | heap slots hold function values; a task applies the summary of each one |
| OL-1b | U | FNVAL | one rule | the `ret` and `stores` parts read the heap slots behind a reference argument |
| OL-R2d-struct | U | FNVAL | one rule | unknown code runs each value in a heap slot that its arguments reach |
| OL-S5c-pair | FP | FNVAL | one rule | a known closure keeps one root at one node; heap slot sets name the values |
| OR1 | U | FNVAL | one rule | the environment of a returned closure is in interface terms (`Param(i)`); σ maps it onto the argument |
| RR2 | U | FNVAL | one rule | a set of closures, not one summary for each type |
| RR6 | U | FNVAL | one rule | the result of a perform is the `resume` values of the clauses (one fixpoint) |
| V075 | U | FNVAL | one rule | values of a type parameter and references behind references carry abstract values |
| V076 | U | FNVAL | one rule | heap slots behind a second `Deref` |
| V105 | U | FNVAL | one rule | the elements of a `Vec` are a heap slot |
| V107 | U | FNVAL | one rule | a tuple part holds a set |
| V111 | U | FNVAL | one rule | `ret` reads the heap slots of a returned container |
| V119 | U | FNVAL | one rule | the summary of the `on abort` function applies at `UnwindValue`, with the values in the finished value |
| V126 | U | FNVAL | one rule | the callee summary `runs` reads the heap slots of its local container |
| V133 | U | FNVAL | one rule | `ret` of the callee holds the function values of the returned struct |
| O3-5 | U | FNVAL | one rule | a task applies the summary of each value in the heap slot of the field |
| V011 | U | SUM | one rule | code of a caller returns the wildcard places of its arguments and the caller frame root |
| V040 | U | SUM | one rule | the `multi` part propagates from the unknown value through the callee summary |
| V043 | U | SUM | one rule | `runs` = many: the summary of the callback applies at `Main` and at `Ret` |
| V051 | U | SUM | one rule | the `tasks` part names the capabilities that the tasks use; the call resolves them |
| OL-2a | U | SUM | one rule | unknown code can run a stored value many times: two applications |
| OL-R2c-2 | FP | SUM | one rule | the continuation summary frees only what the rest of the body frees (callee frame root) |
| OR3 | U | SUM | one rule | two applications for a callback that runs many times |
| OR7 | U | SUM | one rule | `runs` as a task: `spawned_at` at `Main`, `joined_at` at `Ret` |
| OR10 | FP | SUM | one rule | the `reads` part: a call reads what the callee reads |
| V078 | U | SUM | one rule | the caller frame root |
| V080 | U | SUM | one rule | two applications of a stored spawning closure |
| V082 | U | SUM | one rule | `holds` covers each parameter, not only type parameters: a `once` argument held across `multi` is W0503 at the call |
| V106 | U | SUM | one rule | `runs` through a heap slot of a container argument |
| V115 | FP | SUM | one rule | `runs` counts the runs from the CFG (two nodes, a cycle, a closure that runs many times) |
| V127 | U | SUM | one rule | the `pre` part of a clause that runs an argument as a task |
| V132 | U | SUM | one rule | `runs` as a task records the places that the body accesses while the task is active |
| V037 | U | STORE | one rule | the `stores` part of the closure; σ maps its parameter onto the callee frame root when a callee runs it |
| OL-4a | U | STORE | one rule | a read back through a reference parameter gets the `Held` wildcard root |
| OL-R2b-res | U | STORE | one rule | the callee frame root: a place that a callee gives to a closure dies at `Ret` |
| OL-R2b-prec | U | STORE | stays | `rc` group places do not tell objects apart: a language or model decision |
| OL-S5a-store | U | STORE | one rule | the `stores` part maps a store behind a closure parameter onto the argument places |
| FD3 | U | STORE | one rule | a store into a `Group` place is one statement form; the W0204 check runs on `stores` |
| V087 | U | STORE | one rule | a store of a reference into an exiting root behind a parameter: one check on `stores` |
| V108 | U | STORE | one rule | the check runs on the summary of each body: closures and clauses too |
| F3-2 | U | STORE | one rule | the callee frame root |
| RT3b | U | GEN | one rule | `ret` of a generic callee is in terms of its parameter values; extern containers store their by-value arguments into their reference arguments |
| V031 | U | GEN | one rule | the same: a closure in a generic container is in a heap slot |
| V056 | U | GEN | one rule | a closure keeps its modes in its abstract value; `drops` and `holds` apply with the real argument |
| OL-3a | U | GEN | one rule | `holds` is a query over the IR of the generic callee |
| OL-R2c-3 | FP | GEN | one rule | `holds` applies with the type argument at the call, not the worst case |
| OL-NR-ptrfork | U | GEN | one rule | the `tasks` part says which parameter values a fork branch captures; the call checks the type argument |
| RR9 | U | GEN | one rule | a function item value gets its summary with its type arguments where it is made |
| V081 | U | GEN | one rule | the same, with `holds` |
| V023 | FP | PART | stays | a spec rule for each move path (W0301, W0302) |
| V062 | U | PART | construction | `Uninit` of each place field of a value built in place, from the full type |
| R3RT1 | U | PART | stays | a spec rule for each move path; the IR gives the move paths (R3a has a rule change) |
| Q3-1 | U | PART | construction | `Uninit` from the full type, not from the ADT id |
| RT24b | U | STATE | one rule | the `uniq` flag of a variable holds only if each of its values is `@ uniq` |
| V066 | U | STATE | one rule | the same: no lowering order |
| V069 | FP | STATE | one rule | the variable of a part rebinds at each new value of the part or of the whole local |
| OL-4b | FP | STATE | one rule | the same: no stale holder |
| OL-6a | FP | STATE | one rule | a new value of a closure variable rebinds it, so W0313 on a capability root stops there |
| OL-R2b-holds | FP | STATE | stays | `points_into` has no node in the spec (an option: one variable for each definition) |
| OL-NR-flow | FP | STATE | stays | the same |
| V096 | U | STATE | one rule | the must-set of the holders of a task handle |
| O3-9 | FP | STATE | one rule | a task handle flows through callees, tuples, `Option`, `id` and closures as an abstract value |
| R3RT6 | FP | STATE | one rule | the `stores` part of a callee says which arguments flow into which |
| R3RT10 | FP | STATE | one rule | the variable of a part, rebound at the new value |
| OL-R2a | U | MULTI | construction | re-entry edges for a handler of a caller |
| OL-NR-multi | FP | MULTI | stays | the re-run is path-insensitive: a precision choice of the spec |
| V097 | U | MULTI | construction | one-place instances are off on each cycle, re-entry edges included |
| RT16 | U | CAP | one rule | a closure holds the capability root of its handler; a use after the `handle` is W0301 on that root, reported as W0313 |
| R1-SIM | FP | CAP | one rule | the capabilities inside `sim.run` are root capabilities: no stack handler |
| V046 | U | CAP | one rule | a check at each perform and resume through `h`: no operand holds the capability of `h` |
| V047 | U | CAP | one rule | the same check for the `resume` argument and the result |
| V050 | U | CAP | one rule | the `pre` part of the clause: it runs its argument as a task that holds a stack capability (W0314) |
| V052 | U | CAP | one rule | a task applies the summary of a value from a heap slot; its capabilities count |
| V054 | FP | CAP | one rule | capabilities flow through `Box.new`, `Rc.new` and generic callees as abstract values, with no worst case |
| OL-1c | U | CAP | one rule | a clause value or store that holds a capability root of an outer handle: W0204 on that root |
| OL-S5a-w0314 | U | CAP | one rule | the `tasks` part of code of a caller with its capabilities |
| OR9 | U | CAP | one rule | a task that holds a continuation holds a stack value of the clause: W0314 |
| RR3 | U | CAP | one rule | a closure that resumes holds the continuation root, which ends at the clause `Return` |
| V077 | U | CAP | one rule | a value read through a clause parameter keeps its capabilities |
| V120 | U | CAP | one rule | the check at `resume` of rule V046 |

### 5.4 Classes that stay

| Class | Unsound | False positives | Why |
| --- | --- | --- | --- |
| SPEC | 13: RT24c, F6, V010, V016, OR5, FD4, IP1, IP3, V095, V117, V124, F3-5, F3-8 | 3: V013, QA6, V130 | a rule of the spec or a fact model is too weak or too coarse; the IR gives cleaner input (move paths for F3-5), but the fix is the rule |
| TYPE | 12: RT3c, RT15, RT24d, F5, QR5, QR7, V063, V067, RR8, QA3, F3-4, F3-6 | 4: RT20, OL-3b, OL-R2e-reassign, R3RT11 | type properties, signature checks and prelude signatures (`props.rs`, W0118 inputs aside) |
| INF | 1: QR6 | 1: V001 | the bounds of the inference over the call graph |
| NAMES | 1: V003 | 2: V138, Q3-3 | name resolution and visibility |

### 5.5 The new findings

These findings are not in `docs/plan/core-ir-inputs/root_causes.md`. Each one is open at `616f99c` (R3a): I
re-ran each probe there (Appendix A).

| Id | Source | Shape | Verdict in this design | Mechanism |
| --- | --- | --- | --- | --- |
| N1 (map) | `docs/plan/core-ir-inputs/map_lowering.md` 4.2, `work/map/opres.wf` | the result of an operation of a caller's handler does not point into the reference arguments | one rule | the result of code of a caller: argument places and the caller frame root (4.3) |
| N2 (map) | `work/map/fnres2.wf` | the result of a call of a function parameter with no reference argument has no places | one rule | the same rule |
| N1 to N3 (semantics) | `docs/plan/core-ir-inputs/semantics.md` 2.2, probes p2, p9, p10 | a place operand is read later than the facts say (binary operator, `print`, index base) | construction | choice A: each operand is read where it is written (3.1.1) |
| N4 (semantics) | probes p25, p27 | `assert` aborts the task, but has no abort edge | construction | the `Assert` terminator with `unwind`; the `aborts` part of the summary (3.33) |
| M1 | `work/machine/m1_post_resume.wf` | the code of a clause after `resume` changes a place that the value of the handled body points into | construction | the `Exit` node binds the value; the `Post` node after it runs the `post` part of the clause (4.4) |
| M2 | `work/machine/m6b_resume_result_ref.wf` | the result of `resume` does not point where the value of the handled body points | one rule | the `ret` of the continuation summary (4.5) |
| M3 | `work/machine/m8_abort_value_into_body.wf` | a clause that does not resume returns a reference into a local of the handled body | construction | `AbortValue` before the cleanup chain (4.4, 4.6) |
| M4 | `work/machine/m10_abort_value_callee_local.wf` | the same with a local of a callee that performs | one rule | the callee frame root (4.3) |

### 5.6 How the classes met, and what meets now

`docs/plan/core-ir-inputs/root_causes.md` lists ten soundness regressions of fixes. In each one, a fix in one
class broke an assumption of the code of another class. In this design each pair is one
mechanism:

| Regression | Classes | One mechanism in this design |
| --- | --- | --- |
| V045 | TWO | the interpreter compiles the IR, so effect resolution is the one of the builder |
| V073 | VAL, DROP | the value of a `handle` is `dest`; `empty_at` comes from the abstract value of each source that binds it (`Exit`, `AbortValue`) |
| V074, V088 | CAP, SUSP | W0313 is a reference rule on capability roots, and each abort path is an edge of the IR with its destination |
| V089 | CAP, POST | no post-pass: stored values are heap slots of the analysis, and their abort edges come from their summaries before the facts exist |
| V095 | SPEC, SUSP | the continuation summary gives `releases_at` from the frees of the rest of the body; no `x..` encoding of "a change above" |
| V096 | LOOP, STATE | the must-set of task holders is a part of the state; the loop is a cycle of the same analysis |
| V097 | SPEC, MULTI | one-place instances are off on each cycle; re-entry edges are cycles |
| V116 | SUSP, ENV | `spared_at` comes from the cleanup chains; a by-move capture is a field of the closure environment, which the abort finishes with the closure |
| V125 | ENV, SPEC | `KeptCell` is a capture mode of its own; a reference that the task makes into the cell is an ordinary `&x` with an owner |

A new feature in this design needs a new IR form or a new summary part. Each run node
and each template gets it at once, so the pattern "a feature adds a mechanism at the
sites that its author knew" (`docs/plan/core-ir-inputs/map_lowering.md` 3.2) has no sites to miss. The
remaining interaction risk is inside the analysis and the summary procedure. Section 6.3
tests them at run time.

### 5.7 What stays

- **Spec and fact model (SPEC, 13 + 3).** Part moves (F3-5, R3RT1, V023) need rules for
  each move path. The IR gives the move paths. A flow-sensitive `points_into`
  (OL-NR-flow, OL-R2b-holds) is a spec change; the option is one fact variable for each
  definition of a local (section 9.3).
- **Types and signatures (TYPE, 12 + 4).** `props.rs`, `!Move`, exhaustiveness, the
  `on abort` parameter types (F3-4), `Task<T>` with a linear `T` (F3-6, I3-1), prelude
  signatures (RR8, OL-3b).
- **Inference bounds (INF) and names (NAMES).**
- **`rc` group identity (OL-R2b-prec).** A language or model decision (ADR 0011).
- **The interpreter defects (class I, 17).** Scheduler, oracle and unwinder gaps (I3-2,
  I3-3, I3-4, F3-9 and others). Stage 3b removes the unwinder order differences (N6,
  N7) because the unwinder runs the cleanup chains of the IR, but not the gaps in what
  it finds (closure cells, task results).

---

## 6. The interpreter runs the IR; differential tests

### 6.1 Decision: compile the IR to the stack code of today

The interpreter keeps `machine/` (frames, handlers, continuations, the unwinder, the
scheduler, the oracle). A new module `weft-interp::compile_ir` (about 1 500 lines)
replaces `compile.rs` (1 544 lines). It translates each body to one `Code` unit:

| IR | Stack code |
| --- | --- |
| `Body` of kind `Fn`, `Test`, `Closure`, `Clause`, `Handled`, `Scope` | `Code` of kind `Fn`, `Test`, `Closure`, `Clause`, `HandleBody`, `ScopeBody` |
| a local | a slot; `Live(l)` is `BindEmpty(slot)`, `Dead(l)` is `DropSlots([slot])` |
| `Assign(p, rv)` | the ops of `rv`, the ops of the place `p`, `Store` |
| `Drop(p)` | a new op `DropPlace`: drop the value at the place and leave `Moved` |
| `copy p`, `move p` | the place ops, `Read` |
| `Ref(p)`, `Ref(p[])` | the place ops, `Borrow`, `BorrowAll` |
| `Deref(_)` | the place ops follow the pointer (`Field` and `Index` already do; a new op `Deref` for a bare dereference) |
| `(*env.k)` in a closure, a clause, a handled or a scope body | `Var(Cap(k))`: the captured cell |
| `Binary(op, ty, a, b)` | `a`, `b`, `Bin(op)`, `CheckInt(ty)` |
| an aggregate | `Tuple`, `MakeVec`, `MakeStruct`, `MakeEnum`; a closure aggregate is `MakeClosure` with the cells of its `ByRef` and `KeptCell` operands and the `owned` list of its `ByMove` operands |
| `Switch` on a discriminant | a new op `Tag`, then a jump table |
| `Call`, `Perform`, `Resume` | `Call`, `CallValue`, `Perform`; `Resume` is `CallValue` of the continuation |
| `Handle`, `Scope`, `ScopeWait`, `Fork`, `Assert`, `IterNext`, `Print` | the ops of the same name |
| `Spawn`, `Join`, `Detach` | the natives of today, with the arguments as operands |
| `Bounds` | a new op `Bounds` (today `Index` checks the bounds) |

What goes away: the span-keyed exports `FnFacts::by_value`, `arg_order` and `int_ops`
(they are in the IR); `StmtBegin` and `StmtEnd` for compiled IR (the temporaries are
slots with `Dead`); the operand stack holds values only inside one IR instruction.

**Stage 3b: the unwinder runs the cleanup chains.** Today the unwinder finds the values
of a frame at run time (`frame_values`, `extract_linear`). In stage 3b each `Code` has a
table from the pc of each suspending instruction to its cleanup block, as landing pads
are. The unwinder runs the `UnwindValue`, `UnwindKont` and `Dead` instructions of that
block in unwind mode (root handlers only, as today), then leaves the frame at
`UnwindExit`. So the order and the content of an unwinding come from the IR. The
checker, the interpreter and the effects model then use one order (N6, N7).

**Why not a new machine.** `machine/` has the scheduler, the deterministic simulation,
the oracle and three rounds of fixes. The IR already has the frame structure of the
machine (one body for each `CodeKind`), so a translation keeps all of it.

### 6.2 Run-time changes that the IR makes

| Change | Programs that see it | Source |
| --- | --- | --- |
| a place operand is read where it is written (choice A) | `x + { x = 5; 1 }` gives 2, not 6 (p1); a program that faulted on a late read through a dangling reference (p2, p9, p10) now reads before the change | `docs/plan/core-ir-inputs/semantics.md` 2.2 |
| the tail temporaries of a loop body end at each iteration | `Weak.upgrade` of a tail temporary of the body of a loop (p24) | `docs/plan/core-ir-inputs/semantics.md` 4.2 |
| the unwind order is the order of the IR | none in stage 3a (the IR takes the order of the interpreter); in stage 3b the unwinder finishes what the cleanup chain names, also a closure environment (a part of I3-2) | `docs/plan/core-ir-inputs/semantics.md` 7.3 |

`docs/design.md` states the order of evaluation and the end of temporaries after stage
3a.

### 6.3 Differential tests and run-time oracles

The IR makes five run-time checks possible. Each one runs on the corpus, the examples
and the probe sets of section 8.2.

1. **Interpreter against interpreter** (stage 3a). Run the AST compiler and
   `compile_ir` on each input, with the six seeds and worker counts of
   `SCRATCH/r3/oracle/harness.py`, with and without `--oracle`. Compare the output, the
   exit status and the oracle verdict. Each difference must be in the table of 6.2. The
   harness gets a flag `--interp=ast|ir`.
2. **Trace conformance** (stage 3b, A1). Each compiled op carries its `NodeKey`. With
   `--ir-trace`, the machine records the node of each step. A checker tests that each
   two steps in one frame follow a `cfg_edge` of the facts of the component. This
   includes a splice (the `Handle` node, then the entry of the handled body), an abort
   path (the suspending node, then the copy of the cleanup chain for the destination
   that the run took), and a re-entry (`Post`, `Copy`, `Ret` for the second `resume` of
   a `multi` continuation). A run that leaves the CFG of the facts shows a bug of the
   builder or of the fact generator.
3. **Fact oracle** (stage 4; the B6 hypotheses on concrete runs). The machine maps each
   cell to a fact root:
   - the slot of a frame to the root of its local;
   - a slot of a frame that the component does not hold to the callee frame root of the
     call node, or to the caller frame root;
   - a heap cell to the place on its ownership path;
   - an `Rc` object to its group root.

   At each step it checks:
   - each free of a cell has `frees_at` at the node for a place that covers the cell
     (C4);
   - each pointer that a used variable holds is inside a place of `points_into` of the
     variable (C1);
   - each read and each write of a cell has `reads_at` or `mutates_at`, `lends_mut` or a
     footprint at the node (C5, F4);
   - each move has `moved_at` or `moved_part` (D1);
   - each suspension (a perform, a yield, a wait) is at a node with `may_abort` if a live
     linear value is in a frame that the abort can unwind (D4).
4. **Summary oracle** (stage 4; A3). At each call of a body, the machine records the
   cells that the body changes, frees and reads, and the pointers in its result. A
   checker maps them through σ of the run node and tests that each one is inside the
   applied summary. This tests the one procedure that section 5 calls "one rule".
5. **Agreement and lints** (each stage). `weft agree` on the facts of the IR for each
   input; the lints `gen_kill.dl` and `unbound_use.dl` on each component (V4 makes the
   second one hold for closure and clause components too, not only for the component
   that starts at `n0`).

The probe generators of rounds 2 and 3 (`gen3.py`, `gen4.py`, `mutate3.py`,
`sweep*.py`) feed checks 1 to 4. A fault of check 3 or 4 on an accepted program shows
the defect before a review finds the program.

---

## 7. Proof alignment

The angle of this design is to make the IR the common middle of the proofs. Today the B6
link proves "exec core to model", and the facts of sema are hypotheses
(`proofs/link/README.md`). With the IR, the hypotheses become statements about the
builder and the fact generator, and some of them become lemmas.

### 7.1 B1 (`proofs/borrowing/src/cfg.rs`)

**Embedding.** Each fact node of a component is one B1 `Node`. Its successors are the
`cfg_edge` successors. The instructions:

| IR | B1 instruction |
| --- | --- |
| `r = &x` | `Borrow { dst: r, x }` |
| `r = &(*s).f[i]` (an unstable step below `*s`) | `Child { dst: r, src: s, label }` |
| `r = copy s` (a reference) | `Copy { dst: r, src: s }` |
| a read or write of a scalar through `r` | `Read { src: r, field }`, `Write { src: r, field, val }` |
| `Call` with summary `Σ` | `Call { args: [(var, is_mut)], ret }`; `is_mut` from `Σ.muts`; `ret` from `Σ.ret` |
| a closure aggregate | `MkClosure { clo, caps }` with its `ByRef` fields |
| `Call` of a closure value, `Perform`, `Resume` | `Invoke { clo, args, ret, once }` (`perform`, `resume` of `model.rs`) |
| `Live`, `Dead`, `Drop`, a move of an owner | not in B1: the extension below |

**Extension B1+.** B1 has a fixed set of locals and no frees. The IR needs
`Alloc { x }` (a `Live` with a value) and `Free { x }` (a `Dead`, a `Drop`, a move of an
owner): `Free` removes the tree of `x`, and the checker kills each reference whose group
has root `x`. The proof shape is the one of `lemma_preserve` for a mutable call
argument. A free of a part (`moved_part`) is `FreeSub { x, path }`. With B1+, the free
rules of `invalidated_at` (`frees_at`) are inside the link; today they are outside it
(`proofs/link/README.md`, L2: "the link definition has only the call rule").

**Closures.** L2 excludes `MkClosure` and `Invoke` (`facts_ok`). In the IR a closure is
an aggregate of its environment, and B2 (`lemma_perform_is_call`) proves that an invoke
is a call with the captured references as extra arguments. So the IR fragment with
closures fits B1 with `Invoke`, if the summary of the closure body is inside the
`is_mut` flags of its captured references. That condition is the summary hypothesis
(7.6).

### 7.2 B3 (`layout.rs`)

The projections are the steps of B3: `Field` is `Field(f)`, `Variant` after a `Switch` is
the B3 `Variant` instruction (a safe abort if the tag is another one), and `Index`,
`Elems` and `Deref(Box)` are `Kid(label)`. `Deref(Rc)` is a `Kid` of a group root.
`Deref(Ref)` follows a reference variable. So L1 (`places_link.rs`) applies to α
directly: the embedding of `places_link` (`kind_code`) is the map from projections to
steps. B3 programs are straight-line; B3 needs the CFG lift of B1 (`sub_state`,
`join`), with `LSState` in place of `SState`.

### 7.3 B4 (`tasks.rs`)

B4 runs two straight-line programs at the same time. The IR has `Spawn`, the task body,
and the part of the parent between `Spawn` and `Join`, `ScopeWait` or the `Ret` of
`Fork`. To use B4, the link cuts that part of the parent CFG out as the second program,
and needs a CFG form of B4. B4 also checks a stronger rule than W0405 (held groups, not
accesses). This stays a documented gap (ADR 0006).

### 7.4 The effects model (`proofs/effects/src/model.rs`)

**Embedding.** `embed_eff` maps the IR program to a `Prog`:

| IR | Effects model |
| --- | --- |
| a body | a `Block` |
| the capability operands of a body: `Row(E)` for each `E` of its inferred row (in a fixed order), then the capability parameter of a handled body | `Sig::caps` |
| the capabilities in the abstract value of `_0` that are parameters | `Sig::rets` |
| the continuation of a clause and its mode | `Sig::kmode` |
| a new value of a linear local (`Assign`, `Ret`) | `Acquire { slot: local, on_abort }` |
| `Consume`, a move of a linear value into a call | `Consume { slot }`; a move into a call needs the extension below |
| `Call` with `CapArgs::Lexical(env)` | `Call { block, caps }`; `caps[j]` is the index of the capability that `env` gives for the `j`-th effect of the callee row |
| `Handle` | `Handle { eff, clauses, body }` |
| `Perform` with `Local` or `Row` capability | `Perform { cap: index, op }` |
| `Resume` | `Resume` |
| `Return` | `Return` |
| `UnwindValue(_, OnAbort)`, `UnwindKont`, `UnwindExit` | `step_unwind_abort`, `step_unwind_drop`, `step_unwind_pop` |

**Changes of the model** that the IR needs:

1. **The unwind order (N6).** `max_slot` takes the newest resource (the largest
   resource id). The IR takes the highest slot (the reverse declaration order of the
   interpreter). The change: compare slot numbers, not resource ids, in `max_slot`. No
   theorem uses the order.
2. **A clause frame before its fresh continuation (N7).** `step_unwind_drop` drops the
   fresh continuation before the frame's own values. The interpreter does the opposite.
   The change: `step_unwind_drop` requires `!nonempty(pf(s).slots)`, and
   `step_unwind_abort` drops the `holds_fresh` guard. The proof of `inv_b` (`own.rs`)
   must follow, and the error predicates `err_unwind_dead` and `err_no_on_abort` drop the
   same guard.
3. **Moves of linear values into calls.** `Call` passes no slots. The extension
   `Call { block, caps, moves: Seq<Slot> }` moves each slot into the callee frame. The
   ownership invariant `inv_b` holds with the move (one owner, also after it).
4. **The CFG lift.** Blocks are straight-line. The checker state `SS` needs a join: `env`
   is static (equal on each edge), `lin` must be equal on each edge (W0601 rejects a
   difference), `k` is the conjunction (a `once` continuation that one path resumed is
   not usable after the join). The lift is the B1 argument (`lemma_inv_sub`).

With these, the B6 link can relate the IR to the effects model: if W0601, W0602, W0501
and W0503 accept the facts of a body, the effects checker accepts its embedding. Tasks,
scopes, timeouts and `fork` stay outside the model (`step_cancel` models a cancel at a
perform).

### 7.5 What the link can prove, step by step

| Step | Statement | Hypothesis that it removes |
| --- | --- | --- |
| L0 | `ir_wf(body)`: a Verus spec of V1 to V7 (the sketch has them as Rust); the exec verifier proves `verify(body) == [] ==> ir_wf(body)`, or the link includes the verifier source with `#[path]` | none yet; it is the base |
| L2-IR | for a body with `ir_wf`, the facts that the templates emit for the B1 relations (`cfg_edge`, `rebound_at`, `uses`, `points_into` from the `Ref`, `Copy` and `Call` rules, the call rule of `invalidated_at`) are the link facts of `embed(body)` | `facts_ok` (well-formed CFG, groups of bindings), `bound_before_use` (from V4), `no_gen_kill` (the `Ret`, `FrameEnd`, `Exit` and `Post` phases) |
| L2-free | the same with B1+ for `frees_at` | "the link definition has only the call rule" |
| L2-clo | the same with `MkClosure` and `Invoke` for closure aggregates and closure calls | "no closures in the link" |
| L4 | `ir_wf` and acceptance of the linear and `multi` rules on the facts imply `check(embed_eff(program))` for the fragment with no tasks | the effects facts of sema (D4, D5, E1, G1) |
| (stays) | each summary contains the effects of its body; the analysis gives sound abstract values | A3, C1: tested by the oracles of 6.3, not proved |

`ret_ok` stays false for the `in` form (ADR 0005): it is a property of B1 acceptance,
not of the facts.

---

## 8. Migration plan and the diff gate

### 8.1 Stages

Each stage ends with the gates of `CLAUDE.md` (`cargo fmt`, `cargo clippy -D warnings`,
`cargo test --workspace`, `proofs/verify-all.sh`) and with its own gate. The old fact
generation stays the default until stage 5. The ship rule of the user
(`SCRATCH/ship_rule.md`) allows at most two review rounds after the IR lands, so the
gate of stage 4 must find the defects that a review round would find.

| Stage | Work | Gate | Effort |
| --- | --- | --- | --- |
| S0 Baseline | A tool `weft dev snapshot` writes, for each input of 8.2, the diagnostics of `check --json`, a stable text dump of the facts, and the oracle verdicts of the six seeds and worker counts of the harness. The inputs are deduplicated by content hash. | the snapshot of `b073ea7` (or of the commit before stage 1) is stored | small |
| S1 Typed tree | `ExprId` on each `Expr`. A new pass `typeck` gives the THIR: final types, callees, effect identities, argument order, integer types, capture modes. It is new code (a copy of the inference parts of `Lower`), and `Lower` does not change. `Ty::Fn` loses `summary` in the THIR. | on each input, the type of each expression in the THIR equals the final type that `Lower` infers (except the closure summaries); the same type diagnostics | large |
| S2 IR | `weft-ir`: types, builder, verifier, printer; `weft ir FILE [FUNCTION]`. | the builder is total on each input (no panic); `verify` finds nothing; golden IR files for the corpus are reviewed | large |
| S3a Interpreter | `compile_ir` behind `--interp=ir`. | check 1 of 6.3 on each input: each difference is in the table of 6.2. Then `--interp=ir` is the default, and `compile.rs` and the span-keyed exports go away | medium |
| S3b Unwinder | the unwinder runs the cleanup chains (landing-pad table). | check 1 again (no new difference); check 2 (trace conformance) on each input that runs | medium |
| S4 Facts | the analysis, the summaries, the effect inference over the IR, the fact generator, W0313 and W0314 over the IR; `--facts=old|ir|both`. | the diff gate of 8.2; checks 3 and 4 of 6.3 on each accepted input | very large |
| S5 Cut over | `--facts=ir` is the default. The corpus markers move where the gate says. `--facts=old` stays for one review round, for comparison only. | the corpus and the examples pass with the new facts; a fresh sweep of the generators (8.2) finds no accepted fault | medium |
| S6 Removal | `body/`, the re-lowering loop of `infer.rs`, `FnTy::summary` go away. ADR 0012, `docs/architecture.md`, `docs/traceability.md`, `docs/design.md` (order, temporaries) change. | the gates of `CLAUDE.md` | small |
| S7 Spec | changes that the IR allows, each through the checklist of ADR 0002: W0314 as a rule (`stack_cap`), rules for each move path (R3RT1, F3-5, V023), and, as an option, one fact variable for each definition of a local (OL-NR-flow) | agreement, corpus, the diff gate against S5 | medium for each rule |
| S8 Proofs | the link of section 7.5: L0, L2-IR, L2-free, L2-clo; the effects model changes and L4 | `proofs/verify-all.sh` | large |

Stages S1 and S2 do not change any output. Stage S3a changes the run-time behavior of
the programs in the table of 6.2 only. Stage S4 is the first stage that changes
diagnostics, and only behind a flag until S5.

### 8.2 The diff gate

**Inputs.** All counts are `.wf` files outside worktree copies (no `target/`,
`tests/`, `crates/`, `std/`, `examples/`, `backup/` below `SCRATCH`). There are 57 247
distinct files by content:

| Set | Files | Mode |
| --- | --- | --- |
| `tests/programs` (the corpus, with `//~` markers) | 129 | single file, markers |
| `examples/` | 4 | package and single file |
| the stage verifiers and fix work of rounds 1 to 3: `verify/*` (with `verify/s5` and `verify/quality`), `redteam`, `specreview`, `partb`, `edge`, `edgefix`, `s1fix`, `s2`, `s2fix`, `s5`, `s5r`, `fix`, `p`, `core`, and single files | 7 815 | single file; packages for `verify/pkg1`, `verify/pkg2`, `redteam/pkg` |
| round 2: `r2/redteam`, `r2/fidelity`, `r2/interp`, `r2/quality`, `r2/triage` | 391 | single file |
| round 2 oracle sweeps: `r2/oracle` | 27 669 | single file, oracle |
| round 3: `r3/redteam`, `r3/fidelity`, `r3/interp`, `r3/quality`, `r3/triage` | 957 | single file |
| round 3 oracle sweeps: `r3/oracle` (`sweep*`, `gen3`, `gen4`, `mutate3` outputs, `probes`, `repro`) | 22 383 | single file, oracle |
| the IR maps: `ir/probes`, `ir/work/map`, `ir/work/machine` | 46 | single file, oracle |
| **Total** | 59 261 files, 57 247 distinct | |

The list is a file in the repository (`tests/gate/inputs.txt`, generated by a script),
so a later round adds its probes to the gate.

**Procedure.** For each input, run `weft check --json` with `--facts=old` and with
`--facts=ir`. Compare the multisets of `(code, line)` of the errors. Each input falls
into one class:

| Class | Meaning | What happens |
| --- | --- | --- |
| same | the same errors | nothing |
| new rejects | `ir` has an error that `old` has not, and `old` accepts | run the oracle (six configurations). A fault: the old pipeline was unsound, record it as a fix. No fault: a new false positive; it needs a reason class, and it counts against the budget |
| new accepts | `old` has an error, and `ir` accepts | run the oracle. A fault: a **regression**; the stage cannot end. No fault: an old false positive that the IR removes; record it |
| both reject | the errors differ | group by the pair of codes; review each group once |

**Exit criteria of stage S4.**

1. No regression: no input that `ir` accepts faults under the oracle.
2. Each corpus file and each example passes its markers. A marker moves only with a
   reviewed reason (a line moves from a hidden variable to the source operand, for
   example).
3. New false positives: none in the corpus and the examples; at most 0.5% of the inputs
   that `old` accepts, and each one with a reason class (an issue with the label
   `precision`, by the ship rule).
4. Agreement: `weft agree` holds on the `ir` facts of each input. The lints of the proof
   link (`gen_kill`, `unbound_use`) hold on each component of each input with no expected
   error.
5. The verifier finds nothing on each input.
6. Checks 3 and 4 of 6.3 (the fact oracle, the summary oracle) find nothing on each input
   that `ir` accepts.
7. Cost: the total time of `check` on the inputs is at most two times the time of `old`,
   and the facts of each function are at most three times as many. `crates/weft-check/
   tests/scale.rs` and `crates/weft-cli/tests/limits.rs` pass.
8. A fresh sweep: the generators `gen3.py`, `gen4.py`, `mutate3.py` and `sweep4.py` of
   `SCRATCH/r3/oracle` with new seeds (50 000 programs) find no accepted fault.

**Cost.** I measured `weft check` of the R3a release binary on 200 files of
`r3/oracle/sweep2`: 1.1 s, so about 5.5 ms for each file. Two pipelines on 57 247 files
take about 10.5 minutes on one core, and about 3 minutes on the 4 cores of this machine.
The oracle runs only for the inputs whose verdict differs (six runs of at most 10 s
each).

### 8.3 Old and new side by side

- `FnFacts` has the same schema in both, so the checker, the spec, the bridge and
  `diagnose.rs` read both.
- `--facts=both` runs both and writes the diff classes of 8.2 for one input, for a
  developer.
- The interpreter runs the IR from stage 3a for both fact generators (the old one needs
  only its own `by_value`, `arg_order` and `int_ops` exports, which stage 3a removes from
  the interpreter; the old lowering keeps them for itself until S6).
- While both exist, a fix goes into the IR only, except a realistic blocker that a user
  can meet in the old default before S5.

---

## 9. Risks, size and what stays out

### 9.1 Size

| Part | New lines (estimate) | Lines that go away |
| --- | --- | --- |
| `weft-syntax`: `ExprId` | 150 | |
| `typeck` and the THIR (from the inference parts of `body/`) | 4 500 | |
| `weft-ir`: types, printer, verifier | 2 500 | |
| builder | 6 000 | |
| analysis: states, transfer functions, widening, heap slots, tasks | 3 500 | |
| summaries and effect inference over the IR | 2 000 | the re-lowering loop of `infer.rs` (about 300) |
| fact generator: templates, α, roots, splices, cleanup copies, re-entry edges | 2 500 | `body/` (19 097) |
| W0313, W0314 and the W0204 forms over the IR | 600 | |
| `compile_ir` and the unwinder change | 1 800 | `compile.rs` (1 544) |
| tests: golden IR files, verifier tests, the oracles of 6.3, the gate tools | 3 000 | |
| **Total** | **about 26 500 (23 500 without tests)** | **about 21 000** |

The sketch crate (2 078 lines) covers the types (944 lines with the docs), V1 to V7 of
the verifier, the templates and one worked example.

### 9.2 Risks

| Risk | Likelihood | Impact | Mitigation |
| --- | --- | --- | --- |
| R1. The split of type inference from `Lower` is hard: inference and value flow are mixed (`Ty::Fn` summaries, `fn_joins`, `tentative` moves) | high | stage S1 takes long | S1 writes `typeck` as new code next to `Lower` and compares the types on each input; value flow moves to the analysis, so `typeck` drops it |
| R2. Precision regressions: today's precision features are scattered (one-place instances, known closures at a node, part holders, split ids, `writes_via`) | high | many new false positives in the gate | port each one as a feature of the analysis, with its corpus file (`102_wild_instances.wf`, `143_arg_roots.wf` and others) as its test, before S4 ends; the budget of 8.2 |
| R3. The summary procedure and the analysis are the new single points of failure ("one rule") | medium | a missed effect is a new unsound class, at every run node | the summary oracle and the fact oracle (6.3) on each input and on fresh sweeps; summaries as projections of all relations, not of chosen fields |
| R4. Cost: more variables (each temporary), cleanup copies for each destination, SCC iteration | medium | slower checks | silent temporaries (no facts for a temporary of plain data with no references); the cost gate of 8.2; widening bounds as today |
| R5. Diagnostics name temporaries and move lines | medium | noisy corpus diffs, harder messages | `TempKind` and `Origin` give names and spans; the gate reviews code pairs in groups |
| R6. Run-time changes (choice A, loop tail temporaries) are visible to users | low | a program changes its output | they are rare shapes (p1, p24); `design.md` states the order; the gate lists each changed output |
| R7. The proof changes (B1+, effects model order, moves into calls, CFG lifts) cost Verus work | medium | stage S8 is long | S8 comes after the cut over and does not block shipping |
| R8. Two pipelines for a while | medium | work on two code bases | stages S4 and S5 are time-boxed; the old pipeline gets only realistic blocker fixes |
| R9. The review budget after the IR lands (two rounds) | medium | a new class found late | the gate of 8.2 includes all probes of three rounds and a fresh sweep; the oracles of 6.3 aim at the new single points of failure |
| R10. A once-run frame is spliced; a construct that runs a body twice in one run of its terminator would break the splice | low | wrong facts | only a `multi` resume runs a handled body again, and the re-entry edge covers it; the verifier can check that `Handled` and `Scope` bodies are named by exactly one terminator |
| R11. `KeptCell` keeps a semantic exception (a copy capture outlives its variable) | low | V125-like shapes | a decision for ADR 0012: keep, or make copy captures `ByRef` and let W0301 reject the escape |

### 9.3 What stays out, and options

- **Spec changes** beyond stage S7: the part-move rules and a flow-sensitive
  `points_into`. The option for the second one is one fact variable for each definition
  of a local, with `uses` of each definition that reaches a use and `rebound_at` of all
  definitions at each new definition. It gives a flow-sensitive `points_into` with no
  change of the rules. It costs more variables.
- **Monomorphization** of generic bodies for checking. The design keeps generic IR and the
  `drops`, `holds` and `tasks` parts. An option: check each generic body once for each
  profile of the props of its type arguments (plain, affine, linear, `once`, immovable,
  nonportable) that the program uses. Then a value of `T` gets real flags in the body.
- **Whole-program closure analysis.** The design uses summaries with abstract values,
  which work for a library alone. A 0-CFA over the IR of the whole program is more
  precise for stored values. It is an option of the analysis, not of the IR.
- **Regions for function values (STORE)** and the identity of `rc` objects: language
  decisions (ADR 0011).
- **TYPE, SPEC, INF, NAMES** classes; the interpreter defects of class I other than the
  unwind order.
- **B4** (tasks) over CFGs, and the `multi` copy of affine values in the effects proof
  (E5).
- A native back end: the IR has the shape that one would need (frames, explicit drops,
  cleanup paths, capability passing), but Phase 1 does not need it.

---

## Appendix A. Four new unsound findings (M1 to M4)

The machine view says: a clause runs in place of the handled body; the code of a clause
after `resume` runs after the handled body has ended; a clause that does not resume
returns its value before the unwinder finishes the handled body. I wrote one probe for
each consequence. All probes are in `SCRATCH/ir/work/machine/`. "b073ea7" is
`SCRATCH/ir/probes/weft` (built after `b073ea7`); "616f99c" is a copy of
`/home/user/wt-core/target/release/weft` (the R3a fixes), `weft-r3a` in the same
directory. I did not build or change anything in `/home/user/wt-core`.

| Id | Probe | `check` at b073ea7 | `check` at 616f99c | `run --oracle` | Tag (ship rule) |
| --- | --- | --- | --- | --- | --- |
| M1 | `m1_post_resume.wf` | accepted | accepted | read of a freed cell, line 16 | realistic: clean-up code after `resume` is a common handler form (commit, release, log) |
| M2 | `m6b_resume_result_ref.wf` | accepted | accepted | read of a freed cell, line 10 | realistic: the same form, with a read of the `resume` result |
| M3 | `m8_abort_value_into_body.wf` | accepted | accepted | read of a freed cell, line 11 | realistic: an early-exit handler that returns a reference into its argument |
| M4 | `m10_abort_value_callee_local.wf` | accepted | accepted | read of a freed cell, line 16 | edge: three features (a callee that performs with its own local, a clause with no `resume`, a returned reference) |

**M1. Clause code after `resume`.**

```weft
effect Tick { fn tick() }

fn main() {
    let v = Vec.new()
    v.push(1)
    let r = handle Tick {
        fn tick() {
            let x = resume(())
            v.clear()
            x
        }
    } in {
        tick()
        &v[0]
    }
    print(r)
}
```

The facts put the whole clause at the perform node (`run_handler`). There `&v[0]` does
not exist yet, so `v.clear()` invalidates nothing. At run time `v.clear()` runs after
the handled body made `&v[0]`. Fix in the design: the `Exit` node binds `r`, and the
`Post` node after it applies the `post` part of the clause (section 4.4).

**M2. The result of `resume`.**

```weft
effect Tick { fn tick() }

fn main() {
    let v = Vec.new()
    v.push(5)
    let r = handle Tick {
        fn tick() {
            let x = resume(())
            v.clear()
            print(x)
            x
        }
    } in {
        tick()
        &v[0]
    }
}
```

In the clause, `x` does not point into `v`, so `v.clear()` does not invalidate it. Fix:
the `ret` of the continuation summary (section 4.5).

**M3. A clause value into a local of the handled body.**

```weft
effect Pick { fn pick(v: &Vec<u64>) -> &u64 }

fn main() {
    let r = handle Pick {
        fn pick(v) { &v[0] }
    } in {
        let w = Vec.new()
        w.push(3)
        pick(&w)
    }
    print(r)
}
```

The clause value points into `w` through the operation argument (`clause_refs_onto_args`
maps it there), but the abort path binds `r` after the unwinder ended `w`, and a bind
stops `invalid`. Fix: `AbortValue` binds before the cleanup chain (section 4.6 shows the
facts).

**M4. A clause value into a local of a callee.**

```weft
effect Pick { fn pick(v: &Vec<u64>) -> &u64 }

fn body(g: &Vec<u64>) -> &u64 in g[] / Pick {
    let w = Vec.new()
    w.push(3)
    let x = pick(&w)
    &g[0]
}

fn main() {
    let g = Vec.new()
    g.push(1)
    let r = handle Pick {
        fn pick(v) { &v[0] }
    } in body(&g)
    print(r)
}
```

The call `body(&g)` reaches the handler. The caller sees the argument `&g` as the
operation argument (a call gives "any place inside each reference argument"), but the
operation got a place in a local of the callee. Fix: the callee frame root of the call
node; the abort path frees it (section 4.3). This is the F3-2 family with a clause value
in place of a store.

**Controls.** These probes test the same area. The checker rejects each one, and each
one faults with `run --unchecked --oracle`, so the rejections are right:

| Probe | Result at 616f99c | Note |
| --- | --- | --- |
| `m2_post_resume_move.wf` (the clause moves `v` after `resume`) | W0302 at line 16 | the right verdict for the wrong reason: the facts put the move at the perform node, so the error points into the handled body, not at `print(r)` |
| `m4_post_resume_callee.wf`, `m4b_post_resume_callee.wf` (M1 through a callee) | W0312 (and W0204 for `m4`: its signature states no returned place) | the clause changes `v` and the call passes `&v` |
| `m6c_resume_result_body_local.wf` (the body value points into a local of the body) | W0301 | the R3a holder of the frame value |

`m6_resume_result_body_local.wf` and `m9_resume_twice_tail.wf` are accepted and run with
no fault: they are correct programs.

## Appendix B. Files

- This document:
  `docs/plan/core-ir-inputs/design_machine.md`.
- The sketch crate (IR types, verifier, fact templates, worked example; `cargo test` and
  `cargo clippy --all-targets -- -D warnings` pass):
  `SCRATCH/ir/work/machine/weft_ir_sketch/` (`src/lib.rs`, `src/verify.rs`,
  `src/facts.rs`, `src/example.rs`). Build with
  `CARGO_TARGET_DIR=SCRATCH/ir/work/machine/target_sketch cargo test --offline`.
- The generator of section 5: `SCRATCH/ir/work/machine/tools/section5.py` (reads
  `SCRATCH/ir/work/findings.py`).
- The probes of Appendix A and the R3a binary copy: `SCRATCH/ir/work/machine/*.wf`,
  `SCRATCH/ir/work/machine/weft-r3a`.
- The probe set counts of section 8.2: `SCRATCH/ir/work/machine/probe_sets.txt`.
- The parts of this document before assembly: `SCRATCH/ir/work/machine/section*.md`,
  `appendix.md`.
