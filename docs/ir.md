# The Weft core IR: specification

Status: specification for ADR 0012 (proposed). Date: 2026-10-20. Base: `/home/user/weft`
at commit `b25faf0` (the R3a fixes are in it; the spec has 74 input relations).

This document specifies the core IR that goes between the typed tree and fact
generation. It is the synthesis of three designs and three judge reports:

| Source | Role in this document |
| --- | --- |
| `docs/plan/core-ir-inputs/design_machine.md` | the base: the IR copies the interpreter frames and the proof models |
| `docs/plan/core-ir-inputs/design_mir.md` | grafts: upvar locals, the resume point, the handle value, the fact oracle, the claims test, the gate ledger, reference versions (after the migration), the verified fact kernel (after the migration) |
| `docs/plan/core-ir-inputs/design_minimal.md` | grafts: rule CAPTURE, the relation table `RELS`, validator rules per component, the rollout by construct group, the parity tests before any fact change |
| `docs/plan/core-ir-inputs/judge_soundness.md`, `docs/plan/core-ir-inputs/judge_feasibility.md`, `docs/plan/core-ir-inputs/judge_proofs.md` | the fixes H6 to H9, H15, the gate rule, the W0313 and W0204 decisions, the proof decisions |

`SCRATCH` is `SCRATCH`.
All other paths are relative to the root of the repository. The compiled sketch of the
types, the verifier, the fact templates and the relation table is
`SCRATCH/ir/work/final/weft_ir_final/` (14 tests and `cargo clippy -D warnings` pass).
Section 3 copies its types. The implementation plan is `plan.md` next to this file.
In the repository, stage S00 of the plan copies this file to `docs/ir.md`, the ADR to
`docs/adr/0012-core-ir.md` and the plan to `docs/plan/core-ir.md`.

## Contents

1. Overview: problem, answer, pipeline, code, principles
2. The typed tree (THIR)
3. The IR types
4. Well-formedness rules (the verifier)
5. Lowering rules: typed tree to IR
6. Fact generation
7. The invariants and how each one holds
8. The interpreter and the run-time semantics
9. Proof alignment
10. Verdicts: what the IR removes and what stays
11. Options after the migration

Terms:

| Term | Meaning |
| --- | --- |
| THIR | the typed tree: the AST with final types, resolved names, callees, argument order and implicit dereferences |
| body | one frame: a function, a test, a closure, a clause, a handled body or a scope body |
| inner body | a closure, a clause, a handled body or a scope body |
| once-run frame | a handled body or a scope body: it runs once each time its terminator runs (a `multi` resume aside) |
| splice | the fact generator puts the nodes of a once-run frame into the component of its site |
| component | one CFG of the facts: a function or a test with its spliced bodies, or a closure or a clause with its spliced bodies |
| run node | a node that runs another body through its summary: a call, a perform, a resume, a spawn, a cleanup node with `on abort`, the `Post` node of a `handle` |
| summary | what one run of a body does to what it can name from outside: its parameters, its environment, its upvars, its capabilities, its result |
| cleanup chain | the cleanup blocks of a frame: they finish the values of the frame on an abort path and end at `UnwindExit` |
| abort destination | where an abort stops: the `handle` of a local handler, or the caller of the function |
| move path | a local or a part of a local with no `Deref` and no `Index`: the unit of moves, ends and fact variables |
| α | the place abstraction: it maps an IR place to fact places (section 6.3) |
| σ | the substitution of a summary at one run node (section 6.7) |
| old pipeline | `crates/weft-sema/src/body/` and `crates/weft-interp/src/compile.rs` at `b25faf0` |

---

## 1. Overview

### 1.1 The problem

Fact generation lowers the surface AST straight to facts (`crates/weft-sema/src/body/`,
19 410 lines). Each surface form needs its own special case: temporaries, block tails,
handled-body tails, partial moves, closures in fields, clauses, `resume`, `multi`
re-runs, tasks, generics, `on abort`, loops. The cases meet, and a fix in one breaks an
assumption of another. Three internal review rounds each found about 20 soundness
blockers. `docs/plan/core-ir-inputs/root_causes.md` classifies 180 unsound findings and 53 false positives
into 27 root-cause classes. Most of them are in the lowering mechanics.

### 1.2 The answer

A small IR between the typed tree and the facts. Its form copies the machines that the
proofs and the interpreter use:

| Machine object | Interpreter | Proof model | IR form |
| --- | --- | --- | --- |
| frame | `CodeFrame`, one `Code` unit | effects `CFrame`, one `Block` | `Body` |
| instruction | `Op` | B1 `Node { instr, succs }` | one `Stmt` or one `Term` (one fact node, plus fixed phases) |
| local cell | slot, temporary cell | B1 local, effects slot | `LocalDecl` with `Live` and `Dead` |
| captured cell | `Var(Cap(k))` | captured group | upvar local (clause, handled body, scope body); environment field (closure) |
| capability | handler id in `HEnv` | `env: Seq<HId>`, `Perform { cap }`, `Call { caps }` | `CapOperand`, `CapArgs`, a `Cap` local of a handled body |
| continuation | `Clause { cont }` | `CFrame::k`, `Resume` | `LocalKind::Kont`, `TermKind::Resume` |
| unwinder | `unwind_frame`, `frame_values` | `step_unwind_abort`, `step_unwind_drop`, `step_unwind_pop` | cleanup blocks: `UnwindValue`, `UnwindKont`, `UnwindExit` |
| suspension point | `Perform`, `Call`, `Join`, `ScopeWait`, `Fork` | `is_susp` | a terminator with an `unwind` block |
| `multi` copy | `copy_frames` | `Resume` of a `multi` `Kont` | a re-entry edge through a `Copy` node in the facts |

The facts become a function of the IR. Each instruction has one fact template. One
analysis (a fixpoint for each body, and one over the call graph) gives the abstract
values. One pure function emits the facts. There are no post-passes, no pending queue,
no hidden variables and no re-lowering of loops. The spec (`spec/weft.dl`), the facts
schema (`crates/weft-facts`) and the checker (`crates/weft-check`) do not change before
the cut over. The interpreter runs the same IR.

### 1.3 Pipeline

```text
source ──parse──► AST (an ExprId on each expression)
       ──resolve + typeck──► THIR: final types, callees, effect identities, argument
                             order, implicit dereferences, integer types
       ──build──► IR: bodies, blocks, locals, cleanup chains (no places, no rows)
       ──verify──► V1 to V18
       ──analyze──► for each body: abstract states (places, function values, tasks, init)
                    for each SCC of the call graph: summaries and effect rows
       ──emit──► FnFacts (schema unchanged) ──► checker and spec (unchanged) ──► diagnostics
       ──compile_ir──► stack code ──► machine (frames, effects, unwinder, scheduler)
```

During the migration the old pipeline runs next to the new one
(`--facts=old|ir|both`, `--engine=ast|ir`). Section 8 and `plan.md` give the details.

### 1.4 Where the code goes

| Code | Content |
| --- | --- |
| `crates/weft-syntax` | `ExprId` and `PatId` on the AST nodes |
| `crates/weft-ir` (new) | the IR types, the final type table (`ty.rs`), the printer, the verifier. No dependence on `weft-sema`. |
| `crates/weft-sema/src/thir/` (new) | the THIR tables; first a recorder inside the old lowering, later the standalone `typeck` |
| `crates/weft-sema/src/irbuild/` (new) | the builder: THIR to IR; the scope test of the migration (`scope.rs`) |
| `crates/weft-sema/src/analysis/` (new) | the abstract domain, the transfer functions, widening, heap slots, summaries, `apply`, the fixpoint over the call graph (effect inference) |
| `crates/weft-sema/src/factgen/` (new) | nodes and phases, roots and α, variables, templates, frames (splices, cleanup copies, re-entry), `RELS`, the Rust checks (W0313, W0314, W0204 stores), the reference-fragment kernel |
| `crates/weft-interp/src/compile_ir.rs` (new) | IR to the stack code of today; landing pads |
| `crates/weft-gate` (new, not published) | the diff gate, the oracle cache, the ledger, the claims test, the sweeps |
| `crates/weft-sema/src/body/`, `infer.rs` re-lowering, `crates/weft-interp/src/compile.rs` | removed at the end (stages R3, R4 of the plan) |

### 1.5 Principles

1. **One body is one frame.** Each function, test, closure, clause, handled body and
   scope body is a body with its own locals, `_0` and cleanup chain.
2. **One instruction is one node.** A terminator that hands control to another frame
   has a fixed list of more nodes (phases). The order inside a node is the order of one
   instruction.
3. **A value binds where it exists, before each free that comes after it.** No node
   binds and frees one variable. This is the rule that the round-3 frame findings broke.
4. **Explicit machine objects.** Capabilities, continuations, the unwinder and `multi`
   copies are IR forms.
5. **The facts are a function of the IR.** One template for each instruction kind. One
   analysis. One emit pass.
6. **The IR holds no analysis results.** No places, no effect rows, no function value
   sets. So the IR is built once, before effect inference.
7. **The interpreter runs the IR.** The checker and the interpreter read one set of
   decisions: order, moves, captures, temporaries, ends, unwind order.
8. **One decision, one place.** `typeck` decides types and names. The builder decides
   order, temporaries, ends and cleanup. The analysis decides places, function values,
   tasks and capabilities. The fact generator only translates.
9. **The spec stays the single source of the rules.** Checks that stay in Rust (W0313,
   W0314, the store forms of W0204) read the abstract values of the analysis, and
   `RELS` says which relation carries what.

---

## 2. The typed tree (THIR)

### 2.1 What the THIR holds

The THIR is the AST plus side tables keyed by `ExprId` and `PatId`. The builder reads
only the AST and these tables. It never infers a type.

| Table | Content | Today in |
| --- | --- | --- |
| `expr_ty: ExprId → TyId` | the final type of each expression | `Lower` unification (`body/expr.rs`) |
| `pat_ty: PatId → TyId`, `binding: PatId → BindingId` | the type and the binding of each pattern | `body/stmt.rs` |
| `res: ExprId → Res` | each name: a binding, a function item with type arguments, a variant, an operation, a built-in (`print`, `fork`, `assert`) | `Lower` name resolution |
| `call: ExprId → CallInfo` | the callee (item, method, value, operation, intrinsic, constructor); the receiver mode (by reference, by value) and its dereference count; the argument order (`Vec<Option<u32>>`, ADR 0009) | `body/call.rs`, `body/args.rs`, `FnFacts::arg_order` |
| `adjust: ExprId → Vec<DerefKind>` | the implicit dereferences of section 2.4 of `docs/plan/core-ir-inputs/semantics.md`: at a field, an index, a method receiver, a compound store, an operator, a condition, a pattern | `deref_lval`, `through_ref`, `resolve` |
| `field: ExprId → FieldIdx` | the field index after the dereferences | `body/expr.rs` |
| `int_ty: ExprId → IntTy` | the integer type of each arithmetic operation and compound assignment | `FnFacts::int_ops` |
| `closure: ExprId → ClosureInfo` | the parameters, the result type, the stated row of the type, if any | `body/fnval.rs` |
| `handle: ExprId → HandleInfo` | the effect (with its identity), the clause of each operation, `multi` | `body/mod.rs` |
| `effect: ExprId → EffectId` | the effect identity of each operation name and effect path | `program.rs` |

A function type in the THIR has its parameter types, its result type and its stated
row. It has no closure summary and no item (today `FnTy::summary`, `fn_joins`). Value
flow is a result of the analysis, not of the types.

The types of the tables are in `crates/weft-sema/src/thir/mod.rs` (plan stage T3). The
tables there also have:

| Table | Content |
| --- | --- |
| `bindings: BindingId → Binding` | the binder (a parameter, a name pattern, a closure or clause parameter, a `resume`, a scope binder), the name and the type of the local |
| `pat_adjust: PatId → Vec<DerefKind>` | the implicit dereferences of the value at a pattern, before its test |
| `conflicts` | the keys whose visits gave two values (test D0 fails on them) |
| `error`, `free` | the body has an error type; the expressions whose type had a free type variable |

`FieldIdx` is a field of a struct or a tuple, or the payload of a variant (`o.Some`).
`adjust` is keyed by the expression whose value the lowering dereferences: the base of a
field or an index, a receiver, the place of a borrow or a compound store, an operand, a
condition and a call argument.

### 2.2 Two phases of `typeck`

The type inference is mixed with value flow in `body/` (191 call sites of `unify` and
`inf`). All three designs rate its extraction as the highest risk. This specification
splits the risk:

1. **Phase 1 (plan stage T3): the recorder.** The old lowering fills the THIR tables
   during its last lowering of each body, after its types settle. The recorder only
   adds calls; it changes no behaviour. The tables are then right by construction for
   the old types, and every later stage can use them.
2. **Phase 2 (plan stages R1, R2): the standalone `typeck`.** Before `body/` goes away,
   `crates/weft-sema/src/thir/typeck/` is carved out of a copy of the inference parts
   of `body/`. A parity test compares its tables with the recorded tables on each input
   of the gate (test D0). When D0 holds, `typeck` becomes the source of the tables, and
   the recorder goes away with `body/`.

### 2.3 Final types and properties

`crates/weft-ir/src/ty.rs` holds the final type table: an interner of `Ty` values with
no inference variables. `Ty` has the cases of `crates/weft-sema/src/types.rs` minus
`Ty::Var`, `Ty::IntVar`, `Ty::Error` and the closure summary of `Ty::Fn`: unit, bool,
`Never`, the integer types, `String`, `Duration`, references, `Box`, `Rc`, `Weak`, `Vec`,
arrays, slices, tuples, ADTs with type arguments (the prelude types, the extern types
with their declared props, and raw pointers `*T`, which are opaque copy values with no
place and no `Deref`), function types (parameters, result, stated row), type
parameters, `Task<T>`, the scope capability, capabilities, continuations, iterators. An
`AdtDecl` table gives the fields and variants with their types, the place fields,
`on abort`, linear and `!Move`.

In `ty.rs` (plan stage T2), the prelude types `String`, `Duration`, `Box`, `Rc`, `Weak`,
`Vec`, `Task`, the extern type `Scope` and raw pointers are ADTs: `AdtDecl::lang` names
them, so the builder finds a `Box` or an `Rc` without a search by name. Each `AdtDecl`
also holds the property rows of its definition (`Program::props`), so `Props` comes from
the table alone. `Props` is in `ty.rs` too.

A reference type has no place. The `in` place and the modes (`@ uniq`, `@ shared`,
`@ once`, `@ portable`, ...) of a parameter, a field or a declared local are in the
declaration tables (`FnDecl` parameters, `AdtDecl` fields, `LocalDecl`), as in
`types.rs` today. `Props` and the static facts (6.3) read them there.

**Free variables.** `Infer::resolve` gives `i64` to a free integer variable, but it keeps
a free type variable (for example the element type of `Vec.new()` when the program puts
no element in it). `to_ir_ty` gives such a variable the type unit. This is sound: each
value that the program makes fixes the type of the variable that holds it, so no value
of a free type variable can exist at run time. A body with `Ty::Error` gets no IR (5).

`Props` (section 3) comes from one function, `crates/weft-sema/src/props.rs`, applied to
the final type. The builder stores it in each `LocalDecl`. For a binding whose type has
a function part, the builder joins the modes that the analysis infers for its values
(`thir::Binding::value`, 5.22). The facts read the flags of a variable from the props of
its move path, joined with the modes of the closures that the analysis says it can hold
(V061).

### 2.4 Checks that stay in `typeck`

W01xx (names, types, signatures, W0107, W0116, W0119; the statement structure: W0111
`break` or `continue` outside a loop, also in a closure inside a loop; W0114 a range
outside `for`), W0102 (a literal that does not fit), W0120 (exhaustiveness, with its
budget), W0504 (a clause of `Fail.fail` resumes), the into-plain-data form of W0502, the
`fip` checks (W1001 to W1004) and the struct-declaration form of W0605. They read types
and the syntax tree, not places or flow. ADR 0002 lists them already.

Until stage R2 of the plan, the old lowering is the `typeck`. In `--facts=ir` mode the
pipeline keeps only these diagnostics of the old lowering. It drops each other
diagnostic of the old lowering (W0204, W0313, W0314, W0315, W0701, W0704, W0707)
and its facts, and the IR pipeline gives its own (5.36, 6.8, 6.9). W0303 stays a
diagnostic of the old lowering: a body with W0303 gets no IR (5.36).

As built (plan stage F1): the drop list is by code, and only for the diagnostics of the
lowering and of its effect inference (`weft_sema::IR_DROPS`); the item checks (also the
W0204 of a signature) stay. The W0315 of the builder replaces the W0315 of the lowering.
The `ir` pipeline also gives the exports of the AST compiler from the IR: the `ByMove`
captures (and a moved `once` continuation) as `by_value`, the THIR argument order of a
call of a method of a value or of a local with named arguments as `arg_order`, and the
THIR integer types as `int_ops`. A body with no IR keeps the exports of the old lowering.

---

## 3. The IR types

### 3.1 Design rules of the types

- **No right side can change memory or suspend.** `Rvalue` reads and builds values.
  Each change of memory is an `Assign` destination, a `Drop`, a `Dead`, or a
  terminator. Each suspension is a terminator.
- **Each read of a place is an `Operand`** at exactly one statement or terminator.
- **`Deref` is a projection of its own.** A place through a reference, a `Box` or an
  `Rc` names the pointer local in its path.
- **Moves are `Operand::Move`.** A move of a part is a `Move` of a projection.
- **Storage is explicit.** Each local except the parameters, `_0`, the capability
  parameter, the continuation, the upvar locals and the environment of a closure gets
  `Live` before its first use. Each local except the upvar locals and the environment
  gets `Dead` on each path out of its scope, also the parameters and the continuation at
  the frame end. At `Return` only `_0` has a cell (and the locals whose cells belong to
  another frame: the upvar locals and the environment).
- **`Dead` is the drop.** `Dead(l)` drops the value that is still in `l` and ends the
  cell. An `Assign` drops the old value of its place. `Drop(p)` exists only for a place
  behind a pointer, right before a new value of it (ADR 0007: behind a reference the
  old value is always there). So each free is a `Dead`, a move, a consume, an unwind
  step or a summary part, and the verifier checks each `Dead` (soundness judge, H9).
- **Frames are bodies.** A `Handle` names a handler declaration with the handled body
  and the clause bodies. A `Scope` names the scope body. A closure aggregate names the
  closure body.
- **Upvar locals and environments.** A clause, a handled body and a scope body name
  each local of the site that they use as an upvar local (`LocalKind::Upvar`). An upvar
  local has the cell of the site local, has no `Live` and no `Dead`, and a move of it
  moves the site local. A closure is a value: its captures are fields of its
  environment, with the mode of rule CAPTURE (section 5.1.7). A body nested in a
  closure body names the captures through an upvar local of the environment (a view,
  `u.k`; section 5.1.7).
- **Capabilities.** `CapOperand::Local` is a capability value: the `Cap` local of a
  handled body, an upvar local that names one, or a `Cap` field of a closure
  environment. `CapOperand::Row(E)` is the capability that the caller gives, valid in
  each body whose capability environment does not bind `E`. A call passes
  `CapArgs::Lexical(env)`; an `on abort` call passes `CapArgs::Root`.
- **The IR has no places, no rows and no function value sets.**

### 3.2 The types

This is the type part of `SCRATCH/ir/work/final/weft_ir_final/src/lib.rs`, with the doc
comments cut to one line. The compiled file is the reference; plan stage B1 copies it to
`crates/weft-ir/src/lib.rs` and adds the type table.

```rust
// Ids: u32 newtypes with `index()`: BodyId, BlockId, LocalId, FnId, ClosureId,
// HandlerId, ScopeId, TestId, SpawnId, TyId, EffectId, OpIdx, FieldIdx, VariantIdx,
// SplitId, CapEnvId, ExprId. Plain data: Span { unit, lo, hi }, Origin { span, expr },
// IntTy { U8, U16, U32, U64, Usize, I8, I16, I32, I64 }.

/// A whole program: each body of each unit, and the declarations.
pub struct Program {
    pub bodies: Vec<Body>,          // index: BodyId
    pub fns: Vec<FnDecl>,           // index: FnId
    pub closures: Vec<ClosureDecl>, // index: ClosureId
    pub handlers: Vec<HandlerDecl>, // index: HandlerId
    pub scopes: Vec<ScopeDecl>,     // index: ScopeId
    pub spawns: Vec<SpawnDecl>,     // index: SpawnId
    pub cap_envs: Vec<CapEnv>,      // index: CapEnvId
    pub tests: Vec<TestDecl>,       // index: TestId
}
/// A test block: its name (the interpreter runs tests by name) and its body.
pub struct TestDecl { pub name: String, pub body: BodyId }

/// A function item. `body: None` for an extern function: its summary comes from its signature.
pub struct FnDecl {
    pub name: String,
    pub body: Option<BodyId>,
    pub params: Vec<TyId>,
    pub ret: TyId,
    pub generics: u32,
    pub stated_row: Option<Vec<EffectId>>,
    pub intrinsic: Option<Intrinsic>,
}
pub enum Intrinsic { SimRun, WithTimeout }

/// A closure literal.
pub struct ClosureDecl {
    pub body: BodyId,
    pub maker: BodyId,
    pub captures: Vec<Capture>, // in the order of the fields of the environment
    pub once: bool,             // it moves a capture that is not plain data, or holds a once value
    pub cap_env: CapEnvId,      // where it is made: it performs through it
}
pub struct Capture {
    pub source: Place, // a local or an upvar local of the maker, or a capture of a maker closure: env.j, (*env.j)
    pub mode: CaptureMode,
}
/// One function (`capture_mode`, rule CAPTURE) decides the mode.
pub enum CaptureMode {
    ByRef, // a reference to the cell; in the closure body `(*env.k)`
    ByMove, // the value moves in when the closure is made; `env.k`
    Kept,  // the cell of plain data that no body borrows; `env.k`; it outlives the variable
    Cap,   // a copy of a capability value
    Kont,  // a copy (or a move, for once) of a continuation value
}

pub struct HandlerDecl {
    pub effect: EffectId,
    pub clauses: Vec<(OpIdx, BodyId)>,
    pub handled: BodyId,
    pub site: BodyId,
    pub multi: bool,
}
pub struct ScopeDecl { pub body: BodyId, pub site: BodyId }
pub struct SpawnDecl { pub scope: Option<ScopeId>, pub fork: bool, pub origin: Origin } // scope: None for a fork branch, or a capability that is not a scope binder; origin: the task argument or the fork branch
/// A static capability environment: handlers are lexical.
pub struct CapEnv {
    pub parent: Option<CapEnvId>,      // None at the entry of a function or a test
    pub adds: Vec<(EffectId, Place)>, // the Cap local of a handled body, or a Cap field
}

/// What a body is. Each kind is one `CodeKind` of the interpreter.
pub enum BodyKind {
    Fn(FnId),
    Test(TestId),
    Closure(ClosureId),           // first parameter: the environment
    Clause(HandlerId, OpIdx),     // parameters: the operation arguments; upvar locals
    Handled(HandlerId),           // the Cap local; upvar locals
    Scope(ScopeId),               // parameter: the scope capability; upvar locals
}

/// One body: one frame.
pub struct Body {
    pub kind: BodyKind,
    pub parent: Option<BodyId>,
    pub locals: Vec<LocalDecl>,   // index: LocalId
    pub ret: LocalId,             // `_0`
    pub params: Vec<LocalId>,
    pub caps: Vec<(EffectId, LocalId)>, // only a handled body: its capability
    pub kont: Option<(LocalId, bool)>,  // only a clause: the continuation and `multi`
    pub blocks: Vec<Block>,       // index: BlockId
    pub entry: BlockId,
    pub unwind_exit: BlockId,     // the block with `UnwindExit`
    pub cap_env: CapEnvId,
    pub origin: Origin,
}

pub struct LocalDecl {
    pub ty: TyId,
    pub kind: LocalKind,
    pub name: Option<String>,
    pub props: Props,
    pub in_place: bool, // built for one call in place: not a move of a !Move value (W0604)
    pub origin: Origin,
}
pub enum LocalKind {
    Return,
    Param(u32),
    Env,            // the closure value of the run node; no Live, no Dead; a Move below it only in a once closure
    User,
    Temp(TempKind),
    Iterator,
    Cap(EffectId),
    Kont(bool),
    ScopeCap,
    TaskResult(SpawnId),
    Upvar(LocalId), // the cell of this local of the parent body
}
pub enum TempKind {
    Operand, Callee, Receiver, Scrutinee, Borrowed, Discarded, Value,
    Promoted, // a borrowed value of plain data: in the Frame scope, Dead at each frame exit (5.10)
}
pub struct Props {
    pub copy: bool, pub linear: bool, pub on_abort: bool, pub once: bool,
    pub immovable: bool, pub nonportable: bool, pub uniq: bool, pub callable: bool,
    pub generic: bool, pub holds_refs: bool,
}

pub struct Place { pub local: LocalId, pub proj: Vec<Proj> }
pub enum Proj {
    Deref(DerefKind),
    Field(FieldIdx),    // stable
    Variant(VariantIdx), // unstable; only after a test of the variant
    Index(LocalId),     // stability from the type; `Bounds` before it
    Elems,              // `&v[]`
    Split(SplitId, Side), // only in interface places of a summary (a signature place `v[..k]`); no expression writes it
}
pub enum DerefKind { Ref, Box, Rc }
pub enum Side { Left, Right }

pub enum Operand { Copy(Place), Move(Place), Const(Const) }
pub enum Const { Unit, Bool(bool), Int(i128, IntTy), Str(String), Duration(u64), Fn(FnId, Vec<TyId>) }

/// No right side can change memory or suspend.
pub enum Rvalue {
    Use(Operand),
    Ref(Place),
    Binary(BinOp, Option<IntTy>, Operand, Operand), // the result is checked against its type
    Unary(UnOp, Option<IntTy>, Operand),
    Aggregate(AggKind, Vec<Operand>),
    Len(Place),
    Discriminant(Place),
    Concat(Vec<Operand>),
    Iter(IterSource),
}
pub enum BinOp { Add, Sub, Mul, Div, Rem, Eq, Ne, Lt, Le, Gt, Ge }
pub enum UnOp { Neg, Not }
/// For a closure: one operand for each capture, in order: `&x` (ByRef), `move x`
/// (ByMove), `copy x` of the whole local whose cell the environment shares (Kept),
/// `copy` of a capability (Cap), `copy` or `move` of a continuation (Kont).
pub enum AggKind { Tuple, Array, Vec, Struct(TyId), Variant(TyId, VariantIdx), Closure(ClosureId) }
pub enum IterSource { Elems(Place), Range(Operand, Operand) }

pub enum CapOperand {
    Local(Place),   // a Cap local, an upvar local that names one, or a Cap field of an environment
    Row(EffectId),  // the capability that the caller gives; valid where the cap env does not bind E
}
pub enum CapArgs { Lexical(CapEnvId), Root }

pub struct Block { pub stmts: Vec<Stmt>, pub term: Term, pub cleanup: bool }
pub struct Stmt { pub kind: StmtKind, pub origin: Origin }
pub enum StmtKind {
    Live(LocalId),       // a new cell, no value
    Dead(LocalId),       // drop what is left, end the cell
    Assign(Place, Rvalue), // the old value goes away first
    Drop(Place),         // only behind a pointer, right before an Assign of the same place
    Consume(Place),      // a linear value is finished
    Uninit(Place),       // no value from here
    Bounds(Place, Operand),
    Mention(Place),      // named, not read
    Print(Vec<Operand>),
    UnwindValue(Place, UnwindAction), // only on a cleanup path
    UnwindKont(LocalId), // only on a cleanup path, first in the chain of a clause
}
pub enum UnwindAction { OnAbort(FnId), Drop, Fault }

/// The origin of a `Return` is the expression whose value the frame gives back.
pub struct Term { pub kind: TermKind, pub origin: Origin }
pub enum TermKind {
    Goto(BlockId),
    Switch { on: Operand, arms: Vec<(u128, BlockId)>, otherwise: BlockId },
    Return,
    UnwindExit,
    Unreachable,
    Call { callee: Callee, args: Vec<Operand>, dest: Place, caps: CapArgs,
           next: Option<BlockId>, unwind: Option<BlockId> },
    Perform { cap: CapOperand, op: OpIdx, args: Vec<Operand>, dest: Place,
              next: BlockId, unwind: Option<BlockId> },
    Resume { kont: Place, arg: Operand, dest: Place, next: BlockId, unwind: Option<BlockId> },
    Handle { handler: HandlerId, dest: Place, next: BlockId, unwind: Option<BlockId> },
    Scope { scope: ScopeId, dest: Place, next: BlockId, unwind: Option<BlockId> },
    ScopeWait { scope: Place, orphans: Vec<LocalId>, next: BlockId, unwind: Option<BlockId> },
    Spawn { site: SpawnId, scope: Operand, task: Operand, dest: Option<Place>, next: BlockId },
    Join { task: Operand, dest: Place, next: BlockId, unwind: Option<BlockId> },
    Detach { task: Operand, next: BlockId },
    Fork { sites: Vec<SpawnId>, branches: Vec<Operand>, dest: Place, next: BlockId,
           unwind: Option<BlockId> },
    Assert { cond: Operand, next: BlockId, unwind: Option<BlockId> },
    IterNext { iter: Place, dest: Place, next: BlockId, done: BlockId },
}
pub enum Callee { Fn(FnId, Vec<TyId>), Value(Operand) }
// TermKind::{normal_successors, unwind, suspends, can_abort}: see the sketch.
// can_abort = suspends || Assert. suspends = Call, Perform, Resume, Handle, Scope,
// ScopeWait, Join, Fork.
```

Changes from the machine sketch, each with its source:

| Change | Why | Source |
| --- | --- | --- |
| `LocalKind::Upvar` replaces the environment operands of `Handle` and `Scope` | a handled body can move an outer local (O3-14); `(*env.k)` with rule V9 forbade it | proofs judge, graft 4 (MIR `Upvar`) |
| `CaptureMode::Kept` only for plain data that no body borrows | J5 and J5d: a closure that borrows a kept cell after its variable ended | soundness judge, graft 1 (minimal rule CAPTURE) |
| `Dead` always drops and emits `scope_end`; `Drop` only behind a pointer | each free had to hang on a `Drop` that the verifier did not check | soundness judge, H9 |
| `Row(E)` valid wherever the capability environment does not bind `E` | a handled body or a clause can perform an effect of a caller | proofs judge, fix 10 |
| no `CapOperand::Root` | root capabilities come from `CapArgs::Root` and the driver | simplification |
| `UnwindKont` first in the chain of a clause | the order of `step_unwind_drop` of the effects model | proofs judge, graft 7 |
| parameters and the continuation end before `Return` | W0204 of a reference into a by-value parameter; the continuation root ends at the clause end | minimal rule FRAME, step 5 |
| `Term::origin` of `Return` is the returned expression | W0204 reports the line of the returned expression (45 corpus markers) | feasibility judge, 3.3 |
| a cleanup chain finishes `_0` first (after `UnwindKont`), then the temporaries, the locals and the parameters | today the value of a frame is on the operand stack, which `frame_values` unwinds first; an `on abort` of the value can still read the locals | completeness review |
| `Program::tests` (`TestDecl`) | the interpreter runs a test by its name | completeness review |

### 3.3 Text form

`weft ir FILE [FUNCTION]` prints the IR (with `FUNCTION`: its body and the bodies inside
it, such as its closures). Each local is `_n` with its kind and name. A
block is `bbN`, and `(cleanup)` marks a cleanup block. Each terminator shows its normal
successors and its cleanup block. The printer is the format of the golden files
(`crates/weft-sema/tests/ir_golden/*.ir`). Section 5.37 has an example.

---

## 4. Well-formedness rules (the verifier)

`weft_ir::verify::verify_program` checks these rules. It runs in each unit test, in
debug builds after each build, and on each input of the gate. A broken rule is a bug of
the builder, not an error of the program. The sketch implements V1 to V7, V11 and V13
to V17; the others need the type table.

| Rule | Statement | What the facts get from it |
| --- | --- | --- |
| V1 | Each successor is a block of the body. | A1 path cover |
| V2 | A normal edge goes from a normal block to a normal block. An `unwind` edge goes to a cleanup block. A cleanup block goes only to cleanup blocks. | the abort paths are separate (D3 versus `unwound_at`) |
| V3 | A cleanup block ends with `Goto` to a cleanup block or with `UnwindExit`. No `Return` is on a cleanup path. | each abort path ends at the frame boundary |
| V4 | Each use of a local is on a path where the local has a cell on each path from the entry. The `Dead` of a promoted temporary (5.10) needs no cell: its `Live` can be on one path only. | `bound_before_use` for each component (closure and clause components too) |
| V5 | No `Live` of a local that has a cell, except a promoted temporary in a loop: each run of its `Live` makes a new cell (5.10). | one binding for each cell |
| V6 | At `Return` only `_0` (and the upvar locals and the environment) has a cell. At `UnwindExit` only the upvar locals, the environment and the promoted temporaries (5.10) have a cell. | D3 (each normal end has `scope_end`), C4 (each free has a node), W0204 of parameters |
| V7 | `UnwindExit` is the only terminator of `Body::unwind_exit`, and only there. | one frame boundary for the unwinder |
| V8 | Each projection fits the type: `Deref` only on a reference, a `Box` or an `Rc`; `Field` in range; `Variant` only in a block that a `Switch` on the discriminant of the same place dominates (not in an `Uninit`: it names a path and reads nothing, 5.2; not in an `UnwindValue`: the unwinder finishes the payload only if the value has the variant, 5.1.6); `Index` with a `usize` local; `Split` only on a slice. | B2 typed stability, B3 variant steps |
| V9 | `Copy` only for a type with `Props::copy`; `Move` only for other types; no `Move` through `Deref(Ref)` (W0303: the body gets no IR, 5.36). A `Move` of an upvar local is valid. A part of a function or continuation type is not checked: the props of a closure come from the analysis, and a `multi` continuation is plain data while a `once` one is not. | D1 (each move is a `moved_at`), C4 |
| V10 | Each terminator with `can_abort()` has an `unwind` block, except a `Call` of an extern function whose stated row is empty and that has no `assert`. | A1 for abort paths, D4 |
| V11 | `CapOperand::Local` names a `Cap` local, an upvar local of one, or a `Cap` field of the environment. `Row(E)` appears only where the capability environment of the body does not bind `E`. `Resume` names a `Kont` local of the clause, an upvar local of one (a body inside the clause), or a `Kont` field of an environment. A field of an environment view (5.1.7) is a field of the environment. | capabilities and continuations are values of one frame |
| V12 | A temporary has one `Live`, and a `Dead` on each path from it to an exit (a promoted temporary: on each normal path to a `Return`, 5.10). A temporary of the tail of a frame body ends after `_0` gets the value. | C2 holder cover, the frame-end order |
| V13 | A `Kept` capture is never borrowed: its aggregate operand is `copy` of its source, the source is a cell (a whole local, or a capture `env.j` or `(*env.j)` of a maker closure), and no `Ref` in the closure body (or an inner body) names a place at or below `env.k` that is not behind a further reference. The verifier also recomputes `capture_mode` and compares. It reads each environment view (5.1.7): `u.k` in a handled body, a clause or a scope body inside the closure is `env.k`, and a source `u.j` or `(*u.j)` is a cell. | F5 `kept`; the kept cell is outside the reference fragment of B1 |
| V14 | Upvar locals exist only in clause, handled and scope bodies; each names a local of the parent body; none has `Live` or `Dead`. The environment local exists only in a closure body and has no `Live` or `Dead`; a `Move` of a place below it, or below an environment view of it (5.1.7), is valid only in a `once` closure. | splices share the cells of the site; the closure value outlives each run |
| V15 | Each handled body and each scope body is named by exactly one terminator; each clause by exactly one handler; each closure body by one aggregate kind. | the splice assumes a once-run frame (machine risk R10) |
| V16 | The cleanup chain of a clause starts with `UnwindKont` of its continuation. A cleanup chain lists `_0` if it has a value, then the live temporaries newest first, then the live locals from the highest index, then the parameters. (`Dead(_0)` with no value comes before the parameters.) | one unwind order for the interpreter, the facts and the effects model |
| V17 | `Drop(p)` only on a place with a `Deref`, and the next statement is `Assign(p, _)`. | the drop pair of W0601 behind a reference |
| V18 | Each `Return` has the origin of the expression whose value it returns. | W0204 spans |

---
## 5. Lowering rules: typed tree to IR

The builder `irbuild::build` lowers the THIR of one item (a function or a test, with the
closures, clauses, handled bodies and scope bodies inside it) to bodies. It runs once,
before effect inference. Section 5.1 gives the general rules. Sections 5.2 to 5.35 give
the rule for each construct of `docs/plan/core-ir-inputs/map_lowering.md`, section 2 (the map number is in
brackets), and name the special cases of the old lowering that go away.

The builder builds a body only if `typeck` reports no error in it. A body with a type
error gets no IR and no facts; the program keeps its `typeck` diagnostics (W01xx), as the
corpus markers expect. W0118 at the name of an `on abort` function is not a `typeck`
error: it is a check of the effects of the function, and the `ir` pipeline asks the
summary of the body for it (6.9). So such a body gets its IR (plan stage F7).

Notation: `t`, `t1` are new temporaries. `t := rv` is `Live(t); t = rv`. A terminator is
`dest = kind(args) -> [next, unwind: C]`. `C` is the cleanup block of the current point
(section 5.1.6).

### 5.1 General rules

#### 5.1.1 Destinations and operands

The builder has three entry points for an expression `e`:

- `into(e, dest)`: write the value of `e` into the place `dest`. A block tail, a branch,
  an arm, a `handle`, a `scope` and a call use it. So the value of each frame and each
  branch is an assignment of an operand: a move if the type is not plain data, else a
  copy (class TAIL). An aggregate, a call, a `handle`, a `scope`, a block, an `if` and a
  `match` write into `dest` itself, with no temporary between: a value is built where it
  stays. So the construction of a `!Move` value is not a move of it (W0604, 5.36).
- `operand(e)`: evaluate `e` now and give an `Operand`. **An operand is read where it is
  written (choice A of `docs/plan/core-ir-inputs/semantics.md` 2.2).** A place of a copy type gives
  `t := copy p`. A place of another type gives `t := move p` in a move position (an
  argument, a field value, a `let` value), and `t := &p` in a read position (a
  comparison, `print`). A value gives a temporary. A constant stays a constant. A place
  operand may skip the temporary only if no later operand of the same construct can run
  code (each later operand is a constant or a plain local): then the order cannot show.
  As built (plan stage F8): a `move` operand also needs a temporary if a later operand
  names the same local (`f(v, v)`, `f(s.items, s.n)`): the move is then a statement
  before the call or the aggregate, and the facts see the later read after the move
  (W0302). One node with both would hide the order (review of stage F8, hole H1).
- `place(e)`: evaluate a place expression and give a `Place`. Its index expressions run
  now, in order, into temporaries (`Index(t)`). A value that is not a place goes into a
  temporary of the current statement.

The order inside one construct is the order of `docs/plan/core-ir-inputs/semantics.md` 2.1, with the three
changes of choice A (a place operand of a binary operator, of `print`, and the base of
an index are read where they are written). The other exceptions stay and are written
once in the builder: named arguments in parameter order (ADR 0009, from the THIR
argument order), the value before the target in an assignment, a positional struct in
field order, and a method receiver read at the call.

Why choice A: the facts of the old pipeline already put the read at the operand. The
interpreter reads later. That gap is the unsound findings N1 to N3 of
`docs/plan/core-ir-inputs/semantics.md`. Choice A moves the interpreter to the point that the checker
assumes, so both agree by construction. The cost: `x + { x = 5; 1 }` gives 2, not 6
(probe p1). `docs/design.md` states the order (plan stage C3).

#### 5.1.2 Scopes

The builder keeps a stack of scopes:

| Scope | Opened by | Holds | Closed by |
| --- | --- | --- | --- |
| `Frame` | each body | the parameters, the tail temporaries of the body, the promoted temporaries (5.10) | the frame end (5.1.4) |
| `Block` | each block `{ }` | its `let` locals and the bindings of `match` arms | the end of the block, or a jump out of it |
| `Stmt` | each statement that is not a tail; the condition of `while`; the tail of a loop body | the temporaries of the statement | the end of the statement |
| `Loop` | `while`, `loop`, `for` | the iterator of `for`; the `break` and `continue` targets | the end of the loop |
| `Fence` | a handled body, a clause, a scope body | nothing; `break`, `continue` and `return` cannot cross it (W0315) | the end of the body |

A temporary goes into the innermost `Stmt` scope; a promoted temporary goes into the
`Frame` scope (5.10). A block tail is not a statement, so
its temporaries go into the scope around the block (`docs/plan/core-ir-inputs/semantics.md` 4.2). The
temporaries of the tail of a loop body go into a `Stmt` scope of their own: they end at
the end of each iteration (decision N5, a run-time change).

#### 5.1.3 Ends and drops

- At each exit of a scope, on each path, the builder writes `Dead(l)` for each local of
  the scope that has a cell, in reverse declaration order. `Dead` drops the value that
  is still there. A moved local has nothing to drop: the interpreter skips `Moved`, and
  the facts see the move (`moved_at`) before the end (`scope_end`).
- `Assign(p, rv)` drops the old value of `p` first, as the `Store` of the interpreter
  does. No `Drop` statement is needed for it. The facts see the overwrite through
  `rebound_at` (a whole local) or `overwrites` (a part).
- A place behind a pointer gets `Drop(p)` right before its `Assign(p, rv)`, if the old
  value can be linear (V17). The facts give the old value a drop pair (W0601: behind a
  reference the old value is always there, ADR 0007).
- A value that nothing keeps goes into a temporary of kind `Discarded`, and its `Dead`
  at the end of its statement drops it: an expression statement, `let _ = e`, a block
  statement, the tail of a loop body, the branch of an `if` with no `else`.
- A pattern `_` over a part of a value that an arm or a `let` takes: `t := move p.k;
  Dead(t)`. So the facts see a part move and the end of the part (W0601 for a linear
  part).
- The results of tasks with no handle are `TaskResult` locals of the scope body.
  `ScopeWait` gives them their values, and the frame end ends them.

A linear value at a `Dead` is the error that W0601 reports: `scope_end` of a live
linear value. So the forms of RT14 (`let _`, a wildcard part, `print`, `match _`, an
overwrite) and V057 (a `T` moved into a holder that goes away) are one rule.

#### 5.1.4 The end of a frame

Each body ends in the order of the machine (`docs/plan/core-ir-inputs/semantics.md` 5.3):

```text
_0 = <tail operand>        // the value leaves into the return slot (a call writes _0 itself)
ScopeWait(s) -> [next, C]  // only a scope body: wait for the tasks
Dead of the block locals   // reverse declaration order (TaskResult locals too)
Dead of the tail temporaries and the promoted temporaries (5.10)
Dead of the parameters, the capability parameter and the continuation (not the environment)
Return                     // origin: the expression whose value leaves
```

A reference in `_0` into a local, a tail temporary or a by-value parameter of the frame
is a reference into a dead cell at the node that uses `_0` next: the `Return` node
(`uses(_0)`), the `Exit` of a spliced frame, or the `Ret` of a call (section 6). This
is the rule that O3-2, O3-3 and F3-7 needed, written once for each frame kind. A
reference parameter ends its own cell, not what it points into.

The `Dead` of a fresh continuation drops it: the frames of the handled body unwind
after the clause returns, as `do_return` of the effects model. A `return e` writes
`_0 = <e>` and jumps to the frame end of its own exit, which has its own `Return` with
the origin of `e` (V18).

#### 5.1.5 Jumps

`break`, `continue` and `return` exit each scope between the jump and its target, from
the innermost: the `Dead` of 5.1.3 for each one, then `Goto`. A value on its way (an
operand in a temporary of an open statement) is a temporary of an exited `Stmt` scope,
so it gets its `Dead` there (OL-3c). A `Fence` scope stops the search: W0315 for a jump
out of a handled body, a clause or a scope body. The builder reports W0315
(`Built::diags`), only at a point that can run, and ends the path with `Unreachable`; a
`return e` there evaluates `e` as an expression statement first. A `Frame` scope (a
closure body) stops the search of `break` and `continue`: that is W0111 of `typeck`.

#### 5.1.6 Cleanup chains

Each terminator with `can_abort()` gets `unwind: C`. `C` is the cleanup chain of the
frame at that point. It finishes each value that has a cell there:

```text
cleanup:     UnwindKont(k) ; Dead(k)                               // a clause: the fresh continuation first
             [UnwindValue(_0, a) ; Dead(_0)]                       // `_0`, only if it has a value
             UnwindValue(t_newest, a) ; Dead(t_newest) ; ...       // live temporaries, newest first (not a promoted one, 5.10)
             UnwindValue(l_highest, a) ; Dead(l_highest) ; ...     // live locals, highest index first
             [Dead(_0)]                                            // `_0` with no value
             [UnwindValue(s, Drop)] ; Dead(params), Dead(cap)      // the parameters (a scope body cancels and joins its tasks at its ScopeCap), the capability
             Goto(unwind_exit)
unwind_exit: UnwindExit
```

- The order of values inside a frame is the order of the unwinder of the interpreter
  (`frame_values`, `machine/effects.rs:424`): first the operand stack (today the value of
  the frame, for example the value of a scope body at its end, and each operand on its
  way), then the temporary cells newest first, then the slots from the highest. In the IR
  the value of the frame is `_0` and the operands are temporaries. So the chain finishes
  `_0` first, then the temporaries newest first, then the locals from the highest index,
  then the parameters. The effects model changes `max_slot` to compare slots, not
  resource ids, with the slot numbers of section 9.5. One order for the interpreter, the
  facts and the model (N6). The value of the frame goes before the locals, so an
  `on abort` of the value can still read a local that the value points into.
- In a clause, the fresh continuation unwinds first: the order of `step_unwind_drop`
  of the effects model. The interpreter changes to this order when it runs the cleanup
  chains (plan stage I6; N7). `UnwindKont` of a continuation that is no longer fresh does
  nothing at run time.
- `_0` is in the chain only after it gets a value: the value of a scope body is in `_0`
  across `ScopeWait`, which can abort (F3-7; soundness judge H9). Before that, the chain
  has only `Dead(_0)`, before the parameters.
- A plain-data value needs no `UnwindValue`: its `Dead` is enough. The builder writes
  `UnwindValue` for each value that is not plain data.
- `UnwindValue` of the `ScopeCap` local of a scope body cancels the tasks of the scope
  and waits for them (the unwinder does this today, V084).
- Two chains with the same suffix share the blocks of the suffix, as the drop trees of
  MIR do. The chain of a handled body and of a scope body ends at their own
  `UnwindExit`; the fact generator connects it to the site (section 6.5).

`a` (the `UnwindAction`) comes from the type:

| Type of the value | Action |
| --- | --- |
| no linear part | `Drop` |
| linear, and the type declares `on abort = f` | `OnAbort(f)` |
| linear, no `on abort` on the type, each linear part has one | one `UnwindValue` for each linear part, in field order (`extract_linear`, `machine/effects.rs:458`) |
| a linear part with no `on abort` | `Fault`: W0602 rejects each program that can reach it |

How the builder applies the table (`irbuild/cleanup.rs`, plan stage B8):

- The walk follows the fields of a struct, the parts of a tuple, the payload of each
  variant of an enum (`(p as V).k`) and the target of a `Box` (`(*p)`), in that order.
  A `Variant` step in an `UnwindValue` needs no test (V8): the unwinder finishes the
  payload only if the value has the variant. The elements of an array or of a `Vec`
  get one `UnwindValue(p[], a)` if the element type has one action for the whole
  value; else the buffer gets one action as a whole.
- A part that the walk does not follow (a recursive type on the way, an `Rc`, more
  than 16 steps deep, or more than 64 parts) gets one action for the whole part:
  `Fault` if a linear part in it has no `on abort`, else `Drop`.
- A linear extern type whose runtime gives `on abort` (a `Task` handle: a cancel) gets
  `Drop`, or `Fault` if a type argument has a linear part with no `on abort`.
- A value of a type parameter gets `Drop`: the instance decides at run time, and the
  summary of the function gives the obligation to its callers (W0602 of a generic
  callee, section 6.7).
- A value whose type has no linear part, but whose local properties say linear (a
  closure: plan stage B9), gets `Fault` if its properties have no `on abort`, else
  `Drop`. The `Drop` of a closure finishes the linear values that it owns in its
  `ByMove` fields, each with its `on abort` (`extract_linear` goes into the cells of a
  closure). A field of an environment is not a place of the IR, so the action is one
  for the whole closure.
- A parameter that is not plain data gets its `UnwindValue` too, before its `Dead`.
- `_0` has a value from the write of the frame value (the frame end) or of a `return`
  value, to the `Return`. In a scope body `ScopeWait` comes between (5.29), so its chain
  starts with `_0`. `Dead(_0)` with no value has no `UnwindValue`.
- The `ScopeCap` local of a scope body is plain data, but it gets `UnwindValue(s, Drop)`
  before its `Dead` in each chain: the unwinder cancels the tasks of the scope and waits
  for them.
- An `UnwindValue` of a local with a cell but with no value (a `let` local before its
  value, a moved value) finishes nothing at run time; the facts see the move first.

#### 5.1.7 Captures and upvars

**Rule CAPTURE.** One function, `capture_mode(var, closure)`, decides how a closure
holds each local of an outer body that its body (or a body inside it) names. The
interpreter reads the decision from the IR (no `by_value` side table).

1. `ByMove` if the body (or an inner closure of it) moves the variable or a place below
   it: a `Move` operand, a by-value pattern (a `Consume` too), or an inner closure with
   a `ByMove` field for it. An inner closure that moves a capture makes each closure
   around it move it (ADR 0003, OR2).
2. Else `Kept` if the type is plain data and no statement of the body, or of a body
   inside it, borrows a place at or below the variable: no `Rvalue::Ref`, no binding by
   reference, no by-reference receiver or argument, no iterator over its elements. A
   borrow through a reference that the variable holds (`&(*r).f` with `r: &T`) points
   into the target, not into the cell of `r`: it does not count.
3. Else `ByRef`.
4. `Cap` and `Kont` for capability and continuation values.

How the builder applies the rule (`irbuild/closure.rs`, plan stage B9):

- The captures of a closure literal are the names of its body (and of the bodies inside
  it) that the maker resolves: a local, an upvar local, or a capture of the maker when
  the maker is a closure body. They are the fields of the environment, in the order of
  their first use. So an inner closure that names a variable of the function makes each
  closure around it capture the variable too, and `Capture::source` of the inner
  closure is the field of the maker (`env.j`, or `(*env.j)` for a `ByRef` capture).
- The builder builds the closure body with each capture as `env.k`. Then it reads the
  body: a `Move` or a `Consume` at or below `env.k` gives `ByMove`; else a borrow at or
  below `env.k` with no `Deref(Ref)` after `env.k` gives `ByRef`, and so does a variable
  that is not plain data; else `Kept`. The aggregate of an inner closure is in the
  body, so its operand (`&env.k`, `move env.k`, `copy env.k`) counts. Then each place of
  a `ByRef` capture gets its `Deref` (`(*env.k)`), also the sources of the inner
  closures. A store into a capture gets its `Drop` (5.1.3) only if the capture is
  `ByRef`.
- A `Kept` capture of a `ByRef` capture of the maker shares the cell that `(*env.j)`
  names: the cell of the variable, not a copy of its value. The mode of an inner
  closure depends only on its own body and the bodies inside it.

So `|| count += 1` is `Kept` (it writes, it does not borrow): the counter closure that
leaves its function stays legal (`125_multi_values.wf` `shared_closure`,
`ir/work/judge/p/d5_count.wf`). `|| print(norm(&p))` is `ByRef`: the closure points into
the cell of `p`, so a maker that returns it gets W0204, and a call after the end of `p`
gets W0301 (J5, J5d; open today). V13 checks the rule.

A `ByRef` capture points into the **cell root** of the variable, not into its value
root (section 6.3). A move of the variable frees its value root but not its cell: a
closure that holds `&x` reads the new value of `x` when it runs (O3-11). Only `Dead(x)`
and the unwinding of `x` end the cell.

A `Kept` cell stays readable for the closure after the end of the variable (the
interpreter today, ADR 0006 `kept`). While the variable lives, the closure and its maker
share the cell: a write of the closure (`|| count += 1`) is a write of the variable at
each node that runs the closure (6.7), so a task that writes a kept counter conflicts
with a read of the counter in the parent (W0405). No reference can point into it (V13), so its
lifetime is outside the reference fragment of the proofs (section 9.1).

**Upvars.** A clause, a handled body and a scope body do not capture into an
environment. They name each local of the site that they use as an upvar local
(`LocalKind::Upvar(site_local)`). A body inside a handled body names a local of the
function through the chain of upvar locals. An upvar local has the cell of the site
local. A read, a write, a borrow or a move of it is a read, a write, a borrow or a move
of the site local. The interpreter gives the frame the captured cells of its upvar
locals (`Var(Cap(k))`).

How the builder makes upvar locals (`irbuild/upvar.rs`, plan stage B10):

- Before it builds the bodies of a `handle`, the site finds each name of the handled
  body and of the clauses (and of the bodies inside them) that it resolves, and each
  capability that they can use (5.1.8). A name of an outer body gets an upvar local in
  the site too, so the chain of upvar locals reaches the function.
- A nested body makes the upvar local of a site local at its first use. It has the type,
  the name and the props of the site local, no `Live`, no `Dead`, and it is not in a
  cleanup chain.
- An upvar local names a whole local of the site. A capture of a closure body (`env.k`)
  is not a whole local, so a `handle` or a `scope` in a closure body names the captures
  and the `Cap` fields of the closure through an **upvar local of the environment**
  (plan stage B12). Its kind is `Upvar(env)` (or `Upvar(u)` of such an upvar local of
  the site, in a deeper body), and it has the type and the props of the environment. A
  capture is the place `u.k` (or `(*u.k)` for a `ByRef` capture), as `env.k` is in the
  closure body. All captures of one closure share one upvar local in each nested body.
  The *environment views* of a closure are its environment local and each upvar local
  whose chain of `Upvar` kinds ends at it. A view has the place type of the
  environment: `u.k` has the type of field `k`.
- Rule CAPTURE reads each view: a `Move`, a `Consume` or a borrow at or below `u.k` in
  a handled body, a clause or a scope body inside the closure counts as one at or
  below `env.k` (a closure that a nested body makes counts by its aggregate operand, as
  in the closure body). The builder builds the nested bodies before it knows the modes
  of the closure, with `u.k` for each capture. When it knows the modes, it puts the
  `Deref` of each `ByRef` capture into each place of each view (`(*u.k)`), also into the
  sources of the closures that the nested bodies make, and it keeps the `Drop` of a
  store only for a `ByRef` capture (5.1.3).
- V13 and V14 read the views too: no `Ref` names a place at or below a `Kept` capture
  in any view; a `Move` of a place below a view is valid only in a `once` closure; a
  `Kept` capture of a nested body has the source `u.j` or `(*u.j)`. V11 accepts a
  `Cap` or `Kont` field of a view. At run time a view has the cell of the environment,
  as each upvar local has the cell of its site local.

#### 5.1.8 Capabilities

Handlers are lexical, so the builder resolves each effect at each point from the static
capability environment (`CapEnv`):

- In a handled body, the innermost `handle` of `E` around the point binds `E` to the
  `Cap` local of that handled body (or to an upvar local that names it, in a nested
  body).
- In a closure, the closure's `cap_env` binds `E` to a `Cap` field of the environment if
  the closure is made inside the handled body of `E`; the aggregate copies the
  capability into that field.
- Else `E` resolves to `CapOperand::Row(E)`: the caller of the function gives it.

A clause runs in the capability environment of its site, without the capability of its
own handler (rule 6 of the effects proof). A call passes `CapArgs::Lexical(env)`: the
callee takes the capability of each effect of its row from `env`. An `on abort` call
passes `CapArgs::Root`.

How the builder applies this (`irbuild/caps.rs`, plan stage B10):

- Each body keeps the capabilities that it binds, with their places in the body: the
  `Cap` local of a handled body, the `Cap` fields of a closure, and the upvar locals of
  the capabilities of the site (made at the first perform). A perform takes the first of
  these for its effect, else `Row(E)`.
- A handled body gets a new environment: its parent is the environment of the site, and
  it adds `(E, _1)`. A clause has the environment of its site. The place of an `adds`
  entry is a place of the body that opens the environment; a nested body names it
  through an upvar local.
- A closure gets one `Cap` field, after its variables, for each effect that its maker
  binds and that its body (or a body inside it) can use: an effect that it performs, an
  effect of the stated row of a call in it, and each effect if a call in it has a row
  that the builder does not know (a function with no stated row, a function value with
  no stated row, a task builtin). An effect that the code does not use gets no field,
  so a closure that only computes holds no capability (no W0313 for it). A closure with
  `Cap` fields has its own environment: its parent is the environment of the maker, and
  it adds `(E, env.k)` for each field. `ClosureDecl::cap_env` stays the environment of
  the maker.
- The site of a `handle` finds the capabilities of the handled body and the clauses by
  the same rule, with only the calls inside closures counted: a call outside a closure
  passes the lexical environment and needs no place.

#### 5.1.9 Builder limits

The parser bounds nesting at 96 levels and cuts long operator chains into hidden locals
(`docs/architecture.md`, "Size limits"). The builder recurses only along that nesting,
so its depth is bounded. It runs inside `weft_sema::on_large_stack`. Long flat chains
(`1 + 1 + ...`, `t && t || t ...`, 20 000 terms) give long straight lines of blocks;
each later pass works over blocks in reverse post-order with a worklist, so its cost is
linear on such chains. `crates/weft-cli/tests/limits.rs` and
`crates/weft-check/tests/scale.rs` run with the IR pipeline in each stage of the plan
that changes the builder or the analysis.

As built (plan stage B12):

- At the end of the build, `weft_ir::order::renumber` gives the blocks of each body new
  numbers in reverse post-order. The walk visits the successors of a block from the
  last one, so the first successor comes right after its block: the next block of a
  call before its cleanup block, the first arm of a `Switch` before the others, the
  body of a loop before its exit. The blocks that the entry does not reach come last.
  So the text reads from top to bottom, and each edge that is not a back edge goes to a
  larger number. The verifier does not need this order: it computes its own.
- The verifier has no pass that is quadratic in the blocks. The dominators come from
  the algorithm of Lengauer and Tarjan (a wide `match` has one block with an edge in
  from each failed test). The storage rules V4 to V6 keep one bit set of cells only for
  the entry and for each block with more than one edge in; a walk from such a block
  goes on into each block with one edge in, and a worklist takes these blocks in
  reverse post-order. So the memory is the join blocks times the locals / 64 words.
- The size of the IR itself is not linear in the source in one case: each abort point
  lists each live temporary in its cleanup chain, and a temporary of an outer statement
  (the value of an `if` statement) lives across all of its inner statements. So nested
  `if` statements with calls give about depth times calls cleanup blocks (80 levels with
  100 calls each: 330 000 blocks). The nesting limit of the parser bounds the factor.

### 5.2 Function body, parameters, exit [2.1]

```text
body f (Fn):  params _1.._n (cells at the entry), _0
  bb0: <body block into _0>; <frame end>; Return
  unwind_exit: UnwindExit
```

- A by-value parameter is a local of the frame. A reference parameter is a local of
  reference type: a place through it is `(*_i).proj`.
- A by-value parameter is built in place (ADR 0007): at the entry, `Uninit(_i.q)` for
  each place field path `q` of its full type (5.17), also below a variant or a `Box`.
  A path that stops at a struct or an enum of a cycle on the way stands for each place
  field at or below it.
- The row capabilities are `CapOperand::Row(E)`.
- A test body is a `Test` body with no parameters.
- **Goes away:** the second `Param` root of a by-value parameter that holds references
  (α of `Deref`, section 6.3); "the temporaries of the tail get no `scope_end`"
  (`stmt.rs`); `check_returned_refs` after `op_refs` (the local W0204 forms are
  `error(_0, Return)` in the spec, section 6.9).

### 5.3 `let` and patterns [2.2]

```text
let x = e        =>  Live(x); <into(e, x)>
let x: T         =>  Live(x); Uninit(x)                (a tuple pattern: the same for each binding)
let (a, b) = e   =>  t := <e>; Live(a); a = move t.0; Live(b); b = move t.1   (copy for plain data)
let S(a, b) = s  =>  Live(a); a = move s.0; Live(b); b = move s.1; Consume(s)  (a linear struct)
let _ = e        =>  t := <e>; Dead(t)
```

- The binding is one `Assign` node after the nodes of the value. A call result binds at
  the `Ret` node of the call (section 6.2), so no node both invalidates and binds.
- **Goes away:** `assign_local`, the cell root of a reference local, `point_local`,
  `wild_drops`, `drop_linear`.
- **Closes:** O3-2: the temporary of a handled body ends before its `Return`; `_0`
  holds the value across that free; `Exit` uses `_0`: W0301.

### 5.4 Expression statements and place statements [2.3]

```text
e;  (a value)            =>  Stmt scope { t := <e>; Dead(t) }
p;  (a place of a local) =>  Stmt scope { <index temporaries>; Bounds(..); Mention(p) }
{ ... v };  (a block)    =>  Stmt scope { t := <block>; Dead(t) }
```

- A place in statement position names the place. It reads only the lengths of its
  indexes. It moves nothing (OR6).
- A discarded value always gets a temporary and its `Dead`: a scope statement (O3-1),
  a spawn statement with a handle type (O3-4, unless it is the `dest: None` form of
  5.29), a block statement (V118).
- The tail of a block whose value nothing keeps (the branch of an `if` with no `else`,
  a loop body) is not a place statement (ADR 0003, 5.1.3): a tail place whose value is
  not plain data moves into a `Discarded` temporary, and its `Dead` drops it
  (`t := move p; Dead(t)`); a tail place of plain data is a `Mention`. As built (plan
  stage F8, `irbuild/stmt.rs` `drop_tail`; review of stage F8, hole H2): until F8 the
  builder gave a `Mention` there, which accepted `if c { v }; print(v.len())`. The tail
  of a frame body whose `_0` is `()` (`fn f() { v }`) stays an expression statement, as
  in the old lowering.
- **Goes away:** `drop_value` and its early returns, `discard_block_value`,
  `local_place`.

### 5.5 Assignment to a local: `x = v` [2.4]

```text
x = v   =>  t := <v>; x = move t
```

- The value runs first, then the target, then the store (`compile.rs:481`). The
  `Assign` drops the old value.
- `x = v` on a reference local gives `x` a new reference. `x += v` on a reference local
  writes through it: `(*x) = (*x) + v` (RT9).

### 5.6 Assignment to a place [2.5]

```text
p.f = v       =>  t := <v>; <place p>; p.f = move t
(*r).f = v    =>  t := <v>; [Drop((*r).f)]; (*r).f = move t     (Drop if the old value can be linear)
v[i] = x      =>  t := <x>; ti := <i>; Bounds((*v), copy ti); (*v)[ti] = move t
```

- The target place runs after the value (its index expressions too).
- The source names the target before the value. So a value that gives the base of a
  variant step of the target a new value is W0301, also when the test of the variant
  after the value would stop the run (`e.A.hp = { e = Two.B(..); 5 }`, and the same
  with `+=`): the write uses the `N` variable of the step, which binds where the value
  starts (6.3).
- A new value of a part of a local is an assignment to a move path. The fact generator
  gives each move path that the body assigns its own fact variable (section 6.3): the
  part holders of today (`part_holder`, `retire_holders`, `retire_stale`, S069) are
  this rule.
- A self-reference field of a `!Move` struct: the `Assign` emits `ref_at` and `ref_in`
  (W0605).
- **Goes away:** `drop_replaced_uses`, `assigned_places`, `field_referents`,
  `writes_through`.

### 5.7 Compound assignment: `x += v`, `x -= v`, `x *= v` [2.6]

```text
x += v   (x a local)        =>  t := <v>; t2 := Add(copy x, move t) as T; x = move t2
p += v   (p through a ref)  =>  t := <v>; t2 := Add(copy p, move t) as T; p = move t2
```

`-=` and `*=` are the same with `Sub` and `Mul`. The grammar has no other compound
assignment.

The integer type is in the `Binary` right side, from the THIR (`int_ty`). The
span-keyed `int_ops` table goes away (RR14). The builder writes each `Deref` that the
type asks for (RT9, V014, V098).

### 5.8 Names, field places, index places, slices [2.7]

| Source | IR place |
| --- | --- |
| `x` (a local) | `x` |
| `x` (a local of the site, in a clause, handled body or scope body) | the upvar local `u` with `Upvar(x)` |
| `x` (a closure capture, `ByRef`) | `(*env.k)` |
| `x` (a closure capture, `ByMove` or `Kept`) | `env.k` |
| `x` (a closure capture, in a clause, handled body or scope body inside the closure) | `u.k` or `(*u.k)`, with `u` the upvar local of the environment (5.1.7) |
| `r.f` with `r: &S` | `(*r).f` |
| `b.f` with `b: Box<S>` | `(*b).f` (`Deref(Box)`) |
| `h.f` with `h: Rc<S>` | `(*h).f` (`Deref(Rc)`) |
| `v[i]` with `v: Vec<T>` | `ti := <i>; Bounds(v, copy ti); v[ti]` (unstable element step) |
| `a[i]` with `a: [T; n]` | `a[ti]` (stable element step) |
| `t.0` | `t.0` |
| `o.Some` | `td := Discriminant(o); Switch(move td) [Some: next, otherwise: Unreachable]`, then `(o as Some).0` (the interpreter faults on another variant) |
| `o.A` with `A` of no field or of more than one field | no place: the type is `()` or a tuple that the payload does not hold; the body gets no IR (`NoIr::VariantPayload`, 5.36) |
| `&v[]` | `&v[]` (`Elems`) |

No expression writes a split step. A split place (`v[..k]`, `v[k..]`) comes only from a
signature, for example the result of `split_at`. α gives it the split step of the
`SplitId` of its call node and parameter when the summary applies (6.3, 6.7). So
`Proj::Split` appears only in interface places of a summary.

The builder writes each implicit dereference of the THIR (`adjust`). So `held_refs`,
`deref_lval`, `through_ref`, the `*rs` roots of `held_root` and `handle_deps` become α of
one projection (section 6.3). A read through `(*h).f` names `h`, so a task that reads
it reads the handle (O3-6).

### 5.9 Borrow [2.8]

```text
&p        =>  t := &<place p>
&p[]      =>  t := &<place p>[]
&value    =>  tv := <value>; t := &tv          (tv in the current Stmt scope)
&plain    =>  tv := <plain>; t := &tv          (tv promoted: in the Frame scope, 5.10)
&plain.f  =>  tv := <plain>; t := &tv.f        (the base value promoted; also `&plain.f.g`, `&(1, 2).0`)
&b.items  =>  t := &(*b).items                 (names b: a read of the Box, OL-R2d-box)
```

`plain` is a value (not a place) of plain data with no function part and no resource
part (`weft_sema::props::ir_promotes`): a constant (`&1`, `&"s"`, `&true`, `&()`,
`&2.s`), a tuple or a struct of plain data (`&(1, 2)`, `&P { x: 1, y: 2 }`), the result
of a call or an operator (`&g()`, `&(a + 1)`). A `Vec` literal, an array and a struct
with a `Vec` are not plain data: `&mkv()[0]` and `&V { v: Vec.new() }` borrow a
temporary of the statement (W0301 at a later use, `32_temporaries.wf`).

A borrow does not read the value. A borrow of a place field with no value is a use
(W0304). **Goes away:** `temp_root` (S007).

### 5.10 Temporaries [2.9]

A temporary ends at the end of its `Stmt` scope, or at the frame end for a tail
temporary of a frame body. Each frame kind uses 5.1.4. The summary of a closure or a
clause reports the frees of its own temporaries as frees of the callee frame root, not
as `scope_end` of hidden variables (`Summary::dropped` goes away).

**Promoted temporaries.** Weft has no `let` extension of temporaries: `let r =
&mkv()[0]; print(r)` is W0301. But a borrowed temporary of plain data (5.9) is a
*promoted* temporary (`TempKind::Promoted`): it ends with its frame, not with its
statement. So `let r = &1; print(r)` (`temp_copy` of `32_temporaries.wf`, no marker)
is valid, and `fn f() -> &u64 { &1 }` is W0204 (`error(_0, Return)`, 6.9: a reference
into a local of the frame at the `Return`).

- The builder writes `Live(t)` at the borrow and puts `t` into the `Frame` scope. So
  each exit of the frame (the frame end and each `return`) has `Dead(t)`, with the
  tail temporaries (5.1.4). The `Live` can be in a branch: on a path that did not run
  it, the `Dead` has no cell to end (V4 allows it, and the interpreter does nothing).
- The `Live` can be in a loop. Each run of it makes a new cell (V5 allows it); the old
  cell stays, so a reference of an earlier iteration stays valid
  (`while i < n { v.push(&(i + 1)); i += 1 }` keeps one cell for each element). The
  facts see one variable `S(t)`: its first value after a `Live` writes nothing (6.4),
  and its `scope_end` is at the frame exit.
- No cleanup chain lists `t` (5.1.6): its value is plain data, so the unwinder has
  nothing to finish (V6 allows the cell at `UnwindExit`).

Why this rule: it is the rule of the old pipeline. The old lowering gives a temporary
of plain data no variable (`Lower::temp_root`: no `may_free`), so no node ends it in
the body, and the check of a returned reference sees a temporary of the frame (W0204).
At run time, both engines keep the value of a temporary cell of plain data after its
end and the oracle does not mark the cell as ended (`Heap::end_cell_value`): a read
through the reference runs clean, after the statement and after the frame. So the rule
changes no run-time behaviour. A temporary that is not plain data can hold a linear
value or a buffer, and its end frees them: it keeps the end of its statement.

Two choices that the rule does not take: a constant place that never ends (Rust
promotion to `'static`) accepts `fn f() -> &u64 { &1 }`, which the old pipeline
rejects, and covers only constants, not `&g()` or `&(a + 1)`; a temporary with its
`Live` at the frame entry shares one cell between the iterations of a loop, so a
reference of an earlier iteration would see a later value.

The old lowering also promotes a plain-data temporary that holds a reference, but it
drops the references in it: `let rr = &&v; let w = v; print(rr.len())` is accepted
and faults at run time. The IR keeps them: `t := &v; rr := &t`, and the facts see
`rr` through `t` into `v`.

A known false positive of this rule with loops (stage F10b, review of stage F10,
`pt09`): `v.push(1); while i < 3 { rs.push(&&v[0]); i += 1 }; print(rs[0])` is W0301.
`S(t)` points into `v[]` at each node, so the change of `v` before the loop makes it
invalid, and the path with no iteration takes that to the read. A new value of `S(t)`
at its first value in an iteration would be unsound: `rs` keeps the references to the
cells of the earlier iterations, and a later change of `v` must make them invalid.
The fix is a version for each definition (plan track P1; test `ir_loops`
`a_promoted_temporary_in_a_loop_after_an_earlier_change_is_a_known_false_positive`).

A receiver value of plain data that a method borrows (`self` by reference, 5.19) is a
borrow of a value too: `mkp().px()` with `fn px(self) -> &u64 in self` puts `mkp()`
into a promoted temporary, and `let r = mkp().px(); print(r)` is valid, as in the old
pipeline.

### 5.11 Blocks and tails [2.10]

```text
into({ s1; ...; sn; e }, dest)  =>  Block scope { Stmt{s1} ... Stmt{sn}; into(e, dest) }; <Dead of the block locals>
```

The value moves into `dest` before the block locals end. A reference in the value into
a block local is invalid after the end (`hold_out` and `use_held` of RT1/F1 go away).

### 5.12 `if`, `&&`, `||` [2.11]

```text
into(if c { a } else { b }, dest)  =>  tc := <c>; Switch(move tc) [true: bbA, false: bbB]
  bbA: into(a, dest); Goto(join)      bbB: into(b, dest); Goto(join)
a && b  =>  t := <a>; Switch(copy t) [false: done, true: bbB];  bbB: t = <b>; Goto(done)
```

The temporaries of the condition belong to the statement around the `if`. A condition
that is a place or a constant is the operand of the `Switch` itself (no code runs
between). `a && b` and `a || b` write `dest` itself and switch on `copy dest`. Each
branch has a `Stmt` scope of its own: its temporaries end before the join. With no
`else`, the value of the `then` block is dropped (its tail place moves, 5.4) and `dest`
gets `()`. The value of
each branch moves into `dest` (S059, V059). A branch of type `Never` ends in
`Unreachable` or in a jump. **Goes away:** `branch_state`, `set_branch`, `joined`,
`join_uniq` (the join of the analysis), `retire_stale`, `join_val`.

### 5.13 `match` and its patterns [2.12]

```text
into(match e { P1 => a1, P2 => a2 }, dest)
  =>  s := <place_or_temp e>
      td := Discriminant(s); Switch(move td) [v1: bbA1, v2: bbA2, otherwise: Unreachable]
  bbA1: Block scope { <bind P1 from s>; into(a1, dest) }; Goto(end)
```

This is the form for flat variant patterns. The general rule, which the interpreter
follows today (`Op::Match`: `pat_test`, then `pat_bind`; the first arm that matches
wins):

```text
test_i:  the tests of P_i, in pre-order, left to right:
           a variant at place q:          td := Discriminant(q); Switch(move td) [v: next, otherwise: test_i+1]
           an integer or bool literal:    Switch(copy q) [lit: next, otherwise: test_i+1]
           a unit literal:                no test (`()` has one value)
           a string literal:              tb := Eq(copy q, const "..."); Switch(move tb) [true: next, false: test_i+1]
                                          (a `String` is plain data; else tq := &q and Eq(move tq, ..))
           a tuple, a binding, `_`:       no test (a tuple tests its parts)
         then: Block scope { <bind P_i from s>; into(a_i, dest) }; Goto(end)
test_n+1: Unreachable                    (W0120 says that the arms cover each value)
```

- No binding and no move happens before all the tests of the arm pass. A test only
  reads (`Discriminant`, `copy` of a scalar, a borrow for a string). A `Variant`
  projection comes only after the test of its variant (V8).
- The temporaries of the tests (`td`, `tb`) end on each edge out of their tests: first
  in the block after the last test of the arm, and in a block of its own on each failed
  test, before the `Goto` to the tests of the next arm. They are in no scope. The
  bindings live in the `Block` scope of the arm; the value of the arm has a `Stmt`
  scope inside it.
- The arm takes the value if a binding moves a part of it, or if the scrutinee is a
  temporary. A `let` always takes it. `let (a, b) = e` puts the value in a temporary
  first; `let S(a, b) = s` takes the parts of the place `s`.
- A binding by value: `x = move (s as V).0`. A binding through a reference (the
  scrutinee is `(*r)`): `x = &((*r) as V).0`. A binding of a reference payload by value
  copies the reference, and α of a copy of a reference is the places that the stored
  reference points into (R3RT2).
- A pattern `_` over a linear part of a value that the arm takes: `t := move (s as V).k;
  Dead(t)`.
- An arm that matches a variant with no payload consumes a linear local scrutinee:
  `Consume(s)` (ADR 0007 `empty`).
- W0120 (exhaustiveness) stays in `typeck`. A variant pattern in a `let` is W0113 in
  `typeck`: a `let` pattern never fails.

### 5.14 Loops [2.13]

```text
while c { b }    =>  head: Stmt scope { tc := <c> }; Switch(move tc) [true: body, false: out]
                     out:  <Dead of the condition temporaries>; Goto(exit)
                     body: <Dead of the condition temporaries>
                           Block scope { b (tail in its own Stmt scope) }; Goto(head)
loop { b }       =>  head: Block scope { b }; Goto(head)
for p in e { b } =>  it := Iter(Elems(<place_or_temp e>))   (or Range(lo, hi))
                     head: Live(x); IterNext(it, x) -> [next: body, done: out]
                     out:  Dead(x); Goto(exit)
                     body: Block scope { <bind p from x>; b }; Dead(x); Goto(head)
                     exit: Dead(it)
break / continue =>  <exit scopes up to the loop>; Goto(exit / head)
```

- Each statement of a loop body, the tail too, is in a `Stmt` scope of its own. A tail
  value goes into a `Discarded` temporary (5.1.3). With no condition temporary, the
  `Switch` of a `while` goes to the exit itself.
- The condition of a `while` and the source of a `for` run before the `Loop` scope
  opens: a `break` in them goes to an outer loop, as in `typeck`. The temporaries of the
  source belong to the `for` statement, so they end after `Dead(it)`.
- `x` is a temporary (`Scrutinee`) of a `Stmt` scope of each iteration: `break` and
  `continue` end it, and the head can give it a new cell (V5). The bindings of `p` are in
  a `Block` scope inside it. A `for` pattern has no test.
- The place of `Elems` has the type `[T]`: `v[]` itself, or `v` with an `Elems` step for
  `for x in v`. `x` has the type `T` for a scalar `T` (an integer, `bool`, `()`,
  `String`, `Duration`), else `&T`. `it` has the type `Iter<type of x>` and the `@ uniq`
  mode of the local of the place.

- The loop is a cycle in the CFG. The analysis iterates to a fixpoint with widening at
  the loop head (section 6.6). **Goes away:** `lower_loop`, `LoopHead`,
  `FnFacts::rewind`, `Locals::restore`, `next_carry`, `retire_loop_stale`, the pass
  bound W0707. V025, V041 and RR1 came from the passes.
- An element of scalar type is a copy. Another element is a reference into the buffer.
  The iterator is `@ uniq` if its source is (RT18). `IterNext` reads the length at each
  step.
- As built (plan stage F10a, facts): `Iter(Elems(q))` is a borrow of `q` (`uses` of the
  variables of `q`, `reads_at` of its pointers); the value of the iterator points into
  α(`q`) and the handle places on the way, and is `@ uniq` if the value of the local of
  `q` is. `Iter(Range(a, b))` reads its operands and holds nothing. `IterNext(it, x)`
  uses the variables of `it`, reads its place and the places that it points into, and
  gives `x` the element as an `Assign` of a whole local: a reference into the places of
  the iterator (an element type that can hold a reference), else plain data. The `done`
  edge gets the same state; the block there ends `x`. The iterator does not point into
  the places that the elements point into (the old lowering added them): so a stale
  reference in an element is an error at the first read through the element, not at the
  `for` (`r3/redteam/p/i5_formatch.wf`, class `moved`).

### 5.15 `return` [2.14]

`return e => into(e, _0); <exit all scopes of the frame>; <end of parameters>; Return`
(origin: `e`). In a closure, `return` leaves the closure frame. W0315 for a handled
body, a clause or a scope body.

### 5.16 Operators and literals [2.15]

```text
a + b    =>  ta := <operand a>; tb := <operand b>; t := Add(move ta, move tb) as T
a == b   =>  ta := &<place a>; tb := &<place b>; t := Eq(move ta, move tb)   (not plain data)
-a, !a   =>  ta := <operand a>; t := Neg(move ta) as T
"{a}{b}" =>  ta := <operand a>; tb := <operand b>; t := Concat(...)
```

Choice A: `r.hp + { v.push(..); 1 }` copies `r.hp` before the push (safe), and a
comparison of two `Vec`s borrows each where it is written, so a push in a later operand
invalidates the borrow: W0301 (N1 of `docs/plan/core-ir-inputs/semantics.md`, probe p2). `-128` is one literal.

- `a - b`, `a * b`, `a / b`, `a % b` and the comparisons are the same as `+` and `==`.
  `/` and `%` by zero, and an overflow, are faults that stop the run (5.33).
- An interpolation `{e}` in a string is a read position, as `print` is: a place of
  another type than plain data is borrowed where it is written (`t := &p`), and `Concat`
  reads through the borrow. The interpreter compiles each part to `ToStr`. The value is
  not moved.
- `2.s` (an integer, a dot and a unit name) is a `Const::Duration`. The THIR `res` table
  gives the unit.
- `a..b` is valid only as the source of `for` (`IterSource::Range`). `typeck` reports
  W0114 for each other range.

### 5.17 Aggregates [2.16]

```text
(a, b)           =>  ta := <a>; tb := <b>; t := Tuple(move ta, move tb)
S { b: x, a: y } =>  tx := <x>; ty := <y>; t := Struct(S)(move ty, move tx)   (written order; field order in the aggregate)
S(x, y)          =>  in the order of the fields of S
Some(a)          =>  ta := <a>; t := Variant(Option, Some)(move ta)
[a, b]           =>  ta := <a>; tb := <b>; t := Vec(move ta, move tb)      (Array if the expected type is an array)
```

- A part that moves is a temporary that lives until the aggregate: a jump or an abort in
  a later part finishes it (its `Stmt` scope and the cleanup chain). **Goes away:**
  `hold_moved`, `hold_later`, `hold_part`, `take_held_here` (RT4, V015, V072, OL-3c, S072).
- A struct with a place field that the literal does not give: `Uninit(t.f)` after the
  aggregate, for each place field at each depth of the full type. The walk is keyed by
  the full type with a visited set, so a recursive or polymorphic type ends (Q3-1, V062,
  the R3a review item on `place_paths`). The aggregate has one operand for each field;
  the operand of a field that the literal does not give is `const ()`, and the `Uninit`
  after the aggregate tells that the field has no value.
- A call result is built in place too (ADR 0007): `Uninit(dest.q)` after the call, on
  its normal edge, for each place field path `q` of the result type. The result of a
  perform is the value of a `resume`, which a place of the clause held: no `Uninit`.
- A `!Move` part that the aggregate builds (a literal or a call result, not a place) is
  built in place: its temporary has `in_place: true`, as the old lowering, which reports
  W0604 only for an argument of a call.
- `[a, b]` is an `Array` aggregate if the THIR type of the literal is an array (the type
  of a field or a parameter gives it), else a `Vec` aggregate.
- A variant with no payload as a value (`None`, `Color.Red`) is a `Variant` aggregate
  with no operand. A variant or a function item as a function value is section 5.23.
- A struct literal that gives a place field a reference: `ref_at` with no `ref_in`.

### 5.18 Calls of function items [2.17]

```text
f(x, y)  =>  tx := <operand x>; ty := <operand y>;           (parameter order)
             Live(t); t = call f<T..>(move tx, move ty) caps Lexical(env) -> [next: bb, unwind: C]
```

- One terminator for each call form. A by-value argument moves where it is evaluated.
- The THIR `CallInfo::args` gives the argument of each parameter (ADR 0009): an index
  into the written arguments, or the trailing block. The builder evaluates the
  arguments in that order. A parameter with no argument is W0103 of `typeck`, so the
  body has no IR. `sim.run` can leave out `workers`: then the argument is the constant
  `4u64` (5.30).
- A place argument skips its temporary only if no later argument can run code (5.1.1),
  and only in a call with no receiver: the read of a receiver comes after the
  arguments (5.19).
- A `!Move` value built for a parameter of its own type (the declared type, not a type
  parameter), or for `Box.new` and `Rc.new`, has `in_place: true` (W0604 skips it).
- `unwind` is present if the callee can abort by its kind (V10): each callee but an
  extern function whose stated row is empty and that has no run-time meaning. The
  stated row of an extern function is its full row. An extern function that the
  runtime can make fail with an empty row (`raises`, as `FsCap.read`) gets no stated
  row, so its calls get an `unwind` block. The fact generator keeps the abort edge only
  when the summary says the call can abort.
- An extern function of the prelude gets its `FnDecl` at its first call in a body that
  the builder finishes (`Built::fns`). `sim.run` (the function `run` of the standard
  module `sim`) and `with_timeout` have their `Intrinsic`.
- The cleanup chain of a call is the chain of 5.1.6 (plan stage B8,
  `irbuild/cleanup.rs`). Chains share their suffixes: one block for each local and the
  block after it.
- **Goes away:** `item_arg_slots`, `eval_item_args`, the `arg_order` export (RR10),
  `hold_operand`, `hold_generic`, `release_generic`, `callee_drops`, `item_fn_args`,
  `arg_tasks`, the "call again" nodes (a `Many` run applies a second time at `Ret`).

### 5.19 Method calls [2.18]

```text
x.m(a)  (self by reference)  =>  ta := <a>; tr := &<place x>; t = call m(move tr, move ta)
x.m(a)  (self by value)      =>  ta := <a>; t = call m(move <place x>, move ta)
T.f(a), module.f(a)          =>  a function item call
E.op(a), op(a)               =>  a perform (5.26), from the THIR `res` of the name
f(a) { block }               =>  f(a, || { block })          (a trailing block is a closure with no parameters)
```

The receiver is a place first; the call reads it after the arguments (p7, p8). The
index value of a receiver place is fixed before the arguments, and the element is the
one at that index when the call reads the receiver, after the arguments: the `Bounds`
before the arguments gives no safety, the check of the index at the read does (the
engine checks it again, 8.1; `w.entities[0].plus(reorder(&w))` runs `plus` on the
element that `reorder` put at index 0). A variant step of a receiver place is tested
before the arguments too, and read after them. So an argument that gives the base of
the step a new value (an assignment, a move, a change through a reference or by a
call) is W0301: the read uses the `W` variable of the test (6.3). The engine checks
the tag again at the read (8.1).

The THIR `Recv::mode` gives the read: `Borrow` is `tr := &<place x>` (a `Receiver`
temporary), `Ref` copies the reference, `Value` copies plain data and moves another
value, `Deref` copies the value through the reference (`adjust` of the receiver has the
dereferences). A receiver that is not a place goes into a `Receiver` temporary first;
with `Borrow` and a value of plain data it goes into a promoted temporary (5.10).
`s.spawn(..)`, `t.join()`, `t.detach()` are `Spawn`, `Join`, `Detach` (5.29). **Goes
away:** `note_via_call`, `finish_via_calls` (QA6): `writes_via` at a call is one rule of
the template.

### 5.20 Generic calls and type parameters [2.19]

- The IR is generic: a value of type `T` is a local of a type parameter. Its props are
  "maybe linear, maybe not plain data" (`Props::generic`). The builder writes `Dead` and
  `UnwindValue` for it as for a value that is not plain data.
- The `drops` and `holds` parts of the summary are queries over the IR (section 6.7).
- The types are final when the builder runs, so a move of a value whose type was an
  inference variable is a move or a copy for sure (`tentative`, `settle_moves`, V060 go
  away).
- A generic function item as a value is `Const::Fn(f, tys)`. A value that code outside
  the body can run gets the summary check of `f` with those type arguments where it is
  made (RR9, V081).

### 5.21 Calls of function values [2.20]

```text
v(a)  =>  tv := copy v; ta := <a>; t = call (copy tv)(move ta) caps Lexical(env) -> [bb, C]
```

The callee is an operand, read before the arguments. As each place operand (5.1.1),
it skips its temporary (`TempKind::Callee`) if no argument can run code: then the call
reads `v` itself. The analysis gives the set of values the callee can be (section 6.6).
A `once` closure moves at the call: the callee operand is `move v` (W0502). The builder
knows this for a local that a closure literal goes into: the local gets the properties
of the closure (5.22), and a read of a local or of a capture whose properties are not
plain data is a `move`. For another value (a parameter, a field, a local that gets a
closure through a copy) the call copies the value, and the fact generator adds
`moved_at` of the callee from the analysis (6.4). A call of a function value always has
an `unwind` block (V10).

Named arguments of a function value bind by the parameter names of the function item
that the local holds (ADR 0009), so the THIR order of the arguments comes from the
value flow of the old lowering. A local that a loop gives another value can get a
second order in a later pass: the THIR then has a conflict for the call. `typeck`
reports W0104 for such a call, so the body gets no IR (a conflict alone gives
`NoIr::Conflict` too). Else the builder uses the THIR order, as for a call of a
function item.

### 5.22 Closures [2.21]

```text
|p| body  =>  te := Aggregate(Closure(c))(<one operand for each capture>)
              &x (ByRef), move x (ByMove), copy x (Kept: the cell), copy cap (Cap), copy/move kont (Kont)
body c (Closure):  params _1 = env, _2 = p; _0
  bb0: <body into _0>; <frame end>; Return
```

- The abstract value of the closure (section 6.6) holds its body and its environment:
  the cell roots of its `ByRef` captures, what its `ByMove` values hold, the capabilities
  of its `Cap` fields.
- The modes of the closure are the props of its fields: linear if a field is linear,
  `once` if a `ByMove` field is not plain data or a field is `once`, nonportable if a
  field is (RT8, OL-5, V061).
- One `ClosureDecl` and one body for each literal. A trailing block is a literal with
  no parameters (5.19). The ids of the closures and of their bodies follow the order of
  the literals in the function (pre-order), after the body of the function: a maker has
  a lower id than its closures. `_1` is the environment (`LocalKind::Env`, the type of
  the closure; no `Live`, no `Dead`, not in a cleanup chain); the parameters follow, with
  the `Uninit` of their place fields at the entry (5.2). The body writes its value into
  `_0`; a body whose closure type returns `()` but whose value has another type is an
  expression statement, then `_0 = ()`. The `Return` has the origin of the body (or of
  the literal, if the body gives no value).
- The type of a function value is plain data (`TyTable::not_copy`). A whole local that
  a closure literal goes into (a `let` local, an operand temporary, `_0`) gets the props
  of the closure joined into its own: linear, `on_abort`, nonportable, `holds_refs`,
  `once` (also for a field that is `@ uniq`), and `copy` only if the closure is not
  `once`. So the chains finish it (5.1.6), and a read of it moves it (5.21). The analysis
  joins the modes of the closures that a value can hold for each other place (2.3).
- Each other local of a binding whose type has a function part (`let g = f`, a
  parameter of a function, of a closure or of a clause, a pattern binding) gets the
  modes that the analysis infers for the values of the binding (`Binding::value` of the
  THIR, from the `VarInfo` flags of its variables): linear, no `on abort`, nonportable,
  `once`, and `copy` only if it is not `once` (plan stage B12). A function parameter
  holds a value that the body does not know, so the analysis gives it no closure modes.
  A field of a function type has the props of its type: the facts take the modes of the
  closures that it can hold from the analysis (2.3).
- **Goes away:** `{closure}` hidden variables, `note_capture`, `moved_captures`,
  `captures_live_at`, the `closure end` node, `late_join` and its functions (RR7, V103,
  V104, O3-11, F3-11), `union_ret`, the `by_value` export (OR2, V017).
- **Decision of stage F11 (the class closure-copy of stage I5).** A function value is
  plain data in the IR, and the run time shares a closure value: a copy does not clone
  the environment (I2). The old analysis moves a value that holds a function value when
  a body reads it (13 programs of tier 1, all rejected: `exports_parity.rs`
  `CLOSURE_COPY`). The old behaviour is right for a `once` closure and too strict for
  any other: two copies of a `once` closure share its `ByMove` cells, so a call through
  each copy runs the closure twice (the IR engine faults at the second call). So the
  facts give `moved_at` of the variable at each read of a value that the analysis says
  can be a `once` closure (a copy into another local, an argument, a part of an
  aggregate) and at each call of it; the IR keeps `copy`, and the capture modes stay
  those of rule CAPTURE. The `Kept` operand of a closure aggregate shares the cell and is
  no read of the value. A read of any other function value is a copy. Stage F11 knows
  the values of whole locals; stage F12 applies the rule to function values in fields,
  elements and captures (the 13 programs: a closure that reads `a[1]` out of a captured
  array moves the element when it can be `once`). The mode `once` of a local that comes
  from a `@ uniq` field is for a `multi` resume only (W0503): it does not make a call a
  move (B12-fn-once uses the `once` of the closures that the value can be, not the
  `once` of the local).

### 5.23 Function items as values, joins [2.22], stored values [2.23]

```text
f (an item as a value)   =>  t := Use(Const::Fn(f, tys))
a store into a field      =>  (*r).f = move tclosure
```

A function value is a value. It flows through locals, fields, elements and tuples as
other values do. A struct constructor or a variant with a payload is not a value in
Weft: `typeck` reports `Some`, `S` or `E.A` as a value (W0101, W0104), so the body gets
no IR (plan stage B12 checked this; no IR form is necessary). A variant with no payload
as a value is an aggregate with no operand (`None`). The analysis keeps the set of
closures and items that each place can hold, also in the abstract heap behind references (heap slots). **Goes away:**
`FnTy::summary`, `fn_joins` (RR2, V107), `join_val`, `escape`, `escape_all`, `keep`,
`store_into`, `apply_stored`, `insert_after`, `reach`, `known_at` (V027, V028, V089,
QA17). `sim.run` as a value emits `sim_run_at` at the `Assign` (RT17).

### 5.24 `handle`, clauses and the handled body [2.24]

```text
dest = handle E { op_i(params) { clause_i } } in body
  =>  dest = handle h -> [next, unwind: C]
body H (Handled h):  cap _1 = the new capability of E; upvar locals; _0
body K_i (Clause h, op_i):  params = the operation arguments; kont = resume; upvar locals; _0
```

- The `Handle` makes the capability, runs the handled body, and gives `dest` the value
  of the body or of a clause. Its `unwind` is for an abort that goes past the handler.
  The value comes from a frame, as a call result: `dest` gets the `Uninit` of its place
  fields after the `Handle` (5.17).
- The clauses run in the capability environment of the site, without the new
  capability.
- As built (`irbuild/handle.rs`, plan stage B10): the ids of the handler, the handled
  body and the clauses are reserved at the `handle`, in that order, so the site has a
  lower id than its bodies. The handled body has the `Cap` local `_1` (in `Body::caps`,
  not a parameter), then its upvar locals and its own locals; `_1` ends with the
  parameters, after the locals and the temporaries of the tail, and is last in each
  cleanup chain. A clause has its parameters, then the `Kont` local `resume` (its
  binding, or the type `resume(ret) -> T` of the operation), with `props.copy` for a
  `multi` operation; the continuation ends after the locals and before the parameters,
  and is first in each cleanup chain. The body of each one has a fence scope (5.1.5): a
  `return`, `break` or `continue` that leaves it is W0315. The value of the handled body
  is an expression into `_0` (as a closure body, 5.22); the value of a clause is its
  block into `_0` (as a function body, 5.2). Both have the parent and the site.
- **Goes away:** the inline lowering of the handled body (map 4.3), its own statement
  record (R2c), `body_frees`, `inner_frees`, `merge_summary`, `run_handler`,
  `run_clause_caps`, `end_clause_locals`, `join_clause_vals`, `clause_refs_onto_args`,
  `finish_aborts`, `finish_spared`, `op_refs`, `resume_refs_pending`,
  `check_cont_escape` and `check_cap_escape` (W0313 reads roots, section 6.9).
- The fact generator splices the handled body into the component of the site, with the
  phases `Exit`, `Post` and `Landing`, and each suspending node that aborts to the
  handler gets an `AbortValue` node (section 6.5). This is where M1, M3, J1 and J3 close.

### 5.25 A `multi` handled body [2.25]

No special lowering. The fact generator adds re-entry edges for each `multi`
suspension point (section 6.5). **Goes away:** `handled_again`, `again_node`,
`resumes_at_most_once` (a syntax count; the clause summary counts resume points on the
CFG). O3-14: the tail move `_0 = move u` of an upvar local `u` is on the cycle, so the
second run sees `moved`: W0302.

### 5.26 Perform [2.26]

```text
op(a, b)  =>  ta := <a>; tb := <b>;                         (parameter order)
              t = perform cap.op(move ta, move tb) -> [next, unwind: C]
```

`cap` comes from 5.1.8. **Goes away:** `perform_op`, `op_slots`, `eval_op_args`,
`perform_effect`, `note_abort_ctx`, `note_op_fn`, `give_held_to_op`, `op_arg_places`,
`op_fn_values`, `op_suspends`, `op_result`.

### 5.27 `resume` [2.27]

```text
resume(v)  =>  tv := <v>; t = resume(kont, move tv) -> [next, unwind: C]
```

In a clause body `kont` is the `Kont` local. In a closure inside the clause it is a
`Kont` field of the environment (the closure copies a `multi` continuation and moves a
`once` one; then the closure is `once`). In a handled body or a clause inside the clause
it is an upvar local of the `Kont` local. The argument is an operand: a constant or a
place with no later code is the operand itself, as for a perform (5.1.1). **Goes away:** `ContInfo::muts`,
`ContInfo::frees`, `resume_through_params`, `onto_param`, `finish_resume_runs`.

### 5.28 `on abort` [2.31]

An `on abort` function is a function item with a body. The cleanup chain names it
(`UnwindAction::OnAbort(f)`). The fact generator applies the summary of `f` at the
`UnwindValue` node, with `CapArgs::Root`. W0118 becomes a query over that summary
(section 6.9).

As built (plan stage F7): `apply` with `RunKind::OnAbort` gives `reads_at`,
`mutates_at` and `lends_mut` (not of `Caller..`) at the `UnwindValue` node, with σ of the
parameter onto the value at the place (a change through a reference in the value changes
the place that it points into, F3-1). With the root handlers, no effect leaves the code
that aborts (no `escapes_at`), no clause resumes it (no `multi_at`), and the node has no
`may_abort` and no argument checks. The analysis state does not change at the node: the
unwinder drops the result, and W0118 rejects a function that keeps a value outside its
parameter. The call graph links a body to the `on abort` function of each of its
`UnwindValue` statements, so its summary is ready first.

### 5.29 `scope`, `spawn`, `join`, `detach`, `fork` [2.28]

```text
dest = scope { s => body }  =>  dest = scope k -> [next, unwind: C]
body S (Scope k): params _1 = s (ScopeCap); upvar locals
  ... <body into _0>; ScopeWait(_1, orphans) -> [bb, unwind: C]; <frame end>; Return

h = s.spawn(f)    =>  tf := <f>; Live(h); spawn site_i(copy s, move tf) -> h, [next]
s.spawn(f);       =>  tf := <f>; spawn site_i(copy s, move tf) -> None, [next]
                      (a TaskResult local r of the scope body; ScopeWait gives it its value)
x = h.join()      =>  join(move h) -> x, [next, unwind: C]
h.detach()        =>  detach(move h) -> [next]
dest = fork(f, g) =>  tf := <f>; tg := <g>; dest = fork(move tf, move tg) -> [next, unwind: C]
```

The scope body waits for its tasks before its locals end (ADR 0006). `ScopeWait` can
abort (F3-7). A spawn in statement position gives the result to the scope (O3-4,
I3-1). Its `TaskResult` local is a once value of the scope body from the `Spawn` on: the
`Spawn` gives it `rebound_at` and `empty_at` (no linear value yet), and `ScopeWait`
gives it the result. So a `multi` node of the scope body between the spawn and
`ScopeWait` is W0503: a `multi` resume cannot copy a scope that has children (I3-8). A
task handle `h` is a once value too (`once_var`).

As built (`irbuild/task.rs`, plan stage B11):

- The ids of the scope and of the scope body are reserved at the `scope`, so the site
  has a lower id than its body. The scope body has the `ScopeCap` local `_1` (its only
  parameter), then the `TaskResult` locals, then its own locals and its upvar locals
  (made at the first use, as in a handled body, 5.24). It runs in the capability
  environment of the site. A fence scope stops each jump (W0315).
- The scopes of the scope body, from the outermost: the frame (`_1`, the temporaries of
  the tail), the fence, a block with the `TaskResult` locals, the block of the body. So
  the frame end is: the value into `_0`; `ScopeWait`; `Dead` of the block locals, of
  the `TaskResult` locals, of the tail temporaries, of `_1`; `Return` (5.1.4). A body
  whose end cannot run has no `ScopeWait`.
- A spawn is in statement position if `Builder::expr_stmt` lowers it: a statement of a
  block that is not its tail, the tail of a loop body, or the tail of the block of an
  `if` with no `else` (5.4, 5.12, 5.14). Before it lowers the block, the scope body
  finds each such spawn whose receiver names its own `s`, also in the closures and the
  bodies inside it. Each gets its `SpawnDecl` and a `TaskResult` local now, with `Live`
  at the entry (in source order). So each chain of the scope body has the local, and a
  spawn in a loop has one cell (each run of the spawn rebinds it). `ScopeWait` lists
  these locals as `orphans`. The props of a `TaskResult` local are those of the result
  type, with `once`.
- A spawn in statement position that the search does not find (a receiver that is not
  a scope binder, such as a parameter `s: Scope`; the tail of a closure or a clause
  whose value goes away; a `return` out of the fence) is a `Spawn` with no `dest` and
  no `TaskResult` local: the scope at run time keeps its result, and the facts do not
  see it. A spawn whose value is used (a `let`, a tail, `let _ = s.spawn(f)`) has its
  `dest`.
- `SpawnDecl::scope` is the scope of the receiver if the receiver names the scope
  binder `s` (also through a capture or an upvar of a nested body: the THIR binding
  names the `scope`); else `None`.
- `spawn`, `join` and `detach` are method calls: the receiver is a place first, then the
  arguments, then the read of the receiver (5.19). The spawn reads `s` as plain data
  (`copy s`). `join` and `detach` move the handle (a move through a reference is
  W0303, 5.36). `detach` writes `dest = ()` after it.
- The value of `scope`, `join` and `fork` comes from another frame, as a call result:
  the destination gets the `Uninit` of its place fields after the terminator (5.17).
- `fork` evaluates its branches as operands in written order (a trailing block is the
  last branch); each branch gets a `SpawnDecl` with `fork: true` and no scope.
- The origin of a `SpawnDecl` is the task argument of the spawn (the closure or the
  function value), or the branch of the `fork` (plan stage I4). The checker names a
  task by the span of this expression, and the interpreter finds the `stealable`
  mark of the task by it (8.1). **Goes away:** `start_task`, `task_captures`, `task_ret`, `end_tasks`,
`finish_task_values`, `finish_task_ends`, `finish_task_marks`, "task end" nodes,
`restart_after`.

### 5.30 `sim.run` [2.29]

`sim.run(seed, workers) { body } => t = call sim.run(seed, workers, move tclosure)`.
`workers = 4` when the call leaves it out is a constant argument (`4u64`). The THIR
`CallInfo` of `sim.run` gives the argument of each parameter, with no argument for a
`workers` that the call leaves out. The function has `Intrinsic::SimRun`, so the call
has an `unwind` block (V10). The fact generator
emits `sim_run_at`, the `handler` and `sim_root` facts of the root handlers of the
simulation, and applies the summary of the closure with those handlers as its
capabilities.

### 5.31 `with_timeout` [2.30]

A call. Its summary runs the closure exactly once; the call can abort and perform `fail`
through the capabilities at the call.

### 5.32 `Rc`, `Box`, `Weak` [2.32]

`Deref(Rc)` goes to the group root of the inner type, and α adds the handle place
(`h.*`) to the places of each reference made through it. `Deref(Box)` is an unstable
step below the owner. `Box.new` builds its argument in place. `Weak` has no `Deref`.

### 5.33 `print` and `assert` [2.33]

```text
print(a, b)  =>  ta := <operand a>; tb := <operand b>; Print(copy ta, copy tb); Dead of the temporaries
assert(c)    =>  tc := <c>; Assert(move tc) -> [next, unwind: C]
```

`print` reads its operands where they are written (N2). A value that is not plain data
is borrowed, not moved. A local or a capture that holds a `once` closure (its
`props.copy` is false, 5.22) is not plain data here either: a read of it would move it,
so `print(f)` and an interpolation `"{f}"` borrow it (plan stage B11; a tier-2 program
broke V9 before). So each operand of `Print` is plain data or a reference, and
`Print` copies it. A condition of `assert` that is a place or a constant is the
operand itself, as the condition of `if`. `assert` can abort the task: its cleanup
edge and `may_abort` come from the terminator, and the summary of a body with an
`Assert` can abort, so its callers get `may_abort` too (N4, probes p25 and p27). A
bounds check, an overflow and a division by zero are faults: they stop the run and
have no cleanup edge.

### 5.34 Effects at calls and handlers of a caller [2.34]

For each effect `E` of the callee row, the analysis resolves `E` through `CapArgs` to a
local handler capability (then `performs_at` with the footprint of its clauses), to
`Row(E)` (then `escapes_at`), or to a root handler. **Goes away:** `perform_at`,
`effect_lends`, `raise_here`, `callee_ops`, `may_run_again`.

### 5.35 Item values and checks of code a caller runs

A function item or a closure that a caller can run (a returned closure, a value stored
behind a parameter, an argument of an extern function) gets its summary checked where
it is made, with the type arguments of that point. This is the rule of `check_item_value`
of today, as one query (RT24a, RR9).

### 5.36 What the builder reports

W0315 (a jump out of a fence). Type errors, names, W0111, W0113, W0114, W0120, W0102 and
W0107 stay in `typeck` (2.4).

A body that moves a value that is not plain data through a reference (W0303) gets no IR,
as a body with a type error: `NoIr::MoveThroughRef`, "no IR: W0303". The old lowering
gives the W0303 diagnostic, and it stays the error of the program (2.4). The IR has no
form for the move: V9 rejects a `Move` through `Deref(Ref)` and a `Copy` of a value that
is not plain data. A move in a closure or a nested body of the function gives the whole
function no IR.

Other bodies with no IR (plan stage B12), each with its reason:

- `NoIr::VariantPayload`: a field expression `o.A` of a variant `A` with no field or
  with more than one field (5.8). `typeck` gives it the type `()` or a tuple, but the
  payload has no place of that type. No program of tiers 1 and 2 has one.
- An assignment whose left side is not a place is W0112 of `typeck` (a type error). A
  constructor as a value is W0101 or W0104 (5.23). The builder never sees these bodies.

W0604 stays the spec rule `moved_immovable(V, P)`: a `moved_at` of a variable with the
`immovable` flag. The fact generator gives the flag from the props of the type (6.3),
with two exceptions, as the old lowering does today: the variable of an `in_place`
local (a value built for a parameter of its own type, or for `Box.new` and `Rc.new`),
and a construction that `into` writes into its destination (5.1.1). A `!Move` value
that goes to a parameter of a type parameter is a move of its temporary, so it is W0604
(the callee can move it, as `Vec.push` does).

### 5.37 Example: probe M3

`SCRATCH/ir/work/machine/m8_abort_value_into_body.wf`:

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

The IR, as `example.rs` of the sketch builds and prints it (`verify_program` accepts
it):

```text
body main (Fn)                         body handled (Handled h0)
  _0: Return; _1: User `r`               _0: Return; _1: Cap(Pick); _2: User `w`
  bb0: Live(_1)                          _3: Temp(Receiver); _4: Temp(Discarded); _5: Temp(Operand)
       _1 = handle h0 -> [bb1, unwind: bb2]   bb0: Live(_2); _2 = call Vec.new() -> [bb1]
  bb1: Print(copy _1)                    bb1: Live(_3); _3 = &_2; Live(_4)
       _0 = const ()                          _4 = call push(move _3, const 3u64) -> [bb2]
       Dead(_1); Return                  bb2: Dead(_4); Dead(_3); Live(_5); _5 = &_2
  bb2 (cleanup): Dead(_1); Dead(_0)           _0 = perform Local(_1).pick(move _5) -> [bb3, unwind: bb4]
       Goto(bb3)                         bb3: Dead(_2); Dead(_5); Dead(_1); Return
  bb3 (cleanup): UnwindExit              bb4 (cleanup): Dead(_5); UnwindValue(_2, Drop); Dead(_2)
                                              Dead(_0); Dead(_1); Goto(bb5)
body clause (Clause h0, pick)            bb5 (cleanup): UnwindExit
  _0: Return; _1: Param `v`; _2: Kont `resume`; _3: Temp(Operand)
  bb0: Live(_3); _3 = const 0usize; Bounds((*_1), copy _3); _0 = &(*_1)[_3]
       Dead(_3); Dead(_2); Dead(_1); Return
  bb1 (cleanup): UnwindKont(_2); Dead(_2); Dead(_0); Dead(_1); Goto(bb2)
  bb2 (cleanup): UnwindExit
```

Section 6.10 gives the facts of the abort path, which reject `print(r)` with W0301.

---
## 6. Fact generation

The fact generator `factgen::emit` reads the IR, the states of the analysis (6.6) and the
summaries (6.7). It writes one `FnFacts` for each function and each test, with the schema
of `crates/weft-facts` as it is. It is a pure function: no fact depends on the order of
passes, and no node is added after the analysis.

### 6.1 Components and splices

One `FnFacts` holds the components of one function or test:

- the component of the function (or test) body;
- one component for each closure body and each clause body inside it.

A handled body and a scope body are spliced into the component of the body that runs
them: they run once for each run of their terminator (V15), so a summary would only lose
order. A closure and a clause can run at many nodes, so their effects reach each run
node through their summary. The components share the tables of roots, places and
variables of the `FnFacts`.

### 6.2 Nodes and phases

Each statement is one node. Each terminator is one node (phase `Main`), and some
terminators have more nodes in a fixed order. A node is a `NodeKey`:

```rust
pub struct NodeKey {
    pub body: BodyId,
    pub block: BlockId,
    pub at: u32,      // the statement index, or u32::MAX for the terminator
    pub phase: Phase, // Main, Ret, FrameEnd, AbortValue, Exit, Post, Landing, Copy
    pub dest: u32,    // the abort destination that this node serves (0: the normal path)
}
```

| Terminator | Nodes on the normal path | Nodes on the abort path to destination `d` |
| --- | --- | --- |
| `Call`, `Resume` | `Main` → `Ret` → `FrameEnd` → next | `Main` → [`AbortValue(d)` if `d` is a local handler whose clause gives a value] → `FrameEnd(d)` → the cleanup copy for `d` |
| `Perform` | `Main` → `Ret` → next | `Main` → [`AbortValue(d)`] → the cleanup copy for `d` |
| `Join`, `Fork` | `Main` → `Ret` → next | `Main` → [`AbortValue(d)` if `d` is a local `Fail` handler: a child failure, 6.5] → the cleanup copy for `d` |
| `Handle` | `Main` → (the spliced handled body) → `Exit` → `Post` → next | the end of an abort to this handler: `Landing` → next |
| `Scope` | `Main` → (the spliced scope body) → `Exit` → `FrameEnd` → next | through the chain of the scope body to the cleanup copy of the `Scope` |
| `ScopeWait` | `Main` → next | `Main` → [`AbortValue(d)` if `d` is a local `Fail` handler] → the cleanup copy for `d` |
| `Assert` | `Main` → next | `Main` → the cleanup copy past the function (a failed `assert` ends the task, `abort_task`) |
| other terminators | `Main` → successors | none |
| a cleanup block | one copy of each node for each destination (`NodeKey::dest`) | |

`Copy` nodes are on re-entry edges (6.5). The order of the phases is the order of the
machine: a value binds where it exists (`Ret`, `Exit`, `AbortValue`), before each free
that comes after it (`FrameEnd`, `Post`, `Landing`, the cleanup chain). So no node both
binds and invalidates one variable (`no_gen_kill`, A5).

`cfg_edge` links the nodes of a block in order, the last node of a block to the first
node of each successor, the phases in the order of the table, the `unwind` edges that
the fact generator keeps (6.5), the splice edges and the re-entry edges. A statement
node with no facts and one successor may merge with its successor; this changes no
derivation of the spec.

As built (plan stage F12, labels): diagnostics name a node by its label. Each node of a
`Call` or a `Perform` (each phase, also on an abort path) has the label of its callee, as
the old lowering: the name of the function item (`push`, not `Vec.push`), the local of a
function value (also through its callee temporary), or the operation (`note`). An
`Assign` of a whole variable `x` has the label `x =` (a W0301 note says `x : new value`).
Each other node has the name of its statement or terminator kind. The node has no detail
(a W0301 note shows `push : mut(v)`). The kind of the node and its phase (`call ret`) and
its IR location (`b1 bb3`) are the fields `kind` and `at` of `NodeInfo`, for tests and
tools; the old pipeline leaves them empty. Before, the label was the kind (`` `call`
performs `Note` ``) and the detail the location (`call : b1 bb0`).

### 6.3 Roots, α and variables

**Roots.**

| IR object | Root kind | Shown as | Owner variable |
| --- | --- | --- | --- |
| the value of a local of a body of the component (also a temporary, a by-value parameter); an upvar local maps to the root of its site local | `Local` | the name, or the temporary kind | `S(l)` |
| in a closure component: the environment (the closure value of the run node) | `Arg` | `env` | none; instantiated (6.5) |
| the cell of a local that a closure captures `ByRef` | `Local` | `x (cell)` | `C(x)`: only `Dead(x)` and the unwinding of `x` end it, not a move |
| the pointee of reference parameter `i` of the function | `Param` | `*p` | none |
| the pointees of the references inside parameter `i` (by value or behind a reference) | `Param` | `*p..` (wildcard) | none |
| the `rc` group of a type | `Group` | the type | none |
| in a closure or clause component: what an environment field or a reference parameter of the body points into | `Arg` | the capture or the parameter | none; instantiated (6.5) |
| the capability of a `handle` | `Local` | `capability of handle E` | `S` of the `Cap` local: it ends at the frame end of the handled body and on its cleanup chain |
| the continuation of a clause | `Local` | `resume` | `S` of the `Kont` local: it ends at the frame end of the clause |
| the scope capability | `Local` | `s` | `S` of the `ScopeCap` local |
| a place of a caller that the body cannot name | `Arg` | `a place of a caller` | none; `lends_mut` at each node that runs code of a caller |
| a local of the callee of call node `n` that the callee gives back (to a callback, an operation, its result) | `Local` | `a local of f` | `F(n)`: `rebound_at` at `n.Main`, `scope_end` at `n.FrameEnd` and at each `n.FrameEnd(d)` |
| a local of a clause of handler `h` that the clause gives back (to `resume`, as its value) | `Local` | `a local of the clause` | `K(h)`: `rebound_at` at the `Handle` `Main`, `scope_end` at its `Post` and `Landing` |
| in a clause component: a place of the handled body that the clause cannot name, given back by `resume` | `Local` | `a local of the handled body` | `R(n)` of each `Resume` node `n`: `scope_end` at `n.FrameEnd` |

The last four rows are the frames of the machine that a body cannot see. The caller
frame root closes N1 and N2 of `docs/plan/core-ir-inputs/map_lowering.md`: the result of code of a caller (a
perform through `Row`, a call of a function parameter or of an unknown value) points
into the argument places and into the caller frame root. The callee frame root closes M4
and F3-2. The clause frame root closes O3-3 and J6. The handled-body frame root closes
M2 shapes whose value points into a local of the handled body.

**α: from an IR place to fact places.** α walks the projections:

| Projection | Fact step |
| --- | --- |
| the base local `l` (owned), or an upvar local of `l` | the root of `l` |
| `Field(f)` | the field step (stable) |
| `Variant(v)` | the variant step (unstable) |
| `Index(_)`, `Elems` | the element step; its stability comes from the type (`elem_step`) |
| `Split(s, side)` | the split step of split `s` (one split for each call and parameter, QA17) |
| `Deref(Box)` | the deref step (unstable) |
| `Deref(Rc)` | the group root of the inner type; the handle place `h.*` joins the places of each reference made through it (ADR 0003) |
| `Deref(Ref)` of a move path `p` of the component | the places in the abstract value of `p` in the state at the node |
| `Deref(Ref)` of an interface place (a parameter, an environment field) | the interface root of that place, or its `Held` wildcard root for a second `Deref` |
| `Deref(Ref)` of `env.k` of a `ByRef` capture | the value root of the captured variable (its current value at the run node, after instantiation); the closure value itself points into the cell root |

So the stability of each step comes from the type of the projection (B2), and a place
through a reference names the reference (C8). `ptr(q)` is the list of pointer places on
the path of `q`: for each `Deref`, the place before it. An access of `q` reads them.

**Variables.**

| Variable | For | Facts |
| --- | --- | --- |
| `S(l)` of each local `l` | moves, linear values, ends, owners, unset locals, the references of the whole value | `rebound_at` at each whole assignment and at the entry of a parameter; `uses` at each operand at or below `l`; `moved_at`; `scope_end` at `Dead(l)`; `unwound_at` on cleanup paths; `overwrites`; `empty_at`; `unset_at`; `owner(root(l), S(l))`; `points_into` of the values of the parts of `l` that have no `H` variable |
| `H(l.q)` of each move path `l.q` that the body assigns on its own and whose type can hold a reference, a function value, a capability or a task | the references of a part (the part holders of today) | `rebound_at` at a new value of `l.q` or of `l`; `points_into` of the value; `uses` at each use of an overlapping place |
| `U(l.q)` of each place field path that can have no value | W0304 for place fields | `unset_at` where the value is built in place; `rebound_at` at a store into it; `uses` at each read at or below it |
| `C(x)` | the cell of a `ByRef` capture | see the roots |
| `F(n)`, `K(h)`, `R(n)` | frames that the body cannot see | see the roots |
| a heap slot variable | a function value or a capability stored behind a reference, in a `Box`, a `Vec` or an `rc` object | `points_into` of the places that its values hold; `uses` at each node that runs a value from the slot; a store is a weak update: no `rebound_at` |
| a drop pair | `Drop(p)` behind a pointer of a maybe-linear type | `rebound_at` at the `Drop` node, `scope_end` at the `Assign` after it (W0601) |
| `W(b, v)` of each base place `b` with a `Discriminant(b)` and each variant `v` that the body reads through `(b as v)` | the variant test of a place (as built F8d) | `rebound_at` and `points_into(α(b as v))` at each `Discriminant(b)`; `uses` at each access through the step `(b as v)` |
| `N(t, b, v)` of the target of an assignment `p = move t` or `t2 := Op(copy p, move t)` with a step `(b as v)` | the variant that the target names before the value (5.6, 5.7; as built F8d) | `rebound_at` and `points_into(α(b as v))` at `Live(t)`; `uses` at the write (or the read) of the target |

During the migration the move and linear facts use `S(l)` of the whole local, as the R3a
encoding does today: a move of a part `l.q` emits `moved_at(S(l), n)`, `moved_part(α(l.q),
n)`, and `rest_linear(S(l), n)` if another part of `l` can hold a linear value. So W0302
and W0601 keep their meaning; a variable for each move path for moves is an option after
the migration (section 11). Flags: `linear`, `has_on_abort`, `once_var`, `immovable` and
`nonportable` come from the props of the type of the move path, joined with the modes of
the closures that the analysis says it can hold (V061). `immovable` is off for an
`in_place` local and for a value that `into` builds in its destination (5.36).
`once_var` also holds for a task handle, a `TaskResult` local, a `ScopeCap` local and a
`once` continuation. `uniq(v)` holds only if each value of `v` is `@ uniq` (RT24b, V066).
Diagnostics show the name of the local, or the kind of a temporary with the span of its
origin.

**Variant steps (as built F8d).** A variant step `(b as v)` of a place is valid only for
the value of `b` that the test of the variant saw, in the same way as a reference into
`b.v`: the step is unstable, so a write of `b` or of a place above it, a move or the end
of `b`, and a change of `b` by a call (`mutates_at`, `lends_mut`) end it. The `W`
variable of the step points into `α(b as v)` from each test of `b`, and each access
through the step uses it (the operands, a borrow, a `Discriminant` of a place below it,
a write). So an access after such a change, with no new test, is W0301 with the text
``the variant test of `b` used after it was invalidated``. Only a receiver place (5.19)
has code between its test and its access; in a `match` the binds come right after the
tests, and a later bind of one pattern does not use `W` (an earlier bind can move a part
below the variant place, as with `S`). A write below the payload (`e.A.hp = 7`) does
not end the step. The target of an assignment runs after the value (5.6) but the source
names it first: its `N` variables bind at `Live(t)` of the temporary that the value
starts with, in the state before the value, and the write of the target uses them
(``the assigned place `e.A` used after it was invalidated``). No new relation: the
W0301 rules of the spec apply to these variables as to a reference. Before F8d the IR
pipeline accepted `e.A.plus({ e = Two.B(..); 0 })` (the old pipeline gives W0301 for its
early borrow of the receiver) and the IR engine read the payload of the other variant
(third review of F8, R1); both pipelines accepted the assignment form. Loops (group B,
F10) keep the rule: each test rebinds `W`.

**Parts with variables of their own.** When a move path `l.q` has an `H` variable, the
places of the value of `l.q` belong to `H(l.q)` only. `S(l)` holds the places of the
parts of `l` that have no `H` variable. A use of a place `p` uses `v(p)`: `S(l)` and the
`H` variables at, above or below `p`. So a new value of `t.1` replaces the places of
`t.1`, and a stale reference in the old `t.1` does not make `t` invalid (R3RT10, V069).

**Relations with no node.** These input relations of the spec hold for the whole
`FnFacts`. They come from the place interner and the declarations, not from a template:

| Relation | Source |
| --- | --- |
| `place`, `parent`, `unstable`, `wildcard` | the place interner of `weft-facts` (unchanged); α gives the steps and their stability from the type of each projection (B2) |
| `one_place` | a one-place instance of a call result (6.6) |
| `step_alias`, `step_within` | the interner, from the steps: two element steps, a split step and an element step, the two sides of one `SplitId` |
| `param_rooted` | each place below a `Param` or `Group` root |
| `owner(Rt, V)` | `owner(root(l), S(l))` for each local with storage (also a temporary and a by-value parameter); the frame roots `F(n)`, `K(h)`, `R(n)` and the cell roots `C(x)` own their roots; `Param`, `Arg` and `Group` roots have no owner |
| `linear`, `has_on_abort`, `once_var`, `immovable`, `nonportable`, `uniq` | the flags above |
| `shared_root(S)` | the root place of each reference parameter whose type states `@ shared` (`FnDecl` parameters) |
| `has_signature`, `declared_mut(D)`, `declared_effect(E)` | the stated row of the function (`FnDecl::stated_row`): α of each `mut` place in the `Param` roots, and each stated effect closed under implication, as `program.rs` does today |
| `task(T)`, `fork_task(T)` | one task for each `SpawnDecl`, each branch of a `Fork`, and each `runs` entry that a run node applies as a task; `fork_task` for a `Fork` branch and for a run as a thread |
| `library()`, `std_effect(E)`, `started()`, `no_runtime()` | the unit and the driver, as today: the file marker or `weft.toml`, the effects of the prelude, `main` or a test of the root, the no-runtime profile |

As built (plan stage F2, `crates/weft-sema/src/factgen/`): `rels.rs` holds `RELS` with
the parts of 6.7 (`rebound_at` in `rebinds`, `joined_at` in `tasks`); `nodes.rs` makes the
nodes of one body for a list of abort destinations (F2 knows one: past the function), with
`Main` of a `handle` or a `scope` linked to its `Exit` until the splices (F14, F18), and no
`Landing` or `Copy` node yet (F15, F16). In `alpha.rs` the payload of a variant with one
field is the variant step itself (as the old lowering), a slice names its elements
(`Index` or `Elems` of a slice adds no step), a split step has the stability of the
element step before it, a `Box` step has the text of the old lowering (none), and
`Deref(Ref)` gives an error until F3, an environment field until F11 (see "As built (F11)"
below). In `vars.rs` the `H`
variables are the parts (fields and variants only) that a statement or a terminator
writes and whose type can hold a reference, a function value, a capability or a task (a
type parameter can); `U` comes from each `Uninit` of a projected place; `C` from each
`ByRef` capture of a whole local (at the site local of an upvar); `has_on_abort` needs
`linear`; `uniq` is the property of the local until the analysis (F3).

As built (plan stage F8a, `factgen/holders.rs`): `points_into` has no node, so one `H`
variable for each part would collect the places of each value that the part gets, and a
reference in an old value would make a later use of the part invalid (76 `reassign_*`,
87 `branch_stale`). Each value of a part gets a *version* of the variable: the versions
of one part are keyed by the places of the new value (two writes with the same places
share one), and a weak definition (a store through a pointer, an element, a part with no
variable of its own) adds its places to each version that the part can hold there. A
version is *current* at a node if the state of the analysis before the node lets the part
hold one of its places. A use of the part uses the current versions; a write of the part
or of a part above it rebinds each version; at each node where a version is not current it
gets `rebound_at`, so an old value that a branch replaced does not carry its invalid state
to the join. The versions have the name of the part holders of the old lowering
(``value in `w.x` ``). Not closed: a place field reference into a boxed value moves with the
box and makes the destination point into the source local (154 `move_set`, and the
W0301 of the `n*_immov` probes): a relocation of place fields (ADR 0007), stage F20.

### 6.4 Templates

Each instruction has one template: the input relations of `spec/weft.dl` that it can emit
at its nodes. `factgen/templates.rs` has one function for each statement kind and each
terminator phase, and no other code emits node facts. The table is the output of the
test `print_table` of the sketch (`facts.rs`); the test `each_relation_has_a_source`
checks it against the input list that it reads from `spec/weft.dl` (74 relations with
`rest_linear`).

Statements (third column: what a cleanup path adds):

| Statement | Relations | On a cleanup path |
| --- | --- | --- |
| `Live` | cfg_edge, rebound_at, points_into (the `N` variables of an assignment target, 6.3) | |
| `Dead` | cfg_edge, scope_end | unwound_at (in place of scope_end) |
| `Assign` | cfg_edge, points_into, mutates_at, reads_at, rebound_at, uses, moved_at, scope_end (a drop pair), overwrites, empty_at, moved_part, rest_linear, writes_via, sim_run_at, ref_at, ref_in, unset_at (the place fields of a value built in place) | |
| `Drop` | cfg_edge, reads_at, rebound_at (a drop pair), uses | |
| `Consume` | cfg_edge, moved_at, moved_part, rest_linear (a part) | |
| `Uninit` | cfg_edge, unset_at | |
| `Bounds` | cfg_edge, reads_at, uses | |
| `Mention` | cfg_edge, uses, reads_at (its pointers and index locals, F9) | |
| `Print` | cfg_edge, reads_at, uses | |
| `UnwindValue` | cfg_edge, unwound_at, and the summary of `on abort` (mutates_at, reads_at, lends_mut, ...) | |
| `UnwindKont` | cfg_edge | |

Terminators:

| Terminator | Phase | Relations |
| --- | --- | --- |
| `Goto`, `Unreachable`, `UnwindExit` | Main | cfg_edge |
| `Switch` | Main | cfg_edge, reads_at, uses |
| `Return` | Main | cfg_edge, uses (of `_0`), ref_at, ref_in |
| `Call` | Main | the operands; the summary parts (points_into, mutates_at, reads_at, performs_at, uses, moved_at, moved_part, rest_linear, releases_at, may_abort, multi_at, spared_at, resumes_at, escapes_at, spawned_at, task_reads, task_writes, captures, mut_through, kept, spawns_in, opaque, call_mut, call_arg, lends_mut); handler, sim_root, sim_run_at (`sim.run`); arg_at, param_in, uniq_param, arg_aliased, fn_arg_effect, param_effect |
| `Call` | Ret | cfg_edge, points_into, rebound_at, moved_at (held arguments), empty_at; a second apply of a `Many` callback |
| `Call` | FrameEnd | cfg_edge, scope_end (the callee frame `F(n)`) |
| `Call`, `Join`, `Fork`, `ScopeWait` | AbortValue | cfg_edge, points_into, rebound_at, empty_at (the `dest` of the `Handle`) |
| `Call`, `Perform`, `Handle` | Copy | cfg_edge, rebound_at, empty_at |
| `Perform` | Main | as `Call` `Main` without the `sim.run` facts |
| `Perform` | Ret, AbortValue | cfg_edge, points_into, rebound_at, empty_at |
| `Resume` | Main | as `Call` `Main` (the continuation summary) |
| `Resume` | Ret, AbortValue | cfg_edge, points_into, rebound_at, empty_at |
| `Resume` | FrameEnd | cfg_edge, scope_end (`R(n)`) |
| `Handle` | Main | cfg_edge, points_into, rebound_at (the capability), handler, footprint, clause_multi, body_multi, clause_performs |
| `Handle` | Exit | cfg_edge, uses (`_0` of the handled body), rebound_at, points_into, empty_at (`dest`) |
| `Handle` | Post | the post parts of the clauses (as `Call` `Main`), scope_end (`K(h)`) |
| `Handle` | Landing | cfg_edge, scope_end (`K(h)`) |
| `Scope` | Main | cfg_edge, rebound_at, points_into (the scope capability), performs_at or escapes_at (`Async`), may_abort |
| `Scope` | Exit | cfg_edge, uses (`_0` of the scope body), rebound_at, points_into, empty_at |
| `Scope` | FrameEnd | cfg_edge |
| `ScopeWait` | Main | cfg_edge, uses, joined_at, lends_mut, may_abort, spared_at, performs_at, escapes_at, rebound_at (orphans) |
| `Spawn` | Main | the operands; spawned_at, task_reads, task_writes, captures, mut_through, kept, spawns_in, opaque, call_mut, call_arg, performs_at, escapes_at; rebound_at, points_into (the handle); for a spawn statement rebound_at, empty_at (its `TaskResult` local) |
| `Join` | Main | cfg_edge, uses, moved_at (the handle), joined_at, may_abort, spared_at, performs_at, escapes_at |
| `Join` | Ret | cfg_edge, rebound_at, points_into, empty_at, lends_mut |
| `Detach` | Main | cfg_edge, uses, moved_at; a drop pair for a linear result |
| `Fork` | Main | the operands; the task facts of each branch; may_abort, spared_at |
| `Fork` | Ret | cfg_edge, joined_at, lends_mut, rebound_at, points_into, empty_at |
| `Assert` | Main | cfg_edge, reads_at, uses, may_abort, spared_at |
| `IterNext` | Main | cfg_edge, reads_at (the elements and the length), uses, rebound_at, points_into, empty_at |

**The rules of the templates.** `n` is the node; `v(p)` are the variables of the move
paths that overlap `p` (`S` of the base, the `H` and `U` variables at, above or below
`p`); `refs(o)` are the places that the value of an operand holds (6.6).

*Operands.* Each operand `copy q` or `move q` at `n` emits: `uses(v, n)` for `v` in
`v(q)` and for the variables of each pointer local on `ptr(q)`; `reads_at(n, α(q))` and
`reads_at(n, a)` for each `a` in α of `ptr(q)` (a task that reads through a handle reads
the handle, O3-6); `reads_at(n, root(x))` if the base `x` is a source local (a use of a
variable reads it, OR8). A `move q` also emits `moved_at(S(l), n)` for the base `l`, and
for a part also `moved_part(α(q), n)` and `rest_linear(S(l), n)` (6.3). A `move` of an
upvar local moves the site local. A `copy` of the `Kept` field operand of a closure
aggregate emits `uses` and `reads_at` of the variable and no reference.

*Statements.*

- `Live(l)`: no fact but the edge, except for the temporary `t` that the value of an
  assignment starts with: `rebound_at(N, n)` and `points_into(N, α(b as v))` of each `N`
  variable of a variant step of the target (6.3).
- `Dead(l)`: on a normal path `scope_end(v, n)` for `S(l)`, for each `H` and `U`
  variable of `l`, and for `C(l)`. On a cleanup path `unwound_at` in place of
  `scope_end`. `Dead` of an upvar local or of the environment does not exist (V14).
- `Assign(p, rv)`: the operands of `rv`. `rv = Discriminant(q)` also gives
  `rebound_at(W, n)` and `points_into(W, α(q as v))` of each `W(q, v)` (6.3). The write
  of an assignment target, and the read `copy p` of a compound assignment, use the `N`
  variables of its value temporary. Then for the destination:
  - `p` is a whole local `l`: `rebound_at(S(l), n)` and `rebound_at` of each `H` and
    `U` variable of `l`; `points_into(S(l), A)` for `A` in `refs(rv)`; `empty_at(S(l), n)`
    if `rv` has no linear part; `mutates_at(n, root(l))` if `l` is a source local and the
    analysis says that `l` can hold a value before `n` (an overwrite writes the variable,
    W0405, and frees what the old value owns below an unstable step). The first value
    after `Live` or `Uninit` writes nothing: a `let` and a loop variable make a new
    variable (ADR 0006), so a task that keeps the old cell does not conflict with it.
  - `p` is a part of `l` (no `Deref`): `uses(S(l), n)`; `rebound_at(H(p), n)` and
    `points_into(H(p), A)`; `rebound_at(U(p), n)` for a place field; `mutates_at(n, α(p))`;
    `overwrites(S(l), n)` if the part can hold a live linear value.
  - `p` goes through `Deref` of `r`: `mutates_at(n, α(p))`; `uses` and `reads_at` of
    `ptr(p)`; `writes_via(n, S(r))` if the first `Deref` is of a whole local `r` of type
    `&X` with no reference in `X`, and each `mutates_at` of `n` is at or below a place of
    `r` (C6; as built F10a, the rule of the old lowering: the places can be more than one,
    or a wildcard place after a loop widens, because at run time `r` points to one place
    and the write changes it or a place below it); a
    store of a reference value into the held places of a local is a weak definition there
    (`points_into` with no `rebound_at`); a store into a `Param`, `Arg` or `Group` root
    goes into the `stores` part (6.7) and the W0204 store check (6.9); the `scope_end` of
    the drop pair of a `Drop` before it.
  - `rv = Ref(q)` into a place field of a `!Move` struct: `ref_at` and `ref_in` (W0605).
  - `rv` holds `Const::Fn(sim.run)`: `sim_run_at(n)` (RT17).
- `Drop(p)`: `uses` and `reads_at` of `ptr(p)`; `rebound_at` of a new drop-pair variable
  with the props of the old value (its `scope_end` is at the next node, the `Assign`).
- `Consume(p)`: `uses(S(l), n)` and `moved_at(S(l), n)`: the linear value is finished.
- `Uninit(p)`: `unset_at(U(p), n)`, or `unset_at(S(l), n)` for a whole local.
- `Bounds(q, i)`: `reads_at(n, α(q))` (the length and the buffer, OR5) and the operand.
- `Mention(q)`: `uses` of `v(q)` and of the pointer locals on `ptr(q)`; no read.
- `Print(ops)`: the operands; an operand that holds a reference reads through it
  (`reads_at` of its `refs`, and the `uses` of the owners of each place on the chain of
  references that holds a reference; as built F8c). A part of a `Concat` and an operand
  of a `Binary` read through their values in the same way.
- `UnwindValue(p, a)`: `unwound_at(v, n)` for `S(l)` and the variables below `p`. If `a`
  is `OnAbort(f)`: `apply` of the summary of `f` at `n` with its parameter mapped onto
  `α(p)` and `CapArgs::Root` (FD1, F3-1, F3-3, V119).
- `UnwindKont(k)`: the edge. The frames of the continuation unwind in the component
  where they live: the site component, through the cleanup copies of 6.5.

*Terminators.*

- `Switch`: its operand.
- `Return`: `uses(S(_0), n)` and of the `H` variables of `_0`. So a reference in `_0`
  into a local, a temporary or a by-value parameter that the frame end freed is
  `error(_0, Return)` (section 6.9: W0204 for a function or a closure); `ref_at(n, A)`
  for `A` in `refs(_0)` and `ref_in(n, D)` for each stated returned place, on a node
  with no edges.
- `Call`, `Perform`, `Resume` at `Main`: the operands; `call_arg(n, A, root)` for each
  place `A` that an argument reaches, also through stored references (R3RT3), with one
  root kind of `body/roots.rs` for each; `call_mut(n, M, root)` for each place `M` of the
  applied `muts` part, with the root of the parameter that the summary names (a change
  that comes from a run of function argument `i` gets the root of argument `i`, so a
  closure argument does not conflict with itself, O3-7); `arg_at`, `param_in`, `uniq_param`,
  `arg_aliased`, `fn_arg_effect`, `param_effect` from the signature of the callee (also
  of an operation, R3RT7); the summary of each body that the callee can be (6.7);
  `spared_at(V, n)` (6.5); `may_abort(n)` if `n` keeps an abort edge; `multi_at(n)` if the
  summary, the operation or a clause can resume more than once. For `Resume` also
  `uses(S(k), n)`, `moved_at(S(k), n)` for a `once` continuation (W0501) and
  `resumes_at(n, cap(h))`. For a `Call` of a `once` closure value, `moved_at` of the
  callee (W0502).
- `Ret`: `rebound_at(v(dest), n)`, `points_into(v(dest), σ(Σ.ret))`, `empty_at`;
  `moved_at` of each argument that the callee holds (the `holds` part); a second `apply`
  of a callback that the callee runs `Many` times (OR3, V043, V106).
- `FrameEnd`: `scope_end(F(n), n)` for a call, `scope_end(R(n), n)` for a `Resume`.
- `AbortValue(h)`: `rebound_at(v(dest_h), n)` and `points_into(v(dest_h), A)` for `A` in
  the value of each clause of the operation that can end with no resume point, with σ of
  the node (a clause parameter maps onto the argument places, a clause-local place onto
  the root of `K(h)`); `dest_h` is the `dest` of the `Handle` of `h`.
- `Handle` `Main`: `handler(H, E)`; `footprint(cap(h), M)` for each place that the
  clauses change outside themselves (both parts, mapped at the performs of `h`);
  `clause_multi(cap(h))` if a clause can pass two resume points; `body_multi(cap(h))` if
  a node of the handled body has `multi_at`; `clause_performs(H, E')` for each effect that
  a clause performs through a capability outside `h` (F6); `rebound_at(S(cap), n)` and
  `points_into(S(cap), capability root)`; `rebound_at(K(h), n)`.
- `Handle` `Exit`: `uses(S(_0 of H), n)`; `rebound_at(v(dest), n)`; `points_into(v(dest),
  A)` for `A` in the places of `_0` of the handled body and in the values of the clauses
  of `h` with `ResumeResult` mapped to the places of `_0` (J3; the soundness judge, H8);
  `empty_at` only if all of them are empty (V073).
- `Handle` `Post`: `apply` of the post part of each clause of `h` (6.7), with σ of the
  performs that ran it; then `scope_end(K(h), n)`.
- `Handle` `Landing`: `scope_end(K(h), n)`.
- `Scope` `Main`: `rebound_at` and `points_into` of the scope capability (RR4, V134);
  `performs_at` or `escapes_at` of `Async`; `may_abort`.
- `Scope` `Exit`: `uses` of `_0` of the scope body, and its value into `dest`.
- `ScopeWait`: `joined_at(T, n)` for each task of the scope; `lends_mut(n, M)` for each
  place `M` that such a task writes (the end of a task, ADR 0006), except the writes of an
  inner task that is still active (S130); `may_abort`; `rebound_at` of the orphan
  `TaskResult` locals.
- `Spawn`: `spawned_at(T, n)`; the task facts from the summary of the task body with its
  environment (`task_reads`, `task_writes`; `captures(T, v)` for each captured variable;
  `mut_through(T, v)` if the task writes through `v`; `kept(T, root(x))` for each `Kept`
  capture; `spawns_in(T, U)`; `opaque(T)` if the task runs a value that the analysis does
  not know or a callee with `pins`); the task also reads and writes the places of each
  later value of a `ByRef` capture (`finish_task_values` of today); `rebound_at` and
  `points_into` of the handle (its task set is `{T}`). A spawn statement (`dest: None`)
  gives its `TaskResult` local `rebound_at` and `empty_at` instead (I3-8, 5.29).
- `Join` `Main`: `moved_at` of the handle; `joined_at(T, n)` for each `T` of the must-set
  of the handle (6.6); `may_abort`. `Ret`: the result; `lends_mut` of the writes of the
  task.
- `Detach`: `moved_at` of the handle; a drop pair for a linear result (ADR 0007).
- `Fork`: `spawned_at` and the task facts of each branch; `may_abort`. `Ret`: `joined_at`
  of each branch, `lends_mut`, the result (a tuple, also of units, IP6).
- `Assert`: its operand; `may_abort(n)`; `spared_at`.
- `IterNext`: `uses` of the iterator; `reads_at` of the elements and of the length;
  `rebound_at` and `points_into` of the element.

`may_abort(n)` holds at each node whose abort edge the fact generator keeps: a perform
(each effect can abort, ADR 0005), a call or a resume whose summary can abort, `Join`,
`ScopeWait`, `Fork`, `Assert`, `Scope` (it performs `Async`).

As built (plan stage F4, `factgen/templates.rs`, `kernel.rs`, `decls.rs` and
`factgen::emit`):

- `emit` writes the facts of a body of group A with no `Call`, `Perform` or `Resume`, no
  loop and no `OnAbort` action. Another construct gives `Unsupported`, and the old pipeline
  checks the program. `factgen::preview` gives the facts of one body.
- With no group on (the default until stage F8; from F8 group A is on, from F10 the groups A and B, from F13 the groups A, B and C), no program is in scope, also a program
  whose bodies have no IR and so use no group. `weft check|facts|agree|lint|run|test`
  take `--groups=LETTERS` to turn groups on.
- A node `entry` before the entry block binds the parameters: `rebound_at`, `points_into`
  and `empty_at` of each parameter and of its `H` and `U` variables. The `Param` root of a
  reference parameter has the text of the parameter (as the old lowering), and the `Held`
  root has the text `*p`.
- A `move` of a value of a plain-data type is a copy: no `moved_at` (the builder writes
  `move` for a temporary of any type, for example `switch move _2`).
- `Consume` is not a use: the parts of the value moved before it. A part gives
  `moved_part` and `rest_linear`, as a `move` of a part.
- `rest_linear` holds if the type of another part can hold a linear value and the state
  says that the rest of the value can hold one (a part that moved before holds nothing).
- The binds of one pattern move the value once. A bind is an `Assign` of a part to a whole
  local with the origin of that local (the name in the pattern). A later bind of the same
  pattern does not use `S(l)` (the old lowering moves the whole value at a destructure).
  Two `let` statements stay a use after a move (W0302 keeps its meaning).
- A value built in place: an `in_place` local, or a temporary that gets an aggregate
  (`into` writes it into its destination, 5.36). Its `immovable` flag is off. A move of
  it into a move path does not read its place fields: each `U` variable of the
  destination at its place fields gets `unset_at` if the place field can have no value
  (its `rebound_at` goes away). A move of a `!Move` value (W0604) and a move into `_0` do
  not read the place fields either.
- A reference in a place field points into the place that the struct states for the
  field: α of `(*(*f).cur)` is `f.buf[]`.
- W0605 (`ref_at`, `ref_in` of a place field, and `ref_at` of a struct literal) and the
  stated returned places of `Return` use a node with no edges (label `field` or `return`)
  and a `RefSite`, as the old lowering. A returned reference into a local, a temporary or
  a by-value parameter has no `ref_at`: `error(_0, Return)` gives W0301 for it until
  `diagnose.rs` maps it to W0204 (6.9).
- `sim_run_at` holds at a node with an operand `Const::Fn` of `sim.run`.
- `uniq(S(l))` is the meet of the `@ uniq` modes of the values that `l` gets.
- The state of 6.6 also has holes: the move paths that a move or an `Uninit` leaves with
  no value below a path that must hold a value. A move of a whole local gives its holes to
  the destination.

As built (plan stage F5, `factgen/templates.rs` `call`, `crate::analysis::apply`):

- A `Call` of a function item whose summary comes from a signature (6.7: an extern
  function of the prelude or of the program, or a function with a stated row) has the
  nodes `Main`, `Ret` and `FrameEnd`, and `FrameEnd` on the path of an abort. A call of a
  function with no stated row (stage F6), of a function value, of `sim.run` or
  `with_timeout`, a `perform` and a `resume` stay `Unsupported`.
- `Main`: the operands, then the summary: `reads_at` of the places of each argument;
  `call_arg` of each place that an argument reaches, also the places behind a reference
  argument (R3RT3); `mutates_at` and `call_mut` of the part `muts`; `lends_mut` and
  `call_mut` of the places of each argument if an operation of an effect of the row takes
  a reference; `escapes_at` of each effect of the row (group A has no local handler);
  `may_abort` if the summary can abort (an effect of the row, or `raises`); `multi_at`;
  `param_in`, `arg_at` and the argument sites of a stated `in` place; `uniq_param` and
  `arg_aliased`. `writes_via(n, S(r))` at a method call whose callee changes only places
  below `self` (`only_self`), if the receiver reaches through a local `r` of type `&X`
  with no reference in `X` and each change of the node is at or below a place of `r`.
- The callee frame root `F(n)` (a `Local` root, the text `a local of f`) binds at `Main`
  if the part `ret` names the frame; it ends at `FrameEnd`, on each path. A linear type
  argument of a type parameter in `drops` gets a variable of kind `Dropped` that binds at
  `Main` and ends at `Ret` (W0601), and that the abort path unwinds.
- `Ret`: the result binds to `dest` as the destination of an `Assign`. An argument whose
  parameter names a type parameter in `holds` moves here, not at `Main`: a linear value
  is live at the abort edge of `Main` (W0602). The values that go behind a reference
  argument that the call changes (part `stores`) are a weak definition of the variable of
  the place (no `rebound_at`); a place that a caller keeps gets the W0204 store check.
- An access uses the variables of the move path of each pointer place on its path (the
  pointer locals of the rule above). A read or a borrow through a pointer of a place
  whose type can hold a reference uses the variables of the move paths of its places
  (R3RT2): a copy of a reference out of `o` through `p` uses `o`.
- A temporary that gets the result of a call is built in place (5.17): a move of it
  gives its place fields to the destination. A value built in place that a call takes as
  a whole argument keeps `immovable`, unless the builder builds it in place for the
  callee (`in_place`, `Box.new`): `v.push(Frame { .. })` is W0604, as in the old lowering.
- A place field of a boxed value is a path through `Deref(Box)` (5.8): a `U` variable
  overlaps an access by the path that the local owns, with the dereferences of a `Box`.
  A store into such a path gives the `U` variables at or below it a value.
- The W0204 store check (6.9): a reference whose root is a local, a temporary or a
  by-value parameter, that an `Assign` through a reference or the part `stores` of a call
  puts behind a reference parameter or into an `rc` object, is W0204 at the span of the
  node, with the text of the old lowering. The fact generator gives these diagnostics
  (`Input::diags`).

### 6.5 Frames in the facts

**The splice of a once-run frame.** For a `Handle` of handler `h` at node `n` in body
`B`, with handled body `H`, and a suspending node `P` inside `H` (or inside a frame that
`H` splices):

```text
n.Main ──► entry of H
Return of H ──► n.Exit ──► n.Post ──► first node of next                    (normal end)
P.Main ──► P.AbortValue(h) ──► [P.FrameEnd(h)] ──► cleanup copies from P up to H for h ──► n.Landing ──► next
P.Main ──► [P.FrameEnd(d)] ──► cleanup copies from P up to H for d ──► the cleanup copy of n's unwind block for d   (d past h)
```

- At `n.Exit`, `dest` binds: the value of the body exists, and `_0` of `H` is used, so a
  reference in it into a local or a temporary of `H` is W0301 (O3-2).
- At `n.Post` the clauses run their code after their first resume point (6.7). A change
  there invalidates a reference in the value (M1) and a reference that the body kept in
  a site local (J1). Then the clause frames end (`K(h)`).
- At `P.AbortValue(h)`, `dest` binds to the value of the clause, with σ of `P`, before
  the unwinding. One such node exists for each suspending node and each local handler
  that it can abort to, because the cleanup chain that follows depends on `P`. The
  cleanup chain of `H` then frees the locals of `H`, so a reference in the clause value
  into a local of `H` is invalid after the landing (M3). This is the order of the
  machine: the clause returns, `drop_now` unwinds the continuation, then `deliver` gives
  the value to the frame below (`machine/effects.rs:132`).
- `P.FrameEnd(d)` ends the callee frame `F(P)` of a call on its abort path (M4).
- A `Scope` is the same with no `AbortValue`, no `Post` and no `Landing`: no clause stops
  an abort there. `ScopeWait` and the scope body locals end before `Exit`. On an abort
  path the chain of the scope body cancels and joins its tasks (`UnwindValue` of the
  `ScopeCap` local: `joined_at` of each task of the scope, V084).

**Abort destinations.** Each node `P` with `can_abort()` has a set of destinations:

- a perform through the capability of a local handler `h` aborts to `h` if a clause of
  the operation can end with no resume point, and past `h` to each destination of the
  clause summary (`aborts` part);
- a perform through `Row(E)` aborts past the function;
- a call or a resume aborts to each local handler `h` that its summary performs through
  (after the resolution of `CapArgs`) whose clause can end with no resume point, and
  past the function if its summary performs through `Row`, can fail, can be cancelled, or
  has an `assert`;
- `Join`, `ScopeWait`, `Fork`, `Scope` and `Assert` abort past the function when the task
  is cancelled: a cancel ends the task, and no handler stops it.
- A child failure at `Join`, `Fork` or `ScopeWait` is `Fail.fail`, raised through a
  capability environment: the environment at the node for `Join` and `Fork`, the
  environment of the `Scope` site for `ScopeWait` (the interpreter raises it with the
  `henv` of the scope record, `scope_fail_unwind`). So its destination is the local `Fail`
  handler of that environment, with its `AbortValue` (a clause of `fail` cannot resume,
  W0504), or past the function through `Row(Fail)`. A failure in the body of
  `with_timeout` and a timeout resolve `Fail` the same way at the call (5.31). The old
  lowering has this rule in `raise_here`.

The fact generator makes one copy of the cleanup chain of each frame between `P` and a
destination for that destination (`NodeKey::dest`). An abort to `h` never reaches the
cleanup of the frames outside the handled body of `h`. Then:

- `unwound_at(V, Q)` holds exactly on the cleanup nodes of the frames that the abort
  leaves;
- `spared_at(V, P)` holds for each variable `V` live at `P` that no cleanup chain of a
  destination of `P` finishes. This is the meaning that ADR 0005 states, as a fact of
  the CFG (OR4, OL-R2c-1, V116, V074, V084, V086, V088, V089).

An abort edge that the summary says cannot occur is not emitted. The IR keeps the block
(the builder writes every edge that a kind of terminator can have).

As built (plan stage F7, `crates/weft-sema/src/factgen/frames.rs`, `nodes.rs`):

- `frames::destinations` gives the destinations of each terminator: `Dest::Past` or
  `Dest::Handler { handler, value }` (node destination id `2 + handler`). A `Call` of a
  function item takes them from the `aborts` part of the summary of the callee: an effect
  through `Row` resolves in the capability environment of `CapArgs::Lexical` (the first
  environment of the chain that adds the effect; a handled body that opens it names its
  handler), `raises` resolves `Fail` there, `assert` goes past; `CapArgs::Root` goes past.
  A call of an intrinsic, of a function value or of a function with no summary goes past
  and to the `Fail` handler. `Join` and `Fork` go past (a cancel) and to the `Fail`
  handler of the environment of the body (a child failure); `ScopeWait` the same with the
  environment of the `Scope` site. A `perform` through a local capability goes to the
  handler of its effect in the environment of the body. `Assert`, `Scope`, `Handle`,
  `Resume` and a `perform` through `Row` go past.
- A capability of a closure environment counts as one of a caller (past the function)
  until stage F11. A `perform` through a local handler counts as an abort with a value
  until stage F15 finds the clauses that can end with no resume point.
- A terminator with no destination has no abort edge: a call of a function whose
  summary cannot abort keeps its cleanup block in the IR, but the facts have no path to
  it. `may_abort(n)` holds exactly when the node has a destination.
- The node table copies each cleanup block once for each destination whose abort reaches
  it, and makes the abort phases of each terminator for each of its destinations
  (`AbortValue` for a destination with a value, then `FrameEnd(d)` for a call). The
  templates run on each copy with the state of the block.
- The summary part `aborts` has `Abort::Assert` for a body with an `assert` or a call of
  a callee with one (`sig::Inferred::assert`; the `EffectSig` of today has no part for
  it, so `weft-gate sigdiff` does not see it).
- Not yet: the splices to the site (F14, F18), `Landing` and the template of
  `AbortValue` (F15), and `spared_at` (F15). With only `Past` in group A, no variable is
  spared, so `spared_at` is empty, which is sound (it only removes errors).

**Re-entry edges (`multi`).** Let `P` be a node with `multi_at(P)`. Its continuation
holds the frames from `P` up to its destination. For each such `P` the fact generator
adds:

```text
end of the copied region ──► P.Copy ──► P.Ret
```

The end of the copied region is `n.Post` of the `Handle` of a local handler `h` (after the
clause code between two resume points), or the `Return` of the function for a capability
of a caller (OL-R2a). `P.Copy` emits `rebound_at` and `empty_at` for each variable whose
places are all in the roots of the copied frames: the copy of the machine
(`copy_frames`). A variable that points outside keeps its state, so a reference that the
first run invalidates is invalid in the second run (ADR 0005; J4 stays rejected). A tail
move of an upvar local is on the cycle (O3-14). One-place instances are off on each node
of a cycle, re-entry edges included (V097).

**The entry of a component, and instantiation.** A closure or a clause component starts
at the entry of its body. Its parameters, its environment and its continuation bind
there (`rebound_at`). A linear capture by move is a field of the environment, so a new
value of it inside the closure is `overwritten` (S002). The interface roots of the
component (`Arg` roots of its environment fields and reference parameters) are made
concrete when its facts are emitted: each `Arg` root stands for the union of its actual
places over all run nodes of the body, and for `a place of a caller` if the body can run
where the analysis cannot see (a returned or stored closure, an unknown callee). So the
spec sees the real aliasing between two captures or two parameters inside the closure.
The summary (6.7) stays in interface terms.

As built (plan stage F11, `factgen/mod.rs` `emit_parts`, `closure_summary`,
`emit_closure`; group C was a preview with `--groups ABC` until stage F13 puts it in
the default set):

- A closure body is a component of the `FnFacts` of its function: a node `closure entry`
  (its parameters and the `E` variables of its `ByMove` captures bind there, `rebound_at`,
  `empty_at`, `points_into`), then the nodes of its blocks, with its own abort
  destinations. No edge joins it to the function: its effects reach each run node through
  its summary.
- The fact generator makes each component twice. First the summary of each closure (an
  inner closure first: a maker has a lower id), from facts of the body alone in a scratch
  table, in the terms of its interface: a `Kept` capture `env.k` is the `Arg` root
  `Capture(k)`, a `ByRef` capture `env.k` points into it, a `ByMove` capture is a part of
  the environment root `env`, and the references in the value of a capture point into
  `CaptureHeld(k)` (one level) and `CaptureDeep(k)` (each deeper level, a wildcard), as
  `Param(i)` and `Held(i)` do for a parameter. The parameters after the environment have
  `Param` roots. Then the function body, with the closure summaries at its calls. Then
  each closure body, *instantiated*, into the tables of the function: a `Kept` capture is
  the place of the variable of the maker (α of the source of the capture, through the
  makers), a `ByRef` capture points into the value root of its variable, and the analysis
  starts from the join of the states of the maker before each terminator and before each
  closure literal (the values that the maker has where the closure can run: at a call of
  it, or after the return of a closure that leaves). So a change of one capture and a
  reference into another capture of the same variable are visible in the body (the alias
  test), and the variables of the maker (`S(x)`) carry the uses. No edge reaches the
  component from `n0`, so the `bound_before_use` lint of the proof link does not read it.
- The parameters of an instantiated closure keep their `Param` roots: the call checks its
  arguments against the places that the closure changes (`call_mut` with the root
  `STORED` for a capture, W0312), as for an item.
- A whole new value of a `Kept` capture in an instantiated body is a new value of the
  variable of the maker (a strong update, `rebound_at` of `S(x)`): `|| { r = grow(w) }`
  does not use the old `r`.
- The `E(c, k)` variable of a `ByMove` capture `k` (`vars.rs`) has the flags of the type
  of the capture (also `immovable`: a move of a `!Move` capture in the body is W0604); a move of the capture moves it (`moved_at`, `moved_part` and
  `rest_linear` for a part), so the captures are apart. The environment local has no `S`
  variable.
- The summary of the function body reads only the nodes of the function component (the
  closure components come after them, `Emitted::entry_nodes`), and the aborts (a failure,
  an `assert`) of the closure summaries that it applies at its calls.
- A view of an environment in a nested body (`u.k`, 5.1.7) and a capture of a capability
  or a continuation are groups D and E: `Later`.
- The `E` variables of a closure body end at its `Return` (`scope_end`: a linear
  capture that a path does not consume is W0601 there, F11-L1) and at its
  `UnwindExit` (`unwound_at`: the unwinder finishes the owned cells).
- The parameters of a closure body have `Arg` roots (not `Param`): W0703 checks the
  places of the function, and a change through a parameter of a closure is a change of
  a place of its caller, checked at the call (F11-P1).
- The borrow `t := &x` of a `ByRef` capture reads no place field of `x`: the call
  uses the `U` variable of each place field that the closure reads (part `reads`),
  because the closure component does not see where the maker gives the field a value
  (F11-U1).
- A capture that the closure rebinds (part `rebinds`) gets its new value at the `Ret`
  node of the call: the change of the capture at `Main` is no `overwrites` of it.
  The changes and lends that the body makes after a rebind, on some path (part
  `late_muts`, the nodes after the rebind nodes of the component), are at `Ret`
  too, for each place that overlaps a place of a new value: `|| { r = &v[0];
  v.push(3) }` makes `r` invalid after the call (hole H1 of the review of the ABC
  preview, F12-fix). A change before the rebind stays at `Main` only.
- A function with a function value in its signature and no stated row has no summary
  until stage F12 (`callgraph::summary_of`). W0701 takes the row of the old inference
  for it (`Inference::old_rows`), which adds the effects of the closures that the
  function makes. A function that returns a closure inside a struct has a summary with
  no row for the closure: its W0701 waits for F12.

### 6.6 The analysis

The analysis gives the abstract values that the templates read. It replaces the abstract
values that `Lower` computes during its walk (`Val`, `LVal`, `Local`), the loop passes
and the post-passes.

**Domain.** At each point of a component, the state maps:

| Key | Abstract value |
| --- | --- |
| each move path (`S`, `H` variables) | `AbsVal { refs, fns, caps, tasks, linear, empty, uniq }`: the places that the value can point into; the closures (with the abstract value of their environment), items with type arguments, function parameters and unknown values that it can be; the capabilities and continuations that it holds; the task sites that it can be a handle of; whether it can hold a linear value; whether it holds nothing linear (`None`); whether it is `@ uniq` |
| each heap slot | the same, for values stored behind a reference, in a `Box`, in a `Vec` or in an `rc` object; the slot is the fact place of the storage, cut at a fixed depth |
| each move path (may and must) | can hold a value, must hold a value (for an overwrite at `Assign`, for `drops`, `holds`, and W0304 notes) |
| each task | the move paths that can hold its handle (may) and the paths that must (must, for `joined_at`) |

**Transfer.** One function for each statement kind and each terminator kind. `Ref(q)`
gives `refs = α(q)` and the handle places of each `Deref(Rc)` on `q`. `Use(copy q)` gives
the value at `q`. An aggregate gives the union of its operands with the structure of the
move paths. A closure aggregate gives `fns = {Closure(c, env)}` and the cell roots of its
`ByRef` fields, the values of its `ByMove` fields, and the root of the variable of each
`Kept` field (the cell that the closure shares with its maker). A terminator that runs another body
applies its summary (6.7). The result of a perform through a local handler is the union
of the `resume` arguments of its clauses. The result of a `resume` is the value of `_0` of
the handled body (M2).

**Joins and widening.** A join is a union of the may parts and an intersection of the
must parts. At a loop head (the target of a back edge or of a re-entry edge) the analysis
widens with the rules of `loops.rs` today (RR1, QA4, QA7, S101, S102), applied to a
state: a place that goes deeper than the places at the head by more than 8 steps becomes
the wildcard place of the outermost new place; more than 16 places in one root become the
wildcard place of their common prefix (64 for a value outside a loop); a function set that
still changes after `locals + 16` visits becomes `Unknown`. The lattice has a finite
height after widening, so the fixpoint exists, and W0707 goes away.

**One-place instances.** A call result gets a one-place instance (`wild_one`) only if
the call node is in no cycle of the fact CFG (back edges and re-entry edges included), is
in the function component, and the result type is `&T` or `Option<&T>` with `T` holding
no reference (ADR 0003). A second result in one base widens to the shared wildcard place,
as `two_results` does today.

**Interprocedural order.** The analysis of a body reads the summaries of the bodies that
it runs. A graph links each body to each body whose summary it reads: a callee item, a
closure body, a clause, the continuation of a handled body, a task body, an `on abort`
function. Each strongly connected component runs to a fixpoint, callees first. A handled
body and its clauses are always in one component: the result of a perform comes from the
resume values of the clauses, and the result of a `resume` comes from `_0` of the handled
body. Each summary starts empty and only grows; a must part (`rebinds`, the joins of the
`tasks` part) starts empty too and holds only what each path guarantees with the parts
known so far, so it also only grows, and each step is sound; summary places are cut at 8 steps
(`SIG_PLACE_STEPS`). So the iteration is monotone and ends. The emit pass runs after all
summaries are final.

As built (plan stage F3, `crates/weft-sema/src/analysis/`): the state maps the key of each
local (the site local for an upvar) to a tree of its move paths (`Tree`: the `top` of a node
is the part of the value that no child names), and holds the move paths that can and must
hold a value. A local with no entry has no value: `AbsVal::none` (no places, `empty`,
`uniq`) is the identity of the join. A read of a place that is not a move path (through a
pointer, an element) gives the places that the references at α of the place point into,
and a linear part from its type. A reference stored in a place of the pointee of a
parameter points into the wildcard place of the `Held` root `*p` of that parameter (the
`Param` root of a reference parameter has the text of the parameter, as the old lowering).
A store through a pointer or into an element is a weak update of the move path that names
the place (or a move path above it), with no structure. `Live`, `Dead`, `Consume`,
`Uninit` and a `move` operand leave no value. A cleanup block gets the state before the
terminator that aborts. `uniq` holds for a copy of a `@ uniq` value only: a constant, a
borrow and an aggregate are not `@ uniq`. (Until stage F10 there was no widening: a block
that the driver visited more than 64 times was an error, and the fact generator refused a
back edge.)

As built (plan stage F8, cost): the maps of a state (values and the move-path sets) go
in chunks of 64 locals that the states share (`domain::Chunked`): a clone copies no
value, and a change copies one chunk. The driver keeps the state of each *join block*
only (the entry, a block with no edge in or more than one; each block of a body with a
back edge); the fact generator computes the state of another block from its one
predecessor, in reverse post-order (`analysis::edges`). Before this, a long chain of
calls, or a cleanup chain of a call after many `let`s (one block for each live local),
kept blocks times locals trees: tier 2 ran out of memory (9 GB for
`r2/quality/gen/si_4000.wf`, 12 GB for `verify/le_15000.wf`).

As built (plan stage F10a, `crates/weft-sema/src/analysis/widen.rs`; group B was a
preview in F10a, and stage F10b puts it in the default set): a *loop head* is the target of a back edge (an edge to a
block whose rank in reverse post-order is not higher, normal or `unwind`). The driver keeps
the first state at each head (the state before the loop). At each later join into a head
that changes the state, the joined state widens, with the rules of the loop passes of the
old lowering (`widen_deeper`, `widen_place`, `collapse_places`), for the places of each
local:

1. A place below a shared wildcard place `b..` becomes `b..`.
2. A new place below a place that an earlier visit added (a place of the local at the head
   before the join that the state before the loop did not have) becomes the wildcard place
   of the outermost such place. So a walk (`cur = &cur.next[0]`, also ten steps at a time)
   stops after two visits: this is the rule "deeper than the places at the head" with the
   depth of one visit, as the old lowering did it before its pass 8.
3. More than 16 places of one root in one value become the wildcard place of their common
   prefix.
4. After `locals + 16` visits of the head, a new place becomes the wildcard place of the
   deepest place of the local above it, or of its root. The roots are finite, so the head
   is stable after a finite number of visits; `2 (locals + 16) + 32` visits are a bug of
   the analysis (the program is out of scope: "a loop that the widening does not end").

A chain of locals that rotate their values (RR1) needs one visit for each local: rule 4
comes later. The function values of group B are items (a finite set); the function sets of
stage F12 add the `Unknown` rule. W0707 goes away: the ir pipeline drops it (`IR_DROPS`),
and nothing in the analysis can report it. A call in a block of a cycle (a strongly
connected part of the CFG with more than one block, or a block with an edge to itself,
`widen::Cycles`) gives its result no one-place instance (`Sigma::cyclic`): the result of
the iteration before can be inside the result of this one (`102_wild_instances.wf`,
`again`). The templates run once for each block, with the state of the fixpoint.

As built (plan stage F10a, heap slots): a store of references into a place that no local
of the component owns (behind a reference parameter, in a place of a caller: an `Assign`
through a pointer, the `stores` part of a callee, the destination of a run node) is a weak
update of the *heap slot* of that fact place (`State::store_behind`). `held_at` of a place
of a `Param`, `Held` or `Caller` root gives the wildcard place of the root and the places
of each heap slot whose place overlaps it (a place below a wildcard place counts as its
base). So a body that reads back what it put behind `out` (in the same run, or in the
next iteration of a loop) sees the places of the stored references (tier 2
`verify/s5/R2a: .../W3_store_behind.wf`, a lost fault of the preview; the straight-line
form was a lost fault of group A too). The heap slots join by union and widen at a loop
head with the rules above.

As built (plan stage F10.1, heap slot variables; hole H-A of the review of stage F10):
the heap slot gave the *read value* the places of the stored references, but no variable
held them, so the order "store, change the referent, read back" was accepted
(`out.push(&v[0]); v.clear(); print(out[0].hp)`, also through a callee that stores or
reads, an `Option` slot, `pop`, and the next iteration of a loop). Now each heap slot has
variables of its own (`factgen::holders`, as the versions of a part): the state before
each node gives the places that the slot can hold; the places that overlap make one
version (a variable named ``value in `p` ``) with `points_into` of them; a version is
current at a node where the slot can hold one of its places and gets `rebound_at` at each
other node (so a change before the store does not make it invalid). A read of a place
that no local owns uses the slots that overlap it (`owner_vars`: an access through the
place, a copy of a reference out of it, a read through a chain of references, and so each
argument of a call that reaches the slot). As in the old pipeline, a use of `out` that
reaches the slot after the change (`out.len()`, a call with `out`) is W0301 too.

A vector of closures is a vector of references for this rule (group C, F12-fix H4): a
closure that a loop pushes and that borrows a local of the iteration (a `ByRef` capture,
or a `ByMove` capture that holds `&v[0]`) makes the vector invalid at the end of the
iteration, so the next push and each later use of the vector is W0301, also when no
code runs the closures after the iteration (`while .. { let v = mk_v(); ks.push(|| print(v[0])) };
print(ks.len())`). The old pipeline accepts that program, and it rejects the same loop
with `rs.push(&v[0])`. This is stricter than the old pipeline by design (FP2 of the
second review of the ABC preview), not unsound.

As built (plan stage F13, function values in heap slots): a heap slot holds function
values too (`State::behind_fns`, joined by union, widened by `FNS_MAX` as a function set).
A store of a value with function values into a place that no local of the component owns
(an `Assign` through a pointer, `cb.f = || ..`; a callee that changes such a place and
gets a function argument, `keep(f, cb)`; the parts `put_fns` of a callee) puts the values
and the references of their environments into the slot of the place. Before F13 such a
program stayed with the old pipeline ("a function value stored behind a reference").

- A read of a place that no local owns gets the values of each slot that overlaps it
  (`transfer::fns_at`, `place_value`), with the references that the store put there. The
  references of the role of the place (the `Held` wildcard of a parameter) come only with
  a closure of the role, as before, so a value of a caller in the same place does not get
  the environment of a stored closure.
- A callee that reads a function value behind a parameter runs a value of the parameter
  (`FnVal::Param`, part `runs`); the caller applies each value that the argument reaches
  (`transfer::reach_fns`), and that is the values of the slots too. So a value that the
  body stored behind `cb` runs at `run_cb(cb)` (`reaches` of the old lowering is the part
  `runs` of a value inside or behind a parameter). Code of a caller runs each value that
  its arguments reach, also the values of a slot (OL-1a without a task).
- An `rc` object (`Rc<T>`): a place of the group root of `T` holds what a body stores
  through a handle (`h.f = ..`), and a read of such a place gets the function values of
  the handles on the way (`Rc.new` of a value with a closure gives the handle the closure:
  the result of a type parameter, F12), and of the slot. A callee whose argument type
  reaches an `Rc<T>` (`transfer::rc_inners`) reaches the slot of the group root of `T`
  (`rc_stored`). A reference in an `rc` object points into the wildcard place of the
  group and into the places of the slot (`held_at` of a `Group` root; before F13 the
  program stayed with the old pipeline). A reference in a local of a callee frame (a
  value that a closure put behind a reference) points into the wildcard place of the frame
  root (stage F14 before).
- Each slot keeps its variables (`factgen::holders`, F10.1): a stored closure with a
  `ByRef` capture holds the cell of the variable, so the end of the variable makes the
  slot invalid. A slot of an `rc` object is as a `Vec<&T>` local: after a change of the
  referent, each use of the container that reaches the slot is W0301
  (`tests/data/stored/rc.wf`, `main`; the old pipeline accepts a use that does not read
  the reference).
- A run node uses the variables of each heap slot that overlaps a place that the applied
  summary reads (part `reads`, `templates::slot_reads`; F13-fix, class AB-RC3 of the review
  of stage F13): a callee that reads `c.refs[0]` after a change of the group is W0301, as
  the same read in the body. Before, only an argument that reaches the slot through a
  reference (`deep_uses`) used it, and an `Rc` handle argument is no reference. The same
  rule holds for a closure run (`emit_apps`): a closure in a heap slot that keeps a
  reference into the group, or a made closure in a slot of a parameter, reads the slot
  (classes H-RC1 and H-S1). Not done: a callee whose caller filled the object, and that
  changes the group and then reads the references (`use_it` of
  `tests/gate/probes/fixes/f13b/ab_rc3/e17_read_in_param_fn_b.wf`): the body has no heap
  slot of its own for the references that the object holds at its entry (both pipelines
  miss it; ledger `open-old`).
- Stricter than the old pipeline by design (class FP-RC-strict of the review of stage F13):
  a use of the references of an `rc` object (in the body, or in a callee that reads them)
  after a callee whose row allows a change of the group is W0301, also when the callee
  does not change the group at run time (a loop that runs zero times).
- Stricter than the old pipeline by design (class AB-RC1-copy-strict of the final check of
  group C): a reference through a copy of a local `rc` handle that the facts do not follow
  (`let keep = h.clone()`, `let d = same(c.clone())`) that goes into the object of the
  handle is W0204, also when the copy is a handle of the same object at run time (6.9, the
  W0204 store forms).
- A reference in an `rc` object points into the wildcard place of each field of the group
  that its type can point into (`Roots::group_targets`; F13-fix, false positive FP-AB-RC):
  a `&u64` in `Cache.refs` points into `Cache.data..`, so `c.refs.push(c.refs[0])` changes no
  place that the copy points into (before: `Cache..`, W0312 and W0301). A generic struct
  keeps the wildcard place of the group.
- A heap slot holds the join of the values that each store puts there (a weak update):
  after a callee stores another value over a closure that an earlier callee stored there,
  the slot still holds the old closure, and a run of the slot applies its summary too.
  This is stricter than the old pipeline by design (class FP-S3 of the review of stage F13:
  `reg(cb, world); calm(cb); run_ref(cb)` is W0301 for a reference into `world`).
- A value of a caller and a closure in one value (a slot that holds both): the run of the
  value of the caller (code of a caller) gets no environment from the references of the
  value, which are the environment of the closure (F13-fix, false positive FP-S2:
  `s.o = Some(|| ..); let o = s.o; match o { Some(f) => f(), .. }` lent `world..`).
- A closure that another function made (its maker frame is gone) keeps the cell of each
  `Kept` and `ByRef` variable with it: σ of such a capture is the place of the closure
  value, not the places that the variable points into (`apply::other_maker`; F13-fix,
  false positive FP-K4: a returned closure that runs `r = &b.entities[0]` changed `b`).
- A callee that runs two function values runs them in each order (`Applied::again` with
  `order`): each run applies at `Main` or at `Ret`, but one time, so a `once` closure that
  it runs one time is no W0502 (`fn both(f, g) { f(); g() }`, finding (a) of stage
  F12-fix3). The same value that runs two times is W0502.
  As built (class H-ORD of the final check of group C): the order applies only to an
  app that runs one time. An app that a value already runs two times
  (`both(|| { h(); h() }, g)`, `|| twice(h)`, `|| each(2, h)`) keeps `again` without
  `order`. A value that the runs of two keys reach, also through the values that a value
  runs (`both(h, || h())`, `both(|| h(), || h())`), runs two times: `apply_value` writes
  each value that it is asked to apply into `Apps::reached`, also a value that it applied
  before, and `apply_runs` gives the app of such a value `again` without `order` (not for
  an item, which has no `once` part).
- A copy of a function value through a pointer is a copy of the references of its
  environment (`templates::copied_refs`; F13-fix, classes H-S1 and H-RC1): a read back of a
  closure from a heap slot (`let g = cb.f`, `let g = h.f`) uses the variables of the slot.
  A closure that an `rc` object holds and that points into the group can point into the
  object itself, so a copy of it out of the object depends on the handles on the way
  (`transfer::place_value`): `h.f = d.f; d = newh(); run_hook(h)` and a block value `d.f`
  after the end of `d` are W0301.
- A linear closure in a part of a local (`cb.f = || rollback(t)`), through a pointer, in a
  `Box`, or through an `rc` handle makes the local (or the local of the handle) linear
  (`templates::mark_fn_linear_in`; F13-fix, class H-LIN). The store gives `overwrites` of
  the variable, so a linear value there before is overwritten. The drop of an aggregate
  does not run the `on abort` functions of the captures of a closure in it, so such a
  variable has no `has_on_abort` (W0602 across an abort; the interpreter leaks the value).
  A callee that changes a part of a function type of a local that holds a linear closure
  (`calm(&cb)` with `cb.f = || print(2)`) overwrites it; a change of a container
  (`ks.pop()`) does not. This is as strict as the old pipeline, which rejects each such
  store at the closure ("it can go out of scope without a call").

**The post-passes of today**, and where each one goes:

| Today | In this design |
| --- | --- |
| `finish_values` (`apply_stored`, `finish_task_values`) | heap slots; the run node applies the summary of each stored value |
| `finish_aborts` | the `unwind` edges and the cleanup copies (6.5) |
| `finish_task_ends`, `finish_task_marks` | the templates of `Join`, `ScopeWait`, `Fork`, `Spawn` and the `tasks` part |
| `op_refs`, `finish_op_env` | the fixpoint of a handled body and its clauses; the caller frame root |
| `check_returns`, `check_stored_behind` | `error(_0, Return)` in the spec; the `stores` check over summaries (6.9) |
| `summary_to_sig` | the summary is the signature part (6.8) |
| `finish_resume_runs` | the continuation summary at each `Resume` (6.7) |
| `finish_spared` | `spared_at` from the destinations (6.5) |
| `check_int_lits`, `finish_int_ops` | `typeck` and the integer type of `Binary` |
| `settle_moves` | final types: no tentative move |
| `finish_via_calls` | the `writes_via` rule of the `Call` template |
| the flag pass | the props of each `LocalDecl` and the join of 6.3 |
| `dropped_params`, `held_params` | the `drops` and `holds` queries |

### 6.7 Summaries

One procedure `summarize(body)` computes the summary of each body from the states of the
analysis at its nodes. One procedure `apply(Σ, σ, n, kind)` emits the facts of a summary
at a run node. Each part is a projection of the facts of the nodes of the body onto its
interface. The relation table `RELS` (`factgen/rels.rs`, sketch `rels.rs`) says for each
input relation of the spec which part carries it, or why it stays inside its body. A test
reads the input list from `spec/weft.dl` and destructures `FnFacts` field by field, so a
new relation cannot miss a row (minimal design; the machine sketch had a hard-coded list
that missed `rest_linear`). One row differs from the sketch: `rebound_at` goes to the
must part `rebinds` (a projection only of a capture or upvar that each path to `Return`
gives a whole new value). `joined_at` goes to the `tasks` part, as in the sketch, as its
must half.

**Interface roots.** `Param(i)` (what reference parameter `i` points into, or the value of
by-value parameter `i`), `Held(i)` (what the references behind parameter `i` point into),
`CaptureCell(k)` and `Capture(k)` (the cell, and the value, of capture or upvar `k`),
`Cap(j)` (a capability: an effect of the row, or a captured capability),
`OpResult(op)` (in a handled body: what a resume gives to an operation),
`ResumeResult` (in a clause: what `resume` gives back), `Frame` (a local of the frame of
the body that leaves it), `Caller` (a place of a caller), `Group(adt)`.

**Parts.**

| Part | Content (in interface terms) | Replaces today |
| --- | --- | --- |
| `muts` | places that the body changes, with the unstable steps | `Summary::muts`, the `mut` places of an inferred row, `footprint` sources |
| `reads` | places that the body reads | `Summary::reads` (OR10) |
| `frees` | places that the body frees: moves out of a by-move environment field or an upvar, frees through code of a caller, frees of the rest of a handled body (for `releases_at`) | `Summary::dropped`, `ContInfo::frees` |
| `lends` | places that the body gives to code that it does not know | `Summary::lends`, `lent` |
| `performs` | the operations and their capability interface, with their arguments | `performs`, `op_args`, `cap_runs`, `callee_ops` |
| `aborts` | the abort destinations (by capability interface), `assert`, failures (`raises`) | `abortive`, `abortive_local`, `raises` |
| `multi` | the capability interfaces through which the body can resume more than once | `multi`, `reach_repeats` |
| `runs` | each function value of the interface that the body runs: once or many, as a task or not, with which places (and, for a task, the places that the body writes and reads while it runs) | `lent`, `repeats`, `task_runs`, `op_fns`, `held_run` |
| `tasks` | the footprints of the tasks that the body starts in a scope that it does not own, and the capabilities that they hold; the task handles of the interface (parameters, captures) that the body joins on each normal path (a must part: `joined_at` at the run node, O3-9) | `spawns`, `tasks`, `task_effects`, `pins` |
| `ret` | the abstract value of `_0`: places, closures (their environment in interface terms), capabilities, tasks, results of code of a caller | `ret`, `RetFn`, `ret_refs` |
| `stores` | the values that the body writes behind a reference parameter, into an environment field, or into an `rc` object | `stores`, `fn_stores`, `group_stores`, `stored_behind` |
| `drops`, `holds` | the type parameters (and, for `holds`, each parameter) of values that the body drops, or holds across a node that can abort or resume more than once | `drops`, `holds` |
| `uses`, `moves` | the environment fields and upvars that the body uses or moves when it runs | `late_join` uses, `moved_captures` |
| `rebinds` | the `ByRef` captures and upvars that the body gives a whole new value on each path to its `Return` (a must part). At the run node they get `rebound_at` at `Ret`, before the `points_into` of the new value from `stores`, so an old place does not stay (F3-11). A path that can abort has no `Ret`, so it needs no new value | none (F3-11 is open today) |
| `uniq_needs` | interface places that the body gives to a `@ uniq` parameter | `uniq_needs` |
| `only_self` | each change of the body is below its first parameter (`writes_via` at a method call, QA6) | `note_via_call` |
| `pre`, `post` (clauses) | the parts above, split at the first resume point (below) | `run_handler` (the whole clause at the perform) |

**Resume points and the split of a clause.** A resume point of a clause is a `Resume`
node, or a run node whose applied summary resumes (a closure in the clause that calls
`resume`, `runs` of a callee that runs such a closure). The `pre` part is the projection of
the nodes on a path from the entry that passes no resume point. The `post` part is the
projection of the nodes that a resume point reaches, from its `Ret` on. A node on a cycle
through a resume point is in both. A clause with no resume point on some path to its
`Return` can end with no resume (an abort to its handler). This is the MIR definition
(soundness judge, H7: J2 resumes through a closure, and the machine text split only at
`Resume` nodes).

**The kinds of run node.** All use `apply`.

| Run node | Summary | σ maps |
| --- | --- | --- |
| `Call` of an item | the item, with its type arguments | parameters to the argument places; `Row(E)` through `CapArgs`; `Frame` to `F(n)` |
| `Call` of a closure value | the closure body | parameters to the arguments; `Capture(k)` of a `ByRef` field to the current value of the variable at `n` (RR7, V103); `CaptureCell(k)` to `C(x)`; `ByMove` fields to the environment value; `Capture(k)` of a `Kept` field to the root of the variable of the maker (the shared cell: a write of the closure is a write of the variable, `mutates_at` or `task_writes`, W0405) |
| `Call` of a function parameter or an unknown value | "code of a caller" (below) | the same |
| `Perform` through a local handler | the `pre` part of each clause of the operation | clause parameters to the argument places (F3, V035, S053); upvars to the site variables |
| `Perform` through `Row(E)` | "an operation of a caller" (below) | the same |
| `Handle` `Post` | the `post` part of each clause | as at the performs that ran it; `ResumeResult` to the places of `_0` of the handled body |
| `Resume` | the continuation of the handler: the facts of each node of the handled body from the `Ret` of a suspending node of the operation to the `Return` of the handled body; `ret` = `_0` of the handled body | site places as they are (shared tables); places of the handled body that the clause cannot name to `R(n)` |
| `Spawn`, a `Fork` branch | the task body | as a closure call; mutations and lends become `task_writes`, reads become `task_reads` |
| `UnwindValue` with `OnAbort(f)` | `f` | the parameter to the value; `CapArgs::Root` |
| a node of code that can run stored values (unknown code, an extern function, a `reaches` callee) | the summary of each function value in a heap slot that the arguments reach | as a closure call |

A callee that runs a function argument `Many` times gets the summary of that argument
applied at `Main` and again at `Ret`, so that a change of the first run invalidates what
the second run uses (OR3, V043, V106). A function argument that runs as a task gets
`spawned_at` at `Main` and `joined_at` at `Ret` (OR7, V126, V127, V132).

**Code of a caller.** A function parameter, a value that the analysis does not know, and
a function with no body and no stated summary. It lends the wildcard place of each
reference argument and of its held places, and `Caller..`; it reads them; its result
points into these wildcard places and into `Caller` (map N2: also with no reference
argument); it runs each stored value that its arguments reach (`reaches: Many`) and each
function argument (`Many`, as a task in the worst way); it performs its row (a stated row,
or the pass-through of ADR 0005); it can abort; it is `multi` if `may_be_multi` holds.

**An operation of a caller.** It lends and reads the places of the reference arguments
and `Caller..`; its result points into their wildcard places and into `Caller` (map N1);
it can abort; it is `multi` if the operation is.

**Soundness of a summary** is a hypothesis, not a theorem: each part must contain each
effect of the body on its interface. The design reduces it to one procedure, `RELS`
guards its coverage, and the summary oracle tests it on runs (section 8.5).

As built (plan stage F5, `crates/weft-sema/src/analysis/`):

- `summary.rs`: `Summary` has the parts of the table above (`muts` with the callee root
  index of each place, `ret` with the stated places, the stated places of each part of a
  tuple, and the places that flow from the arguments), and the interface of each
  parameter (its name, its callee root index, its stated `in` place). `IPlace` is an
  interface root and its steps; `IPlace::cut` keeps `SIG_PLACE_STEPS` steps and a
  wildcard step. `Summary::has` matches each part of `RELS`. `Summaries` holds the summary
  of each function of the IR, or the reason why it has none yet.
- `sig.rs`: `from_signature` gives the summary of a function with a stated row (an
  extern function too). The parts that only the old inference has for a function with a
  body (`drops`, `holds`, `raises`) come from `Analysis::sigs` until stage F6. A signature
  with a function value, a store into an `rc` object, a foreign change of an `rc` object,
  or a task gives a reason, and the program stays with the old pipeline.
- `apply.rs`: `Sigma` maps `Param(i)` to the places of argument `i` (a reference
  argument, or a by-value argument whose parameter can hold references), `Held(i)` to
  the places that the references behind a reference argument point into (only if its
  pointee can hold a reference), `Group` to the group root, `Frame` to `F(n)`. Each run
  node has its own split ids and its own one-place instances. `transfer::call_out` gives
  the analysis and the templates one σ, one result and one list of stores.
- Rules that resolve this section (as the old lowering, `call_flows`): a result with no
  stated place for each reference can point anywhere inside each argument that can hold
  references (`Param(i)` wildcard); a result that names a type parameter gets the places
  of each by-value argument of a type parameter as they are; a reference argument gives
  the places behind it if its pointee can hold a reference. In a tuple result with stated
  places of its parts, the flows go only to the other parts. A one-place result (`&T` or
  `Option<&T>`, `T` with no reference) gets a one-place instance of each wildcard place
  (group A has no cycle).
- The part `stores` (R3RT6): a reference parameter whose pointee can hold a reference and
  whose root the call changes gets the references behind each other argument, a
  reference into another argument only if its pointee type can hold a reference to a
  part of the pointee of that argument, and the references of a by-value argument only if
  their types meet.
- `raises` is an abort of the summary (6.5), so the node gets `may_abort`; the old
  lowering gives none for `raises` alone.

As built (plan stage F6, `crates/weft-sema/src/analysis/`):

- `summarize.rs`: the summary of a function body is a projection of the facts of its
  component. `mutates_at` gives `muts`: each changed place whose root is a root of the
  interface (`Param`, `Held`, `Group`), cut at `SIG_PLACE_STEPS`; a change below a
  wildcard place is a change of its base; a covered place adds nothing. A change of a
  by-value parameter with no reference in its type is a `Param` place too, as the old
  inference says (W0701 asks for it; σ gives such a parameter no place, so a caller
  applies nothing). `escapes_at` gives `performs` and `aborts` through `Row`; a callee
  that `raises` gives `raises`; a callee that can resume more than once with no effect
  of its row (an unknown function value) gives `multi`. A body that the fact generator
  supports has no type parameter, so `drops` and `holds` are empty.
- The other parts of the summary of a function with no stated row come from its
  signature (`sig::build`): the parameters, the reads (the root of each parameter), the
  result (the stated places and the flows of 6.7 above), the stores and the `@ uniq`
  parameters. The part `ret` is not the value of `_0`: a reference into a local of the
  body at `Return` is `error(_0, Return)` at the callee, so the summary has no `Frame`
  place. This keeps the callers of the old pipeline; the value of `_0` is a later
  precision step. A function with a stated row has its stated row and the parts that
  its body gives (`raises`, `multi`, `drops`, `holds`).
- `unknown.rs`, an operation of a caller (map N1): the run node reads and lends the
  places of each reference argument (`call_arg` and `call_mut` with the root of the
  parameter, for W0312, as the old lowering), gives `call_arg` of the places of a
  by-value argument that holds references, and reads and lends `Caller..`. Its result
  points into the wildcard place of each reference argument, of the `Param` and `Held`
  roots of the parameters of the body (a place of a caller that the body can name: the
  root `Caller` stands only for the places that it cannot name), and into `Caller..`.
  The node has `escapes_at`, `may_abort`, and `multi_at` for a `multi` operation.
- The root `Caller` has the kind `Arg` and the text "a place of a caller". The
  references in a place of a caller point into `Caller..`. σ of `Caller` at a run node
  is the root `Caller` of the run node. A summary that performs an effect of its row
  also lends `Caller..` (the clause of a caller can change the places that a result of
  an operation points into), so a call of it makes such a reference invalid.
- A run node (a call, a perform) that changes a place of a local whose type can hold a
  linear value can put one there and keep the old value (`Vec.push`). The local then
  can hold a linear value: the state joins one, and the node gets `overwrites(S(l), n)`
  if the state says that the local holds none (`let v = []`), so W0601 holds at its end.
- A callee holds each reference argument until it returns: the `Ret` node uses each
  argument of plain data that holds a reference into a value that another argument
  moves (`both(&v[0], v)`). The move frees the value, so the reference is invalid
  (W0301 at the call).
- A stated place of the result in an `rc` group depends on the handles of the
  arguments (`Lower::group_arg_deps`): the handle places on the way to each argument,
  and the handle `h.*` of a reference argument to an `Rc` (or each handle below a
  reference argument whose pointee is `nonportable`).

As built (plan stage F10.2, `analysis::apply::stores`; hole H-C of the second review of
stage F10): a callee can store a reference through a reference that its argument holds.
`put(v: &Vec<T>, out: &Vec<&Vec<&T>>) / mut(out..) { out[0].push(&v[0]) }` changes
`*out` (the part `muts` has `Held(1)`), and it also puts `&v[0]` into `*out[0]`. Before
this stage the part `stores` gave the stored places only to the argument (`out`), so
the referent (`inner` after `out.push(&inner)`) did not point into `v[]`, and
`v.clear(); print(inner[0].hp)` was accepted (a regression where the referent is
behind a parameter: a heap slot).

- The part `stores` reaches the referents of the references that the argument holds,
  with the reach of the part `muts`: each place of `σ(Held(j))` of a reference argument,
  and each place of `σ(Param(j))` of a by-value argument that holds references, whose
  root the node changes. Each such place gets the stored values as a weak update: a
  local joins them into its value (a variable of the local points into them), and a
  place that no local owns gets them in its heap slot (6.6, F10.1).
- The R3RT6 type rule holds for the referent too. The type of the referent is the type
  of the value of its root (a local, or the pointee of a reference parameter), or, if
  the node does not know it, any type that the references in the pointee of the
  argument can point to. A referent whose type cannot hold a reference gets nothing
  (`w: Entity`, held next to `h: H`), a held reference gets the references behind the
  other arguments, and a reference into another argument needs a type that can hold
  one (`can_hold_into`). A callee with `mut(out)` (no `..`) does not change `*out`, so
  it stores nothing through it (`q9_extend_fp` and `R3RT6_ref_arg_flow_fp` stay
  accepted).
- The summary of a body (`sig::build`) has a part `stores` for a by-value parameter
  that holds references too. A body that stores through a held reference changes a
  place of `Held(j)` (or `Param(j)` of a by-value parameter), and `summarize` projects
  that change into `muts`, so its callers apply the store.
- A callee that moves a reference from one referent of an argument to another one of
  the same argument (`out[0].push(out[1][0])`) is W0312 in the callee, so the part has
  no flow from an argument into itself.
- The programs are in `tests/gate/probes/fixes/f10/hc/` and
  `tests/programs/165_store_through_held_ref.wf` (claim F10-HC).

As built (plan stage F11, `analysis::transfer::value_out`, `apply::closure_sigma`,
`summarize::closure`; group C was a preview until stage F13 put it in the default set):

- The analysis gives a closure aggregate the value `fns = {Closure(c)}`, the cell root
  `x (cell)` of the variable of each `ByRef` capture (owned by `C(x)`: only `Dead(x)` and
  the unwinding of `x` end it, so a move and a new value of `x` keep the closure valid,
  O3-11; a capture of a capture of the maker gives the places that the reference of the
  maker points into), and the places and the linear part of each `ByMove` value. A `Kept`
  capture adds nothing: no reference points into the shared cell (V13), so a returned
  counter closure is valid (`d5_count.wf`), and a closure that borrows a captured local
  (`ByRef`) points into its cell, which the frame end ends (J5d, W0204).
- A `Call` of a function value applies the summary of each value that the callee can be:
  an item (as a `Call` of the item) or a closure of the component. A value that the
  analysis does not know (a parameter, a field, a result) is `Later` (stage F12). σ of a
  closure (`closure_sigma`): the parameters map to the arguments; `Capture(k)` of a `Kept`
  or a `ByRef` capture maps to α of the source of the capture in its maker, in the state
  at the run node, `CaptureHeld(k)` to what the value of the source points into now, and
  `CaptureDeep(k)` to what the references there point into (RR7, V103); `Capture(k)` of a
  `ByMove` capture maps to the place of the closure value, and `CaptureHeld(k)` to its
  references. So a closure that writes a `Kept` counter changes the root of the counter at
  each call (`mutates_at`; a task does so as `task_writes`, W0405, with stage F18).
- The parts of a closure summary (`summarize::closure`): `muts`, `reads` and `lends` are
  the places of `mutates_at`, `reads_at` and `lends_mut` with an interface root (callee
  root `STORED` for a capture, the root of the argument for a parameter); `performs` and
  `aborts` from `escapes_at` (each operation can abort), the failures and the `assert`s of
  the callees and of the body; `uses` are the `Kept` and `ByRef` captures (the body names
  each capture); `moves` the `ByMove` captures that a `move` or a `Consume` names;
  `rebinds` the `Kept` and `ByRef` captures that each normal path to a `Return` assigns
  as a whole (a forward must analysis on the IR); `puts` the references of each heap slot
  of an interface place at each `Return` (a store into a capture, into a part of it, or
  behind a reference), and the new references of each `ByMove` capture, with a reference
  into a local of the body as the `Frame` root; `ret` the interface places of `_0`;
  `runs` each capture that the body calls (`Many` for two calls or a call in a cycle).
- At the run node: `Main` has the operands, a move of a callee whose local is `once`
  (`props.once`; a copy of the local moves it too, B12-fn-once, W0502), the parts that
  act at the call (`apply::main`), the uses of the variables of the sources of the `uses`
  captures (a new value of a captured reference that a change invalidates is W0301 at the
  call, RR7), and each value that the closure runs through a capture (`runs`): the value
  of the source of the capture at the run node applies its summary at the same node
  (V103, at most eight levels), and a source that holds a `once` closure moves. `Ret` has
  the result, the `puts` (a weak definition of the variable of each place), the new value
  of each `rebinds` capture (`rebound_at` of the variable and `points_into` of the stored
  places: F3-11 is valid, a new value on one path only is not), and a second application
  of a `Many` run. `FrameEnd` ends the frame root of a closure whose result or `puts`
  name its frame.
- A call of a function value keeps the abort edges of the IR, and gets `may_abort` only if
  a summary that it applies can abort. The part `multi` of a closure summary holds if a
  node of the body can resume more than once (F11-M1).
- A call moves the callee (`moved_at` of its variable) if a closure that the value can
  be is `once` (decision above; F11-O1, F11-C1). A call through a local that holds no
  value (it moved) applies no summary: the use of the local is W0302 or W0502.
- A closure that gives a linear capture a new value finishes the old value in its body
  (the drop pair, W0601 there); the call moves the variable at `Main` and gives it the
  new value at `Ret`, so the new value is no second overwrite.
- The calls of a capture in the summary of a closure body (in the terms of its interface)
  apply nothing there (their effects reach the run node of the closure through `runs`);
  a reference argument or a reference in the result of such a call is stage F12. In the
  instantiated facts the capture holds the values of the maker, so the call applies their
  summaries at its own node.

As built (plan stage F12, `analysis::transfer::value_out`, `apply_runs`, `unknown::code_of_caller`,
`summarize::runs_of`, `summarize::ret_fns_of`; group C was a preview until stage F13 put it
in the default set):

- Function sets (`domain::FnVal`): an item, a closure of the component, `Made(c)` (a closure that a
  callee made and gave back: the value holds its environment, so σ maps each capture to the place
  and the references of the value, `apply::made_sigma`), `Param(i)` (a value of parameter `i`, or a
  value inside it or behind it), `Capture(k)` (a value of a capture in the summary of a closure),
  and `Unknown`. A function parameter starts with `Param(i)`; a read through a pointer or of an
  element gives the values of the places (`transfer::fns_at`). A set with more than
  `domain::FNS_MAX` (32) values drops its items for `Unknown` (the widening; the other values are
  finite). A value with a function part that goes behind a reference (a heap slot) was stage F13:
  until F13 the program stayed with the old pipeline (heap slots of function values: 6.6).
- A closure aggregate holds the references of its `Kept` captures too (a closure that leaves its
  maker, or that a closure gives back, reads them). A call of a value that the analysis does not
  know (`Param`, `Capture`, `Unknown`) is code of a caller (map N2): it reads and lends the places
  of its reference arguments (not their wildcards: a stable place below them stays valid, as for
  the old lowering), the places behind them, the wildcard places of the references of the value
  (its environment) and `Caller..`; its result points into their wildcard places and into
  `Caller..`, and can be each function value of the arguments and the value of the parameter
  again; it can abort (`raises`), and it is `multi` if an effect of the row of its type has a
  `multi` operation (with no row: an effect of the program). It runs each function value that its
  arguments reach, more than once. As built (F13-fix): it also reads (`reads_at`, no `lends_mut`) the wildcard
  places of the parameters of the body and of the `rc` groups that their types reach
  (`transfer::caller_reads`): the value of a caller can point there, and the summary oracle
  found the reads (`let g = h.f; g()` reads `Hook.data[]`). A change there through the value
  is not in the facts of the body: the caller applies the value that it gives, and its W0312
  check rejects a value that changes a place of another argument (map N2).
- Part `runs`: each run node of a `Param(i)` or `Capture(k)` value records a run with the places of
  its arguments (`transfer::RunOf`); `many` for two run nodes, a node in a cycle, or a run again.
  At a call of an item or a closure, `apply_runs` applies each value that the argument (or the
  source of the capture) reaches, and the values that their runs give back (four levels), with
  `Given::Opaque` (each parameter of the value gets the places of the run). A run is at `Ret`
  (`Applied::late`: the callee can change a place first, `clear_then`), at `Main` and `Ret` for
  `many` or for two runs (each order, `run_both`), and has no check of the arguments of the call
  against the value, only of its changes against its environment (`RunKind::Run`, W0312). A run
  again of a `once` closure is W0502. A value applies one time at a run node (Q3-2: a DAG of
  closures is linear); a chain deeper than 64 stays with the old pipeline.
- Part `ret` (`Ret::fns`): the function values of `_0` at each `Return` in interface terms; a
  closure of the body goes out as `Made(c)`, with the places of its `Kept` captures (their values
  where the body makes the closure, `FnParts::made`). A caller maps `Param(i)` to the values that
  argument `i` reaches. A function that gives back a closure has the effects of the closure in its
  row (W0701, W0702 at a caller, as the old inference). The summary of each closure goes into
  `Summaries` for the callers.
- W0705: at a call, `param_effect` of the row of each parameter of a function type with a row, and
  `fn_arg_effect` of the effects of each value of the argument (a closure, an item, or the row of
  the type of a value that the body does not know).
- A function with no body and a function value in its signature runs each function value of its
  parameters more than once and gives back `Unknown` and the values of its parameters
  (`sig::foreign_fn_parts`).
- Code of a caller performs the effects of the stated row of its function type (W0701 of
  `pub fn a(f: fn() / log) { f() }`); with no row its effects pass through.
- A linear closure that goes to a parameter of a type that is not linear, and that the
  callee does not run, is a value that the callee can drop (a `Dropped` variable: W0601).
- A place whose type has a function part (and cannot hold a linear value by its type)
  gets a linear value at a call of a function item only if an argument can hold one
  (`transfer::can_get_linear_with`): an item puts only the values of its arguments into
  a place of the caller, because a function value behind a reference stays with the old
  pipeline. A closure and code of a caller can make a linear closure, so their runs keep
  the rule of the type (false positive FP1 of the review of the ABC preview, F12-fix:
  `ffs.push(fs)` of a `Vec<fn()>` with plain closures was W0601).
- The places of a closure that a body gives back: its `Kept` captures, and the `Kept`
  captures of each closure that they hold, with the last value of each variable (the
  states before each `Dead`, `Em::last`).
- Code of a caller can run a function argument on another thread (ADR 0006): a closure
  that changes or lends a place, puts a reference, has a `ByRef` capture or a nonportable
  capture, and an item that changes a place, stay with the old pipeline when code of a
  caller can run them (the facts of tasks are stage F18; W0401, W0403, W0405).
- A place behind a parameter whose type cannot hold a function value gives no function
  value (`transfer::fns_at`): a closure that captures `world: &World` is no code of a
  caller where a callee runs it.
- A run checks the places that the value changes through its environment against the
  places that the callee gives to it and against the other arguments of the call
  (`Sigma::others`, W0312): the callee can keep references into them across the run. A
  change through a parameter of the value is a change of what the callee gives.
- A closure summary has no `lends` of code of a caller at the runs of its captures and
  parameters: a caller applies the values that it gives there. A closure that a callee
  made (`Made`) runs the values that it holds (follow-up F13.2, below).
- A function value carries the places that its environment points into wherever its
  values go (F12-fix, hole H2 of the review of the ABC preview): `store_fns` gives a
  place that a call changes the references of each function argument with its values
  (`fs.push(mk())`), a read of an element or a place behind a pointer of a type with a
  function part gives the references at the place (`place_value`), a result that is a
  value of an argument (`id(f)`, code of a caller) gets the references that the
  argument reaches (`transfer::reach_refs`), and σ of a `Made` closure maps a `ByRef`
  or `Kept` capture to each place that the value points into as well as to the value
  itself (`apply::made_sigma`): a closure that a closure gives back keeps the cell of
  its `ByRef` capture.
- A `Kept` or `ByRef` capture of a `Made` closure whose variable is a variable of the
  body of the run node, through the `Kept` and `ByRef` captures of its makers
  (`let mk = || || { o = Some(first) }` in the same body), maps to that variable only,
  as for a closure of the component (`apply::made_capture_source`; hole H7 and false
  positive FP4 of the third review of the ABC preview). The closure changes and reads
  each captured variable at its own place, and a reference that it stores into one
  capture goes into the value of that variable (`Some(e)` points into the referent).
  Before, each such capture mapped to all the references of the value: a push into
  `rs` was a change of `w`, and the variable `o` did not get the reference. A capture
  whose variable is not in the body (a maker that a callee gives back) keeps the
  mapping to the value and its references.
- A run that a callee does late (at `Ret`, `Applied::late`) lends at `Main`: the callee
  runs the value before it returns, so the lend invalidates each reference that lives
  across the call, but not the result of the call. The body of the callee checks that a
  run leaves its result valid. A capture that the call rebinds at `Ret` keeps the lends
  at `Ret` (`templates::emit_apps`; false positive FP3 of the third review of the ABC
  preview: `fn g2(m) { let g = give(m); g() }` was W0301 at `g()`).
- The result of a run node whose type holds no reference and no function value (no
  type parameter) gets none (`transfer::typed_result`): the values of a run join their
  results, so the `()` result of a tail call `g()` pointed into the environment of a
  closure that a maker gives back (W0204 class of the third review of the ABC preview).
- The result of a run of a closure maker through a closure or a callee (`|| mk()`,
  `give(mk)`) points into the environment of the closure that the maker makes: the
  places of part `ret` of the maker with σ of the maker at the run node
  (`transfer::result_refs`, for a maker with no parameter, through `RESULT_DEPTH`
  captures that give back captures). Before, only the W0204 of a unit tail call caught
  a made closure that reads a reference that its maker took (`n1c/c05`).
- The closure-copy rule of a callee (`once_copied_out`, the copy-out at a run node)
  also holds for an argument of a type that holds references (an `Option`, a tuple,
  a `Vec` of references, `templates::through_ref`): the call moves the owners of each
  referent behind which a `once` closure can be (`templates::once_vars`, two levels),
  and the argument itself if it holds a `once` closure by value (old holes b14-agg of
  the third review of the ABC preview: `ro(Some(&fs))` two times).
- A callee that puts a closure with a linear capture into a place of its caller (part
  `put_fns`) makes the local of that place linear in the facts
  (`templates::put_linear`, as `fn_linear_args` for a closure argument): W0601 where
  the caller can drop it (`fn add(ks: &Vec<fn()>, t: Tx) { ks.push(|| rollback(t)) }`,
  a hole of stage F13 that the rerun of the review sets found).
- The result of a run of a value of a parameter is `FnVal::ParamResult(i)`, not the
  parameter again, and part `runs` keeps a run of the result apart from a run of the
  parameter (`Run::result`). A caller applies to a run of the result only the values
  that the runs of its values give back (`transfer::results_of`), and a run of a
  parameter and a run of its result are not two values that run in each order. So a
  `once` maker that `fn go(m) { let g = m(); g() }` runs one time runs once (the W0502
  class of the third review of the ABC preview); a maker that a callee runs two times is
  still W0502. Part `ret` gives back `RetFn::Param(i)` for a result, as before.
- Stricter than the old pipeline by design (map N2): a result of code of a caller
  (`let g = m()`) can point into `Caller..`, so a later run of code of a caller, or a
  `fail` operation through a callee, between `m()` and the use of `g` makes it invalid
  (W0301; `twice(m) { let g = m(); let h = m(); g(); h() }`). A `fail` operation does
  not resume, but its clause runs before the body unwinds and an `on abort` function can
  read a reference that the clause invalidated, so the lend stays on both edges: the
  facts have no node for effects of the abort edge only. Ledger `new-fp` (`stricter`).
- The result of a closure maker keeps its effects in a second closure and in a callee
  (F12-fix2, hole N1 of the second review of the ABC preview: `let mk2 = || mk()`,
  `|| run(mk())`, `fn go(m) { let g = m(); g() }`):
  - The result of a run of a function value of the interface (a parameter or a
    capture) is that value of the interface again (`FnVal::Param`, `FnVal::Capture`),
    with no `Unknown`. The caller knows the values that it gives, and it applies their
    results (`transfer::with_results`), also at a run of a capture.
  - A capture that a closure gives back (`RetFn::Capture`) carries the places that the
    environments of its values point into (`transfer::capture_refs`).
  - A cell root in the environment of a `Made` closure or of code of a caller also
    stands for the current value of its variable (`transfer::cell_values`): the
    closure changes the variable through the cell (6.3).
  - A `Made` closure that a run gives back is not in the place of the value that runs:
    σ maps its captures only to the places that the value points into.
- A callee whose result is a function value of a reference argument (`RetFn::Param` of
  `first(fs: &Vec<fn()>) -> fn() { fs[0] }`) copies the value out of the referent: when
  it can be a `once` closure, the `Ret` node moves the owners of the referent
  (`templates::once_copied_out`, the closure-copy rule of 5.22; old hole `b14` of the
  review of the ABC preview, F12-fix). A closure that gives back such a copy does the
  same at its call. A callee or a closure that runs a `once` closure that it copies out
  of a referent (`fn runfirst(fs: &Vec<fn()>) { let g = fs[0]; g() }`) moves the owners
  of the referent at the run node (`templates::emit_apps`, `once_args`), so a second
  run is W0302 (old holes b14-run of the second review of the ABC preview, F12-fix2).
- A run in part `runs` has `maybe` (`Run::maybe`, F12-fix H5): a normal path of the body
  from its entry to a `Return` passes no block whose terminator runs the value
  (`summarize::returns_without`). A linear closure that goes to such a parameter can go
  away with no run (`templates::dropped_fn_args`: a `Dropped` variable, W0601). A
  closure literal gives the `E` variable of a `ByMove` capture of a type with a function
  part the flags of a linear value when the captured value is a linear closure
  (`templates::linear_fn_captures`): a closure that runs it on some paths only is W0601
  at its `Return`. A run that a callee gives (part `runs` of its summary) is on some
  paths only at the run node when it is `maybe` in the callee, and a run that code of
  a caller can do is on some paths only (`RunOf::maybe`): the block of such a run node
  is not a block that runs the value (hole H5b of the second review of the ABC
  preview, F12-fix2: `fn outer(f, c) { maybe(f, c) }`).
- A closure maker whose result is linear (`Ret::linear` of one of its values, also
  through a maker of makers, `templates::gives_linear`) that goes to a callee is
  W0601 at the call, also when the callee runs the maker: the callee does not know
  that the result is linear, so it can drop it (hole H3b of the second review of the
  ABC preview, F12-fix2: `fn go(m) { let g = m() }`). The old pipeline rejects each
  of these programs too.
- A run node in a cycle that changes a local whose type has a function part (and cannot
  be linear by its type) gives it `overwrites` (`templates::gets_linear_but`) also when
  the state joins a linear value of the back edge: the local starts empty
  (`Vec.new()`), so on the first run of the node it holds none (F12-fix H6: linear
  closures pushed in a loop; the push of the next iteration is W0601, as in the old
  pipeline).
- A container that gets a closure holds its places (F12-fix H4): at the `Ret` node of a
  call that changes a place whose local can hold a function value, the holder of the
  place (its `S` variable or heap slot, `templates::store`) gets the places that the
  environments of the closures of the arguments point into (`templates::fn_stores`, the
  facts of `transfer::store_fns`). So the end of a `ByRef` capture or a change below a
  reference of a `ByMove` capture makes the `Vec` invalid; in a loop the next `push` is
  the first use.
- Part `ret` has `linear` (`Ret::linear`, F12-fix H3): `_0` can hold a linear value at a
  `Return` and its type has a function part (no type parameter, not linear by its
  type), so a linear closure that the body gives back (also in a `Vec`, a field or an
  `Option`) makes the result of a call linear (`apply::ret_value`). A caller that drops
  it is W0601; the old pipeline reports the maker (R3RT5 W0204).
- The results of a run (`transfer::with_results`): a closure of the body that gives back a
  capture gives the values of the capture, also through a chain of closures that give
  back closures (16 levels; a longer chain stays with the old pipeline).
- A linear closure that goes to a function value can go away there (a `Dropped`
  variable, W0601): code of a caller can drop it, and an item or a closure that does not
  run it drops it (`templates::dropped_fn_args`). Code of a caller that can run a `once`
  argument runs it again (W0502). A function value that an operation gives to a handler
  stays with the old pipeline (stage F14).
- `Dead(l)` keeps the value of a variable that a closure keeps (`Kept`): a closure that a
  loop makes from a local of the loop body runs its last value after the loop.
- A pattern that binds a part that can be a `once` closure moves the part only: the other
  parts of the same pattern are no use of a moved value.
- A run argument that points into a local of the body (`f(&x)`) is the frame root of the
  run node (`IRoot::Frame`): a closure that keeps it outside the call holds a place that
  goes out of scope at the `FrameEnd` of the call (F3-2, W0301).
- The old lowering stays in the `ir` pipeline (the checks of `typeck`). Its property query
  `Lower::closure_has` looks at each closure summary one time (a visited set), so the
  Q3-2 repros check in less than 50 ms (`Work::closure_queries`).
- A function item as a value whose summary drops or holds a linear type argument stays
  with the old pipeline (`factgen::checks::item_value`, `check_item_value` of the old
  lowering; the facts have no node for it).
- Not done: a run as a task (W0405 of code of a caller, stage F18), the environment of a
  `Made` closure capture by capture (a wildcard environment can give a W0703 that the old
  pipeline does not give, `44_returned_fns`).

As built (plan stage F13, `analysis::summarize::stored_parts_of`, `transfer::put_values`;
group C stayed off until the review of the C shapes passed, and F13 part 2 put it in the
default set):

- Part `stores` of a function body has two halves. The signature gives the references
  that go behind a reference parameter (R3RT6, F10.2, as before). The body gives the
  heap slots of the interface places at its `Return` (`Summary::puts`, `put_fns`): a slot
  of an `rc` object (its references), and each slot with function values (the values in
  interface terms, `RetFn`, with the places of their environments, as part `ret`). A
  closure summary gets `put_fns` for its slots too. A function that stores a closure has
  its effects in its row, as a function that gives one back (`summarize::made_effects`,
  W0701, W0703 as the old inference).
- At a run node (an item call, a value of an item, a closure) the caller maps `puts` and
  `put_fns` with σ: the references go with the part `stores` (a weak definition of the
  holder; the W0204 store check gets them), and the function values join the move path of
  the place, or its heap slot (`transfer::apply_put_fns`). `RetFn::Param(i)` gives the
  values that argument `i` reaches.
- A foreign function that changes an `rc` object can put each argument there
  (`sig::foreign_group_puts`, as `Lower::group_stores_of`); before F13 it stayed with the
  old pipeline, and so did a function whose old signature had `group_stores`.
- Part `reads` gets the reads of a place of an `rc` object (the summary oracle found that
  `run_hook(h)` read `Hook.f` with no `reads` place for it).
- `reaches` (a callee that can run a stored value that its arguments reach) is the part
  `runs` of a value inside or behind a parameter: the caller applies the values that the
  argument reaches, the heap slots included. Plan deviation: there is no
  `analysis/heap.rs`; the slots are in `domain::State` (F10a), cut by the widening of the
  places that α gives.

### 6.8 Effect inference and signatures

Effect rows are a part of the summaries: the effects that a body performs through `Row`
capabilities, directly or through a callee whose capability resolves to `Row` at the call.
The fixpoint of 6.6 is the effect inference. It needs no re-lowering of a body. The parts
start empty and only grow, so `parts_limit` and W0704 go away; W0706 stays as a guard: a
row that grows past the height of its lattice shows a bug.

`analysis::sig::to_effect_sig` projects a summary onto the `EffectSig` of today, for its
users outside fact generation: W0701 (a public function states less than it infers),
`weft deps` (W0901, W0902), the `pins` part that the interpreter reads (ADR 0010). The gate
compares this projection with the `EffectSig` of the old pipeline for each function
(stage F6 of the plan), as a check of the inference.

As built (plan stage F6): `analysis/callgraph.rs` is the fixpoint of 6.6. The graph
links each function body to each function item that a `Call` in its component names
(stage F11 and later add closures, clauses, continuations, tasks and `on abort`
functions). Tarjan's algorithm gives the strongly connected components, callees first.
Each summary starts with the stated row (or an empty row) and empty inferred parts
(`sig::Inferred`). A round runs the fact generator on each body of the component with
the summaries of now and joins the projection of its facts into the inferred parts. The
first round with no growth is the fixpoint; a component of one function that does not
call itself needs one round. The emit pass takes the facts of the last round of each
body. W0706: a row that grows more often than `infer::growth_limit` (the height of its
lattice) stops the iteration of its component, and each function of it gets W0706; the
`ir` pipeline drops the W0706 of the old inference. A body that the fact generator does
not support gives its callers a reason with the group of its construct; a function with
a stated row then keeps the summary of stage F5. A body with no IR (a type error) has
the summary of its signature from the old inference.

`sig::to_effect_sig` gives the changed places (a `Held` root is its parameter with a
first `Held` step; the text is the name of the parameter and the text of each step; a
place cut at 8 steps has the text `..` at the cut), the effects through `Row`,
`raises`, `multi` (only for an unknown function value), `drops` and `holds`. A
function with a stated row keeps its row. In the `ir` pipeline the signatures of the
analysis (`Analysis::sigs`, `BodyFacts::effects`) are these, so W0701, `weft deps` and
the interpreter read them; W0701 comes from them, with the text of the old lowering.
`weft-gate sigdiff` compares them with the old ones on each program in scope; each
difference needs a ledger entry of class `sig`.

As built (plan stage F13 part 2, group C on): `DEFAULT_GROUPS` is A, B and C, so the
`ir` pipeline checks closures, function values and stored function values by default.
The signature diff with the groups A to C has these classes (one `sig` entry each in
`tests/gate/ledger.toml`):

- The parts of the old inference for the function values of a body (`passthrough`,
  `lent`, `ret`, `stores`, `reaches`, `reach_given`, `reach_repeats`, `repeats`,
  `ret_refs`, `fn_stores`, `fn_store_refs`, `group_stores`, `tasks`, `task_runs`):
  `to_effect_sig` does not give them. The summary holds the same facts in its parts
  `runs`, `ret`, `puts` and `put_fns` (6.7), and the `ir` pipeline applies the summary
  at each call. This is most of the difference (1813 of 1841 functions on tier 1).
- `multi` of a run of a function value that the body reads from a field or a
  parameter: the summary has the run in `runs`, and the caller applies the `multi` of
  the value that it gives.
- `muts` of a maker of a maker (`|| || w.entities.clear()`): the old inference puts the
  change of the made closure into the maker; the summary keeps it in the made closure
  (more precise).
- `named` of the old hole RR7 (a rebind of a captured function value): the `ir` summary
  has the effect, the old one does not.
- `muts` of `Sigma::others` (a function parameter that runs with two reference
  arguments changes both): larger than the old place set, sound.
- The text of a place (a segment step, a cut place with `..`), and a wider place at the
  cut of the summary (generated probes of tier 2, groups A and B).

The diff also found two holes of group C (follow-up F13.2 of the plan): an unknown
function value that runs in a body (a capture of a made closure that holds a function
parameter of the maker, `mk_call(push1, world)()`; a function-value local that a
closure gives a new value, `let set = || { g = grow }; set(); g(world)`) was code of a
caller, and its `lends_mut` of the reference parameter and of `a place of a caller` did
not reach the summary of the body. A caller of the body then missed the change
(`verify/p/v06_ret_paths.wf` `ret_passthrough` and the mutant `m01258_43_loops.wf`
`item_later_pub` showed it in the diff; the summary oracle failed on a caller).

As built (follow-up F13.2): the root cause is that the summary of a function body had no
part for code that the body runs and that no caller gives. Code of a caller of a value
of a parameter is in the part `runs`, and the caller applies the value that it gives
there. Code of a caller of any other value (`FnVal::Unknown`) changed the places of the
body only. Two values were code of a caller with no reason:

- A capture of a closure that a callee made (`Made`). The closure holds the values that
  it runs in its own value (`summarize::fn_parts_of` puts the values of each `Kept`
  capture into the part `ret` of the maker). A run of a capture now runs each of these
  values with the places of the run (`transfer::made_held`, through `apply_runs`); a
  capture that is not `Kept`, or a value with no known values, adds code of a caller.
  A node applies each value one time for the arguments of the call and one time for
  each set of places that a run gives it (`Apps::modes`): `f = mk_call(push1, w)`
  holds `push1` and is not `push1`.
- A local that a closure of the body gives a whole new value (part `rebinds`): the new
  value is the value that the closure puts into the capture (part `put_fns`), not
  `Unknown`.

The summary of a function body has the part `lends` (`Inferred::lends`): the interface
places of each `lends_mut` of a summary that the body applies with no entry of `runs`
(`Em::own_lends`): code of a caller of a value that the body does not know, a callee
or a closure that lends. The caller applies it at each call (`apply::main`). A closure
summary keeps these lends at a run node of `run_nodes` too.

A value that a closure runs through a capture changes the places of the environment of
the closure through that environment (`Sigma::env`): the change has the root of the
environment (`STORED`), as the places of `cap_helds`. Before, a closure of the body that
a callee runs (`let f = || g(world); call0(f)`) got W0312 against its own environment
(a false positive of the `ir` pipeline).

Each of the 5 repros and `f13p2/t/rb.wf` is W0301 at the line of the old pipeline, and
the clean twins are clean (probes `tests/gate/probes/fixes/f13d/`, claim F13D-UR;
test `crates/weft-check/tests/data/fn_values/unknown_runs.wf`). The signature of
`ret_passthrough` and of `item_later_pub` now has the change of the old inference.
A value that a callee gives to a run of a maker parameter (`fn rp2(m, w) { let f =
m(push1, w); f() }`) stays code of a callee for a caller of `rp2`: the part `runs` has
places, not function values, so a caller of `rp2` with a maker `mk_call` changes `w`
through code that it does not know (stricter than the old pipeline, sound).

### 6.9 Checks in Rust, and diagnostics

These checks stay outside the spec in the migration (ADR 0002 lists why), but they read
the IR and the analysis, not a surface walk:

| Code | Check over the IR |
| --- | --- |
| W0313 (capability) | At the end of the capability root of handler `h` (the `Dead` of the `Cap` local at the frame end of the handled body, and on each cleanup copy of its chain), a value that holds that root leaves: `_0` of the handled body, the value of a clause, a variable of the site that has a cell, a heap slot that a site variable or a parameter reaches, or a `stores` entry. Each leak is W0313 at the span of the `handle` expression, as today. An `error(R, P)` of the spec whose evidence free is a capability root folds into that diagnostic as a note (its fact key goes into `Diagnostic::facts`). This keeps the escape rule of `codes.rs` and the 61 corpus markers (feasibility judge, 3.2). |
| W0313 (continuation) | The same at the end of the continuation root (the frame end of the clause): a value that holds the root leaves through an upvar, `_0` of the clause, a store, or an argument of `resume`. The span is the leaking statement, as today. |
| W0314 | A task (a `Spawn`, a `Fork` branch, or the `tasks` and `runs` parts at a run node) holds or uses a capability or a continuation of a handler that is on the stack of another task. A query over the `tasks` part and the abstract values. |
| W0204 (local forms) | Not a Rust check any more: `uses(S(_0), Return)` makes the spec derive `error(_0, Return)`. `diagnose.rs` reports an `error` of `_0` at a `Return` node as W0204 for a function or a closure, at the span of the `Return` origin (the returned expression, V18). In a handled body, a scope body or a clause, the same `error` is W0301 with the text "the value leaves after its place ends". |
| W0204 (store forms) | A `stores` entry of a reference into a root that ends at an exit, behind a reference parameter or into an `rc` object. A query over the summary of each body, also of closures and clauses (V087, V108, FD3). |
| W0204 (signature) | A returned reference must state its place. A signature check. |
| W0118 | A query over the summary of the `on abort` function `f`: its changes are below its parameter value (F3-1); its row holds only effects that the root handlers serve; its `raises` part is empty; its `drops` part holds no type parameter of its parameter type (F3-3, F3-4). As built (F7): `factgen::checks::on_abort_rows` projects the summary with `sig::to_effect_sig` and gives the texts of the old check (`program::on_abort_row`); a function with no summary keeps the row of the old inference. An emit that gives no rows keeps the W0118 of the old inference. |
| W0315 | a builder diagnostic (5.36) |
| W0303 | the old lowering; the body gets no IR (5.36) |
| W0604 | the spec rule `moved_immovable`; the fact generator sets the `immovable` flag (5.36, 6.3) |
| W0502 (into plain data) | `typeck`: a `once` closure goes into a place of plain data |

As built (plan stage F13, the W0204 store forms): the check (`factgen::stored_behind`)
reads the stores of each body of the component, also of the instantiated closure bodies,
and the stores that a run node applies (parts `stores`, `puts`, `put_fns` of a callee or a
closure). A reference into the cell of a local that a closure captures `ByRef` counts as a
reference into the local ("puts a closure that captures `v`"). A handle place `h.*` of the
handle of the store itself is no local: the reference goes away with the object
(`fill_self` of `tests/programs/116_rc_stores.wf`, as `check_stored_behind`).

As built (F13-fix, classes AB-RC1 and AB-RC2 of the review of stage F13): the template of
the store gives the handle places through which the store reaches the object (`al.handles`
of the destination, the handles `σ.deps` of the argument of a callee;
`templates::rc_handles`), and the check skips only those. A handle in a local `Vec`, struct
or tuple (`hs[0].data[0]`) is no handle of the object: W0204, as the old lowering (F13 part 1
skipped each handle of the same `rc` type, a regression). A whole local handle of another
object (`let d = newc()`, an `Option` payload, a second by-value handle parameter) is W0204
too: the old lowering skips each whole local handle of the same type and misses the dangling
reference. This is stricter than the old pipeline when the other handle is a handle of a
living object (`other(c, d)` with `d` a handle that the caller keeps; two local objects of
`main` that point into each other). A whole local handle whose value can come from the same
local or parameter as a handle of the store (`let d = c.clone()`, `transfer` gives the clone
the place of `c`) can be a handle of the same object: the facts cannot tell, so the program
goes to the old pipeline ("a reference through a copy of an `rc` handle"). As built (class
AB-RC1-join of the final check of group C): a handle of the store is the handle of the object
only if each other handle of the store is a handle of the same local. A store through a
reference that can reach the object of the caller and a local object (`let x = if b { &c }
else { &d }; x.refs.push(&d.data[0])`, the same through an `Option` or a loop) is W0204
when the sources of the other handle and of `d` are disjoint, and goes to the old pipeline
when they share one. Stricter than the old pipeline by design (class AB-RC1-copy-strict of
the final check of group C): a copy of a local handle that the facts do not follow to the
store (`let keep = h.clone()` and then a store into `h` of a reference through `keep`; `let d
= same(c.clone())` through a callee) is a handle of another object, so W0204, also when it
is a handle of the same object at run time. A store with no
known handle (the `puts` of a callee with a by-value handle argument, a closure) keeps the
rule of the old lowering; such a callee also gets W0312 for an argument that points into the
group. The references of the part `puts` flow from the values of the arguments with their
handle places (`apply::vplaces`), as the part `stores`. A new
check, `factgen::kept_escapes`, gives the late values of `Kept` captures: a closure that
the function gives back or puts into a heap slot of an interface place sees the value of
each variable that it keeps at the `Return`, and a reference there into a local is W0204
(at the returned expression, or at the closure literal for a store). The value of the
closure keeps the references of the variable where the closure is made only (class K3 of
stage F12), so the facts alone did not see `r = &w.entities[0]` after `let f = || print(r.hp)`
(`fixes/f13/kept_rebind_ret.wf`, a hole of ABC before F13).

As built (F13-fix, class K3-Made of the review of stage F13): the check and the summary
part `ret` follow a closure that a closure of the body makes (`FnVal::Made`) and a capture
of a capture (`env.j`): `apply::made_capture_source` gives the variable of the body that the
capture shares through the `Kept` and `ByRef` captures of the makers, and its value at the
`Return` counts (`kept_escapes`, `summarize::fn_parts_of`). So `let m = || || print(r.hp);
let g = m(); r = &w.entities[0]; g` is W0204, and with `r = &b.entities[0]` (a parameter) the
result points into `b.entities[]` too: a caller that clears `b` before the run is W0301
(the run of the result read the late value, and the summary oracle failed on the clean
twins).

As built (plan stage F8a): `_0` has the variable kind `Result` (`weft-facts`), and its
name tells the frame: `the result` (a function or a test), `the closure result`,
`handled body value`, `scope body value`, `clause value`. An `error` of `_0` at the
`return` node whose cause is the end of a local is W0204 for the first two (the text of
the old lowering; a by-value parameter that the signature states as a returned place has
only the W0204 of the signature check, so `ret` keeps the node of the stated places also
when each returned reference is into a local), and W0301 "the value leaves after its
place ends" for the others. The `Dead` of a parameter of a function or a test has the
span of the function, as the end of the parameters of the old lowering: W0601 of a
parameter is at its declaration.

As built (plan stage F8): group A is on by default (`weft_sema::DEFAULT_GROUPS`, plan
§2.6). The review of the `lost-clean` programs found three holes, fixed in F8:

- H1: two operands of one call or aggregate on one local. The builder gives the moved
  operand a temporary (5.1.1). In `emit`, a bind of a part (a `Temp` or a local whose
  origin is the statement) keeps its `uses` of `S(l)` if its path overlaps a part that an
  earlier bind of the same run moved: `_3 = move s.items; _4 = &s.items` is W0302.
- H2: the tail place of a discarded block moves (5.4).
- H3: a read through a value that can hold a reference to a value that holds a
  reference (`**r` with `r = &t.1` and `t.1: &u64`) uses the variables of the owners
  of the places that the value points into (`templates::deep_uses`): at `print` and
  at each argument of a call. So the end of `b[]` in
  `let t = (5, &b[0]); let r = &t.1; b.clear(); print(r)` makes the read W0301 (both
  pipelines accepted it before).

As built (plan stage F8c): the second review of F8 found that H3 went down one level
only, and only at `print` and at call arguments. Both pipelines accepted the programs
(open for the old pipeline).

- N1: `deep_uses` follows the chain of references to a fixpoint. It starts at the
  places that the value of the operand points into. For each place it reads the places
  that the references in that place point into (`transfer::held_at`, the state before
  the node), and visits each place one time (a visited set; the cost is linear in the
  places of the chain). Each place on the chain that holds a reference gives `uses` of
  the variables of its owner (`S` and the `H` and `U` variables on its path). The last
  place (the data that the read gets, `b[]`) gives no `uses`: no reference of it is
  followed. A chain of more than 4096 places is `Later` (the old pipeline checks the
  program). So `t = (5, &b[0]); u = (6, &t); r = &u.1; b.clear(); print(r)` is W0301
  (`r -> u.1 -> t -> t.1 -> b[]`), also with `Option` or `Vec` between two references
  and in a callee that reads `x.1`.
- N2: a read of the whole value through its references (`templates::read_through`:
  `reads_at` of the places of the value and `deep_uses`) is at each `print` operand, at
  each part of an interpolation (`Concat`, 5.16), and at each operand of a `Binary`
  (a comparison of values that hold references, `u == u`, reads through them; a
  scalar operand holds no reference and gives nothing). A call argument and a `perform`
  argument get `deep_uses` (the callee or the handler can read through them).

The entry node of a component is node `n0`, as in the old lowering: the hypothesis
`bound_before_use` of the proof link starts there.

Tier 2 of stage F8 found two false positives of the facts of group A, fixed in F8:

- The `Consume` of a part (a variant with no payload in a pattern) is a moved part of
  the run of the pattern, so a later bind of another part does not use `S(l)`
  (`(None, Some(b)) => ..` gave W0302).
- `rest_linear` of a part move leaves out the parts that moved before (the holes of the
  state) and the moved part, by type: `let (a, b) = p` ends `p` at the move of `p.1`
  (it gave W0601, because the top of the value of a parameter keeps the whole value). A
  move of an element (`a[0]`) leaves the other elements.

`diagnose.rs` names a variable by its local and a temporary by its kind and origin
("the temporary of `mk_v()` at line 3"). The corpus markers keep their lines: the spans
come from `Origin`. Where a marker moves (a hidden variable of today becomes a temporary
with the span of its source operand), the ledger of the gate records the reason.

### 6.10 Worked traces

**M3** (section 5.37). The perform `P` in `bb2` of the handled body aborts to `h`,
because the clause of `pick` has no resume point.

```text
P.Main        performs_at(P, cap_h); call_arg(P, w, param0); may_abort(P)
              (clause pre: reads (*v)[] -> reads_at(P, w[]))
P ──► P.AbortValue(h) = a
              rebound_at(r, a); points_into(r, w[])        (clause value &v[0], v -> &w)
a ──► cleanup copy for h:  Dead(_5) ; UnwindValue(_2 = w, Drop) ; Dead(w) = c
              unwound_at(w, c); owner(w, S(w)) -> frees_at(c, w) -> invalidated_at(r, c)
c ──► ... ──► n.Landing ──► main.bb1:  Print(copy r)   uses(r, q)  -> error(r, q): W0301
```

Today the checker accepts this program, and the oracle faults. The soundness judge
checked this trace with `spec/weft.dl` (`ir/judge_sound/m3_machine.dl`).

**M1 and J1.** The clause is `let x = resume(()); v.clear(); x` (M1), or `resume(());
v.clear()` with the body keeping `keep = &v[0]` in a site local (J1). At `Exit`, `r`
binds to `v[]` (the body value). At `Post`, the post part applies: `v.clear()` changes `v`
below an unstable step, so `mutates_at(post, v)` invalidates `r` (M1) and `keep` (J1).
The uses after the `handle` are W0301. In M1 the clause component also has the error:
`x` gets the places of `_0` (`ResumeResult`), the clear invalidates it, and `_0 = move x`
uses it (`ir/judge_sound/j1_machine.dl`).

**J3.** The clause is `let x = resume(()); &u[0]`. `Exit` binds `r` to the places of `_0`
and of the clause value (`u[]`). A later `u.clear()` invalidates `r`: W0301.

**O3-14 and J4.** A `multi` handled body ends with `_0 = move u` of an upvar local `u`.
The re-entry edge goes from `Post` through `P.Copy` to `P.Ret`. `u` is a site local,
outside the copied frame, so `Copy` does not rebind it, and the second `move u` sees
`moved`: W0302. In J4, `r = &o[0]` of a site place: `Copy` does not rebind `r` (its places
are outside the copied frames), so the clear of the first run invalidates it for the
second run (`ir/judge_sound/j4_machine.dl`).

**J5d.** `make` returns `|| print(norm(&p))`. Rule CAPTURE gives `ByRef`, so the closure
value points into the cell root of `p`. The frame end of `make` ends `p`
(`scope_end(C(p))`), and `Return` uses `_0`: `error(_0, Return)`, W0204.

**F3-2.** `fn apply(f: fn(&u64)) { let x = 5; f(&x) }; apply(|r| last = r); print(last)`.
The summary of `apply` runs `Param(0)` with the place `Frame` (its local `x`). At the call
node `n` in `main`, σ maps `Frame` to `F(n)`. The closure assigns `last` (a `ByRef`
capture) the argument places, so `last` gets `points_into(last, a local of apply)` at
`n.Ret`. `n.FrameEnd` ends `F(n)`, so `print(last)` is W0301, with no node that binds and
frees `last` at once (`ir/judge_sound/f32_machine.dl`).

**O3-2.** `let r = handle Note { .. } in { first(&mk_v()) }; print(r + 1)`. The temporary
of `mk_v()` ends at the frame end of the handled body, after `_0` got the value and
before `Return`; `Exit` uses `_0`: W0301 (`ir/judge_sound/o32_machine.dl`).

---
## 7. The invariants and how each one holds

The invariants are those of `docs/plan/core-ir-inputs/map_lowering.md` section 5. "Construction" means: the IR
has no form for the violation; the verifier and one template give the invariant. "One
rule" means: one function of the analysis or of the summary procedure gives it, so no
construct can forget it; the function itself can still be wrong, and the oracles of 8.5
and the claims test aim at it. "Spec" means: a rule of `spec/weft.dl` gives it.

| Invariant | Status | How |
| --- | --- | --- |
| A1 path cover | construction (abort and re-run edges of a call: one rule) | the CFG of the IR is the code that the interpreter runs (section 8); `unwind` edges, splices and re-entry edges are explicit; trace conformance tests it on runs (8.5) |
| A2 components | construction | one component for each body that can run at many nodes; once-run frames are spliced (V15) |
| A3 run-node cover | one rule | `apply` at each run node (6.7); each part is a projection of all relations, and `RELS` has a row for each input relation |
| A4 order inside a node | construction | one instruction for each node; the phases in a fixed order (6.2) |
| A5 `no_gen_kill` | construction | a right side cannot change memory; a result binds at `Ret` and its frame ends at `FrameEnd`; `Exit` binds and `Post` changes; `AbortValue` binds and the cleanup copy frees; a drop pair binds at `Drop` and ends at the next node |
| A6 `bound_before_use` | construction | V4 for each component: each use has a cell on each path; each component binds its parameters, environment and continuation at its entry |
| B1 interned tree | construction | the place interner (unchanged) |
| B2 typed stability | construction | α takes the stability from the type of each projection (V8) |
| B3 root truth | construction | the roots of 6.3; the caller, callee, clause and handled-body frame roots name the frames that a body cannot see |
| B4 wildcards | one rule | the widening of the analysis and the cut of summary places |
| B5 split ids | construction | `SplitId` in the projection |
| B6 handle places | construction | `Deref(Rc)` in the path; α adds `h.*` |
| C1 points-into cover | one rule | the transfer functions; the `ret` and `stores` parts; the caller frame rule (N1, N2); instantiation of component roots (6.5) |
| C2 holder cover | construction | each value in transit is in a local with storage (V12); a frame value is in `_0` until `Ret` or `Exit` |
| C3 rebind hygiene | construction | a value binds where it exists: `Ret` before `FrameEnd`, `AbortValue` before the cleanup, `Exit` before `Post` (M1, M3, M4, O3-2, O3-3) |
| C4 free cover | construction | each free is a `Dead` (always `scope_end`, V6), a move, a `Consume`, an `UnwindValue` or a cleanup `Dead`, a summary `frees` part, or the end of a frame root at `FrameEnd`, `Post`, `Landing` (F3-2, M4) |
| C5 change cover | one rule | `Assign` through `Deref`; summaries; `lends_mut` of code of a caller |
| C6 `writes_via` exactness | one rule | the `Assign` and `Call` rule of 6.4 (`only_self`) |
| C7 part moves | spec | the R3a rule of `invalidated_at` (F3-5); the IR gives `moved_part` for each part move |
| C8 references behind references | construction | a second `Deref` in the place; `call_arg` of each place that an argument reaches (R3RT2, R3RT3) |
| D1 move cover | construction | `Move` operands; tails are moves; `Consume` |
| D2 new values | construction | `Assign`, `Ret`, `Exit`, `AbortValue`, `Copy`, the entry of a component |
| D3 normal ends | construction | `Dead` on each normal path out of each scope (V6) |
| D4 suspension cover | construction | each terminator with `can_abort()` has its `unwind` (V10): `Assert`, `ScopeWait`, `Join`, `Fork` included (N4, F3-7); the abort bit of a call comes from its summary (one rule) |
| D5 linear holders | construction | each linear value is in a local with the `linear` flag; task results with no handle are `TaskResult` locals (O3-4) |
| D6 flags | construction for the IR; a type rule for `Task<T>` and `on abort` | props from the final type; I3-1 and F3-6 stay type rules |
| D7 unset values | construction | `Uninit` of each place field from the full type, keyed by the full type (Q3-1, V062) |
| E1 `multi` cover | one rule | `multi_at` from the operation, the summary and the clauses (resume points on the CFG) |
| E2 re-runs | construction | re-entry edges for each `multi` node, for local handlers and handlers of a caller (OL-R2a) |
| E3 `spared_at` | construction | the abort destinations and the cleanup copies (6.5) |
| E4 `once_var` | construction | props |
| F1 `spawned_at` | construction | `Spawn`, `Fork`, the `tasks` and `runs` parts at run nodes |
| F2 `joined_at` must | one rule | the must part of the task state |
| F3 task footprints | one rule | the task body summary; heap slots for stored values (O3-5); the handle in the path (O3-6) |
| F4 parent accesses | construction | operands, `ptr` reads and destinations |
| F5 `kept` | construction | `Kept` captures only, and V13: no reference into a kept cell |
| F6 pinning facts | one rule | the environment fields and the `tasks` part |
| G1 effects | one rule | capability resolution through `CapArgs` |
| G2 call roots | construction | one `call_arg` rule for every call form |
| G3 caller changes | construction | α roots `Param` and `Group` |
| G4 call checks | construction | the `Call` and `Perform` templates (R3RT7: an operation parameter with `in` gets `param_in`) |

The hypotheses of the proof link (`proofs/link/README.md`) map to these invariants:
`facts_ok` (`cfg_wf`: A1, A2, V1 to V3; `instr_groups_ok`: C1, C3 and, after reference
versions, one group for each variable), `bound_before_use` (A6), `no_gen_kill` (A5),
`typed_by` and `alias_exact` (B2). Section 9 gives the link steps.

---

## 8. The interpreter and the run-time semantics

### 8.1 The interpreter compiles the IR

The interpreter keeps `machine/` (frames, handlers, continuations, the unwinder, the
scheduler, the oracle). A new module `crates/weft-interp/src/compile_ir.rs` translates
each body to one `Code` unit of the stack code of today. It replaces `compile.rs` (1 544
lines) at the end of the migration.

| IR | Stack code |
| --- | --- |
| `Body` of kind `Fn`, `Test`, `Closure`, `Clause`, `Handled`, `Scope` | `Code` of kind `Fn`, `Test`, `Closure`, `Clause`, `HandleBody`, `ScopeBody` |
| a local | a user local, a parameter and `_0`: a slot; `Live(l)` is `BindEmpty(slot)`; `Dead(l)` is `DropSlots([slot])`. A temporary: a temporary cell of the frame (the `temps` list of `CodeFrame`); `Live(t)` pushes it, `Dead(t)` ends it (a new op `EndTemp`). So before stage I6 `frame_values` unwinds the temporaries newest first and then the slots, as today |
| an upvar local | `Var(Cap(k))`: the captured cell; `Handle` and `Scope` capture the cells of the upvar locals of their bodies |
| `Assign(p, rv)` | the ops of `rv`, the ops of the place `p`, `Store` (it drops the old value) |
| `Drop(p)` | a new op `DropPlace`: drop the value at the place and leave `Moved` |
| `copy p`, `move p` | the place ops, `Read` |
| `Ref(p)`, `Ref(p[])` | the place ops, `Borrow`, `BorrowAll` |
| `Deref(_)` | the place ops follow the pointer (`Field` and `Index` already do; a new op `Deref` for a bare dereference) |
| `(*env.k)` and `env.k` in a closure | `env.k` is `Var(Cap(k))`: the owned cell of a `ByMove` or a `ByRef` field, or the cell that a `Kept` field shares with the maker. A `ByRef` field holds the reference that its operand `&x` made, so `(*env.k)` adds `Deref`, and the oracle checks each read through it after the end of `x` (rule CAPTURE, 8.3) |
| `Binary(op, ty, a, b)` | `a`, `b`, `Bin(op)`, `CheckInt(ty)` |
| an aggregate | `Tuple`, `MakeVec`, `MakeStruct`, `MakeEnum`; a closure is `MakeClosureIr` with the shared cells of its `Kept` operands and cells of its own for its `ByMove` operands (the moved values, in the `owned` list) and its `ByRef` operands (the references) |
| `Uninit(l)`, `Uninit(t.f)` | nothing for a whole local after `BindEmpty`; `MakeStruct` leaves `Moved` in a place field that the literal does not give, as today; nothing for the place field paths of a parameter at the entry (the path can name a variant that the value does not have) |
| `Unary(op, ty, a)` | `a`, `Neg` or `Not`, `CheckInt(ty)` |
| `Concat(ops)` | each operand, `ToStr`, then `Concat` |
| `Iter(Elems(p))`, `Iter(Range(a, b))` | the place ops and `ElemIter`; `a`, `b` and `RangeIter` |
| `Len`, `Discriminant` | new ops `Len` and `Tag` |
| `Switch` | `JumpIfFalse` for a `bool`; a new `JumpTable` for an integer or a tag |
| `Call`, `Perform`, `Resume` | `Call`, `CallValue`, `Perform`; `Resume` is `CallValue` of the continuation |
| `Handle`, `Scope`, `ScopeWait`, `Fork`, `Assert`, `IterNext`, `Print` | the ops of the same name |
| `Spawn`, `Join`, `Detach` | the natives of today, with the arguments as operands |
| `Bounds` | a new op `Bounds` (today `Index` checks the bounds) |
| `Consume` | a new op `Consume`: end the linear record of the value (today inside `Unstruct`) |
| `Mention` | the place ops, `Pop` |
| a back edge | `Jump` and `BackEdge` (the preemption point of the scheduler) |

What goes away at the end: the span-keyed exports `FnFacts::by_value`, `arg_order` and
`int_ops` (they are in the IR); `StmtBegin` and `StmtEnd` (each temporary ends at its
`Dead`); the operand stack holds values only inside one IR instruction.

Each compiled op carries its IR location (`BodyId`, `BlockId`, statement index) for the
trace conformance and the fact oracle.

As built (plan stage I1, `compile_ir.rs`):

- The parameters get the first slots (the frame puts the arguments there), then `_0`
  (`BindEmpty` at the entry), then the variables and the iterators, then the
  temporaries. A slot of a temporary holds a temporary cell: `Live(t)` is `LiveTemp`,
  which also puts the cell on the temporary list of the frame, and `Dead(t)` is
  `EndTemp`. `Code::temp_slots` tells the unwinder and the frame end to find these
  cells on the temporary list and not with the slots. So before I6 the unwinder sees
  the temporaries newest first, then the variables from the highest slot, then `_0`,
  then the parameters.
- A `Field` or `Variant` step of a place is the new op `Part` (the index of the part
  of a struct, a tuple or a payload): `Field` of the AST compiler finds a field by name
  and follows pointers, and a payload has no name. The `Unreachable` of a failed test of
  a payload place (`o.Some`, 5.8) faults with "this value is another variant"; each
  other `Unreachable` faults with the message of a `match` with no arm.
- As built (F8d): a `Variant(v)` step of a place is the op `Variant(v)`. It checks the
  tag of the value at the place again and keeps the place; another variant stops the
  run with "this value is another variant: it has no such field" (the text of the
  failed `o.Some` test). Before F8d the step added no op, because the `Switch` before
  it tested the tag. But an operand can run between the test and the access: the
  receiver place of a method call is tested before the arguments and read after them
  (5.19). An argument that gave the base another variant made the engine read or write
  the payload of the other variant as the wrong type (third review of F8, R1:
  `e.A.plus({ e = Two.B(..); 0 })` printed a field of `Two.B`). The checker rejects
  these programs (6.3, `W` variables); the op is a second guard. It logs no read, as
  `Part` logs none.
- `move p` is the new op `Take`: it moves the value out also when the value is a copy
  value at run time (`Read` copies it). `Return` takes `_0`. So a `move` of a large
  plain value (a deep enum of integers) does not copy it.
- `Uninit` adds no op. The fields that a struct literal does not give (the `Uninit`
  statements after its aggregate) get no value in `MakeStruct`, as with the AST
  compiler.
- A `Switch` on a `bool` local with one arm for 0 or 1 is `JumpIfFalse` or
  `JumpIfTrue`; each other `Switch` is a `JumpTable` (a `bool` value is 0 or 1). An
  edge to a block at or before its own block in the reverse post-order is a back
  edge: `BackEdge`, then `Jump`.
- The cleanup blocks are not compiled before I6. A call (`Call` with the function of
  the analysis), a perform through the row (`Perform`), `IterNext` and `Assert` store
  their result into the place of their destination with `Store`.
- A program whose IR has a handler or a task, or a body with no IR, falls back to the
  AST compiler; `RunOutcome::fallback` (and the note of `weft run --engine=ir`) names
  the construct and the plan stage (I3 or I4).

As built (plan stage I2, closures and function values):

- A closure body is a `Code` of kind `Closure`. Its environment local `_1` gets no
  slot and no argument: the parameters after it get the first slots. A place
  `env.k` is `Var(Cap(k))`, the captured cell `k` of the frame, and the steps after
  `env.k` are the place ops (`(*env.k)` adds `Deref`). The environment as a whole is
  never a place.
- A closure value is the new op `MakeClosureIr`. The compiler reads the mode of each
  capture from the `ClosureDecl` (no `FnFacts::by_value`), and pushes one operand for
  each field: for a `Kept` capture the place of its operand `copy x` (no `Read`), so
  the closure shares the cell of `x` (or the cell that `(*env.j)` names); for a
  `ByMove` capture the moved value; for a `ByRef` capture the reference that `&x`
  made. The op puts each value into a new cell of the closure. Only the cells of the
  `ByMove` captures are in the `owned` list of the closure value: a call takes their
  values (a `once` closure, as with the AST compiler), and the unwinder finishes
  their linear values. The cell of a `ByRef` capture is not in `owned`, so each call
  reads through the reference, and the oracle sees a read after the end of `x`
  (J5d).
- A closure value is a copy value at run time: a `copy f` shares the closure (the
  same cells), it does not clone it. So a `Kept` capture of a local that holds a
  closure calls the closure that the local has at the call (B12 probe
  `late_once_capture`).
- `Const::Fn(f, _)` is `FnValue(f)`. A call of a function value is the callee
  operand, the arguments, then `CallValue`; the result goes to the destination as
  for `Call`. A function item that is an intrinsic (`sim.run`, `with_timeout`) is a
  construct of stage I4.
- A `Cap` or `Kont` capture was a construct of stage I3 (see below). An
  environment view (an upvar local of the environment, 5.1.7) is only in a
  handled body, a clause or a scope body.

As built (plan stage I3, handlers and continuations):

- A handled body is a `Code` of kind `HandleBody`, and a clause is a `Code` of
  kind `Clause` (the names are the names of the AST compiler: "handled
  computation" and "handler `op`"). The capability local `_1` of a handled body
  is its one parameter: the `Handle` op gives the new value `Cap::Handler`
  (the effect and the handler instance) when `HandleSpec::cap` is set. The
  parameters of a clause are the operation arguments, then its `Kont` local:
  the perform gives the continuation value after the arguments.
- An upvar local has no slot. It is a captured cell `Var(Cap(i))` of the frame:
  the upvar locals of a body, in the order of their ids, get the captured cells
  in order. An environment view gets one captured cell for each field of the
  environment, so `u.k` is `Var(Cap(i + k))` and `(*u.k)` adds `Deref`. The
  `Handle` op of the site gives the frame of the handled body and of each clause
  the cells of the site locals: the slot of a local, or a captured cell of the
  site when the site local is an upvar local or a field of the environment. A
  read, a write, a borrow or a move of an upvar local is one of the site
  local. The upvar locals have no `Live` and no `Dead`.
- A `multi` resume copies the frames of the continuation as before: the slots,
  the temporaries and the owned cells of the handled body get new cells, and
  the captured cells (the cells of the site) stay shared (probe J4).
- A perform through a capability place is the new op `PerformCap`: the place
  ops and `Read` push the capability, then the arguments. The machine finds the
  handler in the lexical handlers of the frame, as for a perform through the
  row, with the effect of the capability. In a debug build an assertion checks
  that the handler is the handler of the capability, if the mark of that
  handler is on the stack of the task and has a clause for the operation.
- `Resume(kont, arg)` is the place of `kont`, `Read`, the argument, then
  `CallValue(1)`: a call of the continuation value. The result goes to the
  destination as for a call.
- A closure holds a `Cap` capture or a `Kont` capture of a `multi` operation
  (`copy`) in a cell of its own (`CapHold::Copied`): a call does not take it.
  A `Kont` capture of a `once` operation (`move`) moves into an owned cell
  (`CapHold::Moved`): a call takes it, so the closure runs once.
- The `Handle` terminator stores the value of the handled body, or of a clause
  that does not resume, into its destination, as a call does.
- After stage I3 only a program with a task, `sim.run` or `with_timeout` (I4),
  or with a body that has no IR, falls back to the AST compiler.

As built (plan stage I4, tasks, `sim.run` and `with_timeout`):

- A scope body is a `Code` of kind `ScopeBody` (the name of the AST compiler:
  "scope"). Its `ScopeCap` local `_1` is its one parameter: the `Scope` op
  makes the scope and gives the value `Scope`. The `Scope` op gives the frame
  of the scope body the cells of its upvar locals, as `Handle` does for a
  handled body (the slot of a site local, or a captured cell of the site,
  also for an environment view). `ScopeWait(_1)` is the op `ScopeWait` with
  the slot of `_1`. The `Scope` terminator stores the value of the scope
  body into its destination, as a call does.
- A `TaskResult` local gets a slot (`BindEmpty` at its `Live`), but it gets
  no value at run time: the scope keeps the result of the task, as with the
  AST compiler, and the frame end drops the empty slot.
- `Spawn`, `Join` and `Detach` are the native methods of the AST compiler
  (`CallMethod` with the names `spawn`, `join` and `detach`): the place of
  the receiver operand (`copy s` or `move h`), then the task operand of a
  spawn. The native method reads the scope capability or moves the handle,
  and a `join` that waits runs the op again. A spawn with no destination
  and a `detach` drop the value of the method (`Pop`): the scope keeps the
  task. The span of the task is the origin of the `SpawnDecl` (5.29), so the
  `stealable` mark of the checker is the same as with the AST compiler.
- `Fork` is the op `Fork`: the branch operands, and the origin of the
  `SpawnDecl` of each branch as its span.
- `sim.run` and `with_timeout` are calls of their functions (`Call`): the
  machine runs their native code. A missing `workers` of `sim.run` is the
  constant argument 4 of the IR (5.30).
- After stage I4 the IR compiler compiles each construct. A program with a
  body that has no IR (a type error, an error in a declaration, W0303 a move
  through a reference) still falls back to the AST compiler, and
  `RunOutcome::fallback` and the note of `weft run --engine=ir` name the body
  and the reason. DECISION: `--engine=ir` does not refuse these programs. The
  checker rejects each of them, so their verdict does not depend on the
  engine; with the fallback, `weft run --unchecked --engine=ir` and the
  engine differential (plan stage I5) still run them, and they show as
  "fallback", not as a difference.
- The preemption points of the scheduler are the same (`BackEdge`), but the
  IR engine runs more ops between them, so a quantum ends at another point.
  The output of a program whose output does not depend on the schedule is the
  same; the trace (`Run`, `Preempt`, `Steal`) can be different.

### 8.2 Landing pads

Today the unwinder finds the values of a frame at run time (`frame_values`,
`extract_linear`). With landing pads, each `Code` has a table from the pc of each op with
an `unwind` block to that block. The unwinder runs the `UnwindValue`, `UnwindKont` and
`Dead` ops of the block in unwind mode (root handlers only, as today), then leaves the
frame at `UnwindExit`. So the order and the content of an unwinding come from the IR. The
scan of today stays as an oracle check: after the chain of a frame, no live linear value
is left in its cells (it also finds the closure cells of I3-2).

As built (plan stage I6):

- `compile_ir` puts the cleanup blocks and the `UnwindExit` block of a body after the
  blocks of the normal paths. `UnwindValue(p, a)` is the op `UnwindValue` with the slot
  of the local of `p` and the steps of `p` (`Part`, `Variant`, `Deref` of a `Box`,
  `Elems`); `UnwindKont(k)` is the op `UnwindKont` with the slot of `k`; `Dead` is
  `DropSlots` or `EndTemp`, as on a normal path; a `Goto` is a `Jump` (a chain has no
  back edge, so no preemption point); `UnwindExit` is the op `UnwindExit`.
- `Code::pads` is the landing-pad table: for each terminator with an `unwind` block, the
  op of the terminator that can abort the frame (`Call`, `CallValue`, `CallMethod`,
  `Perform`, `PerformCap`, `Handle`, `Scope`, `ScopeWait`, `Fork`, `Assert`) and the
  first op of its cleanup block. The code of the AST compiler has no table.
- When the unwinder gets to a frame of the IR, the aborting op is the op before `pc` (a
  call with a frame above it, an `Assert`) or the op at `pc` (a `ScopeWait` or a `join`
  that waits: they run again when the task wakes). If the op has a landing pad, the frame
  goes back on top of the task stack in unwind mode, at the first op of the chain, and
  the machine runs the chain as code. Else the unwinder scans the frame, as before.
- `UnwindValue` takes the live linear values out of the value at the place
  (`extract_linear`, so the action of the IR and the action of the run time agree: a
  linear value with no `on abort` is the fault of today) and runs their `on abort` in an
  inner unwinding above the frame, before the next op of the chain. So an `on abort` of
  `_0` runs while the locals of the frame still have their values. A place that names no
  value (a moved value, another variant, a `Deref` of a value that is not a `Box`) does
  nothing. `UnwindValue` of the `ScopeCap` local and of a `TaskResult` local finds
  nothing: the `Scope` mark below the frame cancels and joins the tasks, as before.
- `UnwindKont` aborts the continuation in the slot if it is fresh: its frames unwind in
  an inner unwinding, before the rest of the chain of the clause. The `Clause` mark below
  the frame of the clause then finds the continuation dropped and does nothing.
- A value on the operand stack of the frame at the abort is the result of the aborting
  op on its way to its destination: a handler gave it, and an interrupt that the
  unwinding deferred (a deadline, a cancel) aborts the frame before the store. The
  unwinder finishes it first, as the AST engine does with its operand stack.
- `UnwindExit` takes the frame off the stack. The scan of today (`frame_values`) stays as
  a check: it looks at the cells that the chain did not end and at the closures in the
  cells that it ended. With the oracle on, a live linear value there is the fault
  "oracle: a live linear value is left after the cleanup chain of `f`". The unwinder
  then finishes the value, as before. The captures that the first frame of a task owns
  are not locals of the IR: the unwinder finishes them at `UnwindExit` (no fault).
- The engine differential (plan stage I5) sees two new kinds of difference, and the
  ledger has them: the order of a clause (p20, class `unwind-order`), and a chain that
  runs an `on abort` before the fault at a linear value with no `on abort` (W0602
  programs: the AST engine finds that value first; class `unwind-order`). The fault "has
  no `on abort`" now has the line of the op that aborted the frame (class `fault-text`).
  The frame scan finds nothing on tiers 1 and 2.

### 8.3 Run-time decisions

| Decision | What changes at run time | Programs that see it |
| --- | --- | --- |
| an operand is read where it is written (choice A, 5.1.1) | the interpreter reads a place operand of a binary operator, of `print` and the base of an index at the operand | `x + { x = 5; 1 }` gives 2, not 6 (p1); a program that read through a dangling reference late (p2, p9, p10) reads before the change |
| the tail temporaries of a loop body end at each iteration (5.1.2) | earlier frees | `Weak.upgrade` of a tail temporary of a loop body (p24) |
| the tail place of the branch of an `if` with no `else` and of a loop body moves and drops (5.4, ADR 0003; stage F8) | the value goes away at the end of the branch | `if c { v }; print(v.len())` faults "used after it was moved" on both engines (before F8 the IR engine gave a `Mention` and ran it) |
| the temporaries of a branch of `if` or `match` end before the join (5.12) | earlier frees | `show(if c { first(&mk_v()) } else { &u })` reads a freed temporary: the oracle of the IR engine faults where the AST engine runs; the old checker accepts these programs (stage I5: 24 programs of tier 2, `r3/oracle/sweep1/*__tmp_*__arg.wf`, `R3a_diff/sweep/*ref_temp*`), so the `ir` pipeline must reject them |
| unwind order in a frame: `_0`, then temporaries newest first, then slots from the highest (5.1.6) | none: the AST engine unwinds the operand stack (the value of the frame and the operands on their way) first, then the temporary cells, then the slots. Before stage I6 the IR engine unwound `_0` with the slots, after the locals; from stage I6 the chain finishes `_0` first, as the AST engine does | the effects model changes `max_slot` |
| a clause unwinds its fresh continuation first (5.1.6) | the IR engine runs the chain of the clause, which starts with `UnwindKont` (stage I6); the AST engine unwinds the clause frame first. The engine differential ledgers this (class `unwind-order`) | p20: `rollback 1` (the continuation) prints before `rollback 2` (the clause frame) |
| rule CAPTURE (5.1.7) | a borrowed plain capture is `ByRef`: its cell ends with the variable | the oracle sees a dangling cell where today's kept cell stayed readable; the checker rejects these programs (J5, J5d) |
| `Dead` of a fresh continuation at a clause end | none (the interpreter drops it at the clause return today) | |
| a borrowed temporary of plain data ends at the frame exit (5.10) | none: a temporary cell of plain data keeps its value after its end on both engines, and the oracle does not mark it | `let r = &1; print(r)` |
| `&r` of a local `r` of reference type is a reborrow `&(*r)` (2.1, the THIR adjustment of a reference local used as a place) | `rr = &r` points where `r` points, not to the local `r`, so a later `r = &v[0]` does not change what `rr` reads | `let r = &u; let rr = &r; r = &v[0]; v.clear(); print(rr.hp)` (`probe/p3.wf` of the second review of stage F10): the IR engine prints the value of `u`; the AST engine reads `v[0]` through the local `r`, a freed cell. Both checkers accept the program (the old lowering takes the reborrow too). Stage F10.2: no program of tier 1 or tier 2 has the shape (the engine differential shows no such difference), so no ledger class is needed yet; a program with the shape needs one (or a change of the AST engine) |
| the unwind order of a frame: the slots from the highest (5.1.6) | while a frame unwinds, the IR engine runs the `on abort` function of a value before it frees an older local; the AST engine frees the older local first | `let l = L { o: Some(&v[0]) }; risky(1)` where the `on abort` function of `L` reads `v[0]` (`a/a91`, `a/a92` of the second review of stage F10): the IR engine runs clean, the AST engine reads a freed cell. Both checkers accept a91; the old pipeline rejects a92 (W0301, a false positive under the IR order). Stage F10.2: no program of the tiers has the shape (no such difference). The shape of the class `unwind-order` does not fit it (only one engine faults), so a program with the shape needs a new class (or a change of the AST engine) |

`docs/design.md` states the order of evaluation, the end of temporaries and the unwind
order (plan stage C3). ADR 0010 states that the interpreter runs the IR (plan stage C3).

### 8.4 New machine ops

`Deref`, `Len`, `Tag`, `JumpTable`, `Bounds`, `DropPlace`, `Consume`, `EndTemp`, and the
unwind-mode ops `UnwindValue`, `UnwindKont`, `UnwindExit`. Stage I1 adds three more
(8.1): `Part` (a part of a value by index), `Take` (`move p`) and `LiveTemp` (`Live` of
a temporary). Stage I2 adds `MakeClosureIr` (a closure with the modes of the IR).
Stage I3 adds `PerformCap` (a perform through a capability value).
Stage I6 adds the unwind-mode ops `UnwindValue`, `UnwindKont` and `UnwindExit`.
Stage F8d adds `Variant` (the tag check of a variant step, 8.1).
Each one has a unit test in `crates/weft-interp/tests/semantics.rs`.

### 8.5 Differential tests and oracles

| Check | Stage | What it compares |
| --- | --- | --- |
| D0 types | T3, R2 | the THIR tables against the types of the old lowering (T3: no inference variable, each callee resolved; R2: standalone `typeck` against the recorded tables) |
| D1 exports | I5 | the capture modes of the IR against `FnFacts::by_value` (expected differences: rule CAPTURE), the argument order against `arg_order`, the integer types against `int_ops` |
| engine differential | I5 to R4 | `--engine=ast` and `--engine=ir` on each program with `main` or tests, with `--oracle`, the six configurations of the harness (seeds and workers (1,1), (2,4), (3,2), (7,4), (11,1), (42,3)): the output, the exit status, the kind and line of each fault. Each difference must be in the ledger (choice A, loop temporaries, unwind order, captures) |
| trace conformance (A1) | F9 on | with `--ir-trace`, the machine records the IR location of each step. A checker tests that each two steps of one frame follow a `cfg_edge` of the facts of the component, also a splice, an abort path (the copy for the destination that the run took) and a re-entry |
| fact oracle (B6 hypotheses on runs) | F9 on | the machine maps each cell to a fact root (a slot to the root of its local; a slot of a frame that the component does not hold to `F(n)`, `K(h)`, `R(n)` or the caller root; a heap cell to the place on its ownership path; an `Rc` object to its group root). At each step: each free of a cell has `frees_at` at the node for a covering place (C4); each pointer that a used variable holds is inside a place of `points_into` of the variable (C1); each read and write of a cell has `reads_at` or `mutates_at`, `lends_mut` or a footprint at the node (C5, F4); each move has `moved_at` or `moved_part` (D1); each suspension with a live linear value in a frame that the abort can unwind has `may_abort` (D4) |
| summary oracle (A3) | F13 on | at each call of a body, the machine records the cells that the body changes, frees and reads, and the pointers in its result; a checker maps them through σ of the run node and tests that each one is inside the applied summary |
| agreement and lints | each F stage | `weft agree` on the IR facts; `proofs/link/lints/gen_kill.dl` and `unbound_use.dl` on each component (V4 makes the second one hold for closure and clause components too) |

**As built (I5).** D1 is `crates/weft-sema/tests/exports_parity.rs`, on each file of
tier 1. The `ByMove` captures of the IR, and a `Kont` capture of a `once` continuation
(operand `move`), equal `by_value`. One more difference is expected (class
`closure-copy`): the old analysis moves a capture that holds a function value when the
closure body reads the function value (a read of a function value is a move there:
`let g = fs[0]; let h = fs[0]` is W0302), and the IR copies it (B12b: a function value
is plain data in the IR). The test lists the 13 programs of tier 1 with such a capture;
all of them are programs that the checker rejects. `arg_order` is the order of the
parameters: the IR evaluates the arguments of each call in the order of the parameters,
and binds the arguments that `arg_order` names. The type of each `Binary` and `Unary` of
the IR is the type of `int_ops`; the key of a compound assignment is the span of its
value. D1 found no bug in the builder or in the exports.

The engine differential is `weft-gate engines --tier N` (`crates/weft-gate/src/engines.rs`).
It runs each program with `main` or test blocks in child processes (`oracle-run
--engine ast|ir --observe`), with the oracle and the six configurations, and stops the
runs of an engine after a fault, as the oracle cache does. It compares the runs
configuration by configuration: the output (standard output and `Log` output), the
status (how the run ends), the message and the line of a run-time error; the output of a
run that does not end is not compared. A program with a time limit on one side runs
again, alone. The checker results come from the baseline of the tier. Each difference
needs a ledger entry of class `engine` (`tests/gate/ledger.toml`): the entry names a
difference class, and the shape of the class must hold for the difference. A rule with
`checker = "rejects"` accepts a class on each program that the checker rejects; a
difference on a program that the checker accepts needs an entry that names the program.
The classes are those of 8.3 (`choice-a`, `loop-temps`, `branch-temps`, `unwind-order`,
`capture`) and the
ones that stages I1 to I5 found: `w0315`, `receiver`, `leak-at-dead`, `static-type-read`,
`race-before-dangling`, `race-read-first`, `schedule`, `dangling-moved`, `read-order`,
`mention`, `moved-read`, `moved-closure`, `closure-copy`, `fault-text` and `timeout`.
Stage F8e adds `variant-place`: the AST engine faults at each payload place of a
variant (`e.A`, `o.Some`), and the IR engine reads the payload (8.1).
From stage I5 the gate classifies the programs with the oracle of the `ir` engine
(`tests/gate/oracle-ir.tsv`).

**As built (F8e): references into an enum payload.** The payload of an enum value is in
place, as the fields of a struct are, but its layout depends on the variant. So the oracle
(`crates/weft-interp/src/oracle.rs`, `heap.rs`) ends each reference into the parts of an
enum value when the enum gets a new value: a write of the enum, or of a place above it,
also with the same variant. A write of a part of the payload does not give the enum a new
value, so a reference to another part stays valid (the rule for a struct). A reference to
the enum value itself also stays valid. A read or a write through an ended reference is a
fault: "a read of a part of an enum value that got a new value (a dangling reference)".
This is the rule of the facts: a variant step is unstable (6.3). The machine does it with
two marks. Each new enum value gets an identity (`EnumVal::id`; a copy and a move keep
it). Each new reference (`Borrow`, a pattern bind, a receiver, a part of a tuple or a
struct behind a reference) records the identity of each enum value that its path goes into
(`EnumMark`). Each read and each write through the place compares the marks with the
values there. The oracle is the same for both engines. Before F8e a reference into a
payload read the payload of the new variant as the old type with no fault (third review of
F8, `a15`, `b07`: the checker rejects them; the gate did not see the class).

**As built (F9): the fact oracle and trace conformance.** `RunOptions::fact_oracle`
(`weft run --fact-oracle`) runs the program on the IR engine and checks each frame of the
entry body of a component (`crates/weft-interp/src/oracle/facts.rs`). The input is
`weft_sema::factgen::components`: the facts of each component, made again with the
summaries of the fixpoint, so they are the facts that the checker reads (a test compares
them on the corpus), and the tables that map the IR to them (`factgen::Emitted`: the node
table, the roots, the variables, the versions of the parts, the entry node).
`RunOptions::ir_trace` (`--ir-trace`) records the IR location of each step of each frame.

- Trace conformance: when the location of the next op of a frame changes, the oracle
  keeps the nodes of the new location that a `cfg_edge` path reaches from the nodes of the
  old one. The path can go through the later phases of the old terminator and through
  nodes whose location has no op (a `Goto` that falls through, an `Uninit`, the entry
  node). An abort path goes from the terminator through its abort phases to the cleanup
  copy of its destination.
- The cell-to-root map: a slot is its local; a cell that a value of the frame owns (a
  `Box`, the buffer of a `Vec`, an `Rc` object) is the place of its owner with the step of
  the handle; the target of a reference in a parameter at the entry of the frame is the
  `Param` root of the parameter, a target behind it the `Held` root. α of the IR place
  gives the fact places; each IR place that reaches a cell gives its places. A place with
  no name is counted, not checked. In a frame of a closure body (F12-fix), captured cell
  `k` is `env.k` and the targets of the references in it are `(*env.k)` and below: α of
  the instantiated body names `env.k` with the places of the maker (the cell root of a
  `ByRef` capture, the place of the variable of a `Kept` capture), so C1, C5 and D1
  check the captured cells too (a move of a whole `ByMove` capture is a move of its `E`
  variable). A place through a `ByRef` capture (`(*env.k).f`) is the place of the
  source of the capture in the maker (`x.f`, `oracle::facts::through_env`), through
  each closure that makes the closure, and a place below a parameter of a function
  body starts at its `Param` root. Before F12-fix2 such a place had no name: a change
  or a read of a `ByRef` capture in a closure body was not checked (second review of
  the ABC preview, 5; tests `a_missing_*_of_a_borrowed_*` of `fact_oracle.rs`). A
  place behind a reference that a `ByMove` or `Kept` capture holds (`(*env.k).f` for a
  capture of a reference `x`) is `(*x).f` in the maker (F12-fix3, gap FO-G1 of the third
  review of the ABC preview: `fn go(w: &W) { let f = || w.items.push(10); f() }` was not
  checked): a parameter starts at its `Param` root, and a local of the maker names the
  `points_into` places of its variable (`Comp::s_any`; tests
  `a_missing_mutates_at_behind_a_captured_reference_*`). A deeper reference with no
  parameter still has no name (counted, not checked). The oracle reads the heap with `Heap::peek`: a look at a freed cell does not
  flag the memory oracle.
- C1: at the entry of each node, each reference that a used `S(l)` (the value of `l`
  outside the parts with variables of their own) or a used version of a part holds is
  inside a `points_into` place of the variable (at or below it by stable steps, or below
  the base of a wildcard place; a side of a split counts as the element step, as in the
  coarse embedding of the proof link). C2 (holder cover): when the run follows a
  reference that a local of the frame holds (a `Deref` of a place), the node uses a
  variable of the local. C4: the end of the cell of a local with a root (`Dead`,
  also in a cleanup chain) has `frees_at` of the root. C5: a write of a place that has a
  value has `mutates_at` or `lends_mut` at or above it, and a read has a `reads_at` that
  overlaps it. D1: a `move` operand of a value that is not plain data (by its IR type)
  has `moved_at` of the variable of its local, and a part also `moved_part`. D4: an abort
  that unwinds a frame with a live linear value has `may_abort` at the aborting node. The
  checks of a node take the facts of each phase of its location.
- Rules of the oracle: the read of `_0` at `Return` and a whole write of a temporary or of
  `_0` need no fact (the value goes to the caller; the facts rebind the variable); the
  read of the buffer handle of an array (the machine keeps the elements of an array in a
  buffer cell) is not a read of the facts; a cell that the op frees (the old buffer that
  the memory oracle moves) is changed by the write of its owner; a take inside a native
  function or a `Drop` is a write; a frame in unwind mode gets trace conformance and C4
  only.
- Defects that it found and that F9 fixed (`tests/gate/probes/fixes/f9/`): an access of an
  element of a `Vec` did not read the handle of the buffer (`elem_handle_read.wf`), a read
  through a chain of references read only the first place of the chain
  (`deep_chain_read.wf`), and a `Mention` did not read the pointers and the index locals
  of its place (`mention_index_read.wf`, a variant of the first review of F8). Each is a
  `reads_at` fact, an input of W0405 only (group E): no diagnostic of group A changes.
- `weft-gate fact-oracle --tier N` runs it on each program of the tier with `main` or
  test blocks that the `ir` pipeline checks and accepts, in the six configurations, with
  the memory oracle, and writes `target/gate/fact-oracle-tier<N>.md`. A failure of the
  fact oracle or of trace conformance fails the command.
- As built (F10a, loops): `weft-gate fact-oracle --groups LETTERS` checks the scope of
  more groups (the child processes get `--groups`), for the preview of a stage. Trace
  conformance needs no rule of its own for a back edge: the facts have a `cfg_edge` to
  the first node of the loop head, and `reach` follows it as any other edge (no trace
  failure on the loops of tier 1 with the groups A and B). A place below a wildcard
  place (`(head.next[]..).next`, after a walk widens) is anywhere inside the base of its
  outermost wildcard step, as `wild_at` of the spec says: C1 and C5 use that base. A promoted temporary in a loop gets a new cell at each `LiveTemp`, and the
  references of the earlier iterations stay in the old cells (5.10): the oracle keeps the
  old cell of each temporary that gets a new one (`FactOracle::retire`) and names it as
  the local, so C1 checks those references too (before, they were places with no name).

**As built (F13): the summary oracle (A3).** It runs with the fact oracle
(`RunOptions::fact_oracle`, `oracle::facts::FactOracle::check_summary`). An access of an
op of a frame is an access of each frame below it on the stack (at most
`SUMMARY_DEPTH` = 16 frames) that waits at a run node: the frame names the concrete place
with its own map (its slots, the cells that its values own, the targets of its parameters
and captures: that is σ of the run node), and the facts of its current nodes (the phases of
the run node, where the applied summary is) must cover it: a change (a write of a place
that had a value, a take) a `mutates_at` or a `lends_mut` at or above it, a read a
`reads_at` that overlaps it. A place that the frame cannot name (a local of the callee) is
not checked; a cell that the op frees and the buffer handle of an array follow the rules of
the fact oracle. A failure is a fault "summary oracle (A3)" (`weft-gate fact-oracle`
class `summary-oracle`). The frees and the pointers of the result are not compared here:
C4 and C1 of the frame check them at its own nodes. Tests:
`crates/weft-interp/tests/summary_oracle.rs` (a `muts` place and a `reads` place of an
applied summary, and a `muts` place of a closure summary, removed by hand at the run node:
the run fails; stored function values pass). It found one defect: part `reads` had no
place of an `rc` object (fixed, 6.7).

**As built (F13-fix): what the summary oracle checks, and what it does not.** The review of
stage F13 found that A3 did not check the parts `puts` and `put_fns` (a missing
`points_into` of the value that a callee puts into a place of the caller passed:
`so02`, `so03`, `so04` of the review).

- Now each write of a callee (also a write of a new place, such as `push`) whose value
  holds references (in its parts, boxes, buffers, and the captured cells of its closures)
  is checked against each frame below that can name the place
  (`FactOracle::check_put`): each reference that the frame can name is inside a
  `points_into` place of a variable that holds the place (a variable of the local that owns
  it, or a version of the heap slot that overlaps it; `Emitted::slots`). A closure that
  captures a local by reference points into the cell root of the local in the facts, and
  the run gives the place of the local: the cell root covers it (review rows `fc/c20`,
  `fc/c21` of stage F12 failed the first form of the check). Tests:
  `crates/weft-interp/tests/summary_oracle.rs` (`a_missing_put_fns_place_*`,
  `a_missing_puts_place_of_an_rc_object_*`, each seen passing the broken facts before).
- The report counts what A3 does not check (`FactReport::summary_unnamed`,
  `summary_skipped`; the note of `weft run --fact-oracle`): an access or a reference that the
  frame below cannot name (a local of the callee, a place that no IR place of the frame
  reaches), a captured cell of a closure that a callee puts there (the cell itself is not
  named; the references in its value are), a place of another body of the component, and the
  frames that it
  does not follow: a frame below that unwinds or that is a copied frame of a continuation
  (`uid` 0, group D), and each op of such a frame.
- Limits that stay: at most `SUMMARY_DEPTH` = 16 frames below the callee (a write 18
  frames down is not checked); the frees and the pointers of the result are not compared
  (C4 and C1 of the frame check them at its own nodes); a fresh write is checked for the
  references that it puts, not for the change cover; a `Deref`, the read of the buffer
  handle of an array and an access of a cell that the op frees are skipped; only the frames
  of the current task are walked (a task that writes a place of its parent is not checked
  against the spawn node); only the IR engine has A3 (the AST engine has no facts).
- Code of a caller reads the places behind the parameters of the body and the `rc` groups
  that they reach (6.7, `transfer::caller_reads`): the four A3 failures of the review rows
  of stage F12-fix3 were reads there (`n1c/x08` passes now). A write there through the
  value of the caller is not in the facts of the body by design (map N2): `fc/c19`,
  `lcv/cr_h_vecref` and `h2w/w04` still fail A3, and the checker rejects all three (W0312
  or W0301 at the caller), so the gate does not run them.
- σ of a run of a closure behind a reference argument (`run_all(&fs)`) takes the places of
  the environment from the closures that the reference reaches, not the places that the
  reference itself points into: the facts had `reads_at` of `fs.entities`, a place that
  does not exist (`so04`).

The fact oracle and the summary oracle run with `weft run --fact-oracle` on each accepted
program of the gate. A failure is a defect of the fact generator with a concrete program
and a concrete step, found before a review finds it.

---

## 9. Proof alignment

Today the B6 link proves "exec core to model", and the facts of sema are hypotheses
(`proofs/link/README.md`). With the IR, the hypotheses become statements about the
builder and the fact generator, and some of them can become lemmas. None of this blocks
the migration: the proof work is plan track P, after the removal stages.

### 9.1 B1 (`proofs/borrowing/src/cfg.rs`, `model.rs`)

**Embedding.** Each fact node of a component is one B1 `Node`; its successors are the
`cfg_edge` successors.

| IR | B1 instruction |
| --- | --- |
| `r = &x` | `Borrow { dst: r, x }` |
| `r = &(*s).f[i]` (an unstable step below `*s`) | `Child { dst: r, src: s, label }` |
| `r = copy s` (a reference) | `Copy { dst: r, src: s }` |
| a read or write of a scalar through `r` | `Read { src: r, field }`, `Write { src: r, field, val }` |
| `Call` `Main` | `Call { args: [(var, is_mut)], ret: None }`; `is_mut` from the `muts` part |
| `Call` `Ret` | `Child` (or a chain of `Child`, or `Copy`) from the argument variable that `ret_ok` names into the destination |
| a closure aggregate | `MkClosure { clo, caps }` with its `ByRef` fields |
| `Call` of a closure value, `Perform`, `Resume` | `Invoke { clo, args, ret, once }` (`perform` and `resume` of `model.rs`) |
| `Live` with a value, `Dead`, a move of an owner, `moved_part` | not in B1: the extension B1+ below |
| `Copy` (re-entry) | not in B1: left out of the link (a shared gap) |

The two-node call: B1 binds `ret` at the `Call` node, but the facts bind at `Ret`. So the
call node is `Call { .., ret: None }` and the return node is the `Child` or `Copy` that
`ret_ok` names (proofs judge, gap 1). Then `no_gen_kill` holds and `ret_ok` stays the only
open condition (it stays false for the `in` form, ADR 0005).

**B1+.** B1 has a fixed set of locals and no frees. The IR needs `Alloc { x }` (a `Live`
followed by a value; a local of a loop body starts again), `Free { x }` (a `Dead`, a move
of an owner) and `FreeSub { x, path }` (a `moved_part`). `Free` removes the tree of `x`,
and the checker kills each reference whose group has root `x`. The proof shape is the one
of `lemma_preserve` for a mutable call argument. B1+ also needs a lemma that the sets of
locals agree at a join (`sub_state` checks `a.locals == b.locals`); V4 to V6 give it, and
the link states it as a lemma of the verifier rules.

**Kept cells.** A `Kept` capture is outside the reference fragment: V13 says that no
reference points into it, so its lifetime past the variable cannot make a dangling
reference. B1 does not need to model it.

### 9.2 B2 (closures)

B2 (`lemma_perform_is_call`) proves that an invoke is a call with the captured references
as extra arguments. The IR fragment with closures fits B1 with `Invoke` if the summary of
the closure body is inside the `is_mut` flags of its captured references (the summary
hypothesis). But B1 forbids copying, storing or passing closure values
(`proofs/borrowing/README.md`), and in the IR a closure aggregate is an ordinary value. So
L2-clo needs a B1 extension first: closure values as call arguments (a shared gap, ADR 0012).

### 9.3 B3 (`layout.rs`)

The projections are the steps of B3: `Field` is `Field(f)`; `Variant` after a `Switch` is
the B3 `Variant` instruction; `Index`, `Elems` and `Deref(Box)` are `Kid(label)`;
`Deref(Rc)` is a `Kid` of a group root; `Split` places make L1 (`thm_split_sound`) apply to
α with no change. B3 programs are straight-line; B3 needs the CFG lift of B1.

### 9.4 B4 (`tasks.rs`)

B4 runs two straight-line programs at the same time. The link would cut the part of the
parent between `Spawn` and `Join`, `ScopeWait` or the `Ret` of `Fork` out as the second
program, and needs a CFG form of B4. B4 also checks a stronger rule than W0405 (held
groups, not accesses). This stays a documented gap (ADR 0006).

### 9.5 The effects model (`proofs/effects/src/model.rs`)

| IR | Effects model |
| --- | --- |
| a body | a `Block` |
| the capability operands of a body: `Row(E)` for each `E` of its inferred row (in a fixed order), then the `Cap` local of a handled body | `Sig::caps` |
| the capabilities in the abstract value of `_0` that are parameters | `Sig::rets` |
| the continuation of a clause and its mode | `Sig::kmode` |
| a new value of a linear local (`Assign`, `Ret`) | `Acquire { slot, on_abort }` |
| `Consume`, a move of a linear value into a call | `Consume { slot }`; a move into a call needs change 2 |
| `Call` with `CapArgs::Lexical(env)` | `Call { block, caps }`; `caps[j]` is the index of the capability that `env` gives for the `j`-th effect of the callee row |
| `Handle` | `Handle { eff, clauses, body }` |
| `Perform` with `Local` or `Row` | `Perform { cap: index, op }` |
| `Resume` | `Resume` |
| `Return` | `Return` |
| `UnwindValue(_, OnAbort)`, `UnwindKont`, `UnwindExit` | `step_unwind_abort`, `step_unwind_drop`, `step_unwind_pop` |

Changes of the model:

1. **The unwind order in a frame (N6).** `max_slot` takes the largest resource id (a
   dynamic order). The IR takes the highest slot (a static order that a chain can state).
   Change `max_slot` to compare slot numbers. The embedding numbers the slots of a frame
   in the order of the chain, from the top: `_0` gets the highest number, each temporary
   the next numbers in the order of its `LocalId` (temporaries are made in program order,
   so a higher id is a newer one), then the user locals by `LocalId`, and the parameters
   the lowest numbers. This numbering is fixed for the body, so it is a static order.
   The change touches `inv_b` (`own.rs`,
   `own_steps.rs`), L3 (`unwind_linked` in `proofs/link/src/lifecycle_link.rs`), the
   examples, and the mutation tables of `proofs/effects` and `proofs/link`.
2. **Moves of linear values into calls.** `Call` passes no slots. The extension
   `Call { block, caps, moves: Seq<Slot> }` moves each slot into the callee frame. `inv_b`
   holds with the move (one owner).
3. **The CFG lift.** Blocks are straight-line. The checker state `SS` needs a join: `env`
   equal on each edge (it is static), `lin` equal on each edge (W0601 rejects a
   difference), `k` the conjunction (a `once` continuation that one path resumed is not
   usable after the join). The lift is the B1 argument (`lemma_inv_sub`).

What does not change: the order of a clause frame and its fresh continuation. The IR
takes the order of the model (`UnwindKont` first, `step_unwind_drop` before
`step_unwind_abort`), and the interpreter changes to it when it runs landing pads
(plan stage I6). The machine design changed the model here; the proofs judge preferred
to keep the verified model and change the interpreter, because no user code depends on
this order.

### 9.6 Reference versions and the verified kernel (after the migration)

- **Versions** (MIR D8): one fact variable for each definition of a move path that can
  hold a reference. A use of a local uses the versions that reach it. A later definition
  makes an old version *unbound* from there (`unb` in the link), not rebound: the
  `rebound_at` of an old version at a new definition is the link's "unbound". Versions
  give the static group of one rvalue for each variable, which is the shape that
  `facts_ok` and `instr_groups_ok` need, and a flow-sensitive `points_into` with no spec
  change (OL-NR-flow, OL-R2b-holds, V069, R3RT10). They must keep the `Copy` rule of 6.5:
  a re-entry rebinds a version only if all its places are in the copied frames (J4; the
  MIR `Recopy` broke it).
- **The verified kernel** (MIR 7.5): the templates of the reference fragment (`Borrow`,
  `Child`, `Copy`, `Read`, `Write`, `Call`, `MkClosure`, `Invoke`, `Alloc`, `Free`) move
  into `crates/weft-verified/src/factgen.rs`. The fact generator calls them; the link
  includes them with `#[path]`, and `check-copies.sh` lists them. Then L2-IR is a theorem
  about the code that runs, as the link rule asks. `factgen/kernel.rs` keeps these
  templates as pure functions with a narrow interface from the start, so the move is
  mechanical.

### 9.7 The link, step by step

| Step | Statement | Hypothesis that it removes |
| --- | --- | --- |
| L0 | `ir_wf(body)`: a Verus spec of V1 to V7 and V12. The link can include only Verus code (`check-copies.sh` lists files of `crates/weft-verified` and of the models). So the rules V1 to V7 and V12 move into `crates/weft-verified/src/ir_wf.rs` as exec Verus code over a small mirror of the body (blocks, successors, `Live`, `Dead`, uses), with the proof `ir_wf_check(body) == true ==> ir_wf(body)`; `weft_ir::verify` calls it, and the link includes it with `#[path]` (plan stage P3) | none; the base |
| L2-IR | for a body with `ir_wf`, the facts of the kernel for the B1 relations (`cfg_edge`, `rebound_at`, `uses`, `points_into` from `Ref`, `Copy` and the two-node call, the call rule of `invalidated_at`) are the link facts of `embed(body)` | `facts_ok` (with versions: the static-group part too), `bound_before_use` (from V4), `no_gen_kill` (from the phases) |
| L2-free | the same with B1+ for `frees_at`, with the join lemma | "the link definition has only the call rule" |
| L2-clo | the same with `MkClosure` and `Invoke`, after the B1 extension for closure values as arguments | "no closures in the link" |
| L4 | `ir_wf` and acceptance of W0601, W0602, W0501 and W0503 on the facts imply `check(embed_eff(program))` for the fragment with no tasks | the effects facts of sema (D4, D5, E1, G1) |
| (stays) | each summary contains the effects of its body; the analysis gives sound abstract values | A3, C1: tested by the oracles of 8.5, not proved |

### 9.8 Shared gaps (ADR 0012 records them)

1. B1 binds `ret` at the call; the IR binds at `Ret`. The two-node embedding of 9.1
   closes it.
2. B1 forbids copying, storing or passing closure values, so L2-clo needs a B1 extension.
3. Re-entry (`Copy`) nodes have no B1 instruction; the link leaves them out, or B1 needs a
   frame copy step. E5 covers the linear part only.
4. A `Deref` of a local that two versions reach still gives two places at a join: B1 needs
   its multi-place extension, or the IR needs a phi with one group for each edge.
5. B1 plus `Free` needs the join lemma of the sets of locals (V4 to V6 give it).
6. Summary soundness stays a tested hypothesis.
7. The link includes only Verus code: the verifier rules of L0 move into
   `crates/weft-verified` first (9.7, plan stage P3).

---

## 10. Verdicts: what the IR removes and what stays

The counts use the 180 unsound findings and 53 false positives of `docs/plan/core-ir-inputs/root_causes.md`
(data: `SCRATCH/ir/work/findings.py`), with the verdicts of the machine design
(`docs/plan/core-ir-inputs/design_machine.md` section 5) corrected by the judge reports and by the grafts of this
document. The claims test of the gate (`tests/gate/claims.toml`, plan stage G7) holds a
repro for each verdict "construction" or "one rule" that has one, and each such repro must
be rejected (unsound) or accepted (false positive) by the new pipeline when its construct
group is on. A failure changes the code or the verdict.

### 10.1 By class

| Class | Verdict | Mechanism |
| --- | --- | --- |
| TEMP (9 U) | construction | temporaries are locals with `Live` and `Dead`; the frame end; values bind where they exist |
| TAIL (4 U, 1 FP) | construction | `into(e, dest)`; a discarded value gets a temporary and its `Dead` |
| DROP (8 U, 1 FP) | construction | `Dead` always drops; `UnwindValue` with the `on abort` summary |
| ORDER, ACCESS, DEREF (11 U, 1 FP) | construction | operands at one statement; `ptr` reads; `Deref` as a projection |
| CALLS (8 U, 3 FP) | construction | one `Call`, `Perform` and `Resume` template; `call_arg` of each reachable place |
| ENV (15 U, 5 FP) | construction | the closure aggregate; rule CAPTURE; cell roots; upvar locals; V13 (V125 and J5 now closed). The false positive F3-11 needs the `rebinds` part of the summary (6.7), so it is "one rule" |
| INNER (9 U, 3 FP) | construction | one body for each frame; splices and summaries |
| SUSP (5 U, 5 FP) | construction | `unwind` edges; cleanup copies for each destination; `spared_at` from the CFG |
| LOOP (3 U, 1 FP) | construction | back edges and one fixpoint with widening |
| VAL, POST, TYPES (7 U, 5 FP) | construction | one transfer for each right side; facts are a pure function; the builder runs after `typeck` |
| TWO (4 U) | construction | the interpreter runs the IR (stages I1 to I6) |
| MULTI (2 U) | construction | re-entry edges for local handlers and handlers of a caller; one-place instances off on cycles. The false positive OL-NR-multi stays: the re-run is path-insensitive, a precision choice of the spec |
| PART (V062, Q3-1: 2 U) | construction | `Uninit` from the full type |
| FNVAL (22 U, 2 FP) | one rule | set-valued closure analysis with heap slots; `ret` with closures in interface terms |
| SUM (13 U, 3 FP) | one rule | one summary procedure; parts as projections; `RELS` |
| STORE (8 of 9 U) | one rule | caller and callee frame roots; the `stores` check on every body |
| GEN (7 U, 1 FP) | one rule | `drops` and `holds` as queries; a summary with type arguments where an item value is made |
| STATE (3 U, 6 of 8 FP) | one rule | flow-sensitive state of the analysis; the must-set of task holders; `uniq` of a variable as the meet of its values |
| CAP (11 U, 2 FP) | one rule | capabilities and continuations as values with roots; the W0313 escape check over those roots; W0314 over the `tasks` part |
| PART (R3RT1: 1 U; V023: 1 FP), STORE (OL-R2b-prec: 1 U) | stays | a spec rule for each move path (R3RT1 has the R3a rule `rest_linear`, which the IR emits, so it stays closed); `rc` object identity |
| SPEC (13 U, 3 FP), TYPE (12 U, 4 FP), INF (1 U, 1 FP), NAMES (1 U, 2 FP) | stays | spec rules, type rules, inference bounds and names: causes outside the lowering |

Totals (primary cause; the counts of the machine design, which the judges checked): 87
unsound findings (48%) by construction, 64 (36%) by one rule, 29 (16%) stay. The grafts
close gaps inside these verdicts (V125 and F5 are now true by construction; H7 to H9 of
the soundness judge are closed); they move no unsound finding between the verdicts. For
false positives: 24, 15 and 14 (F3-11 moves from "construction" to "one rule": it needs
the must part `rebinds`). The STATE false positives OL-R2b-holds and OL-NR-flow go with
reference versions (after the migration).

### 10.2 New findings and how each closes

All are open at `b25faf0` (the judges re-ran them). Each goes into the curated gate set
(`tests/gate/probes/ir/`) and the claims file.

| Id | Probe (`SCRATCH/ir/...`) | Shape | Mechanism |
| --- | --- | --- | --- |
| M1 | `work/machine/m1_post_resume.wf`, `work/mir/postres.wf` | clause code after `resume` changes a place that the value of the handled body points into | `Exit` then `Post`; the resume result in the clause (6.10) |
| M2 | `work/machine/m6b_resume_result_ref.wf` | the result of `resume` does not point where the value of the handled body points | `ret` of the continuation summary |
| M3 | `work/machine/m8_abort_value_into_body.wf` | a clause with no resume returns a reference into a local of the handled body | `AbortValue` before the cleanup copy |
| M4 | `work/machine/m10_abort_value_callee_local.wf` | the same with a local of a callee that performs | the callee frame root, ended at `FrameEnd(d)` |
| J1 | `judge_sound/j1_post_resume_keep.wf` | a clause changes a place after `resume`; the body kept a reference in a site local | the `Post` node |
| J2 | `judge_sound/j2_post_resume_closure.wf` | the same with a resume through a closure | resume points include run nodes whose summary resumes |
| J3 | `judge_sound/j3_resuming_clause_value.wf` | a resuming clause returns another reference | `Exit` binds the union of `_0` and the clause values |
| J4 | `judge_sound/j4_multi_outer_ref.wf` | a `multi` re-run with a reference into a site place | the `Copy` rule (rejected today; must stay rejected) |
| J5, J5d | `judge_sound/j5_kept_borrow.wf`, `j5d_maker_borrow.wf` | a closure borrows a captured plain value after its scope | rule CAPTURE and V13 |
| J6 | `judge_sound/j6_resume_temp_keep.wf` | a resume value into a clause temporary, kept by the body | the clause frame root `K(h)` (R3a rejects it; must stay rejected) |
| map N1, N2 | `work/map/opres.wf`, `work/map/fnres2.wf` | the result of code of a caller has no places | the caller frame root |
| sem N1 to N3 | `probes/p2_late_operand_ref.wf`, `p9_print_late.wf`, `p10_index_late.wf` | a place operand is read later than the facts say | choice A |
| sem N4 | `probes/p25_assert_abort.wf`, `p27_assert_callee.wf` | `assert` aborts with no abort edge | the `Assert` terminator with `unwind`; the `aborts` part |

Controls that must stay accepted: `judge_sound/j5b_kept_write.wf` (a closure writes a
kept integer and leaves its scope), `judge_sound/j5c_kept_borrow_task.wf` (W0405 today; must
stay rejected), `work/judge/p/d5_count.wf` (a returned counter closure),
`work/machine/m6_resume_result_body_local.wf` and `m9_resume_twice_tail.wf` (correct
programs).

### 10.3 What stays

- **Spec and fact model:** part moves for each move path (V023, R3RT1, F3-5 has the R3a
  rule); a flow-sensitive `points_into` until reference versions land.
- **Types and signatures:** `props.rs`, `!Move`, exhaustiveness, the `on abort` parameter
  types (F3-4), `Task<T>` with a linear `T` (F3-6, I3-1), prelude signatures (RR8, OL-3b).
- **Inference bounds and names** (INF, NAMES).
- **`rc` object identity** (OL-R2b-prec): a language decision (ADR 0011).
- **Interpreter defects** other than the unwind order: the scheduler and oracle gaps of
  class I (I3-3, F3-8, ...). Landing pads close the closure-cell part of I3-2.

### 10.4 Trace of the round 2 and round 3 blockers

Each blocker of the reports of rounds 2 and 3, and each item that `SCRATCH/r3/issues.md`
gives to the IR (site `ir`), has a row. The repro paths are relative to `SCRATCH`; stage
G2 copies them to `tests/gate/probes/<same path>`. "Claim" is the stage that turns the
claim of the row on (plan §2.5); the claim must hold from that stage on. A row with
verdict "stays" is a claim that the IR pipeline keeps the result of today (the repro
stays rejected, or the rule stays where it is). Groups: A first-order, B loops, C
closures and function values, D handlers, E tasks, F generics. A spawn takes a closure, so
a repro of group E uses group C too; the claims file holds the set of groups that
`irbuild/scope.rs` computes for each repro (plan §2.5).

**Round 2 blockers** (`r2/*.md`; all closed in the old pipeline by stages R2a to R2e):

| Id | Class | Verdict | Mechanism | Repro | Group | Claim |
| --- | --- | --- | --- | --- | --- | --- |
| FD1 (= QA2) | DROP | construction | `UnwindValue(_, OnAbort(f))` applies the summary of `f` with `CapArgs::Root` (5.28, 6.4) | `r2/fidelity/repro/FD1_onabort_*.wf`, `r2/quality/repro/QA2_on_abort_effects.wf` | A | F7 |
| FD2 | interpreter | none (class I) | the engine differential and the interpreter tests | `r2/fidelity/repro/FD2_multi_nested_drop.wf` | D | I5 |
| FD3 | STORE | one rule | the `stores` part and the W0204 store check (6.7, 6.9) | `r2/fidelity/repro/FD3_rc_backchannel.wf` | C | F13 |
| IP1 | SPEC | stays | W0504 in `typeck`; the runtime raises a failure past a clause | `r2/interp/repro/ip_fail_resume_*.wf` | D, E | F19 |
| IP3 | SPEC | stays | the pinning rules; `spawns_in` and `opaque` from the `tasks` part (6.4) | `r2/interp/repro/ip_steal_shares_rc.wf` | E | F19 |
| IP6 | TWO | construction | `Fork` gives a tuple, also of units; the interpreter runs the IR | `r2/interp/repro/ip_fork_unit.wf`, `ip_fork_generic_unit.wf` | E, F | F20 |
| OR1 | FNVAL | one rule | `ret` with the environment in interface terms; σ maps `Param(i)` onto the argument (6.7) | `r2/oracle/repro/OR1_returned_closure.wf` | C | F12 |
| OR2 | ENV | construction | the `ByMove` operand of the closure aggregate; the interpreter reads it from the IR (5.1.7, 8.1) | `r2/oracle/repro/OR2_closure_move_timing.wf` | C | F11 |
| OR3 | SUM | one rule | `runs` = `Many`: a second `apply` at `Ret` (6.7) | `r2/oracle/repro/OR3_repeated_callback.wf` | C | F12 |
| OR5 | SPEC | stays | the R2d rule: `lends_mut` of the task writes at `Join` `Ret` and at `ScopeWait`; `Bounds` reads (6.4) | `r2/oracle/repro/OR5_borrow_during_task.wf` | E | F18 |
| OR6 | TWO | construction | a place statement is a `Mention` (5.4) | `r2/oracle/repro/OR6_expr_statement_move.wf` | A | F8 |
| OR7 | SUM | one rule | `runs` as a task: `spawned_at` at `Main`, `joined_at` at `Ret` (6.7) | `r2/oracle/repro/OR7_tasks_of_fn_params.wf` | C, E | F19 |
| OR8 | ACCESS | construction | an operand reads the root of a source local; an overwrite writes it (6.4) | `r2/oracle/repro/OR8_task_whole_local.wf` | E | F18 |
| OR9 | CAP | one rule | W0314 over continuations (6.9) | `r2/oracle/repro/OR9_resume_in_task.wf` | D, E | F19 |
| QA1 (= RR1) | LOOP | construction | see RR1 | `r2/quality/repro/QA1_loop_pass_cap.wf` | B | F10 |
| QA3 | TYPE | stays | `typeck`: the order of `in` places in a signature | `r2/quality/repro/QA3_param_place_order.wf` | A | F8 |
| RR1 | LOOP | construction | back edges, one fixpoint, widening (6.6) | `r2/redteam/repro/RR1_loop_chain.wf` | B | F10 |
| RR2 | FNVAL | one rule | sets of function values (6.6) | `r2/redteam/repro/RR2_one_summary.wf` | C | F12 |
| RR3 | CAP | one rule | the continuation root ends at the clause end; W0313 (6.3, 6.9) | `r2/redteam/repro/RR3_continuation_escape.wf` | C, D | F17 |
| RR4 | ENV | construction | the `ScopeCap` root; a capture points into it; it ends at the scope end (6.3, 6.4) | `r2/redteam/repro/RR4_scope_escape.wf` | C, E | F19 |
| RR5 | INNER | construction | the `frees` of the continuation summary at `Resume` (6.7) | `r2/redteam/repro/RR5_resume_free.wf` | D | F16 |
| RR6 | FNVAL | one rule | the result of a perform is the `resume` values of the clauses (6.6) | `r2/redteam/repro/RR6_resume_fn_value.wf` | C, D | F17 |
| RR7 | ENV | construction | σ maps a `ByRef` capture to the current value of the variable (6.7) | `r2/redteam/repro/RR7_late_capture.wf` | C | F11 |
| RR8 | TYPE | stays | the prelude signature of `Vec.clear` (`from_signature`, 6.7) | `r2/redteam/repro/RR8_vec_clear.wf` | A | F8 |
| RR9 | GEN | one rule | the summary of an item value with its type arguments (5.20, 5.35) | `r2/redteam/repro/RR9_generic_item_drops.wf` | C, F | F20 |
| RR10 | TWO | construction | the argument order of the THIR; the interpreter runs the IR (5.18, 8.1) | `r2/redteam/repro/RR10_named_args.wf` | A | F8 |

**Round 3 blockers** (`r3/*.md`):

| Id | Class | Verdict | Mechanism | Repro | Group | Claim |
| --- | --- | --- | --- | --- | --- | --- |
| F3-1 | DROP | construction | the `on abort` summary at `UnwindValue`; W0118 as a query (6.4, 6.9) | `r3/fidelity/repro/F3-1_on_abort_ref_in_value*.wf` | A | F7 |
| F3-2 | STORE | one rule | the callee frame root `F(n)` (6.3, 6.10) | `r3/fidelity/repro/F3-2_*.wf` | C, D | F15 |
| F3-3 | DROP | construction | W0118: the `drops` query of the `on abort` function (6.9) | `r3/fidelity/repro/F3-3_generic_on_abort_*.wf` | F | F20 |
| F3-4 | TYPE | stays | `typeck`: the `on abort` parameter with its type arguments | `r3/fidelity/repro/F3-4_on_abort_type_args*.wf` | F | F20 |
| F3-5 | SPEC | stays | the R3a spec rule; the IR emits `moved_part` (6.4) | `r3/fidelity/repro/F3-5_ref_above_moved_part*.wf` | A | F8 |
| F3-6 (I3-1) | TYPE | stays | the type rule for `Task<T>` with a linear `T`; `TaskResult` locals (5.29) | `r3/fidelity/repro/F3-6_*.wf`, `r3/interp/repro/i3_1_*.wf` | E | F18 |
| F3-7 | TEMP | construction | `_0` in the chain of `ScopeWait` (5.1.6) | `r3/fidelity/repro/F3-7_scope_value_across_end.wf` | E | F18 |
| F3-8 | SPEC | stays | a cancelled task drops its by-move linear capture: a rule of the spec and the interpreter | `r3/fidelity/repro/F3-8_*.wf` | C, E | F19 |
| O3-1 | TAIL | construction | `into` of the tail of a scope body; `Exit` (5.11, 5.29) | `r3/oracle/repro/O3-1_scope_tail_move.wf`, `r3/triage/O3-1b_scope_tail_move_value_task.wf` | E | F18 |
| O3-2 | TEMP | construction | the frame end; `Exit` uses `_0` (5.1.4, 6.10) | `r3/oracle/repro/O3-2_handled_body_temporary.wf` | D | F14 |
| O3-3 | TEMP | construction | the clause frame root `K(h)` (6.3) | `r3/oracle/repro/O3-3_clause_temporary.wf` | D | F15 |
| O3-4 | DROP | construction | the `TaskResult` local of a spawn statement (5.1.3, 5.29) | `r3/oracle/repro/O3-4_task_result_linear_leak.wf` | E | F18 |
| O3-5 | FNVAL | one rule | a heap slot of the field; the task applies the summary of each value in it (6.6, 6.7) | `r3/oracle/repro/O3-5_task_runs_field_closure.wf` | C, E | F19 |
| O3-6 | DEREF | construction | `Deref(Rc)` names the handle; `ptr` reads (5.8, 6.4) | `r3/oracle/repro/O3-6_task_rc_handle_move.wf` | C, E | F19 |
| O3-14 | TAIL | construction | the re-entry edge; the tail move of an upvar local is on the cycle (5.25, 6.5) | `r3/oracle/repro/O3-14_multi_tail_place.wf` | D | F16 |
| Q3-1 | PART | construction | `Uninit` from the full type (5.17) | `r3/quality/repro/Q3_unset_place_field_*.wf` | F | F20 |
| R3RT1 | PART | stays | the R3a spec rule `rest_linear`; the IR emits it (6.3) | `r3/redteam/repro/R3RT1_partial_linear_move.wf` | A | F8 |
| R3RT2 | DEREF | construction | a by-value binding of a reference payload copies the reference (5.13) | `r3/redteam/repro/R3RT2_match_through_ref.wf` | A | F8 |
| R3RT3 | CALLS | construction | `call_arg` of each place that an argument reaches (6.4) | `r3/redteam/repro/R3RT3_held_refs_at_call.wf` | A | F8 |
| R3RT4 | INNER | construction | resume points include run nodes whose summary resumes; σ maps the closure parameter to the places that each run node gives, or to `Caller` (6.7) | `r3/redteam/repro/R3RT4_resume_closure_param.wf` | C, D | F16 |

**Items of `r3/issues.md` with site `ir`** (not blockers; the IR must check them again):

| Id | Kind | Verdict | Mechanism | Repro | Group | Claim |
| --- | --- | --- | --- | --- | --- | --- |
| I3-8 | U (edge) | construction | the `TaskResult` local of a spawn statement is a once value from the `Spawn` on (5.29): W0503 | `r3/interp/repro/i3_8_multi_scope_fail.wf` | D, E | F19 |
| R3RT5 | FP | construction | a `ByMove` field has no tie to the variable (5.1.7) | `r3/redteam/repro/R3RT5_byvalue_capture_scope.wf` | C | F11 |
| R3RT6 | FP | partly | `from_signature` gives a `mut` place only the held references of the other arguments whose types fit (F5); the flow before the call stays until reference versions (11) | `r3/redteam/repro/R3RT6_ref_arg_flow_fp.wf` | A | P1 |
| O3-7 | FP | one rule | `call_mut` with the root of the function argument that the change comes from (6.4) | `r3/oracle/repro/O3-7_fp_op_closure_w0312.wf` | C, D | F14 |
| O3-8 | FP | construction | a handled body inside a closure is spliced into the closure component; its performs do not leave the summary (6.1) | `r3/oracle/repro/O3-8_fp_closure_inner_multi.wf` | C, D | F16 |
| O3-9 | FP | one rule | task sets as abstract values; the must half of the `tasks` part (6.6, 6.7) | `r3/oracle/repro/O3-9_fp_join_not_seen.wf` | C, E | F18 |
| O3-10 | FP | construction | a `Spawn` has no `multi_at` (6.4) | `r3/oracle/repro/O3-10_fp_spawn_param_multi.wf` | C, E | F19 |
| O3-11 | FP | construction | the cell root `C(x)` (5.1.7) | `r3/oracle/repro/O3-11_fp_move_then_refill.wf` | C | F11 |
| O3-12 | FP | one rule | a clause reads only what its nodes read; a task that it starts has its own footprint (6.7) | `r3/oracle/repro/O3-12_fp_clause_spawn_self.wf` | D, E | F19 |
| F3-11 | FP | one rule | the `rebinds` part (6.7) | `r3/fidelity/repro/F3-11_closure_rebind.wf` | C | F11 |
| R3RT7 | FP | construction | `arg_at` and `param_in` for an operation parameter (6.4) | `r3/redteam/repro/R3RT7_op_in_param.wf` | D | F14 |
| R3RT10 | FP | one rule | a part with an `H` variable owns its places (6.3) | `r3/redteam/repro/R3RT10_part_refresh_fp.wf` | A | F8 |
| Q3-2 | speed | construction | each closure summary is computed once, in the order of the SCCs (6.6) | `r3/quality/repro/Q3_closure_*.wf` | C | F12 |
| N1 (issues) | message | construction | the drop pair of `Detach` ends at the next node (6.4) | `r3/fidelity/repro/F3-6_control_detach.wf` | E | F18 |

The stage verifiers of rounds 1 and 2 (V001 to V138) and the open lists (`OL-*`) have
their verdicts in `docs/plan/core-ir-inputs/design_machine.md` section 5 and in `docs/plan/core-ir-inputs/root_causes.md`
Appendix A. Their repros are in `SCRATCH/verify/`, `SCRATCH/fix/` and the other stage
directories; plan §2.1 and §2.2 put them in the gate, and stage G7 makes their claims.

---

## 11. Options after the migration

| Option | Classes | Note |
| --- | --- | --- |
| reference versions (9.6) | STATE false positives; `facts_ok` | plan track P, stage P1 |
| a variable for each move path for moves and linear values, with spec rules for each path | PART (V023, R3RT1) | a spec change through the checklist of ADR 0002 |
| W0313 and W0314 as spec rules: an input relation `stack_cap(Rt)` and a rule `foreign_cap(T, V) :- captures(T, V), points_into(V, Path), stack_cap(Rt), prefix(Rt, Path)`; an escape rule over capability roots | CAP | needs an escape relation that keeps the 61 W0313 markers |
| W0204 at `Return` as a sink of its own in the spec | none (clarity) | today `diagnose.rs` maps `error(_0, Return)` |
| monomorphization of generic bodies for checking, by the profile of the props of the type arguments | GEN | the IR stays generic in the migration |
| a whole-program closure analysis (0-CFA over the IR) | FNVAL | more precise for stored values |
| regions for function values, `rc` object identity | STORE | language decisions |
| a native back end | none | the IR has the shape it needs (frames, explicit drops, cleanup paths, capability passing) |
