# Run-time semantics that the core IR must match

Status: analysis for the core IR design. Date: 2026-10-20. Source: commit b073ea7.

This document maps the dynamic semantics of Weft Phase 1, as the reference interpreter
implements it, and the proof models that the B6 link uses. The core IR goes between the
typed AST and fact generation. Its facts must describe what the interpreter does. So
each rule below is a rule that the IR builder, the fact generator and (if it runs the IR)
the interpreter must share.

Sources: `crates/weft-interp/src/{code,compile,value,heap,runtime,oracle}.rs`,
`crates/weft-interp/src/machine/{mod,exec,effects,natives}.rs`, `docs/design.md`,
`docs/architecture.md`, ADR 0003, 0005, 0006, 0007 and 0010, `proofs/README.md`,
`proofs/borrowing/src/{model,cfg,layout,tasks}.rs`, `proofs/effects/src/{model,checker}.rs`,
`proofs/link/README.md`, `crates/weft-verified/src/lifecycle.rs`, and the review reports of
rounds 1 to 3. The sibling analysis `docs/plan/core-ir-inputs/root_causes.md` classifies the findings. This
document does not repeat it.

Probes: 28 small programs in
`SCRATCH/ir/probes/`.
The binary there is a copy of `target/debug/weft`, built after commit b073ea7. Each probe
ran with `weft check` and `weft run --oracle`. A probe name in this document (for example
p2) is the file `p2_*.wf` in that directory.

## Summary

- The interpreter compiles each body to a stack code. Each function, test, closure,
  handler clause, handled body and scope body is one code unit. A frame runs one unit.
  W0315 forbids `return`, `break` and `continue` out of a handled body, a clause or a
  scope body. So each of these bodies has one entry and one exit. The IR can have one
  body for each code unit.
- Evaluation goes from left to right, with these exceptions:
  1. A call of a function item, of a method of a value with named arguments, or of an
     operation runs its arguments in the order of the parameters.
  2. An assignment runs the value first. Then it runs the target place, also the index
     expressions of the target.
  3. A place operand of a binary operator, an operand of `print`, and the base of an
     index are read at the operator. They are not read where they are written.
  4. A method receiver is a place first. The machine reads it, and moves it if it goes
     by value, at the call, after the arguments.
  5. A positional struct constructor runs its arguments in the order of the fields.
- **New, unsound.** Exception 3 is unsound today. Sema records the use of the operand
  where it is written. The checker accepts three programs that read a freed cell: a
  binary operand (p2), a `print` operand (p9), and an index base (p10).
- **New, unsound.** A failed `assert` aborts the task and unwinds it. Sema gives
  `assert` no abort edge and no `may_abort`. A live linear value with no `on abort`
  across an `assert`, also an `assert` in a callee, makes the unwinder fault (p25, p27).
- A value moves when its operand is read. A closure takes its by-value captures when it
  is made. A handler clause and a handled body take a capture when their code reads it.
  A by-value method receiver moves at the call. A `match` arm and a destructuring `let`
  move parts out when they bind.
- A temporary lives to the end of the innermost open statement. A block tail is not a
  statement. So the temporaries of a block tail belong to the statement around the
  block. Three results follow:
  - The temporaries of the tail of a frame body end after the value leaves the frame
    (O3-2, O3-3).
  - **New.** The temporaries of the tail of a loop body live until the whole loop
    statement ends. They pile up over the iterations (p24).
  - The temporaries of an `if` condition and of a `match` scrutinee live to the end of
    the enclosing statement. The condition of `while` is a statement of its own.
- At the end of a block, the locals end in declaration order. No user code runs at a
  normal drop. Only `Weak.upgrade` and the oracle can see when a drop occurs. The order
  inside one drop point cannot be seen.
- Unwinding runs `on abort` for the innermost frame first. In a frame it takes the
  operand stack, then the temporaries (newest first), then the slots (highest slot
  first). **New:** the effects model takes the newest value first, and it unwinds a fresh
  continuation before the clause frame that holds it. The interpreter does the opposite
  in both cases (p18, p20). A fault (an index out of bounds, an overflow, a missing
  handler) stops the whole run. It does not unwind (p28).
- Handlers are deep and lexical. A continuation holds the frames from the handler mark
  to the top. A `multi` resume copies the cells that these frames own. The cells of
  locals outside the handled body are shared between the runs.
- Proof models: B1 is a CFG of one-instruction nodes over references and closure values.
  A MIR-like IR maps onto it with one statement for each node. B1 has no owned locals
  that move or end, so the frees of sema (`frees_at`) are outside it. B3 (layout), B4
  (tasks) and the effects model are straight-line. The effects model has the frame
  structure of the interpreter. For a B6 link from the IR to the facts, the models need
  a CFG form (B3, B4, effects), a free instruction (B1), and one unwind order.

## 1. The machine

### 1.1 Code units and frames

`code.rs` defines the code. `compile.rs` lowers the AST to it. `machine/` runs it.

| Code unit (`CodeKind`) | Made by | Parameters | Ends with |
| --- | --- | --- | --- |
| `Fn(f)` | each function with a body (`compile_fn`, `compile.rs:161`) | the parameters | `block(body)`, then `Return` |
| `Test` | each `test` block | none | `block(body)`, then `Return` |
| `Closure` | each closure literal and each trailing block (`closure_named`, `:1215`) | the closure parameters | `expr(body)`, then `Return` |
| `Clause` | each clause of a `handle` (`:920`) | the operation arguments, then `resume` | `block(body)`, then `Return` |
| `HandleBody` | the body of a `handle` | none | `expr(body)`, then `Return` |
| `ScopeBody` | the body of a `scope` (`:960`) | the scope capability `s` | `block_body`, `ScopeWait`, `DropSlots`, `Return` |

A task has a stack of frames (`machine/mod.rs`, `Frame`):

| Frame | Meaning |
| --- | --- |
| `Code(CodeFrame)` | Runs one code unit. It has the slots (a cell for each live local), the captured cells, the operand stack, the temporary cells, the statement marks, the loop marks and the lexical handlers (`henv`). |
| `Handle(HandleMark)` | A handler instance: its id, its clauses (with their captured cells) and the handlers outside it. It delimits continuations. |
| `Clause { cont }` | A clause that runs, and the continuation that its operation captured. |
| `Scope { scope }` | A `scope`. The scope record has the owner, the children and the first failure. |
| `Fork { scope, tasks, henv }` | A `fork` that waits for its branches. |
| `Timeout { id, henv }` | A `with_timeout` block. |
| `Sim { sim, outer }` | A `sim.run` body. |
| `Unwind(Unwind)` | An unwinding in progress (section 7). |

### 1.2 Cells, places and values

- The heap has cells (`heap.rs`). A cell is a local, a temporary, the buffer of a `Vec`,
  the target of a `Box`, or the object of an `Rc` with its counts. A cell never moves. A
  place is a cell and a path of field, payload or element indices.
- A local has one cell while it is live. A `let` gives its slot a new cell. A
  closure, a clause and a handled body capture the cell of a variable, not its value
  (except the by-value captures of a closure, section 3).
- `Value::Moved` marks a place whose value moved out. It also marks a local with no
  value (`let x` with no `=`, `Op::BindEmpty`) and a struct field that a literal does
  not give.
- Copy and move are properties of the value at run time, not of the type
  (`Heap::is_copy`, `heap.rs:207`):

| Copied when read | Moved when read |
| --- | --- |
| `()`, `bool`, integers, `String`, `Duration`, references, slices, closures, function items, continuations, scope capabilities, root capabilities, HTTP request and response values | `Vec`, `Box`, `Rc`, `Weak`, task handles, iterators |
| a tuple, an enum value or a struct whose parts are all copied, if the struct is not linear and not `!Move` | each other tuple, enum value or struct |

  Consequences: an `Option<Vec<T>>` that holds `None` is copied. A closure is copied,
  also when it owns cells: two copies share the owned cells. Sema decides copy from the
  type (`props.rs`, `NotCopy`) and treats a closure as not plain data. Where sema says
  "move" and the machine copies, sema is stricter, so this is safe. I3-11 shows the cost:
  an inline recursive enum is copied at each move.

### 1.3 The operand stack, temporaries and statement marks

- An expression pushes a value or a place (`Value::Loc`) on the operand stack. A place
  is not read until an instruction reads it.
- `Op::ToTemp` puts a value in a new temporary cell and pushes its place. The frame
  keeps the cell in `temps`.
- `Op::StmtBegin` pushes a mark: the number of temporaries now. `Op::StmtEnd` ends the
  temporaries after the mark (`exec.rs:407`, `:412`).
- `Op::Return` pops the value, removes the frame and calls `cleanup_frame`
  (`exec.rs:197`): it drops the rest of the operand stack, then ends the temporaries,
  then ends the cells of all slots in slot order.
- A value on the operand stack that waits for a later operand (an argument, a part of a
  tuple) is what sema calls a hidden variable (ADR 0007). The unwinder sees it
  (section 7).

### 1.4 The instructions and their IR meaning

| Op | Run-time meaning | IR form |
| --- | --- | --- |
| `Var(v)` | push the place of a local or a captured cell | a place `local` |
| `Field(name)` | follow references, `Box` and `Rc` from the place, then go to the field | projections `Deref*` then `Field` |
| `Index` | pop the index; follow references, `Box` and `Rc`; check the bounds; go to the element | `Deref*`, `Len`, a bounds check, `Index` |
| `ToTemp` | value to a temporary cell | `StorageLive(t); t = value` |
| `Read` | copy or move the value at a place (`use_place`, `exec.rs:176`) | an operand `copy p` or `move p` |
| `Borrow`, `BorrowAll` | a reference to a place, or a slice of all elements | `r = &p`, `r = &p[..]` |
| `Store` | replace the value at a place; drop the old value | `drop(p); p = v` |
| `CompoundStore` | follow references; read, compute, check, write | `p = p op v` through `Deref*` |
| `Pop`, `Nip` | drop a value | `drop` of a temporary |
| `Bin`, `Neg`, `Not`, `CheckInt` | arithmetic; `CheckInt` faults if the result does not fit its integer type | `t = op(a, b)` with the integer type |
| `Jump`, `JumpIfFalse`, `JumpIfTrue` | control | `goto`, `switch` |
| `LoopEnter`, `LoopExit`, `BackEdge`, `Break` | loop marks; `BackEdge` can preempt; `Break` drains the stack and the temporaries of the loop | `goto` with drops on the edge |
| `StmtBegin`, `StmtEnd` | temporaries of a statement | `StorageDead` of the temporaries |
| `Bind`, `BindEmpty`, `DropSlots` | a new cell for a slot; end of slots | `StorageLive`, an assignment, `StorageDead` |
| `Tuple`, `MakeVec`, `MakeStruct`, `MakeEnum` | aggregates; a linear struct gets a linear record | an aggregate statement |
| `Untuple`, `Unstruct`, `Match` | destructuring; consumes a linear struct by value | projections and moves; a consume |
| `Call`, `CallValue`, `CallMethod` | calls | one `Call` terminator |
| `Perform` | an operation | a `Call` through a capability |
| `MakeClosure` | a closure with captured cells; by-value captures move now | an aggregate of the environment |
| `FnValue` | a function item as a value | a constant |
| `Handle`, `Scope` | push a mark and a body frame | a terminator that runs another body |
| `ScopeWait`, `Fork` | wait for children | a terminator that can suspend |
| `Print`, `Assert` | debug output; an assertion that aborts the task | a call; a terminator with an abort edge |
| `RangeIter`, `ElemIter`, `IterNext` | `for` loops | an iterator local and a `switch` |
| `Fault` | a compile error that becomes a run-time error | `unreachable` |

The interpreter code is already a CFG for each body, with explicit places, reads,
borrows, temporaries and drop points. It differs from a MIR-like IR in five ways. It
uses an operand stack, not named temporaries. It decides copy or move from the value. It
ties temporaries to statement marks at run time. It drops values on normal paths only:
the unwinder finds the values of a frame at run time. It has no edges for suspension
and abort: the machine handles them.

## 2. Evaluation order

### 2.1 The rules

| Construct | Order | Source |
| --- | --- | --- |
| `f(args)`, `f` a function item | the arguments in the order of the parameters: a named argument goes to its parameter, the others fill the free parameters in written order, a trailing block goes to the last free parameter; then the call | `call_fn`, `compile.rs:1393` |
| `Type.f(args)`, `module.f(args)` | as a function item; the receiver position is a plain first argument | `method_call`, `:1461` |
| `x.m(args)`, `x` a value | the receiver as a place (a temporary if it is not a place); the arguments in written order, or in parameter order if sema gives an order (`FnFacts::arg_order`); then the call reads the receiver | `method_call`, `ordered_args` `:1295`, `call_method` `exec.rs:1047` |
| `v(args)`, `v` a local | read (copy) `v`; the arguments in written order, or in parameter order from sema; then the call | `call`, `:1326` |
| `(e)(args)`, another callee | the callee expression; the arguments in written order; then the call | `call` |
| an operation `op(args)`, `E.op(args)` | the arguments in the order of the parameters; then the perform | `op_args`, `:1253` |
| `fork(f, g, ...)` | each branch value in written order (the trailing block last); then the spawns, in order | `:1352`, `fork` `exec.rs:1293` |
| `print(a, b, ...)` | each argument as a place (not read); then `Print` reads all of them | `:1343`, `exec.rs:579` |
| `(a, b)`, `[a, b]`, `Some(a)` | written order | `expr_inner` |
| `S { b: x, a: y }` | written order of the fields in the literal | `struct_lit`, `:1135` |
| `S(x, y)`, `S(b: x, a: y)` | the order of the fields of `S` | `positional_struct`, `:1165` |
| `a op b` (arithmetic, comparison) | `a` as a place (not read); `b` as a place or a value; then the operator reads both | `operand`, `:1109`; `Bin`, `exec.rs:339` |
| `a && b`, `a \|\| b` | `a` (read); `b` only if needed | `:809` |
| `-a`, `!a`, `"{a}"` | `a` as a place; read at once by the next instruction | `:1109` |
| `p.f` | the base place, then the field step; references, `Box` and `Rc` are followed at the step | `place`, `:1075` |
| `p[i]` | the base place (not followed yet); then `i`; then the step follows references from the base and checks the bounds | `:1075`, `Index` |
| `&e` | the place of `e`, or a temporary for a value; then the reference | `borrow`, `:1122` |
| `x = v` | `v`; then the target place (its index expressions run now); then the store drops the old value | `StmtKind::Assign`, `:481` |
| `x += v` | `v`; then the target place; then the store follows references, reads, computes and writes | `:481`, `CompoundStore` |
| `let pat = e` | `e`; then the binding (a tuple or struct pattern splits the value) | `stmt`, `:465` |
| `if c { a } else { b }` | `c`; then one branch | `:878` |
| `match e { arms }` | `e` as a place (a temporary for a value); then each arm tests the place in order; the matching arm binds and runs | `:894` |
| `while c { b }` | `c` as a statement of its own; then the body | `:517` |
| `for p in e { b }` | `e` (a place or a temporary), or `lo` then `hi` for a range; then the hidden iterator; then each iteration binds `p` | `for_loop`, `:596` |
| `return e` | `e`; then `Return` ends the frame | `:504` |

`sim.run` gets `workers = 4` when the call leaves it out (`compile.rs:1437`).

### 2.2 Late reads: an unsound gap (new)

The compiler gives a place operand to an instruction that comes later. Between the
place and the read, other operands run. So the read sees the state after them:

- `x + { x = 5; 1 }` gives `6` for `x = 1` (p1).
- `r.hp + { v.push(E { hp: 2 }); 1 }`: the checker accepts it. The oracle faults: a read
  of a freed cell (p2). `r` is used where it is written, in the facts. The machine reads
  through `r` after the push.
- `print(r.hp, { v.push(E { hp: 2 }); 1 })`: accepted; the oracle faults (p9). The stock
  machine prints `<dangling>`.
- `r[{ vs.push(Vec.new()); 0 }]` with `r = &vs[0]`: accepted; the oracle faults (p10).
  The `Index` step follows `r` after the index expression ran.

These shapes are correct in the checker:

- A by-reference method receiver: `r.add({ v.push(...); 1 })` is W0301 (p8). Sema puts
  the use of the receiver at the call.
- A compound assignment: `r.hp += { v.push(...); 1 }` is W0301 (p11).
- A string interpolation: `ToStr` reads the operand at once (p13).

The cause: sema puts the use of a place operand at the operand. The machine reads it at
the operator. The IR must choose one point, and both sides must use it. Two choices:

- **A. Read at the operand (the MIR order).** The IR copies a copy operand into a
  temporary where it is written. For an operand that is not copied (`a == b` on two
  `Vec`), the IR borrows it where it is written and reads through the reference at the
  operator. The interpreter changes: `operand` emits a `Read` or a `Borrow` at once.
  Then a later invalidation of the operand is W0301 on the temporary reference, as for
  each other reference. This is the usual rule, and it makes `x + { x = 5; 1 }` give `2`.
- **B. Read at the operator (the order today).** The IR keeps the place in the operand
  and puts the use at the operator statement. The interpreter does not change. The IR
  must then keep the base of an index as a place until the `Index` step.

Choice A is simpler for the facts: each operand is a value at a point. It changes the
value of programs such as p1. No corpus program depends on it (an assumption: I did not
run the corpus with a changed interpreter).

### 2.3 Other notes on order

- Named arguments: sema and the machine agree. `f(q: v.len(), p: v)` with `p` by value
  moves `v` first, and the checker reports W0302 (p6).
- A by-value receiver moves at the call, after the arguments read it:
  `b.eat(b.items.len())` runs, and the checker accepts it (p7). This is correct.
- A callee value is copied before the arguments run. A later new value of the local
  does not change the callee of this call.
- The parser keeps each part of 32 operators of a long chain in a hidden local
  (`docs/grammar.md`, rule 11). That reads the places of the part at the `let`. With
  choice B, this changes when a place is read. With choice A, it changes nothing.
- An argument of a non-reference parameter that is a reference to a copy value is read
  through the reference at the call (`coerce_args`, `exec.rs:975`). The IR needs an
  explicit read there.

### 2.4 Implicit dereference

Weft has no dereference operator. The machine follows pointers at these points:

| Point | Follows |
| --- | --- |
| `Field`, `Index`, `BorrowAll`, `ElemIter`, a pattern test | references, `Box`, `Rc` (`resolve`, `exec.rs:119`) |
| a method receiver | references, `Box`, `Rc`, until a type with the method |
| `CompoundStore` | references only |
| `Bin`, `Neg`, `Not`, a condition | references only (`deref_value`) |
| `Store` | nothing: `r = v` on a reference local gives `r` a new reference |
| `Untuple`, `Unstruct` of a reference | references, `Box`, `Rc`; the parts become references (copies for scalars) |
| a call of a reference to a function value | references |

The IR needs an explicit `Deref` projection for each of these steps. The stability of the
step comes from the pointer type (ADR 0003).

## 3. Moves

### 3.1 When a value moves

| Form | When the value moves | Source |
| --- | --- | --- |
| an operand that is read (`let y = x`, an argument, a field value, a return value) | when its `Read` runs, at its place in the order of section 2 | `Read`, `use_place` |
| a by-value method receiver | at the call, after the arguments | `call_method` |
| a by-value capture of a closure | when the closure is made: the value goes into a new cell of the closure | `MakeClosure`, `exec.rs:511` |
| a capture of a clause or of a handled body | when the code reads it (there is no by-value list) | `Handle`, `exec.rs:542` |
| a capture of a scope body | when the code reads it | `Scope`, `exec.rs:566` |
| a binding in a `match` arm, not through a reference | when the arm binds: the part moves out of the scrutinee place | `pat_bind`, `exec.rs:922` |
| `let (a, b) = t`, `let S(a, b) = s` | `t` moves when it is read; the parts then go to the new locals | `untuple`, `unstruct` |
| the tail of a block | into the value of the block | section 5 |
| a place of a local in statement position (`v`, `p.tx`, `v[i]`) | never: it names the place only; its index runs | `:473` |

- Sema gives the interpreter the by-value captures for each closure span
  (`FnFacts::by_value`, `by_value_captures`). An inner closure that moves a capture makes
  each closure around it take the value too (ADR 0003).
- A move out of a part (`take(p.a)`) leaves `Moved` in the part. The rest of the local
  stays. At the end of the scope the machine drops what is left.
- A move out through a reference is possible in the machine (`Read` through a
  reference takes the value). Sema rejects it (W0303, p26). The IR must keep this rule.
- A move of a `!Move` value moves it in the machine. The cell of a local never moves, so
  a reference into a `!Move` local keeps its address while the value stays there. Sema
  forbids the move (W0604).

### 3.2 Consume points of linear values

The linear record of a struct (`Linear`, verified) changes state here:

- `Consume`: a destructuring by value (`Unstruct`; a `match` or `let` pattern of the
  struct, not through a reference); a `join` or a `detach` of a task handle.
- `Unwind`: the unwinder, before `on abort` (section 7).
- A move into a call does not consume. The callee gets the value with its live record.
- A drop of a live linear value is a leak. The stock machine does not see it. The oracle
  reports it (`drop_lin`). The checker must prevent it (W0601).

## 4. Temporaries and their lifetimes

### 4.1 Where temporaries come from

`place_or_temp` (`compile.rs:1115`) and `borrow` make a temporary cell for a value that
is not a place:

- the base of a field step or of an index (`mk().x`, `mk()[0]`);
- a method receiver (`mk_v().len()`);
- a `match` scrutinee;
- the source of a `for` loop;
- `&e` and `&e[]` for a value `e`.

A value on the operand stack (an argument that waits for the call) is not a temporary
cell. It lives until the instruction that takes it.

### 4.2 When temporaries end

A temporary ends at the `StmtEnd` of the innermost open statement. These are the
statements:

| Statement | Temporaries end |
| --- | --- |
| each statement of a block that is not the tail | at its end |
| the tail expression of a block | not a statement: its temporaries belong to the statement around the block |
| the condition of `while` | at the end of the condition, before the body |
| the body of `while`, `loop`, `for` | the non-tail statements at their end; the tail temporaries at the end of the whole loop statement |
| the tail of a frame body (function, closure, clause, handled body, scope body) | at `Return`, after the value left the frame |

Results:

- `let w = Rc.new(5).downgrade()`: the `Rc` ends at the end of the `let`. A later
  `w.upgrade()` gives `None`. In one statement, `Rc.new(6).downgrade().upgrade()` gives
  `Some` (p19).
- `let w2 = { Rc.new(7).downgrade() }`: the tail temporary belongs to the `let`, so it ends
  there (p19).
- The temporaries of an `if` condition and of a `match` scrutinee live through all
  branches, to the end of the statement.
- **New.** The tail temporaries of a loop body live until the loop statement ends. They
  pile up (p24: the `Rc` of iteration 1 is still alive in iterations 2 and 3, and dead
  after the loop). The facts are not wrong here if sema ends them earlier: an earlier
  end only frees more. But memory grows with the number of iterations, and the IR must
  choose one rule. Proposal: end them at the end of each iteration, in the IR and in the
  interpreter (`loop_body` wraps the body in `StmtBegin` and `StmtEnd`).
- The tail temporaries of a frame body end after the value leaves. A value that points
  into one of them dangles (O3-2 for a handled body and a scope body, O3-3 for a clause
  and the argument of `resume`). The R3a fixes (another workflow, not in b073ea7) hold
  the value across the end in the facts. In the IR,
  the frame body moves its value into the return local first, and then the temporaries
  end. The value still dangles if it points into a temporary. So the facts must free the
  temporary before the value leaves, at the `Return`, with the return local live.
- `break` and `continue` drain the operand stack above the loop mark and end the
  temporaries of the statements that opened in the loop (`Break`, `exec.rs:392`). They end
  the slots of the scopes in the loop first (`jump_out`, `:575`). A value on its way to a
  call goes away at the jump (ADR 0007).
- `return` ends all temporaries and slots of the frame.

## 5. Blocks, tails and frame ends

### 5.1 Blocks

`block` (`compile.rs:433`) opens a scope, runs `block_body`, and ends the slots of the
scope with `DropSlots`. `block_body` (`:441`) wraps each statement but the tail in
`StmtBegin` and `StmtEnd`. The tail expression leaves the value of the block on the
stack. A block with no tail expression gives `()`.

### 5.2 Tails and discarded values

- The tail is a value. A place there is read: it moves into the value of the block, or
  it is copied.
- An expression statement pops (drops) its value, and then its temporaries end.
- A place of a local in statement position names the place only (`local_place`). It
  moves nothing and drops nothing (ADR 0003).
- These tails go away: a block statement `{ v }`, the body of a loop (each iteration
  pops it), the branch of an `if` with no `else` in statement position. The value moves
  into the tail and the `Pop` drops it. A linear value there is a leak (W0601).
- A `match` keeps the scrutinee place on the stack while the arm runs. The arm bindings
  end after the arm value is on the stack. `Nip` then removes the scrutinee place.
- The value of an `if` or a `match` is the value of the branch that ran. It moves into
  the value of the expression.

### 5.3 Frame ends

At the end of each frame body the order is:

1. the tail value is on the stack;
2. a scope body waits for its children (`ScopeWait`), and raises the failure of a child
   once (section 9);
3. `DropSlots` ends the locals of the outer block, in declaration order;
4. `Return` pops the value and ends the frame: the rest of the operand stack, then the
   temporaries (the tail temporaries too), then the parameters and the other slots, in
   slot order;
5. `deliver` (`effects.rs:132`) gives the value to the frame below. It passes down
   through marks: a `Handle` mark ends the handler, a `Scope` mark ends the scope, a
   `Timeout` mark removes its timer, a `Sim` mark ends the simulation, a `Clause` mark
   ends or aborts its continuation (section 8).

The value of each frame body therefore leaves after its locals end, and its tail
temporaries end after it left. A reference in the value into either is a dangling
reference.

## 6. Drops at the end of a scope

- `DropSlots` ends the cells of the listed slots in declaration order (`exec.rs:247`).
- `end_cell` (`heap.rs:324`) drops the value of a cell if the value is not copied. A copy
  value stays readable, so a closure that captured the cell of an integer can still read
  it after the scope (ADR 0003, `kept(T, Rt)` in ADR 0006). With the oracle on, the cell
  is marked as ended, so a reference into it dangles.
- `drop_value` (`heap.rs:273`) is recursive. It frees the buffer of a `Vec` and the
  target of a `Box`, and drops their contents. It decrements the strong count of an
  `Rc`; at zero it drops the object, and it frees the cell if no `Weak` is left. It
  decrements the count of a `Weak`. It does nothing for a closure (the owned cells stay,
  I3-5), a task handle, a continuation or a scope capability.
- `x = v` drops the old value after the store. A part store (`p.a = v`) drops the old
  part.
- No user code runs at a normal drop. Weft has no destructors. So the order inside one
  drop point is not visible. The statement where a drop occurs is visible through
  `Weak.upgrade` (p19, p24) and through the oracle.
- A task handle that goes away does not end the task. The scope still joins it, and the
  result of the task goes away with no consume (O3-4, I3-1).

The IR needs a `StorageDead` (or `Drop`) for each local and temporary on each normal
path, at the points of sections 4 and 5. It does not need an order inside one point,
but one order must be fixed so that the IR and the interpreter agree. Declaration
order matches today.

## 7. Unwinding and `on abort`

### 7.1 What starts an unwinding

| Cause | What unwinds | After the unwinding | Source |
| --- | --- | --- | --- |
| a clause returns and did not resume (a fresh continuation, `once` or `multi`) | the frames of the continuation | the value of the clause goes to the frame below the clause | `deliver`, `effects.rs:132` |
| `Fail.fail` reaches no user handler (a root `fail`), in the root task | all frames of the task | the task ends with a failure | `root_op` `:735`, `abort_task` `:206` |
| a root `fail` in a child task | all frames of the child | the child ends failed; the scope records the failure | `root_op` |
| `assert` with a false condition | all frames of the task | the task ends with an assertion failure; it is not a perform of `fail`, so no handler gets it | `Assert`, `exec.rs:588` |
| a cancel, at the next suspension point | all frames of the task | the task ends cancelled | `check_interrupt`, `mod.rs:1061` |
| a `with_timeout` deadline, at the next suspension point | the frames from the `Timeout` mark up | `fail("timeout")` with the handlers at the `with_timeout` call | `timeout_unwind`, `:221` |
| a child of a scope or a `fork` failed, at the next suspension point of the owner while the scope frame is on its stack | the frames from the scope frame up | `fail(msg)` with the handlers at the `scope` or the `fork` | `scope_fail_unwind`, `:252` |

A fault is not an unwinding. An index out of bounds, an overflow, a division by zero, a
use after a move, a missing handler of a user effect, and a `Fault` instruction stop the
whole run with an error (`step()?` in `run_quantum`). No `on abort` runs (p28). The IR
needs a trap terminator with no cleanup edge for these.

### 7.2 The algorithm

`unwind_step` (`effects.rs:303`) and `unwind_frame` (`:353`):

1. Prepass: cancel each child of each scope and `fork` in the frames to unwind, also in
   the fresh continuations of clause frames there. Wait until they end
   (`Wait::Children`).
2. Take the top frame (the innermost one).
   - A code frame: take its values innermost first (`frame_values`, `:424`): the operand
     stack from the top, then the temporaries (newest first), then the slots (highest
     slot first). Take the live linear values out of each value (`extract_linear`,
     `:455`): a live linear struct as a whole, a live task handle, and the parts of
     structs, enum values, tuples, lists and owned `Vec` and `Box` buffers, in field
     order. Drop the rest at once. Mark each linear value aborted (`unwind_lin`); a live
     value with no `on abort` is a fault. Queue the values.
   - A `Clause` mark: if its continuation is fresh, its frames join the frames to unwind,
     on top, so they unwind next. Else drop them with no `on abort` (`drop_frames`).
   - A `Scope` or `Fork` frame: cancel the children that run and wait for them.
   - A `Timeout` frame: remove its timer. A `Sim` frame: end the simulation. A `Handle`
     mark: nothing.
   - An inner `Unwind` frame: merge its frames and its queue; drop its value (I3-3).
3. Before the next frame, run the queued `on abort` functions one at a time, in queue
   order. Each runs as a normal code frame with the root handlers only
   (`HEnv::default()`), and gets the value without its linear record. Its result is
   dropped. For a task handle, cancel the task.
4. At the end, do the `After` action of the table in 7.1.

### 7.3 Order (new)

- p18: locals `a` (slot 0, made last), `b` (slot 1), `c` (slot 2), then `fail`. The output
  is `caught boom`, `rollback 3`, `rollback 2`, `rollback 1`. So the order is the reverse
  slot order, not the reverse order of creation.
- p20: a clause holds `c` and calls `fail`; its continuation holds `b`. The output is
  `caught x`, `rollback 2` (the clause frame), `rollback 1` (the continuation).
- The clause of the handler that catches the failure runs first, and the unwinding comes
  after it (both probes). This is the same as `do_return` in the effects model.
- The effects model (`proofs/effects/src/model.rs`) takes the newest resource of a frame
  first (`max_slot`), and it drops a fresh continuation of a clause frame before that
  frame's own resources (`step_unwind_drop` before `step_unwind_abort`). Both orders
  differ from the interpreter. No theorem depends on the order, because the model treats
  `on abort` as atomic and W0118 lets it change only its own value. But an `on abort` can
  print and log, so the order is visible. The IR must fix one order, and the model or
  the interpreter must follow it.

### 7.4 Known gaps of the unwinder

These are interpreter defects of round 3. The IR does not remove them, but its cleanup
paths must name these values:

- The cells of a closure (by-value captures) and the result of a finished child are not
  unwound (I3-2). A cancelled task that never ran drops its linear capture (F3-8).
- An interrupt during an unwinding cuts a running `on abort` (I3-3).
- A linear result of a task goes away when its handle is not kept (O3-4, I3-1).

## 8. Handlers, perform, resume and continuations

### 8.1 Install and resolution

- `Op::Handle` (`exec.rs:542`) makes a fresh handler id, captures the cells of the
  clauses and of the body, pushes a `Handle` mark with the handlers outside it
  (`outer`), and pushes the body frame with the handlers `henv + (effect -> id)`.
- Resolution is lexical. A perform uses the handlers of its frame (`henv`). A closure
  frame uses the handlers where the closure was made. A call of a function item uses
  the handlers of the caller frame. A function item as a value uses the handlers of the
  innermost code frame where it is called (`top_henv`). A clause uses `outer`: an
  operation in a clause goes to a handler outside its `handle`.
- `find_handler` (`effects.rs:57`) takes the handler instances of the effect, innermost
  first, and uses the first whose mark is on the stack of the current task. If no mark is
  found, the operation goes to a root handler (section 8.5). So a closure that leaves its
  `handle`, or runs in another task, reaches an outer handler or the runtime. W0313 and
  W0314 forbid these programs.
- An effect has an identity (`effects::identity`): a user effect `main.Log` is not the
  standard `Log`. The compiler and sema use the same resolution.

### 8.2 Perform

`perform` (`effects.rs:25`):

1. Find the handler mark (index `idx`) and the clause.
2. Move the frames from `idx` to the top, the `Handle` mark included, into a new
   continuation record with the verified state machine `Continuation::new(multi)`.
3. Push a `Clause { cont }` mark and a frame for the clause. Its arguments are the
   operation arguments and the continuation value (the parameter `resume`). Its handlers
   are `outer`.

The handler mark is in the continuation, so a resume installs the handler again: the
handlers are deep. The clause runs in place of the handled computation, below it.

### 8.3 Resume

`resume` (`effects.rs:99`) is a call of the continuation value:

1. `Continuation::resume` fails for a second resume of a `once` continuation and for a
   continuation that was dropped or ended (a fault).
2. A `once` continuation gives its frames back. A `multi` continuation keeps its frames
   as a template and gives a copy (8.4).
3. The frames go on top of the clause frame. The value goes to the top frame: it is the
   result of the `Perform`.
4. A `with_timeout` deadline that passed while the frames were away fires now.

When the handled computation ends, its value passes the `Handle` mark (the handler ends)
and arrives in the clause frame as the result of the `resume` call. A second operation
in the resumed computation captures a new continuation from the mark, which is now above
the first clause. So the clauses of a deep handler nest.

When the clause returns (`deliver`, `Clause` mark):

- If the continuation resumed, `end` closes it, and the template frames (of a `multi`
  continuation) go away with no `on abort`.
- If it did not resume, `drop_now` aborts it: its frames unwind (section 7), and then the
  value of the clause goes to the frame below. This holds for `once` and for `multi`.
- The value of the `handle` expression is the value of the body if no clause ended at the
  outer level, or else the value of the outermost clause.

A `Fail` clause cannot resume (W0504). The continuation value is a copy value: a closure
can hold it. W0313 and W0314 keep it inside its clause.

### 8.4 `multi` copies

`copy_frames` (`effects.rs:590`) makes the copy for each `multi` resume:

- The cells that the frames own get new cells: the slots and the temporaries of each code
  frame, and the `Vec` and `Box` buffers that they reach. The cells of the continuations
  of `Clause` marks inside, at any depth, are copied too, and each such continuation gets
  a new record in the same state.
- References, places, slices, iterators and closures that point into a copied cell point
  into the copy. The clauses of a `Handle` mark in the frames capture the copies.
- An `Rc` is shared, and its count goes up. A `Weak` is shared.
- A cell outside the frames is shared: a local outside the handled body keeps the value
  of the run before (ADR 0005). The owned cells of a closure are not copied either.
- A `Timeout` frame gets a new id with the same deadline. A `Scope`, `Fork` or `Sim` frame
  is shared: the copies share one scope record (I3-8).

The IR side: ADR 0005 lowers a handled body with a `multi` operation as a loop. Each node
that can run a clause gets a path back to the nodes after it, through a node that gives
each local of the body its copy again. The IR can make this a re-entry edge of the
terminator.

### 8.5 Root handlers

`root_op` (`effects.rs:735`) handles a standard operation that no user handler takes:

| Operation | Run-time meaning | Suspension point |
| --- | --- | --- |
| `Log.*` | write to standard error | no |
| `Fail.fail` | abort the task (a child: the failure goes to its scope) | not a suspension; it unwinds |
| `Clock.now` | the virtual time (in a simulation, from its start) | no |
| `Clock.sleep`, `sleep(d)` | block until the virtual time | yes |
| `Rand.*` | the random value of the run or of the simulation | no |
| other standard operations (`Async`, `Net`, `Fs`, `Blocking`) | yield | yes |

A user effect with no handler is a fault. With no runtime (`--no-runtime`), each
standard operation outside `sim.run` is a fault, except `fail` in a child. An extern
function with `blocking` runs on the blocking pool: the task waits one tick (a
suspension point).

## 9. Tasks, scopes, `fork`, cancellation and timeouts

### 9.1 Scopes and spawns

- `Op::Scope` (`exec.rs:566`) makes a scope record (owner, children, handlers), pushes a
  `Scope` mark, and runs the body with the scope capability as its parameter. The body
  captures cells by reference.
- `s.spawn(f)` (`call_method`, `spawn_task` `exec.rs:1219`) makes a task frame for `f`: a
  closure frame with the cells and the handlers of the closure, or a function item frame
  with the handlers of the spawning frame. The task is a child of the scope of `s`. It
  starts on the worker of its parent. The checker marks it stealable or pinned. The handle
  is a linear record whose `on abort` cancels the task.
- At the end of the scope body, `ScopeWait` (`:1250`) waits for all children. Then it
  raises the first failure of a child, once, as `fail(msg)` with the handlers of the
  `scope`. Then the locals of the scope body end (5.3). So the tasks join before the
  locals of the scope go out of scope (ADR 0006).
- `t.join()` (`natives.rs:442`) runs again until the task is done (a suspension point).
  Then it consumes the handle. A value gives the result. A failure or a cancel does
  `fail(msg)` with the handlers of the join. But the owner checks the failure of the
  scope first, so a handler at the join does not get a failure of a scope child (I3-9).
- `t.detach()` consumes the handle. The result is not dropped (I3-5).

### 9.2 `fork`

`fork(f, g, ...)` (`exec.rs:1293`, `:1312`) evaluates all branch values first, makes an
implicit scope with the handlers at the `fork`, spawns the branches in order, consumes
their handles, and pushes a `Fork` frame. When all branches are done: if one failed, it
drops the other results and does `fail(msg)` with the handlers at the `fork`. Else it
gives the tuple of the results, also when each one is `()`.

### 9.3 Cancellation and suspension points

- `cancel(t)` (`mod.rs:648`) sets a flag and wakes a blocked task. The task acts on it at
  its next suspension point (`check_interrupt`, `mod.rs:1061`): it unwinds all its frames
  and ends cancelled. A task that is already unwinding ignores new interrupts only if
  `abort_task` started the unwinding (I3-3).
- Suspension points: a root operation that yields, `sleep`, a blocking call, a `join` that
  waits, the end of a scope that waits, a `fork` that waits, and the first run of a new
  task. A perform to a user handler is not one. `Log`, `Clock.now` and `Rand` at the root
  are not. A loop back-edge can preempt the task, but it does not check interrupts.
- A child that fails cancels its siblings. The owner raises the failure at its next
  suspension point while the scope frame is on its stack, or at the end of the scope. If
  the scope frame is in a continuation, the owner raises it when a resume puts the frame
  back, or at the end of the scope.
- Sema counts each named effect operation, each call that can reach a handler, and each
  join point as `may_abort` (ADR 0005). This covers the suspension points, and it is
  wider than them. `assert` is the gap (section 14).

### 9.4 `with_timeout` and `sim.run`

- `with_timeout(d) { body }` (`natives.rs:327`) adds a timer, pushes a `Timeout` frame
  with the handlers at the call, and calls the body closure. When the timer fires, the
  task gets an interrupt. At its next suspension point it unwinds to the `Timeout` frame
  and does `fail("timeout")` with the handlers at the call. A deadline that passes while
  the frame is in a continuation fires at the resume. A normal end removes the timer.
  Known gaps: I3-4 (two deadlines at one instant, an `advance` before a continuation).
- `sim.run(seed, workers) { body }` (`:350`) pushes a `Sim` frame and calls the body. The
  code above the frame, and each task that it spawns, run in the simulation: its clock
  offset, its randomness and its scheduler. Known gaps: I3-6, I3-7.

### 9.5 The scheduler

One OS thread runs `N` virtual workers. A seeded random choice picks a ready task. An idle
worker steals only a stealable task. Preemption occurs at `BackEdge` after a quantum of
steps (1000 by default). The design says that preemption is invisible: it does not
change what the program can see except the interleaving.

## 10. `Rc`, `Box`, `Vec`, `Weak` and references

| Value | Representation | Copy | Drop | Access |
| --- | --- | --- | --- | --- |
| reference `&T` | `Ref(place)` | copied | nothing | followed by field, index, method and arithmetic (2.4) |
| slice `&v[..]` | buffer, `lo`, `hi` | copied | nothing | elements in range |
| `Vec<T>` | handle to a buffer cell | moved | frees the buffer, drops the elements | `push`, `pop`, `clear` change the length; with the oracle each one moves the buffer, so a reference into the old one dangles |
| `Box<T>` | handle to a target cell | moved | frees the target, drops it | followed by field, index and method |
| `Rc<T>` | handle to a counted cell | moved; `clone` adds one | count minus one; at zero, drops the object | followed by field, index and method; a place through it is in the `rc` group root (ADR 0003) |
| `Weak<T>` | handle to a counted cell | moved | weak count minus one | `upgrade` gives `Some` while the strong count is above zero |

- `v.get(i)` gives a reference to the element. `split_at` and `split_mut` give two
  slices. A `for` over a `Vec` or a slice gives each element: a copy for a scalar
  (integer, `bool`, `()`, `String`, `Duration`), else a reference to the element. It reads
  the length of the buffer at each step.
- A `multi` resume copies `Vec` and `Box` buffers and shares `Rc` objects (8.4).
- The IR needs a `Deref` projection with the stability that the pointer type declares
  (`extern type Vec<T> { elem: unstable }`), and a `Len` read for an index (ADR 0006).

## 11. Integers

- A run-time integer is an `i64`. Arithmetic is checked on `i64`: an overflow, a division
  by zero and a remainder by zero are faults.
- Sema gives each arithmetic expression its integer type (`FnFacts::int_ops`, by span).
  The compiler adds `CheckInt(ty)` after the operation (`check_int`). The check faults if
  the result does not fit the type (`IntTy::range`). A compound assignment takes its type
  from the span of its value.
- A `u64` or a `usize` above `i64::MAX` cannot exist at run time. It faults as an
  overflow of the arithmetic before (p23).
- A literal that does not fit its type is W0102 at compile time (p22). The machine checks
  only the result of arithmetic, a negative value in an unsigned struct field at a
  store, and a negative argument of an unsigned parameter.
- `Duration` addition saturates, and subtraction faults below zero.

The IR should carry the integer type in each arithmetic statement. Then the side table by
span goes away.

## 12. What the IR must state

Each item below follows from sections 2 to 11. Items marked "choice" need a decision.

1. One body for each code unit: function, test, closure, clause, handled body, scope
   body. A `handle` is a terminator that runs the body and names the clause bodies. A
   `scope` is a terminator that runs the body. Each body has one exit (W0315).
2. Operands are explicit. Each operand is a constant, `copy p` or `move p`. The read
   point of a place operand is a choice (2.2). Choice A (read at the operand) needs an
   interpreter change. Choice B keeps the interpreter.
3. Named arguments are in parameter order in the IR. The builder computes the order once.
   The span-keyed table `FnFacts::arg_order` goes away.
4. Assignment order: the value, then the target place, then the store with a drop of the
   old value.
5. A receiver by value moves at the call. A receiver by reference is a place that the
   call follows.
6. Places have explicit `Deref` steps for references, `Box` and `Rc` (2.4), and an index
   reads the length (`Len`).
7. Temporaries are locals with `StorageLive` and `StorageDead`. They end at the end of
   the innermost statement. The tail of a block belongs to the statement around it. Choice:
   the tail temporaries of a loop body end at each iteration (needs an interpreter change)
   or at the end of the loop (today).
8. The tail of a frame body moves into the return local. Then the locals end, then the
   temporaries, then the frame returns. A reference into any of them in the value is a
   dangling reference.
9. A discarded value is dropped at once: an expression statement, a block statement, a
   loop body tail, an `if` with no `else` in statement position, `let _ = e`. A place of a
   local in statement position is not a read.
10. A closure literal is an aggregate of its environment: a reference to the cell of
    each by-reference capture, and a move of each by-value capture. The capture rule is
    one function that the builder and the interpreter share (today `FnFacts::by_value`
    crosses by span). A clause and a handled body capture by reference only.
11. Drops on normal paths at the points of sections 4 to 6, in a fixed order.
12. Cleanup paths for each terminator that can abort, in a fixed order (choice, 7.3):
    take the values of the frame, take their live linear parts, call `on abort` with the
    root handlers. Terminators that can abort: a perform, a call that can reach a handler
    or abort, a `resume`, a `join`, a scope end, a `fork`, a suspension point (a cancel,
    a timeout), and `assert`.
13. A trap terminator for faults, with no cleanup path.
14. A `multi` perform has a re-entry edge. The re-entry copies the locals of the handled
    body and shares the others (8.4).
15. Perform and resume are calls: a perform names a capability (a handler instance of the
    body, or the row of the function); `resume` calls the continuation. The capability
    and the continuation can be locals with storage (choice; sibling class CAP).
16. Spawn, join, scope end and `fork` are terminators with the task id. A spawn whose
    handle is not kept still joins at the scope end (O3-4).
17. Each arithmetic statement carries its integer type.
18. The interpreter runs the IR, or compiles the IR to its stack code. Then `compile.rs`
    and the span-keyed exports (`by_value`, `arg_order`, `int_ops`) go away. The second
    form keeps `machine/` as it is: frames, effects, the unwinder and the scheduler need
    no change. It replaces only the 1544 lines of `compile.rs` with a lowering of an IR
    that already has its order, temporaries and drops.

## 13. The proof models and a CFG IR

### 13.1 B1: the CFG model (`proofs/borrowing/src/cfg.rs`)

- A CFG is a sequence of nodes. A node has one instruction (`Instr`) and a list of
  successors. Node 0 is the entry. A node with no successors is an exit.
- The model does not evaluate conditions. A run can take any successor. A run can stop at
  any point (a safe abort).
- `cfg_check(cfg, ss0, ann)`: each node has an annotation (`SState`: the locals, the
  valid reference variables with their groups, the valid closure values with the groups of
  their captures). Each instruction is accepted in its annotation (`instr_ok`). For each
  edge `n -> m`, `ann[m]` is a `sub_state` of `post(ann[n], instr)`. The intersection
  (`join`) is the greatest such state.
- `cfg_soundness`: if the checker accepts, no run that follows the edges has UB.
- The instructions (`model.rs`): `Borrow { dst, x }` (a reference to a local),
  `Child { dst, src, label }` (a reference into a child group, an unstable step),
  `Copy { dst, src }`, `Read { src, field }`, `Write { src, field, val }` (an inline
  primitive), `Call { args: [(var, is_mut)], ret }`, `MkClosure { clo, caps }` and
  `Invoke { clo, args, ret, once }` (a closure call, a perform or a resume).
- What the base model does not have: owned values that move, locals that end (the set of
  locals is fixed for the whole run), temporaries, aggregates that hold references, frees
  of an owner, a reference with more than one place, stable field steps (they are in B3).

**Closeness to a CFG IR: high for control, medium for the vocabulary.** A basic block of
statements and a terminator becomes a chain of B1 nodes, one for each statement. A
`switch` or a call with a normal edge and an abort edge becomes a node with several
successors. The reference statements of the IR map one to one: `r = &x` to `Borrow`,
`r = &(*s).label[i]` to `Child`, `r = copy s` to `Copy`, a read or a write of a scalar
through `r` to `Read` or `Write`, a call to `Call` with the mutable arguments of the
callee footprint and its returned reference, a closure aggregate to `MkClosure`, a call of
a closure, a perform and a resume to `Invoke`. B1 lacks a statement for the end of an
owner. The IR has `StorageDead(x)` and `move x`, and sema has `frees_at`. A B1 extension
with `Free { x }` (remove local `x` and its tree; the checker kills each reference with
root `x`) would cover them with the same proof shape.

### 13.2 B2: captured references (`model.rs`, `closures.rs`)

A closure, a handler and a continuation are closure values: code and captured
`(pointer, is_mut)` pairs. `lemma_perform_is_call` proves that a perform runs and checks
as a call with the captured references of the handler as extra arguments. This is the
IR rule "a perform is a `Call` terminator through a capability". The link (L2) excludes
`MkClosure` and `Invoke` (`facts_ok`). With a closure aggregate in the IR, the facts of a
closure are the facts of `MkClosure`, so the link could include them.

### 13.3 B3: inline layout (`layout.rs`, `layout_proof.rs`)

- Typed places: a schema gives each type a size and a shape (a primitive, a struct with
  inline fields, an enum with a tag and a payload). A place step is `Field(f)` (stable),
  `Variant(v)` (unstable; valid only while the tag selects `v`) or `Kid(label)`
  (unstable, a child group).
- The instructions (`LInstr`): `Borrow`, `Field`, `Variant` (a safe abort if the tag is
  not `v`), `Child`, `Copy`, `Read { src, path }`, `Write { src, path, val }`,
  `Call { args }`. There is no returned reference and no closure.
- The programs are straight-line (`lcheck`, `is_ltrace`). There is no CFG form.

**Closeness: high for places, low for control.** The IR projections match the steps:
`Field` to `Field`, a downcast after a `switch` on the tag to `Variant`, a `Deref` of a
`Box` and an element of a `Vec` to `Kid`. A `match` that tests a tag and then takes a
payload is the B3 `Variant` instruction on the edge of the arm. B3 needs the CFG lift of
B1 (the same `sub_state` argument) before it can cover an IR body with branches.

### 13.4 B4: tasks (`tasks.rs`)

Two tasks run straight-line programs on one heap. A scheduler interleaves them. The rule
(`separated`): no group in the mutable footprint of one task overlaps a group that the
other task holds at any point. `task_soundness` proves no UB and no data race.

**Closeness: low.** The model has no spawn, no join and no scope: both programs run from
start to end at the same time. An IR has a spawn terminator, the task body, and the part
of the parent between the spawn and the join or the scope end. To use B4, the link must
cut that part of the parent CFG out as the second program. B4 also checks a stronger rule
than W0405 (held groups, not accesses), so it does not cover the access rule of ADR 0006.

### 13.5 The effects model (`proofs/effects/src/model.rs`)

- A program is a map from block ids to blocks. A block has a signature (the effects of
  its capability parameters, the capabilities it returns as closures, and the mode of its
  continuation if it is a clause) and a straight-line list of instructions:
  `Acquire { slot, on_abort }`, `Consume { slot }`, `Call { block, caps }`,
  `Handle { eff, clauses, body }`, `Perform { cap, op }`, `Resume`, `Return`.
- The state has a stack of frames (a code frame with block, pc, capability environment,
  linear slots and continuation; or a handler frame), a pending list for the unwinder,
  the resources, the continuations and the handler instances.
- `Perform` captures the frames from the topmost handler frame of the capability to the
  top, and runs the clause in place of the handler frame, in the environment of the
  `handle`. `Resume` pushes the frames back (a copy for `multi`). `Return` of a clause
  with a fresh `once` continuation sends the frames to the unwinder. The unwinder takes
  the top pending frame, drops its fresh continuation first, then runs `on abort` for the
  newest live resource, one at a time. `step_cancel` aborts at any perform.
- The checker (`checker.rs`) walks each block once with the effects of the capabilities,
  the live linear slots and the state of the continuation. The abort rule and the multi
  rule apply at each suspension point (a call, a handle, a resume, a perform).

**Closeness: high for frames, low for control and values.** The frames, the handler
frames, the continuations and the unwinder of the model are the ones of the interpreter
(section 8). The block structure is the structure of IR bodies. Capabilities are explicit
(`Call { caps }`, `Perform { cap }`): this is the form of item 15 of section 12. The
differences:

| Point | Effects model | Interpreter and IR |
| --- | --- | --- |
| control in a block | straight-line | branches and loops |
| values | linear slots and capabilities only | all values; a linear value moves into calls |
| a move of a linear value into a call | none (`Call` passes no slots) | the callee frame owns it |
| tasks, scopes, `fork`, timeouts | `step_cancel` at any perform | separate frames and rules |
| a fresh `multi` continuation at a clause return | not unwound | unwound (`drop_now`); documented in the link |
| unwind order in a frame | newest resource first | reverse slot order (p18) |
| a clause frame and its fresh continuation | the continuation first | the clause frame first (p20) |
| a fault | not modeled | stops the run |
| `assert` | not modeled | unwinds the task |

### 13.6 The link today (`proofs/link`)

- L1 (places): rule 3 of the exec core and `lkills` of B3 agree. The places of sema are
  a hypothesis.
- L2 (dataflow): on B1 CFGs without closures, if W0301 accepts, the annotation from
  `propagate` passes `cfg_check`. The hypotheses are `facts_ok` (sema gives a well-formed
  CFG, bindings with the static groups of the model, labels that fit), `ret_ok`, and
  `bound_before_use`. The link defines `rebound_at`, `uses`, `points_into` and
  `invalidated_at` from the B1 instructions. `ret_ok` is false for an accepted program
  with the `in` form (ADR 0005).
- L3 (lifecycle): the verified `Continuation` and `Linear` records step with the effects
  model, with three documented differences for `multi`.
- Only tests check the facts that sema emits.

### 13.7 A path to a B6 link over IR -> facts

The IR makes the hypotheses of L2 into a statement about a function, not about sema:

1. **Define the IR in the link crate.** An `IrStmt` enum for the reference fragment, an
   `IrTerm` enum, and a CFG of basic blocks. Include the source file of the IR crate with
   `#[path]`, as the link does for `weft-verified`.
2. **Embed the IR in B1.** `embed: IR CFG -> B1 Cfg`, one node for each statement and
   terminator (13.1). Prove `facts(ir) == link_facts(embed(ir))` for `cfg_edge`,
   `rebound_at`, `uses`, `points_into` and the call rule of `invalidated_at`. Each case is
   one statement kind. Then `facts_ok` and `bound_before_use` become lemmas about the
   builder: the builder gives `StorageLive` and an assignment before each use.
3. **Extend B1 with frees.** Add `Free { x }`. Then `frees_at` (a move of an owner, the
   end of a local) is in the link. `moved_part` needs a free of a sub-tree.
4. **Lift B3 and the effects checker to CFGs.** The B1 argument (`lemma_inv_sub`,
   `join`) applies to B3 with `LSState` and to the effects checker with `SS` (the join of
   the linear slots and of the continuation state must be defined: a slot is live after
   the join only if it is live on each edge, and W0601 rejects a difference).
5. **Fix one unwind order** (7.3) and state it in the IR, the interpreter and the model.
6. **Relate the interpreter to the IR.** If the interpreter runs the IR (item 18 of
   section 12), each machine step is a step of an IR statement. A trace of the machine is
   then a trace of the IR, and the models abstract the IR.

What stays outside: function values that the body does not follow (FNVAL), summaries
(SUM), stored references (STORE), and the `multi` copy of affine values (the effects
proof E5 has no affine values).

## 14. New findings of this mapping

| Id | Kind | Finding | Probe | Status at b073ea7 |
| --- | --- | --- | --- | --- |
| N1 | unsound | A place operand of a binary operator is read at the operator. Sema uses it at the operand. The checker accepts a read through an invalidated reference. | p2 (oracle: read of a freed cell) | open |
| N2 | unsound | The same for the operands of `print`. | p9 | open |
| N3 | unsound | The same for the base of an index whose index expression invalidates the base reference. | p10 | open |
| N4 | unsound | `assert` aborts and unwinds the task, but it is not `may_abort` in sema, also through a callee. A linear value with no `on abort` across it makes the unwinder fault. | p25, p27 | open |
| N5 | semantics | The tail temporaries of a loop body live until the loop statement ends, and pile up over the iterations. | p24 | open; choose a rule (item 7) |
| N6 | model gap | The unwind order in a frame differs between the interpreter (reverse slot order) and the effects model (newest resource first). | p18 | open; choose an order |
| N7 | model gap | The interpreter unwinds a clause frame before its fresh continuation. The effects model does the opposite. | p20 | open; choose an order |
| N8 | semantics | `x + { x = 5; 1 }` is `6`: a consequence of N1. The IR choice A changes it to `2`. | p1 | depends on the choice |

N1 to N3 have one cause: the read point of a place operand. The IR removes it by
construction with either choice of 2.2. N4 needs an abort edge for `assert` and an abort
bit in the summaries (a callee with an `assert` can abort).

## 15. Files

- This document:
  `docs/plan/core-ir-inputs/semantics.md`.
- Probes (sources and the `weft` binary):
  `SCRATCH/ir/probes/`.
  Run `./weft check pN_*.wf` and `./weft run --oracle pN_*.wf` in that directory.
