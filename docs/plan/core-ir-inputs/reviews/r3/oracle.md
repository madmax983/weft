# Review round 3, lens "oracle": differential soundness testing

Commit: b073ea72253fde0bd3e8c0532b404db68de84028 (`review/s5`, after S5b and S5c).
Source copy: `scratchpad/r3/src`. Binary: `scratchpad/r3/target/release/weft`. I did not
change the source copy or the worktrees. All files of this lens are in
`SCRATCH/r3/oracle/`
(below: `ORACLE/`). The repro files are in `ORACLE/repro/`.

## Summary

- I ran 82 140 generated, mutated and swept programs through `weft check`, and 382
  hand-written probes (`ORACLE/probes/`). The checker accepted 22 740 of the programs.
  I ran each accepted program 6 times (seeds 1, 2, 3, 7, 11, 42; workers 1 to 4) with
  `--unchecked --oracle`, and again with the stock interpreter when the oracle found a
  fault. I ran each rejected program 4 times with the oracle.
- I found 7 soundness defects (blockers), 3 major false positives, 3 minor false
  positives and 1 minor defect of the oracle. Each one has a repro in `ORACLE/repro/`.
- One blocker (O3-2, the `let` and assignment forms) and two false positives (O3-7,
  O3-10) are regressions of round 2. The other findings are also in 328a39b. I built
  the heads of R2b, R2c, R2d and R2e to find the stage (`ORACLE/bisect/cmp.sh`).
- The round-2 fixes hold: each round-2 repro (OR1 to OR11) and each round-1 red-team
  probe gets the right result (see "Round-2 checks").

| Id | Severity | Short statement | First bad build |
| --- | --- | --- | --- |
| O3-1 | blocker | A place as the tail of a `scope` body moves in the interpreter, not in the checker | 328a39b (old) |
| O3-2 | blocker | A reference into a temporary of a handled body or a scope body leaves the body | R2c (`let`); 328a39b (argument) |
| O3-3 | blocker | A reference into a temporary of a clause leaves through the clause value or `resume` | 328a39b (old) |
| O3-4 | blocker | A spawn in statement position drops a linear task result | 328a39b (old) |
| O3-5 | blocker | A task or a fork branch that runs a closure from a struct field: no W0405, no W0403 | 328a39b (old) |
| O3-6 | blocker | A task reads through an `Rc` handle; the parent moves the handle: no W0405 | 328a39b (old) |
| O3-14 | blocker | A place as the tail of a handled body moves once for each `multi` resume; the checker counts one move | 328a39b (old) |
| O3-7 | major | W0312 on an operation whose closure argument changes what it captures (false positive) | R2d |
| O3-8 | major | A closure that handles a `multi` operation inside itself is a multi and abort point (false positive) | 328a39b (old) |
| O3-9 | major | A join through a callee, a tuple, an `Option`, `id` or a closure does not end the task (false positive) | 328a39b (old) |
| O3-10 | minor | Two spawns of function parameters get W0503 when the program declares a `multi` operation (false positive) | R2c |
| O3-11 | minor | A move and then a new value of a captured variable invalidates the closure (false positive) | 328a39b (old) |
| O3-12 | minor | A clause conflicts with the task that it spawns (W0405, false positive) | 328a39b (old) |
| O3-13 | minor | `--oracle` does not log a read through a reference in an operand, and `print` hides a moved value | R2e (new code) |

## Method

### Program sources

1. `ORACLE/gen3.py`: a compositional generator. A program is a fixed prelude
   (`ORACLE/lib/pre3.wf`) and a `main` of 1 to 3 episodes. An episode makes a fresh
   object, then a reference, a closure, a task or a linear value through one of many
   channels, then a hazard through one of many channels, then a use through one of
   many channels. Wrappers nest the parts: `if`, block, `loop`, `for`, `while`,
   closure, `apply`, handlers, `scope`, `with_timeout`, `match`.
   - Reference channels: index borrow, `get`, a callee with a stated place, `id`,
     `pass_ref`, a tuple result, a one-place result (`pick_opt`), a tuple part, a
     `Vec<&T>` (also through `keep`), an `Option`, a closure that reads, a returned
     closure (`make_reader`), a reference to the whole `Vec`, `Box` and `Rc` places.
   - Hazard channels: direct, closure, `apply`, `twice`, a stored closure in a `Vec`,
     a struct field, a returned closure, a handler clause, an operation that takes a
     closure, a task, a joined task, `spawn_it`, `fork_it`, `each`, a closure from an
     `if`, a closure that a loop carries, `id`, a `Calls` struct, a function item,
     named arguments.
   - Use channels: `print`, a closure, `apply`, `twice`, a handler clause, a task,
     `spawn_join`.
   - Other episodes: moves (by a call, `let`, a closure that moves, `Some`, a tuple,
     `Box`, a struct, a task, a `Vec`, a block tail, `if` and `match` tails, a place
     statement, `id`, a handled body); linear values (`Tx` with `on abort`, `Lk`
     without it) with aborts, timeouts, failing tasks and many consumers; tasks
     (spawn and parent, joins, two spawns, `fork`, `fork_it`, `spawn_two`, `detach`,
     tuple handles, loops, closures, clauses, nested scopes); effects that leave
     their handler; continuations and `multi` operations.
2. `ORACLE/gen4.py`: one-place call results (`find_n`, `kid_of`, `first_n`) with
   writes through the result, a copy, a second result and the base; references that
   loops carry (rotation, conditional new values, `break`, `continue`); task handles
   in tuples, `Option`s, branches, swaps, loops, callees, closures and clauses.
3. `ORACLE/mutate3.py`: mutation of seed programs: the interpreter programs, the corpus
   programs with `main` or test blocks (the lines with `//~` markers removed, so that
   more of them pass), and 657 accepted generated programs (`ORACLE/seeds3/`). A
   mutation moves, deletes, duplicates or swaps statements, inserts a push, clear,
   pop, move, rebind, borrow or tail place, wraps a statement (block, loop, closure,
   `twice`, handler, scope, task, `fork`, `with_timeout`), swaps `once` and `multi`,
   adds or removes a `resume`, removes a consumer or an `on abort`, removes a
   handler, detaches a task or moves a join.
4. Systematic sweeps (each combination once):
   - `ORACLE/sweep.py`: values that leave a frame. 13 frames (block, `if`, `match`,
     three handled bodies, clause value, `resume` value, scope, closure,
     `with_timeout`, `fork`, task, nested) x 17 payloads (references into
     temporaries and locals, closures that capture locals, outer places in tail
     position) x 5 ways out (`let`, assignment, argument, push, statement).
   - `ORACLE/sweep2.py`: moves, linear consumers and mutations inside 24 frames.
   - `ORACLE/sweep3.py`: function values that perform an operation and leave the
     handler through 18 ways.
   - `ORACLE/sweep4.py`: a task and its parent touch one struct: 5 ways to start the
     task, 10 task accesses, 13 parent accesses, 9 frames.
5. Hand-written probes in `ORACLE/probes/` for shapes that the generators do not make
   (one-place results in `while` conditions, named arguments, late captures,
   operation results that hold references, temporaries, `Rc` stores, `!Move` values,
   stealable tasks, `on abort` handlers).

### Oracles

- `weft run --unchecked --oracle` and `weft test --unchecked --oracle` of the
  commit under review. A `runtime error` that is not an index, an overflow, an
  underflow, a division by zero or a failed `listen` is a fault. A printed
  `<moved>`, `<freed>` or `<dangling>` is a fault too (O3-13).
- The stock interpreter (no `--oracle`) for each oracle fault of an accepted program.
- A patched oracle (`ORACLE/patched/`, binary `ORACLE/target-patched/release/weft`).
  It adds one change: `Machine::deref_value` logs the read (`log_read`), so the race
  detector sees a read through a reference in an operand (O3-13). It gives no false
  alarm on the interpreter programs and on the accepted corpus programs (`run` and
  `test`, seeds 1 and 2). The last runs (`g3p`, `g4p`, `sw4p`, `m3c`) use it.
- Reduction: by hand, from the grouped results (`ORACLE/unsound.py`,
  `ORACLE/fpgroups.py`, `ORACLE/single.py`).
- Bisect: `ORACLE/bisect/build.sh` builds a commit from `git archive` into
  `ORACLE/bisect/<commit>`. `ORACLE/bisect/cmp.sh FILE` prints the codes of the
  round-2 binary (328a39b), f211d13 (R2b), acd05a8 (R2c), ee68916 (R2d), f389b46
  (R2e) and the head.

### Counts

| Run | Source | Oracle | Programs | Accepted, clean | Accepted, fault | Accepted, timeout | Rejected, fault | Rejected, clean | Rejected, other |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| g1 | gen_r2.py (round-2 generator) | stock oracle | 3000 | 499 | 0 | 0 | 1868 | 633 | 0 |
| t3 | gen3.py (trial) | stock oracle | 300 | 60 | 0 | 0 | 191 | 49 | 0 |
| g3a | gen3.py | stock oracle | 6000 | 1205 | 3 | 0 | 3886 | 906 | 0 |
| g3b | gen3.py | stock oracle | 15000 | 3097 | 0 | 0 | 9559 | 2344 | 0 |
| g4a | gen4.py | stock oracle | 8000 | 2548 | 0 | 0 | 2361 | 1910 | 1181 |
| m3a | mutate3.py | stock oracle | 8000 | 2611 | 1 | 5 | 2438 | 2945 | 0 |
| m3b | mutate3.py | stock oracle | 8000 | 2552 | 2 | 8 | 2424 | 1498 | 1516 |
| sw1 | sweep.py | stock oracle | 917 | 30 | 192 | 0 | 695 | 0 | 0 |
| sw2 | sweep2.py | stock oracle | 1152 | 419 | 6 | 0 | 633 | 94 | 0 |
| sw3 | sweep3.py | stock oracle | 90 | 0 | 0 | 0 | 90 | 0 | 0 |
| sw4 | sweep4.py | stock oracle | 3770 | 1324 | 0 | 0 | 1588 | 858 | 0 |
| r2p | round-2 probes and repros | stock oracle | 141 | 29 | 1 | 0 | 90 | 20 | 1 |
| sw4p | sweep4.py | patched oracle | 3770 | 1324 | 0 | 0 | 1675 | 771 | 0 |
| g3p | gen3.py | patched oracle | 10000 | 2104 | 0 | 0 | 6480 | 1318 | 98 |
| g4p | gen4.py | patched oracle | 8000 | 2565 | 0 | 0 | 2370 | 1910 | 1155 |
| m3c | mutate3.py (generated seeds) | patched oracle | 6000 | 2151 | 0 | 4 | 2004 | 1333 | 508 |

Total: 82140 programs, 22740 accepted, 205 accepted with a fault.

Notes on the table:

- "Accepted, fault" counts a program once, with the first fault class. The runs
  `g1`, `t3`, `g3a`, `g3b`, `m3a` and `sw1` to `sw4` used the first version of the
  harness: there "Rejected, clean" also holds the rejected programs that stopped at
  an index or overflow fault. The later runs put them in "Rejected, other". For `m3a`
  I counted again with the final list of benign faults (an integer underflow and a
  failed `listen` of `http.serve` are not soundness faults).
- The accepted programs with a fault reduce to O3-1 (`g3a`, `m3a`, `m3b`, `sw1`, `sw2`),
  O3-2 (`sw1`), O3-3 (`sw1`), O3-4 (`sw2`), O3-5 (`r2p`, the round-2 probe
  `c3_task_stored.wf`) and O3-6 (`m3b`, a mutation of
  `crates/weft-interp/tests/programs/steal.wf`). Probes found O3-14.
- The timeouts are programs that do not end (`http.serve`, a mutated loop).
- I grouped the rejected programs that run cleanly by code and by statement. Most
  groups are correct rejections on a path that did not run (a `for` loop of one
  pass, an `if` with no `else`, a closure that a callee gets) or imprecisions that
  ADR 0003, 0005, 0006 and 0007 state. The new false positives are O3-7 to O3-12.
- `weft agree` gives no difference between the checker and `spec/weft.dl` on 370 of
  these programs (the repros, the sweep of frames, and rejected generated programs).
  So each soundness defect here is in the facts (sema) or in a difference between
  sema and the interpreter, not in the checker.

## Findings

### O3-1 (blocker): a place as the tail of a `scope` body

Repro: `ORACLE/repro/O3-1_scope_tail_move.wf`.

```weft
let v = Vec.new()
v.push(1)
let r = &v[0]
scope { s =>
    v                 // the interpreter moves `v` into the value of the scope
}
print(r + 1)          // oracle: a read of a freed cell
print(v.len())        // stock: a value is used after it was moved
```

- The checker accepts each function of the repro. Each one faults with the stock
  interpreter or the oracle: a use after a move, a dangling reference, a part
  (`p.a`), a linear value that goes away and is then consumed again (oracle: linear
  leak; stock: use after move), a `!Move` value that moves (no W0604), `{ v }` and
  `v;` as the tail, an index tail (`vv[0]`), and a move while a task reads the value
  (no W0405).
- ADR 0003 says: "The tail of a block is its value, not a statement: a place there
  moves into the value of the block ... also when nothing uses the value of the
  block". The OR6 fix covers a block statement, a loop body and an `if` branch. The
  checker gives W0302 for `let x = scope { s => v }`, for `{ v }` and for
  `handle ... in { v }`. Only a `scope` in statement position is wrong.
- The generators and the mutator found it 5 times (`g3a` 3, `m3a` 1, `m3b` 1); the
  sweeps found it 7 times. Probes: `ORACLE/probes/h*.wf`, `l6`, `l7`, `l11`, `l12`, `st3`,
  `st10`, `z8`.
- Fix: lower the tail of a scope body as the value of the scope, also in statement
  position, as for a block: a move, and a drop at the end of the statement.

### O3-2 (blocker): a temporary of a handled body or a scope body

Repro: `ORACLE/repro/O3-2_handled_body_temporary.wf`.

```weft
let r = handle Note { fn note(x) { resume(()) } } in { first(&mk_v()) }
print(r + 1)          // oracle: a read of a freed cell
show(scope { s => first(&mk_v()) })   // oracle: a read of a freed cell
```

- The interpreter runs a handled body in a frame of its own and frees its
  temporaries at its end. ADR 0003 states this rule. The facts free the temporary
  at the end of the body (`scope_end`), and then the local gets the value
  (`rebound_at`). `invalid(R, Q)` does not pass a `rebound_at` node, so the free never
  reaches the local. A local of the body is held across its end (correct: W0301).
- Forms: `&mk_v()[0]`, `first(&mk_v())`, `mk_v().get(0)`, `id(...)`, a `Box` field, a
  struct field, an array literal, an `Option`, a tuple, a closure that a callee
  returns (`make_reader(&mk_v())`), a `handle` with no block, a nested handler, a
  `multi` handler, an assignment, an argument, and a function that returns the value.
  `sweep.py` finds 130 accepted programs that fault: 120 in the frames `handle`,
  `handle_op`, `handle_nb` and `nested`, and 10 in the frame `scope` (argument).
- Regression: 328a39b and f211d13 (R2b) reject the `let` and the assignment forms with
  W0301. acd05a8 (R2c) accepts them. The argument forms and the scope form are
  accepted also in 328a39b: there the checker kept the temporaries to the end of the
  outer statement, but the interpreter frees them at the end of the body.
- Fix: hold the value of the handled body (and of a scope body) across the end of its
  temporaries, as a block value is held across the end of its locals. A hidden
  variable that holds the value on its way out, from before the `scope_end` nodes,
  makes the free reach every holder.

### O3-3 (blocker): a temporary of a clause

Repro: `ORACLE/repro/O3-3_clause_temporary.wf`.

```weft
let r = handle Ask { fn ask() { first(&mk_v()) } } in { let k = ask(); &u[0] }
print(r + 1)          // oracle: a read of a freed cell (the clause value)
let q = handle Give { fn give() { resume(first(&mk_v())) } } in { give() }
print(q + 1)          // oracle: a read of a freed cell (through `resume`)
```

- A clause that does not resume gives the value of the `handle`. A clause that
  resumes gives the value of the handled body, which can be the result of the
  operation. The clause frees its temporaries at the end of its statement, before the
  `handle` gives its value. A local of the clause is correct (W0301, W0204).
- `sweep.py` finds 60 accepted programs that fault in the frames `clause_val` (39)
  and `resume` (21): every payload with a temporary. Also in 328a39b.
- Fix: as for O3-2, hold the clause value and the argument of `resume` across the end
  of the temporaries of the clause.

### O3-4 (blocker): a linear task result that a spawn statement drops

Repro: `ORACLE/repro/O3-4_task_result_linear_leak.wf`.

```weft
scope { s =>
    s.spawn(|| Lk { id: 1 })     // accepted
    print(1)
}                                 // oracle: linear leak at the end of the run
```

- ADR 0006: "A spawn in statement position gives its handle to the scope." The scope
  joins the task, and its result goes away. Nothing consumes the linear value and no
  `on abort` runs. The same holds for a captured linear value (`|| t`), a function
  item that returns one (`s.spawn(make)`) and a `Vec<Lk>`. A bound handle that is
  detached gets W0601 (correct). Also in 328a39b.
- Fix: a spawn in statement position whose result type is linear (or holds a linear
  value) is W0601. Or require `let` and a `join` for such a task.

### O3-5 (blocker): a task runs a closure from a struct field

Repro: `ORACLE/repro/O3-5_task_runs_field_closure.wf`.

```weft
struct H { f: fn() }
let h = H { f: || v.push(2) }
scope { s =>
    s.spawn(|| { let g = h.f; g() })
    print(v.len())       // accepted; oracle: data race
}
```

- W0405 and W0403 do not see what the closure in the field writes. Forms: a copy of
  the field before the spawn, a read of the field in the task, `s.spawn(h.f)`, a field
  that gets the closure by an assignment, a nested struct, a callee that runs the
  field (`run_h(&h)`), two tasks that run the closure, and a `fork` branch (no W0403,
  no W0405).
- The body knows the closure: a call of the field value gets W0301, W0601 and W0502,
  and the same task or fork branch gets W0314 and W0401 (all correct,
  `ORACLE/probes/sc*.wf`, `se*.wf`, `sf*.wf`). The same closure in a `Vec`, a tuple,
  an `Option` or a generic struct gets W0405. Only the footprint of the task misses
  the stored value.
- Not the R2d open item: that item is about a struct that a callee returns, called
  outside a task. Here the struct is a local of the body. Also in 328a39b. It was in
  my round-2 probes (`r2/oracle/probes/c3_task_stored.wf`); my round-2 race detector
  did not report it.
- Fix: a task that reads a function value from a field (or runs a value that can be
  a stored closure) writes and reads what each closure that the body stores there
  writes and reads, as for a `Vec` element.

### O3-6 (blocker): a task reads through an `Rc` handle that the parent moves

Repro: `ORACLE/repro/O3-6_task_rc_handle_move.wf`. Found by mutation of
`crates/weft-interp/tests/programs/steal.wf` (`runs/m3b/p27258.wf`).

```weft
let shared = Rc.new(Node { v: 5 })
scope { s =>
    let b = s.spawn(|| shared.v + 1)
    take(shared)          // accepted; the task reads a moved variable
    print(b.join())
}
```

- The task reads `Node.v` (the group place) and not the variable `shared`. So a move
  of `shared` (`take`, `let m = shared`, a typed callee) is not a free that overlaps a
  read of the task. A new value of `shared` is a data race (oracle). The end of the
  scope of `shared` while the task runs is not a free for the task either
  (`scope_end`; a `Vec` there gets W0405). A handle in a struct field has the same
  defect (`field_handle`: a move of the struct, a move or a new value of the
  field). A `Box` gets
  W0405 ("this code frees `bx` while a task reads `bx.v`"), and so does a task that
  clones the handle. Also in 328a39b.
- Fix: a place through a handle reads the handle variable too (ADR 0003: "the
  reference also depends on the handle place (`handle.*`)"). Record that read in the
  task reads, so the move and the new value conflict.

### O3-7 (major, false positive, regression of R2d): W0312 on an operation

Repro: `ORACLE/repro/O3-7_fp_op_closure_w0312.wf`.

```weft
handle Run { fn run(f) { f(); resume(()) } } in {
    run(|| v.push(5))     // W0312: `run` mutates `v` while another argument points into `v`
}
```

- The operation has one argument. The derivation compares `call_mut(run, v, 3000000)`
  (`roots::clause`, the footprint of the clause) with `call_arg(run, v, 1000000)`
  (`roots::fn_arg`, the closure). The clause footprint holds what the closure itself
  does, so the closure conflicts with itself. The same closure given to a function
  is accepted. A clause that does not call `f` is accepted.
- 328a39b, f211d13 and acd05a8 accept it. ee68916 (R2d) gives W0312.
- Fix: leave out of the clause footprint at a node what the function arguments of the
  operation do (they have the root `fn_arg`), or give them the same root.

### O3-8 (major, false positive): a closure with its own `multi` handler

Repro: `ORACLE/repro/O3-8_fp_closure_inner_multi.wf`.

```weft
let l = Lk { id: 1 }
let g = || {
    handle Pick { fn pick() { resume(true); resume(false) } } in { if pick() { print(1) } }
}
g()                       // W0503 and W0602 for `l`
unlock(l)
```

- `weft facts` gives `performs_at(n17, c0)`, `multi_at(n17)` and `may_abort(n17)` at the
  call `g()`: the closure summary keeps the capability of the handler inside the
  closure. No operation can leave the closure. The same code as a block or a
  function item is accepted. `apply(|| ...)` has the same false positive. Also in
  328a39b.
- Fix: remove the capabilities of the handlers inside the closure (`own_caps`) from the
  `performs` of its summary.

### O3-9 (major, false positive): joins that the body does not see

Repro: `ORACLE/repro/O3-9_fp_join_not_seen.wf`.

- `join_it(t)`, `let (t, _) = p; t.join()`, `match o { Some(t) => t.join(), ... }`,
  `id(t).join()` and `let g = || t.join(); g()` all join the task at run time. The
  checker keeps the task active to the end of the scope, so a later access is W0405.
  A direct `t.join()` is accepted. ADR 0006 names `if`, `match`, `handle` and closure
  results, but not these forms, and the imprecision lists do not name them. Also in
  328a39b. In the run `g4a` of `gen4.py`, each of the 390 rejected programs that has
  only W0405 and runs cleanly has one of these forms.
- Fix: a callee that takes a `Task` by value joins or detaches it on every path (it is
  linear), so the call node can end the tasks of the argument. A tuple pattern and an
  `Option` pattern can carry the task set of the part.

### O3-10 (minor, false positive, regression of R2c): two spawns of parameters

Repro: `ORACLE/repro/O3-10_fp_spawn_param_multi.wf`.

- `fn both(f: fn(), g: fn()) { scope { s => s.spawn(f); s.spawn(g) } }` gets W0503 ("`s` is
  not `many`, but it is live across `spawn`, which can resume more than once") when the
  program declares any `multi` operation. A spawn does not run the parameter in this
  task, and W0314 keeps a task away from the handlers of this task, so no resume of
  this task happens at the spawn. Without the `effect Pick` line, the file is
  accepted. f211d13 accepts it; acd05a8 (R2c) rejects it. ADR 0005 lists the
  whole-program `multi` test for calls of a parameter, not for spawns.
- Fix: a spawn of a function value is not a `multi` point of the spawning task.

### O3-11 (minor, false positive): a move, then a new value of a captured variable

Repro: `ORACLE/repro/O3-11_fp_move_then_refill.wf`.

- `let show = || print(v.len()); take_v(v); v = mk_v(); show()` gets W0301. The closure
  reads the cell of `v` when it runs (ADR 0003), so it reads the new value. A new
  value with no move before it is accepted. Also in 328a39b.

### O3-12 (minor, false positive): a clause conflicts with its own task

Repro: `ORACLE/repro/O3-12_fp_clause_spawn_self.wf`.

- `handle Note { fn note(x) { s.spawn(|| { n += 1 }); resume(()) } } in { note(1); ... }`
  gets W0405 at the spawn: the clause reads its captures at the operation (ADR 0006),
  and the task starts at the operation. Nothing else touches `n` while the task runs.
  Also in 328a39b.

### O3-13 (minor): gaps of `--oracle`

Repro: `ORACLE/repro/O3-13_oracle_gaps.wf`.

- The race detector does not log a read through a reference in an operand or in a
  callee (`q + 0`, `show(&v[0])` with `r + 0`): `Machine::deref_value`
  (`crates/weft-interp/src/machine/exec.rs`) calls `hget` with no `log_read`. Only
  `print(q)` logs the read. A one-line patch (`ORACLE/patched/`) finds these races and
  gives no false alarm on the interpreter programs and the accepted corpus programs.
- `print` of a moved value prints `<moved>`, and `print` of a reference into a moved
  value prints `<dangling>` (`show.rs` catches the error of the read). Neither is a
  fault, also with `--oracle`.
- Effect: ADR 0010 says that the corpus and the interpreter tests run with the oracle,
  and that an accepted program must not fault with it. These gaps hide data races and
  uses after a move from those tests. My harness treats the printed markers as faults
  and uses the patched build for the last runs.

### O3-14 (blocker): the tail place of a `multi` handled body

Repro: `ORACLE/repro/O3-14_multi_tail_place.wf`.

```weft
let v = mk_v()
let w = handle Pick { fn pick() { resume(true); resume(true) } } in {
    let b = pick()
    v                     // the second resume moves `v` again
}
print(w.len())            // stock: a value is used after it was moved (at the tail)
```

- A local handler with a `multi` operation is lowered as a loop (ADR 0003, ADR 0005),
  so a move after the operation must count in each pass. A bare place or `{ v }` as
  the tail is not counted: the checker accepts the file, also in statement position
  and when the clause keeps both results. A tail that is a call, `id(v)`, `(v, 1)`,
  `Some(v)`, a `let` and then the local, or an `if` gets W0302 (correct). 328a39b
  accepts all forms; f211d13 (R2b) and later catch the call form but not the place.
- Fix: in the lowering of a handled body again (`handled_again`), lower the tail
  place as a move inside the pass, as for the other tails.

## Round-2 checks

- OR1, OR3, OR5, OR7, OR8 and OR9: the repros get the errors of the fix.
- OR2 and OR6: the interpreter now moves a captured value when the closure is made,
  and a place statement moves nothing. The repros are accepted and run cleanly with
  the oracle on all seeds.
- OR4: accepted, and clean.
- OR10: still W0405; ADR 0006 now lists it as an imprecision.
- OR11: `--oracle` exists. O3-13 lists its gaps.
- The 141 round-2 probes and repros (`ORACLE/r2probes/`): no accepted program faults
  except `c3_task_stored.wf` (O3-5).
- The round-1 red-team probes (`scratchpad/redteam/`): each one gets at least as many
  errors as in 328a39b. `f01`, `f02` and `f03` (design-doc false-positive probes) are
  accepted.
- Named arguments run in the order of the parameters in the checker and in the
  interpreter, for functions, methods, operations, items in locals and constructors
  (`ORACLE/probes/g*.wf`).

## Files

- Repros: `ORACLE/repro/O3-*.wf`. `ORACLE/verify.sh FILE` prints the checker output and
  runs each function with no parameters alone (stock and oracle, seeds 1 to 3). Its
  output for all repros is in `ORACLE/verify_out.txt`.
- Harness: `ORACLE/harness.py` (`WEFT` selects the binary), `ORACLE/gen3.py`,
  `ORACLE/gen4.py`, `ORACLE/mutate3.py`, `ORACLE/sweep.py` to `ORACLE/sweep4.py`,
  `ORACLE/lib/`, `ORACLE/probe.sh`, `ORACLE/codes.py`.
- Analysis: `ORACLE/unsound.py`, `ORACLE/fpgroups.py`, `ORACLE/single.py`.
- Raw results: `ORACLE/runs/*/results.jsonl` (one line for each program, with its
  class). The programs of the classes other than `ACCEPT_OK`, `REJECT_FAULT` and
  `REJECT_BENIGN` are kept next to the results.
- Bisect: `ORACLE/bisect/build.sh`, `ORACLE/bisect/cmp.sh`, `ORACLE/bisect/target-*`.
- Patched oracle: `ORACLE/patched/` and `ORACLE/target-patched/release/weft`.
