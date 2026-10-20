# Review round 2, lens "oracle": differential soundness testing

Commit: 328a39b (worktree `/home/user/wt-edge`, branch `review/r2`). I did not change the
worktree. All files of this lens are in
`SCRATCH/r2/oracle/`
(below: `ORACLE/`).

## Summary

- I ran 26 400 programs through `weft check`. 8 521 of them were accepted. I ran each
  accepted program 6 times (seeds 1, 2, 3, 7, 11, 42; workers 1 to 4) with the stock
  interpreter and with an instrumented interpreter. That is about 140 000 interpreter runs.
- I found 9 soundness defects (8 blockers and 1 major false positive) and 2 minor items.
  Each one has a minimal repro in `ORACLE/repro/`.
- 6 of the 8 blockers fault with the stock `weft run --unchecked`. OR7 and OR8 are data
  races. Only the instrumented interpreter finds them, because the stock interpreter has
  no race detector (OR11).
- The round-1 fixes hold. Each round-1 red-team probe that must fail gets an error now.
  The checker and `spec/weft.dl` agree on 2 500 generated programs (`weft agree`).

| Id | Severity | Short statement |
| --- | --- | --- |
| OR1 | blocker | A returned closure that captures a reference parameter does not point into the argument |
| OR2 | blocker | The checker moves a captured value when the closure is made; the interpreter moves it when the closure runs |
| OR3 | blocker | A callee that calls a callback twice is not checked for W0301 |
| OR4 | major | W0602 and W0503 for a linear value that lives outside the `handle` (false positive) |
| OR5 | blocker | A reference made while a task is active stays valid after the join |
| OR6 | blocker | A variable as an expression statement drops the value; the checker sees no move |
| OR7 | blocker | A function parameter that runs as a task or a fork branch gets no W0405, W0401, W0403 or pinning check |
| OR8 | blocker | A use or a new value of a whole local is not an access for W0405 |
| OR9 | blocker | A `resume` inside a spawned task runs the handled body on another task |
| OR10 | minor | W0405: a call reads all of its reference arguments (false positive) |
| OR11 | minor | The stock interpreter misses dangling references, linear leaks and races |

## Method

### Program sources

1. `ORACLE/gen.py`: a random generator with a typed environment. Each program has a fixed
   prelude (types `E` and `W`, linear `Tx` with `on abort`, linear `Lk` without it, effects
   `Ask`, `Pick` (multi), `Note`, `Grab`, and about 30 helpers). `main` gets 4 to 12 random
   statements, nested up to 3 levels. The statements:
   - borrows, mutations (push, pop, clear, assignment, `+=`) and uses;
   - moves into calls, into other locals and into closures;
   - closures that are called, given to `apply`, `twice` or `run_both`, or returned from blocks;
   - `if`, `for`, `while`, `loop`, `match` and blocks;
   - handlers with clauses that resume once, twice or never, and that mutate captures;
   - scopes with tasks, joins and `fork`;
   - linear values that are consumed on most paths and dropped on some paths;
   - effect operations with no handler;
   - random helper functions with no stated effects, so inference runs.
2. `ORACLE/mutate.py`: mutation of seed programs. The seeds are the interpreter programs
   in `crates/weft-interp/tests/programs`, the corpus programs that have `main` or tests,
   and 500 accepted generated programs. A mutation moves, deletes, duplicates or swaps a
   statement. It can also insert a push, clear, pop, move or rebind of a local. It can
   wrap a statement in a block, a loop, a closure, `twice`, a handler, a scope, a task or a
   `fork`. It can also swap `once` and `multi`, add or remove a `resume`, remove a consume
   or an `on abort`, remove a handler, or detach a task.
3. Hand-written probes in `ORACLE/probes/` for shapes that the generator does not make.

### Oracles

- Stock: `weft run --unchecked` and `weft test --unchecked` of `/home/user/wt-edge`. A
  `runtime error` that is not an index, an overflow or an underflow is a fault.
- Instrumented: a copy of the same commit with an oracle patch in `weft-interp` only
  (`ORACLE/interp_oracle.patch`, binary `ORACLE/weft-inst/target/release/weft`). It adds:
  - a fault on each access to a freed cell or buffer (a dangling reference);
  - a `Vec` that moves its buffer on each push, pop and clear, as a real `Vec` can;
  - a fault when code follows a reference into a local whose scope ended;
  - a fault when the program drops a live linear value with no consume and no `on abort`,
    and when a linear value is still live at the end of the run;
  - a vector-clock race detector. Spawn, join, scope end, fork end and unwinding are the
    synchronization points. Two accesses to overlapping paths, with one write, and with
    no join between them, are a race. The result does not depend on the seed;
  - a fault when the scheduler marks a task stealable, but the task reaches an `Rc`, a
    `Weak` or a `Scope`.

  The patch makes no false alarm on the accepted interpreter programs and on the corpus
  programs that have `main` or tests (all seeds 1 to 3, workers 1 and 4).
- Reduction: `ORACLE/reduce.py` removes lines while the property holds (an accepted
  program that faults, or a rejected program with one code that runs cleanly).

### Counts

| Run | Source | Programs | Accepted, clean | Accepted, fault | Rejected, fault | Rejected, clean |
| --- | --- | --- | --- | --- | --- | --- |
| g1 to g7 | generator | 20 400 | 5 866 | 37 | 9 785 | 4 712 |
| m1, m2 | mutation | 6 000 | 2 593 | 25 | 1 454 | 1 928 |

After a finding, I turned off its generator feature (`GEN_OFF`) or its oracle class
(`ORACLE_SKIP_WHOLE_LOCAL`), so that later runs could find new shapes. 60 of the 62
faulting accepted programs reduce to OR1, OR2, OR3, OR5, OR6 and OR8. Of the other two,
one is an endless recursion (a timeout, not a fault). The other one showed a gap in my
race detector at unwinding, which I fixed. OR7 and OR9 came from probes.
I reduced about 70 rejected-and-clean programs. Most are correct rejections on a path
that did not run (`if false`, a closure that nobody calls) or known imprecisions of
ADR 0005 to 0007. OR2b, OR4 and OR10 are the new false positives.

## Findings

### OR1 (blocker): a returned closure does not point into the argument

Repro: `ORACLE/repro/OR1_returned_closure.wf`.

```weft
fn reader(v: &Vec<u64>) -> fn() { || print(v.len()) }
fn moved() {
    let v = Vec.new()
    v.push(1)
    let f = reader(&v)
    take(v)
    f()          // runtime error: a value is used after it was moved
}
```

- The checker accepts `moved`, `scope_ended` and `cleared`. Each one faults with the stock
  interpreter.
- The same closure, made in the body (`let f = || print(v.len())`), gets W0301. The same
  closure through `id(...)` also gets W0301.
- Cause: a call result of type `fn()` carries the `ret` part (what a call of it does). It
  does not point into the places of the reference arguments. ADR 0003 says that a call
  result points where the arguments can flow. A move, a free or an unstable mutation of
  the argument therefore does not invalidate `f`.
- Not the ADR 0005 open item: that item is about a closure inside a returned tuple or
  struct. Here the closure is the direct result.
- Fix: give a call result that can hold a function value the `points_into` places of the
  reference arguments (a wildcard place, as for a reference result with no stated place).
  A call of the result then uses those places.

### OR2 (blocker): the move of a captured value happens at different points

Repros: `ORACLE/repro/OR2_closure_move_timing.wf` (unsound),
`ORACLE/repro/OR2b_fp_closure_never_called.wf` (false positive).

```weft
let f = || print(take(v))
v = Vec.new()      // the checker: `v` has a value again
f()                // the closure moves the new value
print(v.len())     // runtime error: a value is used after it was moved
```

- The facts put `moved_at(v)` at the node that makes the closure (n10 in
  `weft facts ... main`). The interpreter takes the value from the cell when the closure
  runs, as ADR 0003 says ("it takes the value only when it runs").
- A new value of `v` between the two points goes into the closure. The next use of `v`
  faults. The task form (`s.spawn(|| print(take(v)))`, then `v = Vec.new()`) faults the
  same way.
- The other side is a false positive. A closure that is made but never called still moves
  `v`, so a later `v.push(2)` gets W0302 (OR2b). The reduced programs
  `ORACLE/fp/W0302_p1066.wf` and `ORACLE/fp/W0502_p3681.wf` show the same cause.
- Fix: choose one point. Either the interpreter moves the captured value when it makes the
  closure (this agrees with ADR 0006 for tasks), or the checker moves it at each node where
  the closure runs and counts a new value of `v` while the closure is live as an
  overwrite.

### OR3 (blocker): a callee that calls a callback twice is not checked for W0301

Repro: `ORACLE/repro/OR3_repeated_callback.wf`.

```weft
fn twice(f: fn()) { f(); f() }
let r = &v[0]
twice(|| { print(r + 1); v.clear() })   // second call: "a place does not exist"
```

- `g(); g()` and `for i in 0..2 { g() }` get W0301. The forms through a callee
  (`twice`, a loop in the callee `each`, two levels `twice2`, and a returned closure that
  calls `f` twice, `wrap`) are accepted and fault.
- Cause: the `repeats` part of a signature (ADR 0006) is used only for tasks that a closure
  spawns. The check does not use it for the captures of the closure.
- Fix: when a closure goes to a parameter in `repeats`, check its captures as for two
  calls: a mutation in the closure invalidates the references that it captures.

### OR4 (major, false positive): W0602 and W0503 outside the `handle`

Repro: `ORACLE/repro/OR4_fp_outside_handle.wf`.

```weft
let l = Lk { id: 1 }
let n = handle Ask { fn ask() { 0 } } in { ask() + 1 }   // W0602
unlock(l)
```

- The clause drops the continuation. The abort ends at the handler, so `l` is not
  unwound. A `multi` resume copies only the frames inside the handled body, so it does not
  copy `l`. All forms run cleanly on all seeds.
- The checker gives W0602 (`inline_abort`) and W0503 with W0602 (`inline_multi`). The same
  code inside a function (`guarded()`, `solve()`) is accepted. So the result depends on an
  inline step, which is not a semantic change.
- Cause: `abort_unhandled` and `live_across_multi` use `may_abort(P)` and `multi_at(P)` at
  a perform node. They do not limit the live values to the values inside the handled
  body of the handler that handles the operation.
- Fix: a perform that a local `handle` handles can abort or copy only the values that are
  live inside that handled body. Treat the `handle` node itself as the suspension point for
  the outer values (rule 1 of `proofs/effects`: "handle: vs all outer caps").

### OR5 (blocker): a reference made while a task is active

Repro: `ORACLE/repro/OR5_borrow_during_task.wf`.

```weft
scope { s =>
    let t = s.spawn(|| v.clear())
    let r = &v[1]
    t.join()
    print(r + 1)      // runtime error: a place does not exist
}
```

- The checker treats the spawn node as the mutation of the task (ADR 0006). `r` gets its
  value after that node, so nothing invalidates it. The task clears `v` while it runs.
- The borrow `&v[1]` is also not an access for W0405. An index reads the length and the
  buffer of `v`, so it races with the task. `v.get(1)` and `let n = v[1]` get W0405.
- `use_after_scope` shows the same with a reference that gets a new value inside the scope.
- Fix: at the join node (and at the scope end), invalidate each reference that points
  strictly inside a place that the task writes, through an unstable step. Record a borrow
  through an index as a read of the indexed place.

### OR6 (blocker): a variable as an expression statement

Repro: `ORACLE/repro/OR6_expr_statement_move.wf`. Found by mutation: a duplicated tail
`v` in `mk_v`.

```weft
let v = Vec.new()
v.push(1)
v
print(v.len())        // runtime error: a value is used after it was moved
```

- The interpreter reads the value out of the variable and drops it (`Op::Read`, then
  `Op::Pop`). The checker sees no move.
- A linear value goes away silently (`linear_dropped`, no W0601). A reference into the
  value dangles (`dangling`). A `!Move` value is dropped while a self-reference points
  into it (`ORACLE/probes/n8_immov_expr_stmt.wf`).
- Fix: make both sides agree. Either compile a bare place in statement position without a
  read, or record a move and a drop in the facts (then W0302, W0601 and W0301 apply).

### OR7 (blocker): function parameters that run as tasks

Repro: `ORACLE/repro/OR7_tasks_of_fn_params.wf`.

```weft
fn par(f: fn(), g: fn()) / par { fork(f, g) }
fn bg(f: fn()) { scope { s => s.spawn(f); s.spawn(f) } }
par(|| n += 1, || n += 2)      // two threads write `n`
bg(|| n += 1)                  // two tasks write `n`
```

- The direct forms get W0403 and W0405. The forms through a callee are accepted. The
  instrumented interpreter finds a race on all seeds.
- `bg_and_call(f, g)` spawns `f` and calls `g` at the same time. It is accepted and races.
- `bg_one(|| print(a.hp))` with `a: Rc<E>`: the scheduler marks the task stealable,
  although it holds a nonportable `Rc`. Work stealing then breaks the mode rule.
- Cause: the `tasks` part of a signature (ADR 0006) checks only W0314 at the caller.
- Fix: a closure that goes to a parameter in `tasks` must pass the spawn checks at the
  call: W0401 and W0403 if the callee can run it on another thread, W0405 against itself
  if the parameter is also in `repeats`, and W0405 against the other function arguments
  that the callee can run in the same scope. Mark such a task pinned unless the value is
  known to be portable.

### OR8 (blocker): whole-local accesses are not W0405 accesses

Repro: `ORACLE/repro/OR8_task_whole_local.wf`.

```weft
let count = 0
scope { s =>
    s.spawn(|| count += 1)
    print(count)          // accepted; a race
}
```

- Accepted and racy: `print(count)` or `let m = count` while a task writes `count`; a
  task that prints `count` while the parent does `count += 5`; `print(v)` of a whole `Vec`
  while a task clears it; a new value `r = &v[1]` while a task reads `r`.
- Checked correctly: a field (`c.k`), an element (`v[0]`), a call with `&v`, and two tasks
  that both write `n`.
- Cause: in `crates/weft-sema/src/body/expr.rs`, `name()` reads only the places that a
  reference local points into. It never reads the root place of the local. So a task
  that only reads a captured variable has no `task_reads` for it. A new value of a local
  is `rebound_at`, which is not an access.
- Fix: a use of a local as a value reads its root place. A new value of a local writes its
  root place for W0405. Keep the ADR 0006 rule that a use of a reference is not a read of
  the places that it can reach.

### OR9 (blocker): `resume` inside a spawned task

Repro: `ORACLE/repro/OR9_resume_in_task.wf`.

```weft
handle Note { fn note(x) { print(x); resume(()) } } in {
    handle Ask { fn ask() { scope { s => s.spawn(|| { let _ = resume(1) }); print("clause") } } } in {
        let a = ask()
        note(a)       // runtime error: no handler for `Note.note` on this task
    }
}
```

- The task runs the rest of the handled body. That body is away from the handlers on the
  stack of the parent task, so a later operation has no handler (an unhandled effect at
  run time). The body also runs at the same time as the clause, so `race()` writes `c.k`
  from two tasks.
- W0314 protects the other direction (a task that performs through a handler of another
  task). Nothing protects this direction.
- Fix: reject a `resume` (and a continuation value) in a closure that runs as a task or a
  fork branch. Or check the handled body as code of that task: W0314 for its operations
  and W0405 against the clause.

### OR10 (minor, false positive): a call reads all of its reference arguments

Repro: `ORACLE/repro/OR10_fp_call_reads_all.wf`.

```weft
let t = s.spawn(|| grow_w(&w))    // grow_w: mut(w.es)
w.score += 1                      // W0405: mutates `w.score` while a task reads `w`
```

- The program runs cleanly. The helper touches only `w.es`. ADR 0006 states the rule ("a
  call reads its reference arguments"). Its cost is not in the list of imprecisions.
- Fix: add it to the ADR 0006 imprecisions, or add a read footprint to signatures.

### OR11 (minor): the stock interpreter is a weak oracle

Repro: `ORACLE/repro/OR11_weak_oracle.wf`. The checker rejects each function in it.
The stock interpreter runs each one to the end with no error.

- `print` of a dangling reference prints `<dangling>` and continues (`show.rs`).
- A reference into a dead local of plain data stays readable.
- `Vec.push` never moves the buffer, so a reference into `v[]` survives a push.
- A live linear value that goes away silently is not reported. Only a double consume is.
- There is no race detector, so W0405, W0401 and W0403 have no dynamic check.

So `weft run --unchecked` cannot show the effect of many checker defects. Fix: take the
checks of `ORACLE/interp_oracle.patch` into the interpreter, behind an option, and use it
in the corpus and agreement tests.

## Round-1 checks

- Each round-1 red-team probe in `scratchpad/redteam/` that must fail gets an error. The
  only accepted files are the design-doc false-positive probes `f01`, `f02` and `f03`.
- The generated and hand-written variants of RT1 to RT7 (owner moves, pending uses,
  references through generics, argument order, callee closures, item values, closure
  summaries) are rejected, and they fault when run unchecked.
- Linear values (OR11 aside), continuations, capability escape (W0313) and immovable
  values held in all probes: `ORACLE/probes/b*`, `d*`, `i*`, `m*` and `n*`.
- `weft agree` passes on 2 500 generated and mutated programs (`ORACLE/agree_out.txt`).

## Files

- Repros: `ORACLE/repro/OR*.wf`. Results for each function with the stock and the
  instrumented interpreter: `ORACLE/verify_out.txt` (made by `ORACLE/verify.sh`).
- Harness: `ORACLE/harness.py`, `ORACLE/gen.py`, `ORACLE/mutate.py`, `ORACLE/reduce.py`,
  `ORACLE/report.py`.
- Oracle patch: `ORACLE/interp_oracle.patch`. Build: `cargo build --release -p weft-cli`
  in `ORACLE/weft-inst`. Options: `ORACLE_NORACE`, `ORACLE_NOREALLOC`, `ORACLE_NOEND`,
  `ORACLE_NOSTEAL`, `ORACLE_SKIP_WHOLE_LOCAL`, `ORACLE_TASKS`, `ORACLE_DEBUG`.
- Raw results: `ORACLE/runs/*/results.jsonl` (one line for each program, with its class).
- Reduced false-positive candidates: `ORACLE/fp/`, `ORACLE/fp2/`, `ORACLE/fp3/`.
