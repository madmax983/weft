# Review round 3, lens "interp": the interpreter and the proofs

Commit: b073ea72253fde0bd3e8c0532b404db68de84028 (read-only copy
`.../scratchpad/r3/src`, release CLI `.../scratchpad/r3/target/release/weft`).
Scratch files: `SCRATCH/r3/interp/`.
Repro files: `.../r3/interp/repro/`. The script `repro/run_all.sh` runs each repro. Its output
is in `repro/run_all.out`. The harness `.../r3/interp/harness` (built from a copy of the source
in `.../r3/interp/work/src`) runs a file with a seed, a worker count, the oracle and the
trace, and it prints `leaked_rc`.

## Summary

| Id | Severity | Title |
| --- | --- | --- |
| I3-1 | blocker | The checker loses the linear result of a task: a spawn whose handle is not kept drops it, and an abort before the join drops it with no `on abort` |
| I3-2 | major | The unwinder does not find a linear value outside a code frame: a moved capture of a closure, the result of a finished child |
| I3-3 | major | An interrupt during an unwinding cuts a running `on abort` function, and the nested unwind drops the linear value of a clause |
| I3-4 | major | A `with_timeout` deadline is still lost: two deadlines at one instant, and `sim.clock.advance` before a continuation |
| I3-5 | minor | `Rc` counts: nothing drops a moved capture of a closure or the result of a detached task |
| I3-6 | minor | `sim.clock.advance` moves the clock of the whole run; `sim.*` works outside a simulation |
| I3-7 | minor | The order in `sim.run` still depends on `--seed`: nested simulations, a join of a task outside |
| I3-8 | minor | A `multi` operation in a scope: the copies share the scope record, and a copy ends the scope normally after its child failed |
| I3-9 | minor | A handler at a `join` never gets the failure; a failure in a continuation is raised later than ADR 0010 says |
| I3-10 | minor | `http.serve` and the virtual clock: a deadline fires before the server accepts a request |
| I3-11 | minor | An inline recursive enum is copied at each move: quadratic time, and a stack overflow aborts the process |
| I3-12 | minor | The race detector keeps 256 accesses for one cell; it misses a race after that |
| I3-13 | minor | Proof documents and scripts: the link README says that the interpreter does not copy a record, but it does; `Continuation::end` is not in the table; the link mutation script accepts any failure |

Proof runs: `proofs/verify-all.sh` passes on a copy of the source. Results: borrowing 169,
effects 122, link 235, `crates/weft-verified` 67, 0 errors, 2 min (log:
`.../r3/interp/verify_all.log`). The counts agree with each README and with
`docs/traceability.md`. No proof file has `assume`, `admit`, `external_body` or a
`#[verifier::...]` attribute. The three mutation scripts catch each mutation of their
tables (26, 8, 9), with the documented counts (see "Proofs").

The round-2 fixes hold: each of the 22 repros of round 2 (`.../r2/interp/repro/`) now gives
the expected result (IP1: W0504; IP2: the scope handler; IP3: the task is pinned; IP4:
`[1, 1]`; IP5: `caught: timeout`; IP6: a tuple; IP7: request tasks are pinned; IP9: the same
order for each `--workers` and `--seed`; IP10: `Clock.now()` outside the simulation reads
the run clock; IP11: ADR 0010 says that the network is not simulated). IP8: the B6 lints
give no lint on the corpus except the documented `stored_in_loop`.

The main pattern this round: the unwinder and the interrupt logic look only at the code
frames and at the one interrupt slot of a task. Values that the runtime keeps in other
places (closure cells, task results, the value of an unwinding) and unwindings that are
already in progress do not get the `on abort` guarantee. I3-2 and I3-3 come from this. The
oracle also finds I3-1, a gap of the checker for one of these values: the result of a task.

## Method

1. I read `docs/design.md`, ADR 0002, 0005, 0006, 0007, 0008, 0010, the interpreter (all
   modules of `crates/weft-interp/src`), the proof READMEs, `lifecycle.rs`,
   `lifecycle_link.rs` and `dataflow_link.rs`, and `git log 328a39b..b073ea7` for the
   interpreter and the proofs.
2. I ran the round-2 repros again with the new CLI.
3. I wrote about 50 programs that must behave in a stated way (handlers, `once` and
   `multi`, `on abort` order, cancellation, scopes, joins, `fork`, timeouts, the scheduler,
   `sim.run`, `Rc` counts, HTTP, integer widths, named arguments). I ran each one with
   `weft check` and `weft run --oracle` or `weft test --oracle`, and with the harness.
4. I ran each corpus program and each interpreter test program with `main` or tests
   (93 files) with the oracle, seeds 0 to 12 and 1, 2, 4 and 8 workers
   (`.../r3/interp/sweep/sweep.sh`). No result changed with the seed or the workers. I
   scanned the traces for a steal of a pinned task (none).
5. I ran Verus on all proof crates, and the three mutation scripts.
6. For B6, I ran `proofs/link/lints/unbound_use.dl` and `gen_kill.dl` on each corpus file
   and on my programs, and I read the facts of call results, assignments, tuples and
   array and `Vec` steps (`typed_by`).

## Findings

### I3-1 (blocker): the checker loses the linear result of a task

**What.** A task or a fork branch can return a value of a linear type. The checker does not
follow that value through the task handle in two shapes:

1. **A spawn whose handle is not kept.** `s.spawn(|| Tx { id: 4 })` as a statement, or
   `let _ = s.spawn(|| Tx { id: 4 })`, gets 0 errors. The scope joins the task at its end
   and drops its result. No path consumes the `Tx`, also with no abort. The run prints
   `spawned`, `end`, and the oracle stops it: `linear leak: a linear value is still live
   at the end of the run`. `let t = s.spawn(...)` with no use of `t` is W0601, and
   `t.detach()` is W0601 (`detach` has `T` in `drops`, ADR 0007). The statement form and
   `let _` are not.
2. **An abort before the join, with no `on abort`.** The child finishes. Then the owner
   aborts before it takes the result (a `fail`, a timeout, a failure of a sibling).
   Nothing consumes the result, and its type has no `on abort`. 0 errors; the oracle stops
   the run with the same message.

```weft
linear struct Tx { id: u64 }                 // no `on abort`
scope { s =>
    let t = s.spawn(|| Tx { id: 3 })         // the task finishes at once
    sleep(5.ms)
    fail("abort before the join")           // the handle `t` is unwound
    commit(t.join())
}
```

```weft
with_timeout(10.ms) {
    let (a, b) = fork(|| Tx { id: 1 }, || slow())   // branch 1 is done, branch 2 sleeps
    ...                                             // the deadline aborts the fork
}
```

The design says: "A linear value must be moved or consumed on every normal path" and "It may
be live across an operation that can abort only if its type declares `on abort`." In shape 1
the result goes away on the normal path. In shape 2 it is live in the finished task across
the abort of the owner.

**Cause.** Shape 1: the drop of a task handle in a statement or in `let _` does not count as
a drop of `T` (the check of `drops` covers `detach`, not the implicit join at the end of the
scope). Shape 2: `props.rs` (lines 364 to 367): "A type with `on abort` finishes its linear
parts." `Task<T>` has `on_abort` in the prelude, so `NoOnAbort` does not pass from `T` to
`Task<T>`, and W0602 accepts a live handle. But the `on abort` of a handle cancels the task,
and a cancel does nothing for a task that is done: it does not finish the result. A `fork`
node can abort while a branch is done, and W0602 does not look at the result types of the
branches. In the control program, the checker rejects the same `Tx` in a closure
(`i3_2_ctl_checker_rejects_no_on_abort.wf`: W0602).

**Repro.** `repro/i3_1_spawn_stmt_drops_result.wf`, `repro/i3_1_spawn_let_wild_drops_result.wf`,
`repro/i3_1_task_result_no_on_abort.wf`, `repro/i3_1_fork_result_no_on_abort.wf` (each: 0
errors, oracle fault).

**Fix.** A spawn whose handle is not kept drops `T`: W0601 if `T` is linear (as `detach`).
`Task<T>` has `on abort` for W0602 only if `T` has it, or `T` is not linear. A `fork` node
that can abort needs `on abort` for each linear branch result type. The runtime must then
run the `on abort` of the result (see I3-2). Add the programs to the corpus with
`//~ W0601` and `//~ W0602`.

### I3-2 (major): the unwinder does not find a linear value outside a code frame

**What.** `unwind_frame` takes the values of a code frame (`frame_values`: operand stack,
temporaries, slots) and `extract_linear` walks structs, enums, tuples, lists and owned
buffers. It does not look at:

1. The cells of a closure. Since round 2 (OR2), a closure takes a moved capture into a cell
   of its own (`Op::MakeClosure`, `exec.rs` line 511). `extract_linear` returns a
   `Value::Closure` as it is, and `frame_values` does not take `CodeFrame.caps` of a task.
2. The result of a finished child. `run_on_abort(Value::Task(t))` (`effects.rs` line 573)
   cancels the task. A task that is done keeps `TaskResult::Ok(v)`, and nothing finishes
   `v`. The unwind of a `Scope` or `Fork` frame does not look at the results either.

So `on abort` does not run for these values. The checker accepts each program (each type
has `on abort`). With `--oracle`, each run faults: `linear leak: a linear value is still
live at the end of the run`. Without the oracle, the run ends with exit 0 and no
`rollback` line.

| Repro | Shape | Result |
| --- | --- | --- |
| `i3_2_closure_lin_abort.wf` | `let f = \|\| commit(t)`, then `fail` before `f()` | no `rollback 2`; oracle fault |
| `i3_2_task_lin_cancel.wf` | a task moves `t` and sleeps; a sibling fails | no `rollback 7`; oracle fault |
| `i3_2_task_result_on_abort.wf` | a task returns `Tx`; `fail` before the join | no `rollback 3`; oracle fault |
| `i3_2_fork_result_on_abort.wf` | a branch returns `Tx`; a timeout aborts the fork | no `rollback 1`; oracle fault |

The design says: "Cancellation ... unwinds the task and runs each live linear value's `on
abort`." ADR 0010 says that the oracle must not fault for an accepted program. Thus the
oracle cannot test the abort paths of closures and tasks.

**Fix.** Mark the owned cells in `ClosureVal` (the `owned` list of `MakeClosure`). Let
`extract_linear` take the linear values from the owned cells of a closure, and let
`unwind_frame` take them from the caps of the first frame of a task. When the unwinder
cancels a task handle or unwinds a `Scope` or `Fork` frame, take the linear values from
the results of the finished children. Add the four programs to
`crates/weft-interp/tests/programs`.

### I3-3 (major): an interrupt during an unwinding cuts `on abort` and drops a value

**What.** ADR 0007 and rule 8 of `proofs/effects/README.md`: "The effects proof models `on
abort` as atomic." An `on abort` function can perform `clock` (W0118 allows the root
handlers). `sleep` in it goes to `sleep_for`, which calls `check_interrupt`. That function
skips interrupts only for a task in `abort_task` (`aborting`). An unwind for a timeout, for a
child failure or for a clause that does not resume does not set `aborting`. So a second
interrupt at the `sleep` unwinds the frames again, and the frame of the running `on abort`
function goes away in the middle:

| Repro | Second interrupt | Output |
| --- | --- | --- |
| `i3_3_timeout_cuts_on_abort.wf` | an outer deadline at 12 ms | `rollback 1 starts at 10ms`, no `rollback 1 ends` |
| `i3_3_cancel_cuts_on_abort.wf` | a cancel (a sibling fails) | the same |
| `i3_3_scope_failure_cuts_on_abort.wf` | a child of an outer scope fails | the same |

The nested unwind also loses a value. `unwind_frame` for a `Frame::Unwind(inner)`
(`effects.rs` lines 409 to 416) drops `After::Deliver(v)` with `heap.drop_value`. That `v`
is the value of a clause that returned without a resume. If it is linear, it goes away with
no `on abort`: `i3_3_unwind_drops_clause_value.wf` (0 errors) faults with `oracle: linear
leak: a live linear value goes away with no consume and no on abort`. An unwind that waits
for cancelled children (`Wait::Children`) is interrupted in the same way, with no `sleep` in
an `on abort` of the task itself: `i3_3_unwind_wait_drops_clause_value.wf` (0 errors) gives
the same fault after `rollback 2 ends at 15ms` (the cancelled child finishes its own `on
abort`; the owner, which waits for it, gets the outer deadline at 12 ms).

**Fix.** While an `Unwind` frame is on the stack (or while an `on abort` frame runs), keep
the interrupts for later: a timeout goes to `expired`, a cancel and a child failure stay
pending, and `check_interrupt` handles them when the unwind ends. In `unwind_frame`, take
the linear values out of `After::Deliver(v)` (as for a code frame) before the drop.

### I3-4 (major): a `with_timeout` deadline is still lost

Round 2 (IP5) fixed the deadline of a block in a continuation. Two other shapes lose it:

1. **Two deadlines at one instant.** A task has one interrupt slot
   (`Task::interrupt`). `fire_timers` (`mod.rs` line 839) writes
   `Interrupt::Timeout(id)` for each timer that is due. When an outer and an inner block
   have the same deadline, the second timer overwrites the first. The inner handler
   catches its timeout, and the outer block goes on: `i3_4_two_deadlines.wf` prints
   `inner caught: timeout at 10ms`, then `outer block goes on after its deadline, at
   110ms`. With the inner deadline 1 ms later (`i3_4_two_deadlines_ctl.wf`), the outer
   block times out at 10 ms.
2. **`sim.clock.advance` before a continuation.** `SimAdvance` calls `fire_timers` while
   the task runs. The timer sets the interrupt of the running task. Then the block
   performs an operation whose handler is outside it, and the clause sleeps.
   `check_interrupt` (`mod.rs` line 1070) takes the interrupt and calls `timeout_unwind`.
   The frame is in the continuation, so that returns `None`, and the deadline is gone: it
   does not go to `expired`. `i3_4_advance_lost_deadline.wf`: `block finished after its
   deadline at 121ms`. The control (no `advance`) gives `caught: timeout at 20ms`. In this
   case `check_interrupt` also returns early, so it does not look for `late_timeout` or a
   failed scope at that suspension point.

ADR 0010: "A `with_timeout` deadline holds also while the block is in a continuation".

**Fix.** Keep a set of expired timeout ids for each task, not one slot. In
`check_interrupt`, if `timeout_unwind` finds no frame, put the id in `expired` and go on
with the other checks.

### I3-5 (minor): `Rc` counts: nothing drops a moved capture or the result of a detached task

**What.** `heap.drop_value` does nothing for a `Value::Closure`. So a value that a closure
took by value (round 2, OR2) stays in its cell when the closure goes away.
`i3_5_closure_drop_weak.wf` moves an `Rc` into a closure that is never called, in an inner
block. After the block, `w.upgrade()` gives `Some(5)`: the `Rc` is still alive.
`leaked_rc=1`. The control without the closure (`i3_5_closure_drop_weak_ctl.wf`) gives
`None` and `leaked_rc=0`.

`Task.detach` (`natives.rs` line 249) consumes the handle, but nothing drops the result of
the task. ADR 0007: "`Task.detach` drops the result of the task." `i3_5_detach_rc.wf`:
`leaked_rc=1`. `RunOutcome::leaked_rc` says that it counts cycles.

**Fix.** Drop the owned cells of a closure when its last copy goes away (`Rc` strong count
of `ClosureVal`). Drop the result of a detached task when it finishes, or at the end of its
scope.

### I3-6 (minor): `sim.clock.advance` moves the clock of the whole run

**What.** `SimAdvance` (`natives.rs` line 384) adds to `Machine::now`, the clock of the run.
ADR 0010: "A simulation is lexical ... A task outside it and a clause of a handler outside
it see the clock of the run." `i3_6_sim_advance_outside.wf`:

- A task outside the simulation sleeps 20 ms. A task in the simulation advances 30 s. The
  outside task wakes at `30001ms`.
- A `with_timeout(1.s)` outside the simulation times out because the simulation advanced
  30 s (`caught: timeout at 30s`). The simulation body does not finish.

Also, `sim.clock.advance`, `sim.net.partition` and `sim.net.heal` run outside any
simulation, in `main` of a binary (`i3_6_advance_no_sim.wf`: `now 5s`, 0 errors). This is a
new shape of IP10.

**Fix.** Give each simulation an offset that `advance` changes, and wake only the timers of
its tasks; or reject the call outside `sim.run`.

### I3-7 (minor): the order in `sim.run` still depends on `--seed`

**What.** ADR 0010: "the order inside it depends only on its seed and its workers, not on
`--seed` or `--workers` of the run, also when a spawned task enters it or two simulations
run at one time". Two shapes break it:

1. **Nested simulations.** `pick` (`mod.rs` line 893) lists each simulation with a ready
   task as one choice of the machine. An inner `sim.run` is a simulation of its own, so the
   machine scheduler (`--seed`) chooses between the outer and the inner simulation.
   `i3_7_nested_sim.wf` (`sim.run(seed: 5)` with a `sim.run(seed: 7)` in a task) gives four
   different orders for `--seed 0` to `3`.
2. **A join of a task outside.** `i3_7_sim_join_outside.wf`: the body joins a task of an
   outer scope. The place of `joined` changes with `--seed` and `--workers`.

This is a new shape of IP9. A failing seed does not replay.

**Fix.** Schedule an inner simulation from the scheduler of its outer simulation. Reject or
document a join of a task outside the simulation.

### I3-8 (minor): a `multi` operation in a scope

**What.** The checker accepts a `multi` operation in a scope body after a spawn
(`i3_8_multi_scope_fail.wf`, 0 errors). `copy_frames` clones the `Scope` frame, so the two
copies share one `ScopeRec`, its children and its failure. The first copy raises the
failure of the child (`caught: child failed`). The second copy runs the same scope body
again, finds `propagated == true`, and ends the scope normally (`branch false ends at 15ms`,
`scope ended normally`) although its child failed. The children are not copied, so the
second copy has no siblings to cancel and no result.

**Fix.** Treat a scope with children as a value that is not `many` (W0503), as a task
handle is, or give each copy its own scope record.

### I3-9 (minor): the handler at a `join`, and the time of a raise after a resume

**What.**

1. A task of a scope fails. The owner calls `t.join()` inside a local `Fail` handler.
   `check_interrupt` (in `call_method` before the join, and when the owner wakes) finds the
   failure of the scope first, and unwinds to the scope. So the handler at the join never
   gets the failure: `i3_9_join_handler.wf` prints `scope handler: task failed`. The
   `TaskResult::Failed` branch of `join` (`natives.rs` line 442) cannot run for a task of a
   scope. ADR 0006 says "A failure of a task goes to the task that joins it", and the text
   of W0504 says "the runtime raises it ... at a `join` of a failed task".
2. ADR 0010: "it raises the failure when a resume puts the frame back". `resume` checks
   only `late_timeout`. `i3_9_resume_raise.wf` prints `the body goes on after the resume`
   and three `work` lines before `scope handler: child failed`, at the next suspension
   point.

The checker is conservative here (a suspension point in a scope can abort to the scope
handler: W0602 fires), so this is not unsound.

**Fix.** Make ADR 0005, 0006 and 0010 say the same thing: the scope handler gets the
failure of a child, also at a join, and the owner raises it at the next suspension point.
Or raise the failure at the join site and at the resume.

### I3-10 (minor): `http.serve` and the virtual clock

**What.** `run_until_done` moves the virtual clock to the next timer before it polls the
server (`advance_to_next_timer`, then `http_poll`). So a pending timer always fires before
the server accepts a connection. `i3_10_http_timeout.wf`: `with_timeout(60.s) {
http.serve(...) }` and a client that connects at once. The run prints `caught: timeout at
60s` and serves no request. A server with a sleeping background task (for example a
ticker) jumps the clock in the same way. The server state (`Machine::http`) also stays set
after the server task unwinds.

**Fix.** Poll the listener (without a wait) before the clock moves, or document that the
virtual clock does not wait for the network.

### I3-11 (minor): an inline recursive enum is copied at each move

**What.** `heap.is_copy` (line 207) says that an enum whose fields are copy values is
copy. ADR 0007 says: "A type that holds itself, such as `enum List { Cons(u64, List), Nil
}`, is not plain data." So the interpreter copies such a list at each move. Two
consequences:

- `l = Cons(i, l)` in a loop copies the whole list each time: 2500 elements take 0.7 s,
  5000 take 3.8 s, 10000 take 15 to 21 s (`i3_11_inline_list_loop.wf`).
- `is_copy` and the drop of a value recurse on the depth. A list of 8 000 000 elements
  built by recursion (`i3_11_inline_list_deep.wf`, 0 errors) aborts the process: `thread
  'weft' has overflowed its stack`, exit 134. 4 000 000 elements run.

**Fix.** Use the property table of sema (`NotCopy`) in `is_copy`. Walk values with a work
list.

### I3-12 (minor): the race detector keeps 256 accesses for one cell

**What.** `oracle.rs`: `LOG_LIMIT = 256`. After 256 records for a cell, `access` does not
record a new access. A later conflicting access then finds no record.
`i3_12_race_log_limit.wf` (rejected by the checker, run with `--unchecked --oracle`): one
task writes 300 elements of a buffer, another task writes element 299 at the same time.
The oracle finds no race. With 200 elements (`i3_12_race_log_limit_ctl.wf`), it reports
`data race: task 2 writes a buffer at [199, 0]`. So the oracle is weaker on programs with
large buffers.

**Fix.** Keep the last access for each (path, task, kind) without a limit, or report that
the limit was reached.

### I3-13 (minor): proof documents

1. `proofs/link/README.md` line 394: "`Continuation` and `Linear` derive `Copy`. The link
   assumes one exec record per model record. The interpreter must not copy a record." Line
   279 of the same README, and `copy_frames` (`effects.rs` lines 636 to 638), say that a
   `multi` resume gives each nested clause frame a copy of its record (`k: state`). Rule 2
   of the effects model keeps a fresh `once` record out of a `multi` continuation, so a
   copy is used or dropped, and `kont_rel` holds for both copies. The README must say this,
   not "must not copy".
2. `crates/weft-verified/README.md`: the `lifecycle` table does not list
   `Continuation::end` (added in R2e, `lifecycle.rs` line 107). The count 15 includes it.
3. `proofs/link/lints/unbound_use.dl` starts `unb` at the successors of `n0`. The
   hypothesis `bound_before_use` also requires `unb(v, 0)` and no use there. Sema puts no
   use at `n0` today, so this is only a difference of the text.
4. `proofs/link/mutations/run.sh` counts a mutation as caught when `verify.sh` fails for
   any reason. A patch that breaks the build, or a failure of `check-copies.sh`, also
   passes. ADR 0008 asks the `borrowing` and `effects` scripts for a result line with at
   least one error; the link script does not check this. Today each of the 26 link
   mutations fails with a Verus error (see "Proofs"), so the table is right.

## Proofs

- `proofs/verify-all.sh`: 169 + 122 + 235 + 67 verified, 0 errors.
- `end_linked` (new in R2e): its precondition (`state != Fresh`) holds at each call of
  `end` in the interpreter (after `drop_now`). `kont_rel` holds for `Dropped` with a used
  `once` record and for a `multi` record, so the theorem is not vacuous.
- The vacuity guards of round 2 still call the theorems on concrete programs and runs
  (`ex_accepted`, `ex_accepted_run`, `ex_loop_accepted`, `ex_rule3_layout_applies`,
  `example_hypotheses_satisfiable`, `example_lexical`, `example_multi_ok`).
- B6 hypotheses on the facts: the lints give one lint on the whole corpus, in
  `stored_in_loop` of `37_fn_values.wf` (a function with an expected error, documented).
  My programs (tuples, `Option<&T>`, `match` on references, loops that rebind, call
  results in `let` and in an assignment, effect results) give no lint. Sema binds a call
  result at a node after the call (`mutates_at(n4)`, `rebound_at(v1, n5)`), so
  `no_gen_kill` holds there. Fixed array steps are stable and `Vec` steps are unstable, as
  `typed_by` needs. `ret_ok` stays false for the documented `in` form.
- Mutation scripts (on a copy, `TMPDIR` in the scratch directory; logs in
  `.../r3/interp/mut/`): `proofs/link/mutations/run.sh`: 26 caught, 17 of them "link
  only", as the README says; each fails with a Verus error (assertion, postcondition or
  precondition), not a build error. `proofs/effects/mutations/run.sh`: 8 caught, with the
  counts of the table (for example `a`: 120 verified, 2 errors). `proofs/borrowing/
  mutations/run.sh`: 9 caught, with the counts of the table (for example `base`: 165
  verified, 4 errors).

## Checks that hold

- Child failures go to the handlers of the scope, also while the owner waits in a nested
  `fork` (`probe/a1_fail_in_fork.wf`: caught at 5 ms). `on abort` order on a child failure:
  innermost frame first, newest value first, then the scope handler, then the value
  outside the scope (`probe/a4_abort_order.wf`).
- A timeout around a scope cancels the children; their `on abort` runs before the handler
  (`probe/b1_timeout_scope.wf`, seeds 1 to 3).
- `multi` with an `Rc` live across the operation: each copy reads it, `leaked_rc=0`
  (`probe/c2_multi_rc.wf`, `c2b_multi_rc_clone.wf`). A `multi` operation in a scope with a
  child that does not fail behaves (`probe/c3_multi_scope.wf`).
- W0504 rejects each round-2 IP1 program, also through a closure. W0314 rejects an HTTP
  handler that performs through a handler of the caller (`probe/k1`, `k2`). A `once`
  closure as an HTTP handler is W0502 (`probe/k6`). A pinned HTTP handler stays pinned when
  the server runs in a task (`probe/k4_http_in_task.wf`).
- Simulation determinism with preemption, randomness and busy tasks outside
  (`probe/f3_sim_preempt.wf`: one order for 16 combinations of seed and workers).
- Integer widths: an overflow through a closure and a generic function faults
  (`probe/h1`); arithmetic on a type parameter is W0102 (`probe/h2`); `i64::MIN / -1`,
  `% -1`, negation and division by zero fault with a message, not a panic (`probe/h3`).
- Named arguments run in the order of the parameters in the checker and in the
  interpreter (`probe/n1`: W0301; `probe/n2`: runs).
- The oracle finds a race on a `Vec` between `push` and `print` or `len`
  (`probe/o1`, `o2`, with `--unchecked`).
- The seed sweep of 93 programs: no result changes with the seed or the workers; no steal
  of a pinned task in any trace.

## Not reported again (known)

The items of `round1b_tasks.md` ("Open after R2a/R2b", "Open after S5a and R2c-R2e", "Open
after S5b/S5c"), the gaps of ADR 0003, 0005, 0006 and 0007, OR11 (no race detector before
R2e), a pure loop that runs to its end after a cancel (by design), and a task that a
simulation body spawns into an outer scope stays in the simulation (ADR 0010 says so).

## Files

- Report: `SCRATCH/r3/interp.md`
- Repros: `SCRATCH/r3/interp/repro/` (`run_all.sh`, `run_all.out`)
- Probes: `SCRATCH/r3/interp/probe/`
- Harness: `SCRATCH/r3/interp/harness/`
- Seed sweep: `SCRATCH/r3/interp/sweep/`
- Verus log: `SCRATCH/r3/interp/verify_all.log`
- Mutation logs: `SCRATCH/r3/interp/mut/`
