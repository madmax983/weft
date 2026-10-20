# Review round 2, lens "interp": the interpreter and the proofs

Commit: 328a39b (worktree `/home/user/wt-edge`, branch `review/r2`).
Scratch files: `SCRATCH/r2/interp/`.
Repro files: `.../r2/interp/repro/`. The script `repro/run_all.sh` runs each repro. Its
output is in `repro/run_all.out`. The harness `.../r2/interp/harness` runs a file with a
seed, a worker count and the trace, and it prints `leaked_rc`.

## Summary

| Id | Severity | Title |
| --- | --- | --- |
| IP1 | blocker | A `Fail` handler can resume a failure that the runtime raises |
| IP2 | major | A child failure goes to the handler at the current suspension point of the owner |
| IP3 | blocker | A stealable task shares an `Rc` with a pinned child: two workers touch it at one instant |
| IP4 | major | A `multi` copy keeps the cells of a handler clause inside the continuation |
| IP5 | major | A `with_timeout` deadline is lost when the block is not on the task stack |
| IP6 | major | `fork` gives `()` when each branch value is `()`: a generic caller faults |
| IP7 | major | Each HTTP request task is stealable: the interpreter ignores the checker |
| IP8 | major | B6: sema facts break `bound_before_use` and `ret_ok` in accepted programs |
| IP9 | minor | The output of `sim.run(seed: N)` changes with `--workers` |
| IP10 | minor | The simulation is global state, not lexical: other tasks and outer clauses see its clock |
| IP11 | minor | ADR 0010 claims a simulated network; `sim.net.partition` changes nothing |

Proof runs: `proofs/verify-all.sh` passes. Results: borrowing 169, effects 122, link 233,
`crates/weft-verified` 66, 0 errors (log: `.../r2/interp/verify_all.log`, 64 s). The
counts agree with the READMEs. No proof file has `assume`, `admit`, `external_body` or a
`#[verifier::...]` attribute. `cargo test --release -p weft-interp` passes.

The main pattern: the interpreter raises failures and deadlines at a suspension point
with the state that is on the stack at that moment. It does not use the lexical state of
the scope, the fork or the timeout. IP1, IP2 and IP5 come from this. One fix can cover
the three: deliver a child failure as an unwind to the `Scope`/`Fork` frame (as
`timeout_unwind` does to the `Timeout` frame), keep the handler environment in the scope
record, and make a runtime failure an abort that a clause cannot resume.

## Method

1. I read `docs/design.md`, ADR 0005, 0006, 0007, 0008, 0010, the interpreter
   (`crates/weft-interp/src`, all modules), the proof READMEs and the link sources
   (`proofs/link/src/dataflow_link.rs`, `places_link.rs`).
2. I wrote programs that must behave in a stated way (handlers, `once` and `multi`,
   `on abort` order, cancellation, scopes, joins, `fork`, timeouts, the scheduler,
   `sim.run`, `Rc` counts, HTTP). I ran each one with `weft check` and `weft run` or
   `weft test`, and with the harness for traces.
3. I ran Verus on all proof crates.
4. For B6, I wrote lint rules over the spec relations (`weft lint --rules`). They test
   `no_gen_kill` and `bound_before_use` on each corpus program. I wrote a program for
   `ret_ok`.

## Findings

### IP1 (blocker): a `Fail` handler can resume a failure that the runtime raises

**What.** `effect Fail { fn fail(msg: String) }` returns `()`. So a clause of `Fail` can
`resume(())`. The checker accepts this. The runtime raises a failure through this
operation at these points:

- `t.join()` of a failed or cancelled task (`natives.rs`, `join`);
- the end of a scope with a failed child (`exec.rs`, `raise_scope_failure`);
- a `fork` with a failed branch (`exec.rs`, `fork_step`);
- a `with_timeout` deadline (`After::Fail` in `effects.rs`);
- a child failure at the next suspension point of the scope owner
  (`check_interrupt`, `Interrupt::Fail`);
- `fs.read` of a file that does not exist.

When the clause resumes, `()` becomes the value of the interrupted expression. The type
of that expression is `T` (`join -> T`, `with_timeout<T> -> T`, the scope value, the
fork tuple). At a retried suspension point (`join`, scope wait, `fork`), the resume
pushes `()` on the operand stack, and the retried instruction then reads the wrong
operands.

Results (all programs: 0 errors):

| Repro | Run |
| --- | --- |
| `ip_fail_resume_join.wf` | ``runtime error: `Add` cannot apply to `()` and `1` `` |
| `ip_fail_resume_scope.wf` | ``runtime error: `Add` cannot apply to `()` and `1` `` |
| `ip_fail_resume_fork.wf` | `runtime error: this value is not a tuple of that size` |
| `ip_fail_resume_timeout.wf` | ``runtime error: `Add` cannot apply to `()` and `1` `` |
| `ip_fail_interrupt_join.wf` | ``runtime error: this value has no method `join` `` (the operand stack is wrong) |
| `ip_fail_interrupt_scope_wait.wf` | ``runtime error: `Add` cannot apply to `()` and `1` `` (the scope value is `()`, not `41`) |
| `ip_fail_interrupt_fork.wf` | `runtime error: internal: a value reached a fork mark` |

```weft
let r = handle Fail { fn fail(m) { print("caught {m}"); resume(()) } } in {
    with_timeout(10.ms) { sleep(100.ms); 5 } + 1     // with_timeout gives ()
}
```

**Proof link.** The effects model states: "`fail` is an operation whose clause does not
resume" (`proofs/effects/README.md`, "Scope and limitations"). The checker does not
mirror this assumption, and the interpreter does not enforce it. The fidelity lens lists
the other model assumptions (FD1, FD4). This one is not in its list.

**Repro.** `repro/run_all.sh`, section IP1.

**Fix.** Choose one and record it in ADR 0005:
- type `fail` as `-> Never` (a clause of `Fail` cannot resume; the checker rejects
  `resume` there), or
- keep `fail` resumable for user code, but raise a runtime failure as an abort: run the
  clause, and if it resumes, fault with a clear message, or do not give the clause a
  continuation.
Also deliver a child failure at the scope frame, not at the instruction that waits (see
IP2). Add the seven programs to `crates/weft-interp/tests/programs`.

### IP2 (major): a child failure goes to the handler at the current suspension point of the owner

**What.** `child_failed` sets `Interrupt::Fail` on the scope owner. At the next
suspension point of the owner, `check_interrupt` performs `fail` with `top_henv()`: the
handlers of the innermost code frame at that moment. This is dynamic resolution. The
design says: "Handlers are lexical". ADR 0006 says: "A failure of a task goes to the task
that joins it, not to a handler". The scope (or the join) is the lexical place of the
failure.

Consequences:

- A private `Fail` handler of a callee gets the failure of the caller's child. It
  resumes, and the scope returns normally with a failed child.
- The handler that gets the failure depends on timing. In
  `ip_child_fail_callee_handler.wf` the child fails at 5 ms in the first run and at 15 ms
  in the second run. The first run prints `callee handler: child failed`, `scope body
  done`, `scope returned normally`. The second run prints `main handler: child failed`
  and aborts the scope.
- `ip_child_fail_inner_handler.wf`: an inner `handle Fail` that does not enclose the
  spawn gets the failure.

**Repro.** `repro/run_all.sh`, section IP2.

**Fix.** Keep the handler environment of the `scope` in `ScopeRec` (and of the `fork`,
which already has one). At the next suspension point of the owner, unwind the frames
above the `Scope` frame (this cancels the siblings), then perform `fail` with the
environment of the scope. `timeout_unwind` does the same for `with_timeout`.

### IP3 (blocker): a stealable task shares an `Rc` with a pinned child

**What.** Task `a` captures nothing, so the checker marks it stealable. Its body makes an
`Rc` and spawns a child `b` that captures the `Rc`. The checker pins `b` to the worker of
`a` at the spawn. Later the scheduler steals `a` to another worker. Then `a` and `b` run
on two workers in the same virtual instant, and both change the count of one `Rc`.

```weft
s.spawn(|| {                                  // stealable
    let r = Rc.new(0)
    scope { t =>
        t.spawn(|| { sleep(5.ms); let y = r.clone() })   // pinned
        sleep(5.ms)
        let z = r.clone()
    }
})
```

Trace with seed 2: `steal t1 w2 -> w0`, `run t1 on w0`, `run t2 on w2`, both at 5 ms.
Seeds 2 to 8 all steal `t1`.

The design says: "A shared-mutable reference is always nonportable. It cannot be
captured by anything that runs on another thread." The rule for stealing ("a task whose
captured state is `@ portable` may move") looks only at the captures of the task. It does
not look at the nonportable values that the task makes and shares with a pinned task. A
native runtime would have a data race on the count. The interpreter cannot show the race:
it has one thread and no race detector (OR11). OR7 (oracle lens) is a different shape: a
function parameter that runs as a task.

**Repro.** `repro/ip_steal_shares_rc.wf`; `run_all.sh`, section IP3.

**Fix.** A task that spawns a pinned task that captures a local of the task is pinned
too (in the spec: `pinned(T) :- spawns_in(T, U), pinned(U), captures_local_of(U, T)`),
or pin a task while it has a live pinned child that captures its locals. Add the program
to `33_stealable.wf` with `//~ pinned`.

### IP4 (major): a `multi` copy keeps the cells of a handler clause inside the continuation

**What.** `copy_frames` (`effects.rs`) gives fresh cells to the slots, temporaries and
owned buffers of the copied code frames. It remaps closure values and `CodeFrame.caps`.
It does not remap a `Frame::Handle` inside the copied frames (`other => other.clone()`).
So the clauses of a handler that the continuation installed still capture the cells of
the template frames. A clause that changes a local then changes the template, not the
copy. Each later resume starts from the changed template, not from the captured state.

```weft
handle Choice { fn choose() { resume(true); resume(false) } } in {
    let count = 0
    let r = handle Tick { fn tick() { count += 1; resume(()) } } in body()  // body: choose(), tick()
    all.push(count)
}
```

Expected `[1, 1]`. The interpreter prints `[0, 1]`. The control program with a closure
in place of the clause prints `[1, 1]`. FD2 (fidelity lens) is a different defect of
`copy_frames`: it shares the `Clause` record.

**Repro.** `repro/ip_multi_clause_caps.wf`, `repro/ip_multi_clause_caps_ctl.wf`.

**Fix.** In `copy_frames`, map each `Frame::Handle` to a new `HandleMark` whose clause
cells go through `map`. Add the program to the interpreter corpus.

### IP5 (major): a `with_timeout` deadline is lost when the block is not on the task stack

**What.** `fire_timers` handles `Timer::Timeout` only if the `Timeout` frame is on the
task stack. Else it drops the timer. Two cases lose the deadline:

1. The block performs an operation whose handler is outside the `with_timeout`. The
   `Timeout` frame goes into the continuation, and the clause sleeps past the deadline.
   When the clause resumes, the block runs with no deadline
   (`ip_timeout_lost.wf`: `block finished after its deadline`, `v = 1`). The same block
   without the outer handler times out (`ip_timeout_ctl.wf`: `caught: timeout`).
2. The block is inside a `multi` continuation. The copies share the timeout id. When the
   first copy returns, `deliver` removes the timer. The second copy runs with no deadline
   (`ip_multi_timeout.wf`: `slow finished after its deadline`).

The design says: "Cancellation means abort at the next suspension point", and
`with_timeout` is "a handler that aborts the block".

**Repro.** `run_all.sh`, section IP5.

**Fix.** When the frame is not on the stack, keep the expiry: mark the timeout id as
expired, and check it when a resume puts the frame back (or at the next suspension
point of the task). Give each `multi` copy its own timeout id, or keep the timer until
the last copy ends. ADR 0007 says that `with_timeout` runs its block once. If a block
cannot hold a `multi` operation, the checker must reject `ip_multi_timeout.wf`.

### IP6 (major): `fork` gives `()` when each branch value is `()`

**What.** `fork_step` returns `Value::Unit` if each branch value is `Unit`, else a tuple.
The checker types a fork of closures that return `()` as `()` too
(`ip_fork_unit.wf` gets W0102 for `let (a, b) = fork(|| print("l"), || print("r"))`).
But in a generic function the checker types `fork(f, g)` as `(T, T)`. With `T = ()` the
interpreter gives `()`, and the destructuring faults.

```weft
fn both<T>(f: fn() -> T, g: fn() -> T) -> (T, T) / par { fork(f, g) }
let (c, d) = both(|| print("x"), || print("y"))   // runtime error: not a tuple of that size
```

**Repro.** `repro/ip_fork_generic_unit.wf` (0 errors, run-time fault).

**Fix.** Always give a tuple, in the checker and the interpreter. The design writes
`let (a, b) = fork(...)`. Then `ip_fork_unit.wf` is accepted.

### IP7 (major): each HTTP request task is stealable

**What.** `http_poll` (`http.rs`) adds each request task with `stealable: true`. It does
not ask the checker. A handler closure that captures an `Rc` (nonportable) runs on
another worker: the trace shows `spawn t2 from t0 on w0 (stealable)`, `steal t2 w0 ->
w3`. The checker accepts the program with 0 errors and has no `stealable` fact for these
tasks. `lib.rs` says: "An idle worker steals only a task that the checker marked
`stealable`". ADR 0006 says: "A foreign function and `http.serve` can run each function
argument as a task". Today the interpreter serves one request at a time, so it shows no
race. A runtime with several requests in flight would race on the count.

**Repro.** `repro/ip_http_pinned.wf`; `run_all.sh`, section IP7 (needs a free port 18431).

**Fix.** Mark the request task stealable only if the checker proves the handler value
portable (W0401 for a nonportable capture of a function argument of `http.serve`), else
pin it to the worker of the server.

### IP8 (major): B6: sema facts break `bound_before_use` and `ret_ok` in accepted programs

**What.** The link theorem `thm_w0301_no_ub` needs `facts_ok` (with `ret_ok`) and
`bound_before_use`. `proofs/link/README.md` says that sema gives `bound_before_use`
"through lexical scope", and that W0312 "probably gives" `ret_ok`. Both statements are
false for accepted programs:

1. `bound_before_use`. The lint `repro/unbound_use.dl` finds 7 uses of a reference at a
   node where it can be unbound (no `rebound_at` on some path from the entry). One is in
   an accepted function: `loop_replaces_part` (`tests/programs/76_ref_flow.wf:312`).
   The hidden part variable of `w.x` has `points_into` and `uses`, but no `rebound_at`
   at the struct literal (`v6`), and the loop variable (`v9`) is unbound when the loop
   runs 0 times. The other sites are in functions with an expected error
   (`37_fn_values.wf` stored values, `73_immovable.wf`, `76_ref_flow.wf`).
2. `ret_ok`. `repro/ret_ok.wf` is accepted. The call `pick(&w, x)` mutates
   `w.entities` and returns a reference derived from the argument `x` in
   `w.entities[]`. The `in` form of ADR 0005 lets the two arguments overlap, so W0312
   does not fire. In B1 terms the call kills the group of `x`, so `ret_ok` is false. The
   callee body check (rule 3 inside `pick`) makes this program safe, but the link
   theorem does not apply to it.

No test checks these hypotheses. FD5 (fidelity lens) says that agreement tests cannot
check them. This finding shows that they are false on accepted programs. The checker
is not unsound here: a missing `rebound_at` only adds invalid nodes. But the B6 claim
covers fewer programs than the README says.

`no_gen_kill` holds: the lint `repro/gen_kill.dl` finds no node that both invalidates
and rebinds a reference, in the corpus and in `repro/holds/ip_genkill_probe.wf`.

**Repro.** `run_all.sh`, section IP8.

**Fix.** Emit `rebound_at` for each hidden part variable at the node that gives its
first value (the struct literal), or state the hidden variables as a gap. Correct the
two README sentences. Add `unbound_use.dl` and `gen_kill.dl` as a corpus test (each
accepted function: no lint output).

### IP9 (minor): the output of `sim.run(seed: N)` changes with `--workers`

**What.** `enter_sim` replaces the scheduler random state, but `pick` draws from a list
of candidates whose length depends on the number of workers. So the interleaving inside
`sim.run(seed: 7)` changes with `--workers` (1, 2, 8 give three different orders). It
does not change with `--seed`. The design says: "a failing seed replays exactly". A
test that fails with `--workers 8` passes with `--workers 1`.

**Repro.** `repro/ip_sim_determinism.wf`; `run_all.sh`, section IP9.

**Fix.** Let `sim.run` fix the number of workers (for example a `workers:` argument
with a default), or document that the replay needs the same `--workers`.

### IP10 (minor): the simulation is global state, not lexical

**What.** `sim` is one field of the machine. While a `sim.run` body runs, each task and
each clause sees the simulated root handlers:

- A sibling task outside the simulation reads `Clock.now()` relative to the start of
  the simulation. Its clock goes back from 12 ms to 7 ms (`ip_clock_outside_sim.wf`).
- The clause of a handler outside `sim.run` reads the simulated clock (5 ms) where the
  real virtual time is 15 ms (`ip_clause_outside_sim.wf`).

The design says that handlers are lexical, and that `sim.run` replaces the root handlers
for its body.

**Repro.** `run_all.sh`, section IP10.

**Fix.** Keep the simulation state per frame (look for the nearest `Sim` frame of the
task, and give spawned tasks the simulation of their spawn site), or reject a task
outside the simulation while one runs.

### IP11 (minor): ADR 0010 claims a simulated network

**What.** ADR 0010: "`sim.run(seed)` replaces every root handler: virtual clock, seeded
randomness, simulated network and scheduler." `sim.net.partition` and `sim.net.heal`
only write a field and a trace event. No code reads the partition. `http.serve` inside
`sim.run` binds a real socket. The round-1 interpreter report said this, but the ADR
still makes the claim.

**Repro.** `run_all.sh`, section IP11 (`grep partition`).

**Fix.** Say in ADR 0010 that the network is not simulated in Phase 1.

## Checks that hold

- `on abort` order: innermost frame first, newest value first (`holds/ip_abort_order.wf`:
  3, 2, 1). Grandchildren of a cancelled task run `on abort` (`holds/ip_grandchild_cancel.wf`).
- Lexical handlers: a closure keeps the handler of its creation site, a function item
  uses the handler of its call site (`holds/ip_lexical.wf`). A clause performs to the
  outer handler (`holds/ip_clause_outward.wf`: 11).
- W0314 rejects a task that performs `Log` through a handler of the parent
  (`holds/ip_task_log_intercept.wf`).
- W0315 rejects `return` out of a scope body and a handled body
  (`holds/ip_scope_return.wf`, `holds/ip_closure_return.wf`). W0103 rejects a one-branch
  `fork` (`holds/ip_fork_one.wf`).
- `Rc` counts: no leak after a cancelled task, an aborted continuation, a timeout, and
  a `multi` resume (`holds/ip_rc_cancel.wf`, `holds/ip_multi_rc.wf`: `leaked_rc=0`).
- Round 1: the false W0314 for a task closure inside `sim.run` is fixed
  (`ip_sim_determinism.wf` checks with 0 errors). `cargo test -p weft-interp` passes.
- The same seed and the same worker count give the same trace.
- Proofs: all four crates verify with the README counts. The vacuity guards
  (`example_hypotheses_satisfiable`, `example_lexical`, `example_multi_ok`,
  `ex_accepted`, `ex_accepted_run`, `ex_loop_accepted`, `ex_rule3_layout_applies`) call
  the theorems on concrete accepted programs and runs. `check-copies.sh` passes.
- Sema stability: a fixed array element is stable, a `Vec` element is unstable
  (`b6/stab.wf`), as `typed_by` needs.

## Not reported again (known)

FD1 (`on abort` effects), FD2 (`multi` copies share a `Clause` record), FD4 (affine values
across `multi`), FD5 (README on agreement tests), OR7 (function parameters as tasks), OR9
(`resume` in a task), OR11 (weak oracle, no race detector), RR3 (a continuation leaves
its clause), RR14 (integer widths). A pure loop that is cancelled runs to its end: this is
by design (cancellation only at suspension points).

## Files

- Report: `SCRATCH/r2/interp.md`
- Repros: `SCRATCH/r2/interp/repro/` (`run_all.sh`, `run_all.out`)
- Harness: `SCRATCH/r2/interp/harness/`
- Verus log: `SCRATCH/r2/interp/verify_all.log`
