# ADR 0010: The reference interpreter

Status: accepted. Date: 2026-10-18.

## Decision

- `crates/weft-interp` runs checked programs on a machine with an explicit frame stack.
  A perform captures a delimited continuation. A `once` continuation uses the verified
  state machine `lifecycle::Continuation`.
- Unwinding runs `on abort` for each live linear value. `lifecycle::Linear` proves that a
  linear value is consumed or aborted at most once. That each live value is finished
  comes from the checker (W0601) and the unwinder, and is tested, not proved.
- One deterministic scheduler with virtual workers. Work stealing obeys `stealable(T)`.
  Preemption happens at loop back-edges. A request task of `http.serve` can move to
  another worker only if the checker marks the handler closure stealable at the call,
  or if the handler is a function item that cannot start a pinned task
  (`EffectSig::pins`, ADR 0006); else it stays on the worker of the server. The
  interpreter finds the mark of a task by the source unit and the span of its
  function value: two units can have the same byte offsets.
- A failure of a child goes to the handlers of its scope or its `fork`, not to the
  handlers where the owner is when the child fails: handlers are lexical. The owner
  unwinds to the scope at its next suspension point (this cancels the siblings), and
  then performs `fail` with the handlers of the scope. If the frame of the scope is in
  the continuation of a clause outside the scope, the owner goes on: it raises the
  failure when a resume puts the frame back, or at the end of the scope. The failure
  stays in the record of its scope, so each scope keeps its own failure. If the clause
  does not resume, the abort unwinds the scope, and the failure goes away with it, as
  the other children do: the abort already ends the scope. If several scopes on the
  stack have a failure, the owner unwinds to the outermost one
  (`crates/weft-interp/tests/programs/child_fail_dropped.wf`).
- A `with_timeout` deadline holds also while the block is in a continuation, for
  example while a clause outside the block runs. The block times out when a resume
  puts it back after its deadline, as a wake after the deadline does. Each copy of a
  `multi` resume gets a timeout of its own with the same deadline.
- A `fork` gives a tuple of the branch values, also when each one is `()`, in the
  checker and in the interpreter. A function that returns `()` can still end with a
  `fork`: the value of its tail goes away. A branch of an `if` and a closure that must
  give `()` follow the rule for each other value: `let _ = fork(...)` drops the tuple.
- A closure captures the cells of the variables that it reads. A capture that the
  closure moves goes into a cell of the closure when the closure is made. Semantic
  analysis names these captures (`weft_interp::by_value_captures`), as the checker
  names the stealable tasks (ADR 0003).
- `sim.run(seed, workers)` replaces the root handlers of the clock, the randomness and
  the scheduler. A simulation is lexical: the code above its frame on the task stack
  is in it, and so is each task that this code spawns. A task outside it and a clause
  of a handler outside it see the clock of the run. The simulation has its own
  scheduler with a fixed number of simulated workers (`workers`, 4 when the call
  leaves it out). A simulation with a ready task is one choice of the machine, and its
  own scheduler then picks its task. A task in a simulation has a simulated worker,
  apart from its worker of the machine. The task that enters `sim.run` starts on the
  first simulated worker, whatever worker of the machine runs it, and a task of the
  simulation starts on the simulated worker of its parent. So the order inside it
  depends only on its seed and its workers, not on `--seed` or `--workers` of the run,
  also when a spawned task enters it or two simulations run at one time, and a failing
  seed replays (`crates/weft-interp/tests/programs/sim_workers.wf`). The same seed
  gives the same trace.
- The result of each arithmetic expression and compound assignment must fit in the
  integer type that semantic analysis gives it (`FnFacts::int_ops`, review round 2,
  RR14). So `a - b` on `u64` faults with an underflow where it is computed, also in a
  local, a result or an operand of `print`. Before, only a field or a parameter got a
  check. A value holds at most `i64::MAX`, so a larger `u64` faults as an overflow.
- The oracle checks (`crates/weft-interp/src/oracle.rs`, review round 2, OR11) are off
  by default. `RunOptions::oracle` and `weft run --oracle` turn them on. With them, the
  machine faults on a read or a write of a freed cell or buffer, a `Vec` buffer that
  moves on each `push`, `pop` and `clear` (as a real `Vec` can), a reference into a
  local whose scope ended, a live linear value that goes away with no consume and no
  `on abort` or that is live at the end of the run, a data race (a vector clock for
  each task; spawn, join, the end of a scope or a `fork`, and unwinding order the
  tasks), and a stealable task that reaches an `Rc`, a `Weak` or a `Scope`. A
  reference reaches only the value at its place, and a slice only its elements: a task
  that holds `&w.score` does not reach an `Rc` in `w.rc` (review of R2e: the first
  version walked the whole cell and gave false alarms). The stock machine prints
  `<dangling>` and goes on. The interpreter program tests and the runs
  of the corpus programs turn the checks on: an accepted program must not fault with
  them.
- The race detector logs each read and each write of a place of a cell (review round
  3, O3-13): a use of a place, a read through a reference or a `Box` on the way to a
  place, a read through a reference in an operand or in an argument of a callee
  (`Machine::deref_value`), a display of a value (`print`, string interpolation), the
  test of a literal pattern and of a variant pattern in a `match`, a copy of a part in
  a destructure through a reference (`let (a, b) = q`), and each write. For each cell
  it keeps the last access of each task, path and kind (a read or a write), with no
  limit on the number of records (I3-12). It drops the records of a task when a join
  has ended the task and each task that can still run sees its accesses: such records
  cannot find a race any more, and a task that starts later sees them through its
  parent. So the cost of an access does not grow with the number of joined tasks.
- With the oracle checks on, a display of a moved value, of a freed cell or buffer, or
  of a value through a dangling reference is a fault, as each other read of it is.
  The stock machine shows `<moved>`, `<freed>` or `<dangling>` and goes on.
- An abort path ends the scope of each local and temporary of a frame that it unwinds,
  as the normal end of a scope does (F3-9). A reference into such a local is dangling
  for the oracle. A copy value stays in its cell, as at a normal end.
- Phase 1 does not simulate the network. `sim.net.partition` and `sim.net.heal` only
  record the partition in the trace, and `http.serve` binds a real socket also in a
  simulation.

- `weft run FILE` runs `fn main` and `weft test FILE` runs the test blocks, through
  `weft_interp::{run_main, run_tests}`. Both check the program first and do not run it
  if it has errors, unless `--unchecked` is given. `--seed` and `--workers` (1 to
  1024) set the scheduler. Errors and a failure give exit code 1; with `--unchecked`,
  the exit code shows only the run. The binary writes the output and the log of each
  test before its result line. A file with no test blocks gets a note.

## Consequences

- The interpreter demonstrates the runtime design. It does not measure task density or
  native performance (Phase 2).
