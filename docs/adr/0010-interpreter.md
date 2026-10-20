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
  another worker only if the checker marks the handler closure stealable at the call
  (ADR 0006); else it stays on the worker of the server.
- A failure of a child goes to the handlers of its scope or its `fork`, not to the
  handlers where the owner is when the child fails: handlers are lexical. The owner
  unwinds to the scope at its next suspension point (this cancels the siblings), and
  then performs `fail` with the handlers of the scope. If the frame of the scope is in
  the continuation of a clause outside the scope, the owner goes on: it raises the
  failure when a resume puts the frame back, or at the end of the scope.
- A `with_timeout` deadline holds also while the block is in a continuation, for
  example while a clause outside the block runs. The block times out at its next
  suspension point after a resume puts it back. Each copy of a `multi` resume gets a
  timeout of its own with the same deadline.
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
  own scheduler then picks its task. So the order inside it depends only on its seed
  and its workers, not on `--seed` or `--workers` of the run, and a failing seed
  replays. The same seed gives the same trace.
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
