# ADR 0006: Modes, separation and work stealing

Status: accepted. Date: 2026-10-18.

## Decision

- Four mode axes: uniqueness, portability, contention, affinity. The lattice is verified
  (`weft_verified::modes`), but the checker does not use it yet: the mode rules use the
  flags `nonportable`, `uniq` and `shared` in the facts (ADR 0004).
- `@ shared` forbids mutation through the reference (W0402).
- A closure takes its modes from what it captures. It is nonportable if it captures a
  nonportable value, because it refers to the variable. It is not `many` if it runs
  only once (ADR 0007) or captures a value that is not `many`, such as a `@ uniq`
  reference: a copy of it would copy that value (W0503). It is `@ uniq` if each
  captured variable that holds a reference is.
- A local is `@ uniq` while it holds a `@ uniq` value: a new aliased value ends it
  (W0406). Its variable is `@ uniq` only if each of its values is, and not `many` if
  one is. The hidden iterator of a `for` loop is `@ uniq` if its source is, so it is
  not `many` either.
- A fork branch must be portable: no nonportable captures (W0401) and no mutation
  through an aliased reference (W0403). `split_mut` gives `@ uniq` parts.
- Separation (W0405): a task is active from its spawn to its join or the scope end. Each
  node that runs while a task is active must not access what the task writes, and must
  not write what the task reads.
- The rule is access-based. Sema records the reads: a use of a reference as a value
  reads the places that it points into, a call reads its reference arguments, a loop
  reads the elements at each iteration, and a handler clause reads its captures at each
  operation that it handles. A plain use of a reference is not an access by itself, so a
  task and the parent can touch separate fields through one reference.
- A move or the end of an owner frees its memory (`frees_at`). A free while a task is
  active must not overlap what the task reads or writes. A task closure that moves a
  capture moves it when the closure is made. A move of a part frees that part only.
- The tasks of a scope join before the locals of the scope body go out of scope, as in
  the interpreter.
- The B4 proof covers a stronger rule: no write to a place that the other task *holds*
  (references and captures, at any point). The access-based rule is more permissive.
  The proof does not cover it.
- A spawn is a mutation at the spawn node. So a reference that a task breaks is invalid
  after the join.
- A spawned task that captures a nonportable value or a shared-mutable reference is
  pinned. The relation `stealable(T)` tells the scheduler which tasks can move.
  `tests/programs/33_stealable.wf` marks each task closure `//~ stealable` or
  `//~ pinned`, and the corpus test checks the marks.
- A spawn in statement position gives its handle to the scope. A bound handle is linear.
- A task joins at the end of the scope of its receiver (`a.spawn` in an inner scope joins
  at the end of the scope of `a`). A closure or a handler clause that spawns into a scope
  outside it starts the task at each node where it runs: a call of the closure, a call
  that gets the closure, and an operation that runs the clause. A body around that
  closure starts the task where it runs the closure. A closure that returns a closure
  that spawns does not start the task: a call of the result does, and so does a callee
  that gets the maker. A task handle stays a task handle through a `handle`, an `if`, a
  `match` and the result of a closure. A join of it joins the task.
- A callee, a function value or a clause can call a closure more than once. Then a task
  that the closure spawns starts again at a node after the call, where it conflicts
  with its first start (W0405). A signature has a `repeats` part: the function
  parameters that the body can call more than once (at two nodes, in a loop, in a
  closure, or after a store). A function with no body can call each function argument
  more than once, except `with_timeout`. A clause can call each function argument of
  its operation more than once.
- A task cannot perform through a handler on the stack of another task (W0314). This
  holds for a closure, a function item and a function parameter that runs as a task:
  the effects of an item resolve against the handlers at the spawn. It holds for the
  function values that the task holds or captures, also in a field of a local. A
  signature has a `tasks` part: the function parameters that a task of the body can
  call. The caller checks the function value that it gives to such a parameter. A
  clause can run its function parameter as a task: each operation that gives it a
  function value checks the value, with the handlers of the `handle`. A foreign
  function and `http.serve` can run each function argument as a task. A signature has
  a `task_effects` part: the effects that its tasks perform through a handler of a
  caller. A caller checks that its local handlers do not get them. The root handlers of
  `sim.run` replace the runtime, so a task of the simulation body reaches them. A
  failure of a task goes to the task that joins it, not to a handler, so `Fail` is not
  part of the rule. The interpreter gives the failure to the joiner also with no
  runtime.

## Consequences

- What stays imprecise (sound, but it can reject a correct program):
  - A clause that spawns after `resume` starts the task at the operation. So the code
    after the operation counts as running while the task is active, but `resume` runs
    it before the spawn.
  - A call of a closure that returns a closure that spawns starts the task also when
    nothing calls the result, if a callee gets the maker.
  - `repeats` counts a call in a closure or in a loop, and a call at two nodes, also
    on two branches of an `if`.
  - W0314 counts each function value that a task holds or captures, also when the
    task does not call it.
- What stays open (not checked):
  - A stored closure that spawns and runs at a node that can reach it starts the task
    there once: the copies of a second run are not seen.
  - A clause that runs a parameter of a closure as a task: the closure has ended when
    the clause is lowered, so its callers do not check the value.
