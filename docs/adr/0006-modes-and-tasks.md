# ADR 0006: Modes, separation and work stealing

Status: accepted. Date: 2026-10-18.

## Decision

- Four mode axes: uniqueness, portability, contention, affinity. The lattice is verified
  (`weft_verified::modes`), but the checker does not use it yet: the mode rules use the
  flags `nonportable`, `uniq` and `shared` in the facts (ADR 0004).
- `@ shared` forbids mutation through the reference (W0402).
- A type states at most one mode on each axis, and not both `uniq` and `shared`
  (W0119). A `shared` value is visible to other threads, so it is not unique. The
  verified lattice keeps its axes independent, so it has an element with `uniq` and
  `shared`. Sema rejects only the written pair.
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
  capture takes it when the closure is made, as each closure does (ADR 0003): the
  interpreter moves the value into a cell of the closure there. A new value of the
  variable while the task is active stays in the variable. A move of a part frees that
  part only.
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
  `match` and the result of a closure. A handle can hold one of several tasks: after
  an `if` or a `match`, or in a loop that passes handles from one local to another.
  Each local keeps the set of tasks that it can hold on its own path; a join of paths
  joins the sets. At run time a handle holds one task. So a join of it ends a task of
  its set only if no other local can hold that task there (`joined_at` is a must
  fact: `active` stops at it). A move of the whole handle, and its join, empty the set
  of the local. After `h.join(); h = s.spawn(...)` in a loop, `h` is the only holder,
  so the join ends each task of its set. After a swap of two handles, the first join
  ends no task, and the second join ends both.
- A callee, a function value or a clause can call a closure more than once. Then a task
  that the closure spawns starts again at a node after the call, where it conflicts
  with its first start (W0405). A signature has a `repeats` part: the function
  parameters that the body can call more than once (at two nodes, in a loop, in a
  closure, or after a store). A function parameter can be live across a node that
  can resume more than once. Then it is part of `repeats` too: the code after the
  node runs again for each resume. A function with no body can call each function
  argument more than once, except `with_timeout`. A clause can call each function
  argument of its operation more than once.
- Such a call runs the closure two times in a row: a node right after the call uses the
  closure again. So a change in the first run that invalidates what the closure
  captures is W0301 at the call, as for `g(); g()`. A call of a function parameter in a
  closure counts where the closure runs. A function that only returns the closure
  does not run it: the value that it returns has a `repeats` part of its own
  (`RetFn::repeats`), and a call of that value runs it two times in a row.
- A node that can run a stored closure more than once starts its tasks again after it
  (W0405). These nodes are:
  - A call of a callee whose body can run a stored value in a loop or in a closure.
    Two nodes where one can follow the other count too (the `reach` part).
  - A call of a function with no body.
  - A call of a function value that the body does not know, with an argument that
    holds a function value.

  A call of a function value that the body does not know runs a stored value once. A
  value that the body does not know is a stored value too, for example one that it
  reads out of a field. A callee that can call it more than once runs it more than
  once.
- A task cannot perform through a handler on the stack of another task (W0314). This
  holds for a closure, a function item and a function parameter that runs as a task:
  the effects of an item resolve against the handlers at the spawn. It holds for the
  function values that the task holds or captures, also in a field of a local. A
  signature has a `tasks` part: the parameters whose function values a task of the
  body can call. The caller checks the function value that it gives to such a
  parameter. It also checks the function values that an argument holds in a field or
  a container, or points to. A parameter of a type parameter can hold a function
  value too. So can a place behind a reference that a reference parameter points to.
  A result that a callee copies out of a reference argument holds the marks of the
  argument. A clause can run its function parameter as a task. Each operation that
  gives it a function value checks the value, with the handlers of the `handle`. Such
  a value can come from a callee. It can be a closure that the callee gives to an
  operation of a handler of its caller (the `op_effects` part, ADR 0005). It can be a
  parameter of a closure that a callee returns (the `ret` part). A closure that a
  callee returns can run its parameter as a task too.
- The capabilities of a value carry marks for W0314. There are three marks:
  - An effect that a closure or a function item in the value performs through a
    handler of a caller.
  - A parameter of the function whose function values the value can hold.
  - A value that the body cannot follow.

  A task that runs a value with a mark of a user effect is W0314. A standard effect is
  part of `task_effects`, and a parameter is part of `tasks`. A value that the body
  cannot follow comes from a parameter of a closure or a clause, in a field or an
  element. It can also come from an operation of a handler of a caller. A task that
  runs it is W0314. A foreign function and `http.serve` can run each function argument
  as a task. A signature has
  a `task_effects` part: the effects that its tasks perform through a handler of a
  caller. A caller checks that its local handlers do not get them. The root handlers of
  `sim.run` replace the runtime, so a task of the simulation body reaches them. A
  failure of a task goes to the task that joins it, not to a handler, so `Fail` is not
  part of the rule. The interpreter gives the failure to the joiner also with no
  runtime.
- A closure takes its modes from what it captures. It is nonportable if it captures a
  nonportable value, because it refers to the variable. It is not `many` if it runs
  only once (ADR 0007) or captures a value that is not `many`, such as a `@ uniq`
  reference: a copy of it would copy that value (W0503). It is `@ uniq` if each
  captured variable that holds a reference is.
- A local is `@ uniq` while it holds a `@ uniq` value: a new aliased value ends it
  (W0406). After an `if`, a `match` or a loop, it is `@ uniq` only if it is at the
  end of each branch. Its variable is `@ uniq` only if each of its values is, and not
  `many` if one is. The hidden iterator of a `for` loop is `@ uniq` if its source is,
  so it is not `many` either.
- A reference to a nonportable value is nonportable. A closure keeps its modes in a
  field, an element, a tuple part and an enum payload, also in a place of type `fn()`.
  The local that holds it gets them (ADR 0007).

## Consequences

- What stays imprecise (sound, but it can reject a correct program):
  - A clause that spawns after `resume` starts the task at the operation. So the code
    after the operation counts as running while the task is active, but `resume` runs
    it before the spawn.
  - A call of a closure that returns a closure that spawns starts the task also when
    nothing calls the result, if a callee gets the maker.
  - A call that can run its function argument again uses the argument again after
    each change at the call. The change can be one of the callee, not of the first
    run, and the callee can run the closure before it.
  - `repeats` counts a call in a closure or in a loop, and a call at two nodes, also
    on two branches of an `if`. The `reach` part counts two nodes only if one can
    follow the other.
  - W0314 counts each function value that a task holds or captures, also when the
    task does not call it. It counts each function value in an argument of a
    parameter in `tasks`, also when the task runs another one.
  - A body can give a value from a field or a container to a function parameter. It
    can also give it to a function value that it does not know. That function value
    can run it as a task, so the parameter of the value is part of `tasks`. So W0314
    counts the function values in that argument. It counts them also when the caller
    gives a closure that starts no task. An example is a helper that calls its
    callback for each element of a `Vec`.
  - A task can run a function value from a parameter of a closure or a clause, in a
    field or an element. That is W0314. So is a value from an operation of a handler
    of a caller.
  - A node that can run a stored value more than once starts each stored closure that
    spawns again. It also starts a closure that the callee does not run.
  - A clause that runs its parameter as a task reports W0314 at the operation and at
    the spawn in the clause.
- What stays open (not checked): a function value that the body cannot follow can go
  to an operation of a handler of a caller (ADR 0005).
