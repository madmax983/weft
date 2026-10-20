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
  through an aliased reference (W0403). `split_mut` gives `@ uniq` parts. Reads from
  several threads need no `@ shared`: W0403 and W0405 check the writes, so two fork
  branches can read through one aliased reference
  (`tests/programs/136_call_reads.wf`).
- Separation (W0405): a task is active from its spawn to its join or the scope end. Each
  node that runs while a task is active must not access what the task writes, and must
  not write what the task reads.
- The rule is access-based. Sema records the reads: a use of a reference as a value
  reads the places that it points into, a call reads its reference arguments, a loop
  reads the elements at each iteration, and a handler clause reads its captures at each
  operation that it handles. A plain use of a reference is not an access by itself, so a
  task and the parent can touch separate fields through one reference.
- A use of a local as a value reads its variable: the root place of an owned local, or
  the root place of the variable of a reference local (ADR 0003). A new value of a
  local (`x = v`, `x += v`) writes its variable. A place through a reference local
  reads the reference too, but not the places that it can reach. A `let` and a loop
  variable get a new variable, as in the interpreter, so they write nothing. An index
  reads the length and the buffer of the indexed place, also for a borrow `&v[i]`, as
  `v.get(i)` does.
- A task keeps the cell of a copy variable that it captures (`kept(T, Rt)`): the
  interpreter keeps a captured copy value readable after its scope ends, as for a
  closure (ADR 0003). So the end of the variable is not a free for the task. A
  reference into the variable is still invalid after the end. So a task does not keep
  a variable when a captured local holds a reference into it, or when the code of the
  task makes one: a borrow, a binding by reference, or a reference argument of a call
  (`tests/programs/130_task_locals.wf`). A capture that the closure moves is in a cell
  of the closure, so the task does not share it with the parent.
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
- A spawn is a mutation at the spawn node. A task can change what it writes at any
  time while it runs. So the node right after the end of a task (a `join`, the end of a
  `fork` or a scope, or an abort of the scope) gives the places that the task writes
  to a value that can mutate them (`lends_mut`). A reference that the parent makes
  while the task runs is then invalid after the end, if the task can break it (W0301).
- A spawned task that captures a nonportable value or a shared-mutable reference is
  pinned: the join of the modes of its captures is not a submode of the mode that
  crosses threads (`portable`). The checker and sema compute this with the verified
  lattice (`VarInfo::capture_mode`, `CROSSES_THREADS`, `modes::{join, submode}`).
  The relation `stealable(T)` tells the scheduler which tasks can move.
  `tests/programs/54_stealable.wf` marks each task closure `//~ stealable` or
  `//~ pinned`, and the corpus test checks the marks.
- A task that runs a function value that the body does not follow (a function
  parameter, a value from a field, a value that the body does not know) is pinned:
  its captures are not known here (`opaque(T)`). A call in the code of the task of a
  value that the body does not know, for example one from a local `Vec` or tuple, can
  be each function parameter in scope there. So the task runs these parameters too
  (`tests/programs/137_task_values.wf`). A pinned task stays on the worker of
  the task that starts it. If that task moved to another worker, the two could share
  a nonportable value from two workers at one time. So a task that starts a pinned
  task in its code is pinned too (`spawns_in(T, U)`). A function can start a pinned
  task for a reason that a caller does not see: a task captures a nonportable value,
  writes through a shared reference, runs a value that the body does not follow,
  or calls such a function (the `pins` part of the signature). A task that calls
  such a function is `opaque`. A task that runs a function parameter does not set
  `pins`: the caller checks the value that it gives there
  (`tests/programs/134_steal_pins.wf`).
- `http.serve` runs its handler as a task for each request. The interpreter lets the
  request task move to another worker only if the checker marks the handler closure
  stealable at the call, or if the handler is a function item that cannot start a
  pinned task (ADR 0010).
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
  captures is W0301 at the call, as for `g(); g()`. A function that only returns the
  closure does not run it. The value that it returns has a `repeats` part of its own
  (`RetFn::repeats`). A call of that value runs it two times in a row, and so does a
  callee or a task that gets that value.
- A call of a function parameter in a closure counts where the closure runs. It is
  part of `repeats` if the closure can run more than once. That is so if the body
  stores the closure or runs it at two nodes. It is so if the closure runs in a loop
  or at a node that can run it again. It is so if it runs in a closure or a clause
  that can run more than once. A closure that runs once does not count. An example is
  the closure of `fn timed(f: fn()) { run(|| f()) }`.
- A callee can get the closure inside a value: a tuple, a struct, an `Option`, a `Vec`
  or a generic struct. Then the closure is a stored value of the caller (ADR 0005).
  The callee can run such a value more than once (`reach_repeats`): a node right after
  the call uses the stored closure again (W0301). `reach_repeats` counts a node in a
  closure only if the closure can run more than once. A stored value is there only
  after the node that stores it, so a node before the store does not run it.
- A node that can run a stored closure more than once starts its tasks again after it
  (W0405). These nodes are:
  - A call of a callee whose body can run a stored value in a loop or in a closure
    that can run more than once. Two nodes where one can follow the other count too
    (the `reach` part).
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
- A signature also has a `task_runs` part: for each function parameter that a task
  or a fork branch of the body runs, whether it can run on another thread (a fork
  branch, or foreign code), whether it can run two times at one time (two tasks, a
  task that starts again while it runs, or a task and a run at a node while it
  runs), and which other function parameters can run while it runs. A parameter that
  the body gives to a callee that runs it as a task gets the part of the callee. At a
  call, the caller checks each function argument there as a task: it starts at new
  nodes after the call node, as a fork task if it can run on another thread (W0401,
  W0403), a second time if it can run two times at one time, and the nodes while it
  runs read what each argument that can run at the same time reads or writes (W0405).
  The part also has the places of the parameters that the body, or another task of
  it, writes and reads while the parameter runs (`TaskRun::writes`, `reads`). A node
  while the argument runs at the call changes and reads them, in the places of the
  arguments. These tasks only stand for the runs of the callee: the interpreter does
  not start them (`tests/programs/133_task_params.wf`,
  `tests/programs/137_task_values.wf`).
- A function value that the body does not know, a closure whose task runs its
  parameter, and foreign code run a function argument in the worst way: on another
  thread, two times at one time, and at the same time as the other function
  arguments. They can also change each place that the reference arguments give while
  it runs. `http.serve` runs its handler two times at one time. A callee can run a
  function value from a field of an argument as a task: each function value that the
  body stores can be that value. A value that a callee makes and gives back inside its
  result, for example a closure in a field of a struct, is one that the body does not
  follow (`caps::MADE`). It can change and read what the result points into.
- A clause of a local handler runs after the handled body is lowered. So a function
  parameter of a clause is the join of the function values that the operations give
  it (`Lower::clause_fns`). A task or a fork branch of the clause that runs the
  parameter has their footprints and captures (W0401, W0403, W0405). A value that a
  callee gives to the operation is a value that the clause does not know. A clause of
  a handler of a caller is code that the body does not know: each operation that
  gives it a function argument runs the argument in the worst way, as a call of a
  value that the body does not know does.
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
  end of each branch: the value has the join of the modes of the branches
  (`weft_facts::join_uniq`, with the verified `modes::join`). W0406 is the rule
  `not_uniq` of the spec: the mode of an argument must be a submode of the mode of
  its parameter (review S5b). Its variable is `@ uniq` only if each of its values is, and not
  `many` if one is. The hidden iterator of a `for` loop is `@ uniq` if its source is,
  so it is not `many` either.
- A reference to a nonportable value is nonportable. A closure keeps its modes in a
  field, an element, a tuple part and an enum payload, also in a place of type `fn()`.
  The local that holds it gets them (ADR 0007).

## Consequences

- What stays imprecise (sound, but it can reject a correct program):
  - A call reads all of its reference arguments. So a task that gives `&w` to a helper
    reads all of `w`, and the parent cannot change another part of `w` while the task
    runs, also when the helper reads or writes only `w.es`
    (`tests/programs/136_call_reads.wf`). A read part in signatures would fix this.
  - A task keeps only the copy variables that its closure captures directly or
    through a captured closure. Another way to reach the cell, for example a closure
    that a callee returns, does not count, so the end of the variable is a free there.
  - A closure whose task runs its parameter, a value that the body does not know, and
    foreign code run a function argument in the worst way: W0403 also when they only
    spawn, and W0405 also when they run it once at a time. A function value from a
    field of an argument that a callee runs as a task can be each value that the body
    stores.
  - A `resume` changes what the handled body changes, also what the function values
    that the body gives to the operation change. So a task that a clause starts
    from such a value before `resume` conflicts with the `resume`, also when the body
    does not touch the places after the operation.
  - A call in a task of a value that the body does not know runs each function
    parameter in scope, also one that the value cannot be.
  - Only an index borrow (`&v[i]`) reads the place that it goes through. A borrow
    through a `Box` (`&b.items`) does not read `b`: a read of the pointer would
    overlap each place inside the box. A later use of the reference is still checked.
  - Foreign code can run each callback on another thread, two times at one time.
    An extern signature cannot state that it runs a callback once at a time
    (`tests/programs/38_callbacks.wf`).
  - The node after the end of a task changes what the task writes. Another task that
    is still active there and reads or writes the same places conflicts again (W0405).
    The first conflict of the two tasks is already an error. A task that the ended
    task starts in a scope outside it is not another task here: the node leaves out
    the places that such a task writes while it can still run, because its own end
    changes them (`nested_join` in `tests/programs/131_task_ends.wf`).
  - A clause that spawns after `resume` starts the task at the operation. So the code
    after the operation counts as running while the task is active, but `resume` runs
    it before the spawn.
  - A call of a closure that returns a closure that spawns starts the task also when
    nothing calls the result, if a callee gets the maker.
  - A call that can run its function argument again uses the argument again after
    each change at the call. The change can be one of the callee, not of the first
    run, and the callee can run the closure before it.
  - `repeats` counts a call in a loop and a call at two nodes, also on two branches
    of an `if`. It counts a call in a closure that runs at two nodes the same way. The
    `reach` part counts two nodes only if one can follow the other.
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
