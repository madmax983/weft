# ADR 0007: Linear and immovable types

Status: accepted. Date: 2026-10-18.

## Decision

- Values are affine. Plain data (integers, references, and structs of plain data) is
  copied. `String` is immutable and copied.
- A `linear` value must be consumed on every normal path: moved into a call, or
  destructured with `let S(a, b) = s` (W0601).
- `on abort = f` names the function that unwinding runs. The unwinder runs it with the
  root handlers only. So its effects, also inferred ones, can name only the standard
  effects that the root handlers serve: not `fail` (the failure does not reach the
  handlers of the code that aborts), no user effect, and with no runtime none (W0118).
  It can change only the value that it gets: not an `rc` group, and not a place that a
  reference in the value points to (W0118). The node that aborts does not state such a
  change. It cannot raise a failure of the runtime either: a `join` of a failed task,
  a scope or a `fork` with a failed child, and a read of a file can fail with no `fail`
  in the row. The signature has a `raises` part for this. A callee and a closure that
  the function makes count, but not a node that a `Fail` handler of the function
  gets. It cannot call a function value that it does not know, for example one from
  a field of its value: the maker of the value states what it does, not the function
  (W0118). The effects proof models `on abort` as atomic: it cannot perform or fail.
  This rule mirrors that assumption. A standard effect that a root handler serves
  (`clock`, `log`) does not suspend the unwinder into a handler of the program.
- The unwinder gives the `on abort` function each instance of the type, and no call
  of the facts checks it there (review round 3). So W0118 also checks these:
  - The parameter type is the type with the type parameters of the function in
    order, as for a method of `impl<T> G<T>`: `fn undo<T>(g: G<T>)` for
    `linear struct G<T>`. For a type with no type parameters, it is the type, and
    the function has no type parameters. A fixed type argument (`G<u64>`) is an
    error: the unwinder can give it a `G<Tx>` (F3-4).
  - A type parameter in the `drops` or the `holds` part of the function is an
    error. The unwinder can give it a linear type argument, and the value of that
    type then goes away (F3-3).
  - A result that can hold a linear value is an error: a linear type, a type
    parameter or a function value. The unwinder drops the result.
  - A change below a reference that the value holds is a change outside the value.
    A by-value parameter that holds references points into a parameter root (ADR
    0003). So the row shows a change through such a reference as a change of the
    parameter, and cannot show it apart from a change of the value itself. If the
    parameter type holds a reference, each change of the parameter in the row is
    outside (F3-1). An inferred row has no change of the value itself: a change of
    an owned by-value parameter is local.
- `struct S: !Move` keeps its address. Moving a named value is an error (W0604). A
  function can return a struct literal: it is built in place.
- Only a `!Move` struct may hold a reference field, and only into `self` (W0605).
- A property of a type holds if a part has it: a field, a tuple part, an enum payload,
  an element and a type argument. `linear`, `nonportable` and `!Move` work so at any
  depth. A reference to a nonportable value is nonportable too. Another thread could
  use the value through it (W0401).
- A table for each type definition (`weft_sema::props`) gives the parts that pass a
  property on. It is a least fixpoint over the definitions. A type that holds itself,
  such as `enum List { Cons(u64, List), Nil }`, is not plain data.
- The flags of a variable come from the type that the whole body infers. So
  `let v = Vec.new()` and a later `v.push(tx)` make `v` linear. Then `let _ = v.pop()`
  before the push drops a linear value. A move of a value whose type is not known yet
  stays a move until `finish` knows the type. If the value is plain data, it is a
  copy, and the move goes away.
- A value has `on abort` for W0602 if each linear part has it. A type around the part
  can have it too: that `on abort` finishes its parts. A tuple of a `Tx` with
  `on abort` and a `Lock` without it has none.
- The `on abort` of a task handle only cancels the task, and a cancel does not finish
  the result of a task that is done. So `Task<T>` has `on abort` for W0602 only if `T`
  has no linear part or `T` has `on abort`: the property passes from `T` through
  `Task` (`props.rs`, review round 3, F3-6). A live handle of a `Task<Tx>` across an
  abort is W0602 if `Tx` has no `on abort`, as a `Tx` is. The unwinder runs the
  `on abort` of the result of a task that is done (ADR 0010).
- A task closure or a fork branch that takes a linear value by value needs `on abort`
  for it: a scope can cancel the task before it runs (W0602 at the spawn or the
  `fork`, ADR 0006, F3-8). The rule asks that the closure of the task captures the
  linear variable. So a block or a closure that consumes a linear value and then
  starts a task in a scope outside it is clean (review of R3x). The unwinder of the
  task finishes the value (ADR 0010).
- A `fork` gives no value when a branch fails or the `fork` aborts. The unwinder runs
  `on abort` for the values of the branches that are done (ADR 0010).
- A closure that moves a linear value is linear: it must run once on every normal path
  (W0601). A callee that gets it can drop it. So a function argument of this kind is
  W0601, except for `with_timeout`, which runs its block once.
- A closure that moves a value that is not plain data runs only once. A second call
  is W0502. A callee that can call its argument more than once cannot get it. An
  operation of a handler cannot get it either: a clause can call it more than once.
- A place of plain data, such as a field of type `fn()` or an element of a
  `Vec<fn()>`, cannot hold a `once` closure. A copy of the place could call it again
  (W0502). A closure that calls a `once` closure, or resumes a `once` continuation,
  moves it, so it is `once` too.
- A closure that goes to a parameter of a type parameter moves there, as another value
  does. It keeps its modes, so `gen_keep(f)` gives back a closure with the modes of
  `f`. A place of the declared type gets the checks above, for example `Vec<fn()>` in
  `v.push(f)`.
- The modes of a closure stay with it in a field, an element, a tuple part and an
  enum payload. This is also so in a place of type `fn()`. A local that holds it is
  nonportable if the closure is (W0401). It is not `many` if the closure is not
  (W0503).
- A closure that a callee returns can hold what an argument points to. So a call
  result that can hold a function value is nonportable if an argument is. It is not
  `many` if an argument is not.
- The value of a branch of an `if` or a `match` moves into the value of the
  expression, as in the interpreter. The value of a closure body moves into the
  result of the closure, as the value of a function body does.
- A linear value cannot go away silently:
  - A pattern `_` drops its part: in a `let`, in a temporary that a `match` takes, and
    in an arm that binds a part by value. An arm can match a value with no linear
    part, such as `None`. Then it consumes its local scrutinee.
  - Some operations only read a temporary: `print`, a comparison, a receiver that a
    method borrows, a field read and a borrow. A linear temporary of this kind goes
    away at the end of its statement.
  - A new value of a place drops the old value. `p.tx = v` on a live linear local `p`
    is `overwrites(V, P)` in the spec (W0601). Behind a reference the old value is
    always there, so a new value there is W0601.
  - A new value inside a closure or a handler clause overwrites a captured linear
    value. The value is live where the closure or the clause starts.
  - A place whose type is not linear cannot keep a linear value. A field of type
    `fn()` or a `Vec<fn()>` cannot hold a linear closure.
- A prelude function can drop values of a type parameter: `Vec.clear` drops each
  element, `Task.detach` drops the result of the task, and `Response.json` drops its
  argument. Their signatures have the type parameter in `drops`, so a call with a
  linear type argument is W0601. A generic function that calls one with its own type
  parameter has that parameter in its `drops` too. When the diagnostic cannot name the
  argument, it names the callee and the type, for example "`clear` drops a value of
  the linear type `Tx`". It does so for a generic function item used as a value too.
- A generic function does not know that a value of a type parameter is linear. So its
  body treats such a value as linear where a linear value can go away:
  - in a pattern `_`;
  - in a holder that goes out of scope: a local, a tuple, an `Option`, a `Vec` or a
    closure;
  - under a new value;
  - in a callee that can drop it.

  These values have no `linear` flag in the facts. `finish` follows them with the
  rules of W0601. Their type parameters are the `drops` part of the signature. A call
  that gives a linear type to a type parameter in `drops` drops a value of it (W0601).
  The check uses the inferred type argument.
- A generic function can hold a value of a type parameter at a node that can abort or
  resume more than once. `finish` follows these values as the rules of W0602 and W0503
  do: from a new value to a move. Their type parameters are the `holds` part of the
  signature. A call can give a linear type to a type parameter in `holds`. Then it has
  a hidden variable of that type. The variable gets a value before the call node and
  moves after it. So the rules see a linear value across the call. W0602 applies if
  the call can abort and the type has no `on abort`. W0503 applies if the call can
  resume more than once. In a generic caller the variable is linear only because a
  type parameter can be. So the caller gets the type parameter in its own `holds`. A
  value that is not `many`, such as a `once` closure, gets the hidden variable too
  (W0503).
- A generic function item can be a value, for example an argument of a parameter of
  type `fn(Lock) -> Lock / fail`. Code that the body does not follow can call it. So
  the value gets the checks of a call where the body makes it. A type argument in
  `holds` gets a hidden variable across a node of its own. That node can abort or
  resume more than once, as the item can (W0602, W0503). A type argument in `drops`
  gets a value that goes away there (W0601). The node is in a part of the graph of
  its own, so no other value is live there.
- A foreign generic function (`extern fn` in user code) has each type parameter in
  `drops`, and in `holds` if it can abort. It has no body to show what it does.
- A linear value can be on its way to a call, a tuple, a struct literal, a constructor
  or an array. It is live while the later operands run. A hidden variable holds it
  from its operand to the node that takes it. An abort in a later operand loses the
  value. Its type must have `on abort` (W0602). A `return`, a `break` or a `continue`
  in a later operand leaves the value: the hidden variable goes out of scope at the
  jump (W0601). A jump that stays inside the later operand does not leave it.
- A new value with no linear part gives a linear variable nothing to consume. An
  example is a variant with no payload (`None`). The spec has `empty_at(V, P)` for
  it. `live_linear` does not start there. A new value of a part (`overwrites`) starts
  it, because the part can now hold a linear value. A `Vec.new()` result is not such
  a value: `push` can add a linear value to it without a new value of the variable.
  A clause gives the value of a `handle` when it does not resume, or after a
  `resume`. So the value of a `handle` has no linear part only if the value of the
  body and the value of each clause have none. The value of the body moves into the
  value of the `handle` then, as the value of a branch of an `if` does.
- A move of a part of a linear value (`rollback(t.0)`, `let x = t.0`, a closure that
  moves `t.0`) leaves the other parts in the value (review round 3, R3RT1). Sema gives
  `rest_linear(V, P)` at the move if another part of the value can be linear: a part
  on another branch of the type, or another element of a `Vec` or an array. Then
  `live_linear` goes on through the move, and so does `abort_unhandled`: the end of the
  value is W0601, and an abort after the move is W0602. A later use of the value is
  still a use after a move (W0302, ADR 0003), so the program must destructure the
  value to consume each part (`let (a, b) = t`). The diagnostic says so. A part move
  that leaves no linear part ends the value, as before. The shell of a `linear` struct
  or enum is a linear part too: a move of a field that is not linear leaves it. A
  handler clause that moves a part of a capture leaves the rest at each node that runs
  the clause (`Summary::rest_captures`). The drop check of a generic body
  (`dropped_params`, `held_params`) does not end a value of a type parameter at such a
  move, so a linear argument is W0601 at the call (review of R3a).
- On an abort path (ADR 0005) the unwinder finishes each value of the handled body:
  `unwound_at(V, P)` in the spec. `live_linear` stops there, and the owner frees its
  memory. The node that aborts needs `on abort` for each live linear value (W0602).
  A linear value outside the body stays live. An operation of a local handler aborts
  only the values of its handled body, so W0602 spares a value outside the body there
  (`spared_at(V, P)`), and W0503 does too. This holds if no clause of the handler
  performs through a handler outside its `handle`, and if the operation is not in a
  closure or a clause inside the body (ADR 0005).
- A `multi` resume copies the values of the handled body (ADR 0005). A value that a
  copy cannot keep is not `many`: a `!Move` value (`once_var(V) :- immovable(V)` in
  the spec), a task handle, a scope, and a value of an extern type that is not plain
  data, also as a part of another value. A `!Move` value in a `Box` or a `Vec` moves
  with the copy of the buffer. A reference that is live across the node into a
  `!Move` value, or a reference argument of the node into it, uses the value there
  (`live_across_multi` in the spec): in the copy it points into the value at its new
  address. A copy of a `Vec` or a `Box` copies its buffer, and the copies share an
  `rc` object, so these do not count. A handle to an `rc` object that can hold a
  function value or a reference counts: the object still points into the locals of
  the run before. Another owned
  value is copied: this is the Phase 1 meaning of a `multi` resume. A native runtime
  pays for the copy at each resume, and the effects proof (E5) does not cover it
  (ADR 0005).
- `!Move` passes through the parts that hold a value inline. A pointer such as `Box`
  or `Rc` does not move its target, so it does not pass `!Move` on. A prelude type
  with no elements, such as `Weak<T>`, is a pointer or a handle too.
- A call builds a `!Move` value in place for a parameter of its own type. It builds the
  argument of `Box.new` and `Rc.new` in place too. A callee with another parameter of
  a type parameter can move the value, as `Vec.push` does when its buffer grows
  (W0604).
- A self-reference field gets only a reference into its own struct (W0605). A struct
  literal cannot give it one: the struct has no place yet. The spec checks both
  (`ref_outside`, with `inside_stated`, review S5b): a struct literal states no place
  of the body for the field.
- A value that no place held before is built in place: a literal, a call result and a
  by-value parameter. Its place fields have no value, also in a part, in an enum
  payload and behind a `Box`. A read or a borrow of such a field, or of the whole
  struct, before the body gives the field a value is W0304.
  - The search for the place fields of a type walks full types (a definition with
    its type arguments) and keeps the paths of each one in a table
    (`Lower::place_paths`, review round 3, Q3-1, Q3-4). A type whose definitions
    cannot hold a place field is not walked (`TypeProps::may_hold_place_field`). A
    second use of one generic definition with other arguments is another type, so
    `Wrap<Wrap<Frame>>`, `Box<Hold>` with a `Box<Frame>` in it and an `Option` in an
    `Option` get their place fields too.
  - A recursive type has a place field at each depth: one literal or one callee can
    build two nodes, and the body gives a value only to the fields that it names.
    So the search cannot stop with no path. It stops at a struct or an enum whose
    cycle of definitions (`TypeProps::cycle`) is already on the way, and gives a
    path that stands for each place field below it. A read or a borrow at, above or
    below that place uses its hidden variable (W0304). A new value of the place, or
    of a place above it, that no place held before gives the variable a value, and
    the place fields of the new value get hidden variables again. `None` has none.
    Each infinite search meets such a struct or enum, also for a type that grows at
    each depth (`Nest<T> { next: Option<Box<Nest<Box<T>>>> }`), so the search stops.
    The result for a type depends only on the type and the cycles on the way, so
    the table keeps it, and each type is walked once for each set of cycles. A type
    with more than 64 paths gets one path for each part that holds place fields,
    which stands for the place fields below it. So the cost and the number of
    hidden variables grow with the number of types, not with the number of paths
    (`scale.rs`, `place_fields_of_a_deep_type_are_found_in_linear_work`).
  - An assignment of a new value to a place gives the place fields of the new value
    hidden variables with no value, as a `let` does. A `let` or an assignment that
    moves a value out of a place does not follow its place fields: each of them
    must have a value at the move (W0304). A `!Move` value cannot move (W0604), so
    this counts only for a place field behind a `Box`.
  - A closure reads the places that its body reads. It reads them where it is made.
  - A local that a `let` declares with no value is the same: a closure, a handler
    clause or a task uses its captures where it is made (W0304). So a local cannot
    get its first value in one of them. Rust rejects the closure form too.
  - `print` and a string interpolation read the whole value.
  - A move of the whole value is not a read. It is W0604.

## Consequences

- What stays imprecise (sound, but it can reject a correct program):
  - A linear closure given to a function parameter is W0601, also when the callee calls
    it once on every path.
  - `drops` names type parameters, not values. A call reports each type parameter in
    `drops` that gets a linear type. It reports it at the first argument that names
    the type parameter. It names that argument only if no other parameter has the
    type.
  - A new value in a closure counts the captured value as live at the closure start,
    also when the closure runs after the value moves.
  - A new value of a local that holds a linear type overwrites its old value. This is
    also so when the old value is an empty `Vec`. After `None` it is not.
  - A call of a generic callee in `holds` holds a linear value across the call node.
    This is also so when the callee holds the value at another node than the one that
    can abort.
  - A `Vec` of linear values is linear, and nothing consumes it. It is W0601 at its
    end, also when each element is popped and consumed. The prelude has no consumer
    for it: `pop` leaves the `Vec`, and a `for` loop gives references. A consumer
    could take the `Vec` by value, such as `drain(self, f: fn(T))`. That is a change
    of the prelude and of the interpreter, not of the checker. The checker keeps the
    error. `tests/programs/88_empty_values.wf` has the cases.
  - A local can hold a generic function item, and a call of the local can run it.
    Then the checks of `holds` and `drops` apply twice: at the value and at the call.
  - A borrow of a struct with a place field that has no value is W0304, also when the
    callee gives the field a value first. A `match` on such a value reads it too.
  - A local with no value that only a closure, a clause or a task gives a value is
    W0304 where the closure is made, and at each use after it, also after the closure
    ran. `tests/programs/112_unset_capture.wf` has the cases.
  - A call result that can hold a function value gets the modes of the arguments,
    also when the callee does not keep them.
  - A closure is not plain data. A branch value, a variable and an argument of a type
    parameter move it, also when it moves nothing that it captures.
  - The length of a `Vec` is not known. A move of an element of a `Vec` of linear
    values leaves the other elements, also when there are none
    (`tests/programs/153_partial_linear.wf`).
  - The search for place fields follows the type, not the value. A read or a borrow
    of a part of a recursive type is W0304 until the body gives the part a new
    value, also if the literal gave it `None`. A type with more than 64 paths to
    place fields has one hidden variable for each part, and the body must give the
    part a new value. A `let` or an assignment that moves a value before the body
    gives its place fields a value is W0304, also if the body gives them a value
    through the new holder later (`tests/programs/154_unset_nested.wf`).
  - An `on abort` function with a type parameter in `drops` or `holds` is W0118,
    also when no instance of the type has a linear type argument. A result of a
    type parameter or of a function type is W0118 too, also when it cannot be
    linear (`tests/programs/160_on_abort_checks.wf`).
  - An `on abort` function whose parameter type holds a reference cannot state a
    change of its own value: the row cannot show it apart from a change through
    the reference (W0118).
  - A task closure or a fork branch that takes a linear value by value is W0602 if the
    type of the value has no `on abort`, also when no scope can cancel the task
    before it runs (`tests/programs/161_task_captures.wf`).
  - A block or a closure that moves a linear value into a task that its code starts
    gets W0602 also where it runs. A block that takes a linear value and starts a
    task that reads another linear value through a reference gets W0602 where it
    runs too (ADR 0006, `tests/programs/163_task_starts.wf`).
- What stays open (not checked), until the core IR replaces the fact generation:
  - A spawn whose handle is not kept (a spawn in statement position, or `let _ =`)
    gives its handle to the scope. The scope joins the task and drops the result.
    W0601 does not see it. The rule: such a spawn drops `T`. That is W0601 at the
    spawn when `T` is linear, as for `detach`. In a generic body, `T` goes into
    `drops`. The handle that the scope gets is live across the end of the scope,
    which can abort. So a linear `T` with no `on abort` is also W0602 at the
    scope, as for a handle that the body keeps and does not use. The checker gives
    both today for a handle that a pattern `_` drops (F3-6, O3-4, I3-1,
    `tests/ir_targets/f3_6_task_results.wf`).
  - A `fork` can abort while the value of one branch is done: the other branch
    fails, or a deadline or a cancel unwinds the owner. A cancel can cut a `fork`
    whose branches cannot fail too, for example when a sibling task of an outer
    scope fails. The rule: a `fork` that can abort needs `on abort` for each linear
    type of a branch value (W0602 at the `fork`). W0602 does not ask for it yet.
    The unwinder cannot finish such a value, and the run stops with a fault (F3-6,
    `tests/ir_targets/f3_6_task_results.wf`).
  - A generic body that holds a handle of a `Task<T>` across a node that can abort
    does not put `T` in `holds`. So a caller that gives `T` a linear type with no
    `on abort` gets no W0602, and the unwinder stops with a fault where it finds the
    result of the task. Example: `fn run_bg<T>(mk: fn() -> T, k: fn(T))` spawns `mk`,
    performs an operation whose clause does not resume, and then joins; the caller
    `run_bg(begin, commit)` needs W0602.
  - A generic body whose task closure or fork branch takes a value of a type
    parameter by value does not put the type parameter in `holds`, and the spawn or
    the `fork` gets no W0602: the value is not `linear` in the body (review of R3x).
    So a caller that gives the type parameter a linear type with no `on abort` gets
    no W0602. If a sibling fails before the task runs, the unwinder stops with a
    fault. Examples: `fn relay<T>(make: fn() -> T, sink: fn(T))` with
    `let y = make(); s.spawn(|| sink(y))` next to a failing sibling, and
    `fn relay<T>(x: T, sink: fn(T))` with `fork(|| sink(x), || boom())`. Their
    callers with `Tx` for `T` need W0602. The core IR puts the type parameters of the
    values that move into a task at a spawn or a `fork` into `holds`.
  - The `fork` shape of this list (a branch value of a linear type with no
    `on abort`) stops the stock interpreter with a fault too, not only the oracle:
    the unwinder finishes the values of the branches that are done, and a value with
    no `on abort` is a fault (ADR 0010). Before review round 3 these programs ran to
    the end and leaked the value.
