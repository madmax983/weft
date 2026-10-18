# ADR 0005: Effects, lexical handlers and footprints

Status: accepted. Date: 2026-10-18.

## Decision

- An effect row has `mut(places)`, named effects and silent pass-through of function
  parameters. Lowercase names are aliases (`net` is `Net`). `io` is a bundle.
  Net, Fs, Clock and Blocking imply Async.
- Handlers are lexical. A function gets its capabilities at the call site. A closure
  keeps the capabilities of the place where it was made.
- A perform, and a call that needs a local handler, is a call with the handler's
  footprint: `performs_at` and `footprint` feed `mutates_at`.
- A perform passes its reference arguments to the clause. Each one is a `call_arg` of
  the perform. It pairs with the `call_mut` of the footprint, so a clause that mutates
  what an argument points into is W0312.
- A reference parameter of a handler clause has its own root (kind `Arg`). A reference
  into it is invalid after a mutation through it. A mutation through the parameter is a
  mutation of the argument at each node that gives places to the operation: a perform,
  a call of a closure that performs, and a call that reaches the handler. For the last
  one the clause can get any place inside a reference argument of the call, so the
  whole argument counts as mutated.
- A `resume` runs the handled computation. A change there of a place that the operation
  got is a change of the clause parameter, so a reference into the parameter that the
  clause holds across `resume` is invalid after it.
- Call-site aliasing (W0312): a callee sees its reference parameters as separate places.
  So the caller must not pass overlapping places when the callee (or a handler that the
  callee reaches) mutates one of them. A by-value argument that holds references points
  into them until the call, as a reference argument does: a closure points into what it
  captures, and a tuple or an `Option` into its references. A perform is a call in the
  same way, and the clause can run a function argument of the operation there.
- A parameter of a closure or a clause that holds references (a reference, a tuple or an
  `Option` with one) points into what the call gives.
- Every named effect can abort (the handler can drop the continuation). A linear value
  live across such a node needs `on abort` (W0602).
- `resume` consumes a `once` continuation (W0501). A `multi` operation needs `many` values
  around it (W0503).
- A spawned task or fork branch cannot perform a user effect (W0314): the handler is on
  another task's stack.
- Extern functions in user code default to `blocking`.
- `print` is a debug built-in with no effect.

### Function values

- A function value is a closure of the body, a function item, a function parameter, or
  a value that the body does not know (for example from a struct field). A call of a
  function value does what each value that it can be does:
  - a function item: its signature, with `mut` places in terms of the arguments and
    its named effects at the call site; a named effect can abort;
  - a closure: its summary;
  - a function parameter: the effects of the caller pass through; the call can abort;
  - an unknown value: the call can abort, and it performs the effect row of its type.
- `if`, `match` and a new value of a local join two function values: the result can be
  either. In a loop, a call before the new value also gets it: the body is lowered
  again with the joined value (ADR 0003). Function values also flow through tuples,
  generic results and the result of a closure call.
- A closure belongs to the function that makes it. So the effect row of a function has
  the effects and the mutations of each closure that the body makes, also one that it
  returns or stores and does not call. A signature with a stated row must allow them
  (W0702, W0703), and an inferred row has them.
- A function that returns a function value has a `ret` part in its signature: what a
  call of the result does, in the places of the parameters. A call of the result does
  that. The body always infers this part, also when the signature states the row. It
  includes the places that the result lends: to a function parameter of the function,
  or to a value that the function does not know.
- A call of a function value returns a value that does what the callee states about
  it: a closure its returned values, a function item its `ret` part. A value that the
  body does not know returns a value that lends each reference argument of the call
  and can run each function argument of the call.
- A closure that returns a function value can also do what the returned value does. So
  a callee that calls the result of its function parameter is seen at the call that
  gives the closure.
- A function value that the body stores where it does not follow it (a struct field,
  an enum payload, a container, a by-value argument that is not a function, or a
  callee that stores its function parameter) can run later. A parameter of a type
  parameter (for example `Vec.push(x: T)`) keeps a function value: the callee cannot
  call it. A stored value runs at each node that can reach it: a call of an unknown
  function value, and a call that gets a value that can hold a function if the callee
  can run a stored value. This applies after the whole body, so it also covers a node
  that comes before the store in a loop. A node in a closure passes the value on to
  each node where the closure runs. There the value uses what it captures (W0301 if a
  captured place changed after the store), and it points into its captures as a closure
  argument does (W0312). An operation of a handler that the stored value performs runs
  its clause at the node, as at a perform.
- A signature has a `stores` part: the function parameters that the body stores. It has
  a `reach` part: whether the body can run a stored value, and the places that it gives
  to it, by argument position. A caller gives a stored value these places. A function
  with no body can store each function argument, and can run a stored value with any
  place inside its reference arguments.
- A call of a function parameter, or of a function value that the body does not know,
  can resume a `multi` continuation more than once if a `multi` operation can reach the
  value: the type states a row with a `multi` effect, or it states no row and the
  program has a `multi` operation (W0503).

### Mutation through the parameters of a function value

- A reference parameter of a closure has its own root (kind `Arg`). A mutation through
  it is not an effect of the function that makes the closure. It is a mutation of what
  the call gives to the parameter:
  - A direct call of the closure gives its arguments: the places of the parameters
    become the places of the arguments.
  - A higher-order call gives what the callee lends to that function parameter. The
    signature has a `lent` part: the places that the body gives to each function
    parameter, by argument position. The body always infers it, also when the signature
    states the row. A callee with no inferred body (`extern`, the prelude) can give any
    place inside its reference arguments: then each reference argument counts as
    mutated.
- Inside a body, a call of a function parameter, or of a function value that the body
  does not know, gives places to a function that can mutate through them
  (`lends_mut(P, M)`). The call invalidates references and conflicts with tasks as a
  mutation of `M` does. The signature does not state it: the caller sees the mutation
  where it gives the closure. An operation of a handler outside the function lends its
  reference arguments in the same way.
- A closure or a handler clause that lends a place lends it again at each node where it
  runs: a call of the closure, and a perform, a call or a `resume` that runs the clause.
  A place below a parameter of the closure or the clause becomes the place that the node
  gives. A task that lends a place can write it (W0405).

### Dependency authority

- `weft deps` checks each function of a dependency, also a private one: the project can
  call it. A function needs its stated effects and the effects that its body infers,
  with the closures that it makes and returns.

## Consequences

- Effect polymorphism needs no syntax.
- What stays imprecise (sound, but it can reject a correct program):
  - A callee with no inferred body: each reference argument counts as mutated by a
    closure argument that mutates through its parameters.
  - A place that the callee lends below a parameter of its own closure has no name in
    the signature. It counts as any place inside the reference arguments.
  - `lends_mut` holds at each call of a function parameter, also when no caller passes a
    closure that mutates.
  - The `multi` test for a function parameter with no effect row looks at the whole
    program, not at the callers.
  - The effects of a closure count in its maker also when nothing calls the closure. The
    effects of a returned closure count at the call of the maker and again at a call of
    the result. A call of a closure that returns a function value does what the result
    does, also when nothing calls the result.
  - A join applies the effects of every value that it can be.
  - A stored function value runs at each node that can reach it, also at a node before
    the store and at a call that does not run it.
  - A function argument of an operation runs at the perform, with any place inside the
    reference arguments of the operation, also when the clause does not call it.
- What stays open (not checked):
  - A function value inside a returned tuple or struct, or a closure that a callee
    makes and stores in a place of the caller: the caller does not see what a later
    call of it does. Its effects and mutations still count in the row of its maker,
    at the call of the maker.
  - A stored function value that runs inside a handler clause: the operation that runs
    the clause does not get it.
  - W0402 inside a higher-order function: a callback that gets a place of a `@ shared`
    parameter can mutate it. The caller sees the mutation on its own place only.
