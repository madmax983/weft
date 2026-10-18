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
- Call-site aliasing (W0312): a callee sees its reference parameters as separate places.
  So the caller must not pass overlapping places when the callee (or a handler that the
  callee reaches) mutates one of them. A closure argument points into what it captures
  until the call, as a reference argument does.
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
  either. Function values also flow through tuples, generic results and the result of
  a closure call.
- A closure belongs to the function that makes it. So the effect row of a function has
  the effects and the mutations of each closure that the body makes, also one that it
  returns or stores and does not call. A signature with a stated row must allow them
  (W0702, W0703), and an inferred row has them.
- A function that returns a function value has a `ret` part in its signature: what a
  call of the result does, in the places of the parameters. A call of the result does
  that. The body always infers this part, also when the signature states the row.
- A function value that the body stores where it does not follow it (a struct field,
  an enum payload, a container, a by-value argument that is not a function, or a
  callee that stores its function parameter) can run later. It runs at each node that
  can reach it: a call of an unknown function value, and a call that gets a value that
  can hold a function. This applies after the whole body, so it also covers a node
  that comes before the store in a loop. A node in a closure passes the value on to
  each node where the closure runs. A signature has a `stores` part: the function
  parameters that the body stores. A function with no body can store each function
  argument.
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
    the result.
  - A join applies the effects of every value that it can be.
  - A stored function value runs at each node that can reach it, also at a node before
    the store and at a call that does not run it.
- What stays open (not checked):
  - A function value inside a returned tuple or struct, or a closure that a callee
    makes and stores in a place of the caller: the caller does not see what a later
    call of it does. Its effects and mutations still count in the row of its maker,
    at the call of the maker.
  - A stored function value that runs inside a handler clause: the operation that runs
    the clause does not get it.
  - W0402 inside a higher-order function: a callback that gets a place of a `@ shared`
    parameter can mutate it. The caller sees the mutation on its own place only.
