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
- W0312 is stronger than the design. The design lets one task mutate through aliases
  (group borrowing). But with `fn attack(a: &Entity, b: &Entity) / mut(a, b)`, the call
  `attack(x, y)` with `x` and `y` both in `world.entities[]` gets W0312. The workaround
  states the shared place with `in`, so the callee knows that the two can alias:

  ```weft
  fn attack(w: &World, a: &Entity in w.entities[], b: &Entity in w.entities[]) / mut(a, b) {
      a.hp -= 1
      b.hp -= 1
  }
  ```

  The caller then passes `attack(world, x, y)`, and the check accepts it.
  `tests/programs/34_alias_in_one_task.wf` has both forms.
- Effect inference iterates over the call graph to a fixpoint (`weft_sema::infer`).
  A worklist lowers callees before callers. When the signature of a function changes,
  only the functions whose bodies name it are lowered again. A last lowering of every
  body finds a signature that a body reads without its name. Each new row is joined
  with the old row, so a row only grows. A row is in a finite lattice: the effects of
  the program, the parameters, and the `mut` places of at most 8 steps under the
  parameters and the `rc` groups. So the inference always reaches a fixpoint for the
  rows. The bound for one row is the height of its lattice
  (`weft_sema::infer::growth_limit`). It depends on the number of effects, parameters
  and types, and on the number of different steps in the places of the program. A row
  that grows past the bound shows a checker bug: the inference stops, and each
  function whose signature can still change gets W0706, an error.
- The other parts of a signature (`lent`, `ret`, `stores`, `reach`, `multi` and `tasks`,
  see below and ADR 0006) are not part of the row. The body always infers them, also when the signature
  states the row, and each new lowering replaces them. They do not only grow: a part
  that is not known yet can be larger than its final value. So the parts of one
  function can change at most 32 times and two more times for each function
  (`weft_sema::infer::parts_limit`). After that, the inference keeps the last parts of
  that function, and its callers use them. Its row can still grow. A function whose
  parts still change at the end gets W0704, an error. A program can get W0704: a
  recursive function that gives one more place to a function parameter on each call
  can need more changes than the bound. The checker never uses effects that can be
  incomplete without an error.
- Every named effect can abort (the handler can drop the continuation). A linear value
  live across such a node needs `on abort` (W0602).
- `resume` consumes a `once` continuation (W0501). A `multi` operation needs `many` values
  around it (W0503).
- The abort rule and the multi rule apply at each suspension point (rule 1 of
  `proofs/effects`): an operation, a call that reaches a handler, a node that runs a
  clause, and a `resume`. A node that runs a clause can resume more than once if a
  clause of the handler can (`clause_multi`). A `resume` runs the handled computation
  and, at its operations, the clauses again. So it can resume more than once if the body
  (`body_multi`) or a clause can. A `once` continuation is a `once` value (rule 2): a
  clause cannot hold one across a `multi` operation, also not across a call that can
  perform one.
- A clause runs in the environment of its `handle` (rule 6): its operations go to the
  handlers outside the `handle`. The value of a clause is the value of the `handle`, so
  a function value or a reference in it joins the value of the body. A `resume` gives its
  argument to the handled computation, so the argument cannot hold a capability of a
  handler inside the clause (W0313).
- A handler intercepts its effect if a clause performs the effect again, through a
  handler outside it (`clause_performs`, `forwards`). In a library, a handler of a
  standard effect that never forwards is a root handler (W0801), also when the function
  states the effect. The root handlers of `sim.run` get W0802 instead.
- A spawned task or fork branch cannot perform a user effect (W0314): the handler is on
  another task's stack.
- A capability lives only while its handled body runs (rule (d) of `proofs/effects`). A
  function value that performs through it cannot leave the body (W0313): not as the
  value of the body (also inside a tuple, a struct, a container or another closure), not
  through a local outside the body, and not to a place or code that can keep it: a
  field or an element behind a reference, a callee that stores it or has no body, a
  function value that the body does not know, a closure that stores its parameter, and
  an operation of a handler outside the body. A struct or a container that a local of
  the body owns can hold the value: it goes out of scope with the body.
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
  captured place changed after the store), also at a call of a value that comes back
  from the store with the summary of its type, and it points into its captures as a closure
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
  program has a `multi` operation (W0503). A function that makes such a call of a value
  that it does not know has a `multi` part in its signature: a call of the function can
  resume more than once too. The body always infers this part.

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
  reference arguments in the same way. The code that gets the places sees them as
  separate places, so a lent place pairs with the other arguments of the call as a
  mutation of the callee does (`call_mut`, W0312).
- A closure or a handler clause can give a local outside it a place below its own
  parameter (`keep = x`). At each node where it runs, the local then points into the
  place that the node gives.
- A closure or a handler clause that lends a place lends it again at each node where it
  runs: a call of the closure, and a perform, a call or a `resume` that runs the clause.
  A place below a parameter of the closure or the clause becomes the place that the node
  gives. A task that lends a place can write it (W0405).

### Dependency authority

- The project can name only the `pub` functions of a dependency, and a dependency only
  the `pub` functions of another unit (W0101). `weft deps` checks each function of a
  dependency, also a private one: a public function or a returned closure can run it. A
  function needs its stated effects and the effects that its body infers, with the
  closures that it makes and returns.
- Authority names standard effects only. A user effect of a dependency needs a handler
  of the caller, not authority.
- Each effect has an identity in the facts and the signatures: a standard effect keeps
  its name, and a user effect gets its module path and its name (`main.Log`,
  `json.Log`). So a user effect with the name of a standard effect is a different
  effect: for W0702, W0803, W0801, W0314 and the authority check. Diagnostics show the
  written name (`effects::shown`, `effects::in_signature`). In a module that defines
  `Log`, `Log` names that effect and the alias `log` names the standard one.

## Consequences

- Effect polymorphism needs no syntax.
- What stays imprecise (sound, but it can reject a correct program):
  - A callee with no inferred body: each reference argument counts as mutated by a
    closure argument that mutates through its parameters.
  - A place that the callee lends below a parameter of its own closure has no name in
    the signature. It counts as any place inside the reference arguments.
  - `lends_mut` holds at each call of a function parameter, also when no caller passes a
    closure that mutates. So overlapping arguments of such a call are W0312, also when
    the callback only reads them.
  - A closure argument points into each place of each reference that it captures, not
    only into the parts that it reads. A closure that captures `world` and reads
    `world.score` overlaps a mutation of `world.entities` (W0312), as `world` given twice
    does.
  - The `multi` test for a function parameter with no effect row looks at the whole
    program, not at the callers.
  - The effects of a closure count in its maker also when nothing calls the closure. The
    effects of a returned closure count at the call of the maker and again at a call of
    the result. A call of a closure that returns a function value does what the result
    does, also when nothing calls the result.
  - A join applies the effects of every value that it can be.
  - A stored function value runs at each node that can reach it, also at a node before
    the store and at a call that does not run it. It uses its captures there.
  - The `multi` part of a signature counts each call of an unknown function value with
    no effect row in a program that has a `multi` operation.
  - A function argument of an operation runs at the perform, with any place inside the
    reference arguments of the operation, also when the clause does not call it.
  - W0313 counts each function value given to code that can keep it, also when that
    code only calls it, and each part of a local of the body that can hold a function.
  - A `resume` can resume more than once if a clause of its handler can, also when the
    handled computation does not perform the operation again.
- What stays open (not checked):
  - A function value inside a returned tuple or struct, or a closure that a callee
    makes and stores in a place of the caller: the caller does not see what a later
    call of it does. Its effects and mutations still count in the row of its maker,
    at the call of the maker.
  - A stored function value that runs inside a handler clause: the operation that runs
    the clause does not get it.
  - W0313 does not follow a callee that copies a function value out of a reference
    argument into another place, or a clause of a handler inside the body that keeps
    its function parameter.
  - W0402 inside a higher-order function: a callback that gets a place of a `@ shared`
    parameter can mutate it. The caller sees the mutation on its own place only.
  - A reference inside a payload that a `match` binds by value, and a parameter of a
    function item that holds a reference inside an `Option` or a tuple, have no places
    (the RT3 family).
