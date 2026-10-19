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
  clause holds across `resume` is invalid after it. A change at or below the argument
  place keeps its steps below the parameter. A change above the argument place, or one
  that can alias it, can change any place below the parameter (`x..`). If such a change
  invalidates a reference to the argument place in the caller, the `resume` can also
  free what the parameter points to (`releases_at(resume, x)`). A wildcard place `x..`
  stands for places at or below `x` only, so it never stands for a change above `x`
  (ADR 0003, rule 4). When an operation runs in a callee, the parameter can be anywhere
  inside the argument of the callee, so each change at or below that argument frees it.
  The handled computation can also move a local from outside the `handle`, or a part of
  it. Then each `resume` frees that place, so a reference of the clause into it, or a
  clause parameter that points into it, is invalid after the `resume`.
- A clause of a handler of an effect with a `multi` operation can resume the handled
  computation more than once. The code after a node that runs the clause then runs
  again. The locals from outside the handled body keep the values of the run before.
  The locals of the body get a copy of their values at that node: the interpreter
  copies the frames of the continuation, and a reference into a copied local points
  into the copy. So the lowering lowers the handled body as a loop (ADR 0003) until
  the values of the locals from outside it are stable. The end of the body gets a
  path back to the nodes after each node of the body that runs a clause of the
  handler, through a node that gives each local of the body its copy again
  (`rebound_at`, with `empty_at`: the copy has the state that the path from the
  operation gives, so no linear value starts there). A local of the body that can
  point into a place of another value keeps its state there. So a reference that the
  first run invalidates is invalid in the second run too, and a value from outside
  the body that the first run moves is moved there. If each clause names `resume` at
  most once, and not in a loop, a closure or a clause of another handler, the body
  runs at most once after each operation, and it is lowered once.
- A clause that can end with no `resume` ends the handled body at the node that runs
  it. Each node of the body that can run a clause of the handler gets an edge to the
  end of the `handle`. Such a node can be a perform, or a call of a closure or a
  function. It can also run a stored function value, or a clause of a handler inside
  the body. The edge goes through an abort node. There the unwinder finishes the
  values of the body (`unwound_at` in the spec). It frees the owners. A linear value
  needs no consumer there: its `on abort` runs (W0602 checks the node that aborts).
  The unwinder also cancels the tasks of the scopes that the body opened, and it
  waits for them. So on that path the code after the node does not run. A reference
  keeps its old value (W0301), and a linear value outside the body stays live
  (W0601). A local outside the body keeps its function value (W0313). A node inside
  a closure or a clause of the body does not get the edge: the node that runs the
  closure gets it. The edges come after the whole body (`finish_aborts`), because a
  stored function value can run a clause too.
- A clause can perform an operation of a local handler outside its own `handle`. A
  node that runs the clause then runs the clause of that handler too. It performs
  through its capability. So it mutates the footprint of that handler, and it can
  abort to the end of that `handle`.
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
- The other parts of a signature are not part of the row. They are `lent`, `ret`,
  `stores`, `reach`, `multi`, `fn_stores`, `op_effects` and `tasks` (see below and
  ADR 0006), and `drops` and `holds` (see ADR 0007). The body always infers them, also
  when the signature states the row, and each new lowering replaces them. They do not
  only grow: a part that is not known yet can be larger than its final value. So the
  parts of one function can change at most 32 times and two more times for each function
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
  a function value or a reference in it joins the value of the body. A reference into a
  reference parameter of the clause points into what each operation gets. A `resume`
  gives its argument to the handled computation, so the argument cannot hold a
  capability of a handler inside the clause (W0313). There the argument is the result
  of the operation: the result carries the capabilities of the function values that a
  `resume` gives (W0313 if it leaves an outer handler). The handler of an operation is
  not installed in its clause. So a function value that performs through that handler
  cannot go to the operation (W0313), also through a callee or a closure that gives
  its function parameter to an operation. A signature has an `op_fns` part: the
  function parameters that the body gives to an operation of a handler of a caller,
  also inside a field or a container. It has an `op_effects` part for each function
  value that the body gives to such an operation. The part has the effect of the
  operation and each effect that the value performs through a handler of a caller. A
  clause can run the value as a task, so the caller checks it with its own handlers
  (W0314, ADR 0006). A value that performs through a local handler of the caller and
  goes to an operation of a handler outside that handler escapes (W0313).
- A handler intercepts its effect if a clause performs the effect again, through a
  handler outside it (`clause_performs`, `forwards`). In a library, a handler of a
  standard effect that never forwards is a root handler (W0801), also when the function
  states the effect. The root handlers of `sim.run` get W0802 instead.
- A spawned task or fork branch cannot reach a handler on the stack of another task
  (W0314, ADR 0006).
- A capability lives only while its handled body runs (rule (d) of `proofs/effects`). A
  function value that performs through it cannot leave the body (W0313): not as the
  value of the body (also inside a tuple, a struct, a container or another closure), not
  through a local outside the body, and not to a place or code that can keep it: a
  field or an element behind a reference, a callee that stores it or has no body, a
  function value that the body does not know, a closure that stores its parameter, and
  an operation of a handler outside the body. A struct or a container that a local of
  the body owns can hold the value: it goes out of scope with the body. A callee with a
  body can keep a function argument only in what its reference arguments point into
  or in its result, so a `Box`, an `Rc` or a generic result holds it as a local of the
  body does. A callee result that is not a function value, for example a tuple, holds
  the function arguments of the call.
- A callee can copy a function value out of what a reference argument points to. It
  can put it behind another reference argument, or in its result. A signature has a
  `fn_stores` part: the reference parameters whose pointee can get a function value
  from the body. The caller puts the function values of each reference argument into
  the arguments of `fn_stores` and into a result that can hold a function value. A
  foreign function and a function value that the body does not know can do this with
  each argument. What a reference argument points to includes what the references
  in it point to. So a callee can copy a value into or out of a struct behind a
  stored reference (`dsts: &Vec<&Job>`). A reference to a value carries the function
  values of that value, so a `Vec` that gets the reference gets them too.
- A parameter of a clause holds the function values that the nodes give to its
  operation, also in what a reference argument points to. A clause can keep its
  parameter, or a value that it reads through it. If it keeps it in a local outside
  the body, in a field, in a container or in its value, the value escapes (W0313).
- The result of an operation can hold a reference. It points where the values that the
  clauses `resume` with point. The clauses are lowered after the handled body, so the
  result first points into a root place of its own. At the end of the body, each fact
  about a place below that root moves. It then holds for the same place below each
  place that a `resume` gives. A call that reaches a local handler gives its result
  these places too. A reference into a local of a clause is not valid after the
  `handle`, and a `handle` that returns one is W0204. The returned references of the
  function are checked after this step, so a result in a place that the signature
  states is valid.
- A result from a handler of a caller can point into any place of the parameters. It
  can also point into a place of the caller that the parameters do not reach, for
  example a local of the caller. That place is below a root of its own
  (`a place of a caller`). Code of a caller can change that place. So a node lends the
  root (`lends_mut`) if it performs an operation of a handler of a caller. A call of
  a function parameter, or of a function value that the body does not know, lends it
  too. A callee can perform through a handler of a caller and return a reference with
  no stated place. Then its result can point there too. A function that returns such
  a reference with a stated place gets W0204.
- A `resume` gives its argument to the handled computation, where the body does not
  follow it. So a function value in it is a stored value: a call of the operation
  result runs it (`apply_stored`).
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
- A function type that the body infers carries the function value: the type of a
  closure has its summary. Two function values can meet in one type variable. Examples
  are the elements of an array or a `Vec`, a new value of an `Option` or of a generic
  field, and an element assignment. Then the variable gets the join of both values. So
  a value of that type can be each of them, with the joined modes (`once`, linear,
  nonportable, `@ uniq`). A variable that unifies with a bound variable links to it, so
  a later join reaches each use of the type. A written function type, such as `fn()`
  in `Vec<fn()>`, stays a value that the body does not know. A call of it runs the
  stored values.
- A part of a tuple literal can hold a function value. Then it gets a type variable of
  its own, as the element of a `Vec` does. So two closures that meet in a tuple join
  too: at a new value of a part (`t.0 = f`) or of the whole tuple. They join in the
  tuples of a `Vec` or an array, and in a tuple in a generic field.
- A closure belongs to the function that makes it. So the effect row of a function has
  the effects and the mutations of each closure that the body makes, also one that it
  returns or stores and does not call. A signature with a stated row must allow them
  (W0702, W0703), and an inferred row has them.
- A function that returns a function value has a `ret` part in its signature: what a
  call of the result does, in the places of the parameters. A call of the result does
  that. The part also has the parameters of the result that it gives to an operation
  of a handler at the call site of the function. It also has the parameters that its
  tasks can call (ADR 0006). The body always infers this part, also when the signature
  states the row. It includes the places that the result lends: to a function
  parameter of the function, or to a value that the function does not know.
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
  a `reach` part: whether the body can run a stored value, and whether it can run one
  more than once. The part also has the places that the body gives to it, by argument
  position. A caller gives
  a stored value these places. A function with no body can store each function
  argument, and can run a stored value with any place inside its reference arguments.
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
  effect: for W0702, W0803, W0805, W0801, W0314 and the authority check. Diagnostics
  show the written name (`effects::shown`, `effects::in_signature`). Some diagnostics
  show the identity when the written name can also name another effect. W0702 does
  this when another stated effect of the function has that name. W0803 and W0805 do
  this when the name is the name of a standard effect, or of another effect that leaves
  the same body. In a module that defines `Log`, `Log` names that effect and the alias
  `log` names the standard one.

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
    Take a new value of a local outside the body, in the part of the graph of the
    local. It counts only if it reaches the end of the `handle`. An abort path to that
    end counts too. So does an abort path to the end of a `handle` around it, if the
    local is declared outside that `handle`. Another value counts always: a value in a
    part, or a new value in a closure or a clause. It counts also when a later new
    value replaces it.
  - The result of an operation carries what each `resume` of its handler gives, also a
    `resume` of another operation of the handler.
  - W0314 counts each function value given to a function value that the body does not
    know (a function parameter): it can run the value as a task.
  - A `resume` can resume more than once if a clause of its handler can, also when the
    handled computation does not perform the operation again.
  - A clause that resumes only in a closure counts as a clause that can end with no
    `resume`. So the nodes that run it get an abort path.
  - A callee in `fn_stores` gets the function values of each other reference argument,
    also when it puts another value there. A result that can hold a function value
    gets them too.
  - A parameter of a clause holds the values that the nodes give to each operation of
    its handler, not only to its own operation.
  - The result of an operation of a handler of a caller can hold a reference. It
    points into each place of the parameters and into a place of the caller. Each
    operation of a handler of a caller and each call of a function parameter changes
    that place.
    A call that reaches a local handler gives its result the places of each `resume`
    of the handler, also of another operation.
  - A node that runs a clause of a handler inside the body runs each clause that the
    clause performs through. This is also so when it performs it only on some paths.
  - If one clause of a handler can end with no `resume`, each node that runs a clause
    of the handler gets an abort path. A node that runs a clause that always resumes
    gets one too.
- What stays open (not checked):
  - A `multi` operation of a handler of a caller can resume the rest of the function
    more than once. The code after the operation then runs again with the values that
    its locals got in the run before. The lowering does not follow these values for
    the function body: it lowers it as code that runs once. W0503 keeps `once` values
    out of such a run, and a call result there is not one place (ADR 0003), but a
    reference that a local of the run before holds is not followed into the next run.
    For a local handler the lowering follows them (see the decision above).
  - A function value inside a returned tuple or struct, or a closure that a callee
    makes and stores in a place of the caller: the caller does not see what a later
    call of it does. Its effects and mutations still count in the row of its maker,
    at the call of the maker.
  - A stored function value that runs inside a handler clause: the operation that runs
    the clause does not get it.
  - Only functions of a dependency are checked for `pub`, not its types and effects.
  - W0402 inside a higher-order function: a callback that gets a place of a `@ shared`
    parameter can mutate it. The caller sees the mutation on its own place only.
  - A reference that a function value gets inside another reference: the value sees
    the outer place only (ADR 0003).
  - A function value that the body cannot follow, and that goes to an operation of a
    handler of a caller. The caller does not check it for W0314. Such a value comes
    from a parameter of a closure, or from an operation of a handler of a caller.
