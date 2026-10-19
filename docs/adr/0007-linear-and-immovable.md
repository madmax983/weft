# ADR 0007: Linear and immovable types

Status: accepted. Date: 2026-10-18.

## Decision

- Values are affine. Plain data (integers, references, and structs of plain data) is
  copied. `String` is immutable and copied.
- A `linear` value must be consumed on every normal path: moved into a call, or
  destructured with `let S(a, b) = s` (W0601).
- `on abort = f` names the function that unwinding runs.
- `struct S: !Move` keeps its address. Moving a named value is an error (W0604). A
  function can return a struct literal: it is built in place.
- Only a `!Move` struct may hold a reference field, and only into `self` (W0605).
- A property of a type holds if a part has it: a field, a tuple part, an enum payload,
  an element and a type argument. `linear`, `nonportable` and `!Move` work so at any
  depth. A table for each type definition (`weft_sema::props`) gives the parts that
  pass a property on, as a least fixpoint over the definitions. A type that holds
  itself, such as `enum List { Cons(u64, List), Nil }`, is not plain data. The flags
  of a local come from the type that the whole body infers, so `let v = Vec.new()`
  and a later `v.push(tx)` make `v` linear.
- A value has `on abort` for W0602 if each linear part has it, or if a type around the
  part has it: that `on abort` finishes its parts. A tuple of a `Tx` with `on abort`
  and a `Lock` without it has none.
- A closure that moves a linear value is linear: it must run once on every normal path
  (W0601). A callee that gets it can drop it, so a function argument of this kind is
  W0601, except for `with_timeout`, which runs its block once. A closure that moves a
  value that is not plain data runs only once: a second call is W0502, also when a
  callee that can call its argument more than once gets it, and an operation of a
  handler gets it (a clause can call it more than once). A place of plain data, such
  as a field of type `fn()`, cannot hold it: a copy of the place could call it again
  (W0502). A closure that calls a `once` closure or resumes a `once` continuation
  moves it, so it is `once` too.
- A linear value cannot go away silently:
  - A pattern `_` drops its part: in a `let`, for a temporary that a `match` takes, and
    in an arm that binds a part by value. An arm that matches a value with no linear
    part, such as `None`, consumes its local scrutinee.
  - `print`, a comparison, a receiver that a method borrows, a field read and a
    borrow only read a temporary: a linear temporary goes away at the end of its
    statement.
  - A new value of a place drops the old value. `p.tx = v` on a live linear local `p`
    is `overwrites(V, P)` in the spec (W0601). Behind a reference the old value is
    always there, so a new value there is W0601.
  - A new value inside a closure or a handler clause overwrites a captured linear
    value: the value is live where the closure or the clause starts.
  - A place whose type is not linear cannot keep a linear value: a field of type
    `fn()` or a `Vec<fn()>` cannot hold a linear closure.
  - A generic function does not know that a value of a type parameter is linear. Its
    signature has a `drops` part: the by-value parameters of a type parameter that a
    path of the body does not move. A caller that gives a linear value there gets W0601.
- `!Move` passes through the parts that hold a value inline. A pointer such as `Box`
  or `Rc` does not move its target, so it does not pass `!Move` on. A `!Move` value
  that a call builds for a parameter of its own type is built in place. For a
  parameter of a type parameter the callee can move it, as `Vec.push` does when its
  buffer grows (W0604).
- A self-reference field gets only a reference into its own struct (W0605). A struct
  literal cannot give it one: the struct has no place yet. A place field that the
  literal does not give has no value. A read or a borrow of the field, or of the
  struct, before the body gives the field a value is W0304.

## Consequences

- What stays imprecise (sound, but it can reject a correct program):
  - A linear closure given to a function parameter is W0601, also when the callee calls
    it once on every path.
  - `drops` counts a path that does not move the value, also when the value there is
    `None` of an `Option<T>`.
  - A new value in a closure counts the captured value as live at the closure start,
    also when the closure runs after the value moves.
  - A borrow of a struct with a place field that has no value is W0304, also when the
    callee gives the field a value first.
- What stays open (not checked):
  - A generic function that can abort or resume more than once while it holds a value
    of a type parameter: W0602 and W0503 do not see that the caller gave a linear value.
  - A `Vec` of linear values is linear, and nothing consumes it: it is W0601 at its end.
