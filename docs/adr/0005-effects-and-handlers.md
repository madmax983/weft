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
- Call-site aliasing (W0312): a callee sees its reference parameters as separate places.
  So the caller must not pass overlapping places when the callee (or a handler that the
  callee reaches) mutates one of them.
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
  A worklist lowers callees before callers. When the row of a function grows, only the
  functions whose bodies name it are lowered again. Each new row is joined with the old
  row, so a row only grows. A row is in a finite lattice: the effects of the program,
  the parameters, and the `mut` places of at most 8 steps under the parameters and the
  `rc` groups. So the inference always reaches a fixpoint. The bound for one row is the
  height of its lattice (`weft_sema::infer::growth_limit`). It depends on the number of
  effects, parameters and types, and on the number of different steps in the places of
  the program. A row that grows past the bound shows a checker bug: each function whose
  row can still grow gets W0706, an error. The checker never uses effects that can be
  incomplete without an error.
- Every named effect can abort (the handler can drop the continuation). A linear value
  live across such a node needs `on abort` (W0602).
- `resume` consumes a `once` continuation (W0501). A `multi` operation needs `many` values
  around it (W0503).
- A spawned task or fork branch cannot perform a user effect (W0314): the handler is on
  another task's stack.
- Extern functions in user code default to `blocking`.
- `print` is a debug built-in with no effect.

## Consequences

- Effect polymorphism needs no syntax. A limit: a closure's mutations through its own
  reference parameters are not visible at the call site of the higher-order function.
