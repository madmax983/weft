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
