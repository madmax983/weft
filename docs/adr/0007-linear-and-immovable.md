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
