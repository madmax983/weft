# ADR 0006: Modes, separation and work stealing

Status: accepted. Date: 2026-10-18.

## Decision

- Four mode axes: uniqueness, portability, contention, affinity. The lattice is verified.
- `@ shared` forbids mutation through the reference (W0402).
- A fork branch must be portable: no nonportable captures (W0401) and no mutation
  through an aliased reference (W0403). `split_mut` gives `@ uniq` parts.
- Separation (W0405): a task is active from its spawn to its join or the scope end. Each
  node that runs while a task is active must not access what the task writes, and must
  not write what the task reads.
- The rule is access-based. Sema records the reads: a use of a reference as a value
  reads the places that it points into, a call reads its reference arguments, a loop
  reads the elements at each iteration, and a handler clause reads its captures at each
  operation that it handles. A plain use of a reference is not an access by itself, so a
  task and the parent can touch separate fields through one reference.
- A move or the end of an owner frees its memory (`frees_at`). A free while a task is
  active must not overlap what the task reads or writes. A task closure that moves a
  capture moves it when the closure is made. A move of a part frees that part only.
- The tasks of a scope join before the locals of the scope body go out of scope, as in
  the interpreter.
- The B4 proof covers a stronger rule: no write to a place that the other task *holds*
  (references and captures, at any point). The access-based rule is more permissive.
  The proof does not cover it.
- A spawn is a mutation at the spawn node. So a reference that a task breaks is invalid
  after the join.
- A spawned task that captures a nonportable value or a shared-mutable reference is
  pinned. The relation `stealable(T)` tells the scheduler which tasks can move.
- A spawn in statement position gives its handle to the scope. A bound handle is linear.
