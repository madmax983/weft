# ADR 0008: Soundness proofs

Status: accepted. Date: 2026-10-18.

## Decision

- We extend the group-borrowing proof (madmax983/group-borrowing-soundness) in
  `proofs/borrowing`, in the order of its review: branches and loops, captured
  references (closures, handlers, resume as calls), progress, inline layout, task
  separation.
- `proofs/effects` models algebraic effects as an abstract machine: effect safety,
  one-shot safety, abort safety (exactly-once `on abort`), lexical resolution, and the
  multi-shot restriction.
- Each theorem has vacuity guards: an accepted program, a rejected program with a bad
  execution, a satisfiable-hypothesis witness, and a documented mutation test.

## Consequences

- The proofs cover a model, not the full language. The README of each crate lists the
  gap between the model and the checker.
