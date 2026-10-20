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
- Each proof crate has a script for its mutation table: `proofs/borrowing/mutations/`,
  `proofs/effects/mutations/` and `proofs/link/mutations/` (`run.sh`). A mutation is a
  patch script that changes a copy of the sources; the test passes if `verify.sh`
  fails on the copy. So each row of a table can run again from the tree (review round
  2, FD15). In `borrowing` and `effects`, a mutation passes only if Verus gives a
  result line with at least one error, and the line is the one of the table (the
  `# EXPECT:` line of the script). A failure with no result, for example with no
  `verus` on `PATH` or a patch that breaks the build, does not pass.

## Consequences

- The proofs cover a model, not the full language. The README of each crate lists the
  gap between the model and the checker.
