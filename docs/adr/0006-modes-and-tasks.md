# ADR 0006: Modes, separation and work stealing

Status: accepted. Date: 2026-10-18.

## Decision

- Four mode axes: uniqueness, portability, contention, affinity. The lattice is verified
  (`weft_verified::modes`), but the checker does not use it yet: the mode rules use the
  flags `nonportable`, `uniq` and `shared` in the facts (ADR 0004).
- `@ shared` forbids mutation through the reference (W0402).
- A fork branch must be portable: no nonportable captures (W0401) and no mutation
  through an aliased reference (W0403). `split_mut` gives `@ uniq` parts.
- Separation (W0405): a task is active from its spawn to its join or the scope end. Each
  node that runs while a task is active must not access what the task writes, and must
  not write what the task reads.
- A spawn is a mutation at the spawn node. So a reference that a task breaks is invalid
  after the join.
- A spawned task that captures a nonportable value or a shared-mutable reference is
  pinned. The relation `stealable(T)` tells the scheduler which tasks can move.
  `tests/programs/33_stealable.wf` marks each task closure `//~ stealable` or
  `//~ pinned`, and the corpus test checks the marks.
- A spawn in statement position gives its handle to the scope. A bound handle is linear.
