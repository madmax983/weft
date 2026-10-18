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
- A reference holds all the places that it points into. A node that uses a reference
  accesses those places, and a task reads the places that its captures point into. This
  is the rule that the B4 proof covers ("no write to a place that the other task
  holds"). It is coarse: two tasks that capture one reference to a struct and touch
  separate fields conflict. Split the struct, or pass references to the fields.
- A spawn is a mutation at the spawn node. So a reference that a task breaks is invalid
  after the join.
- A spawned task that captures a nonportable value or a shared-mutable reference is
  pinned. The relation `stealable(T)` tells the scheduler which tasks can move.
- A spawn in statement position gives its handle to the scope. A bound handle is linear.
