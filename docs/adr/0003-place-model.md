# ADR 0003: The place model

Status: accepted. Date: 2026-10-18.

## Decision

- A place is a root and a sequence of steps. Roots are reference parameters, owned
  locals, and `rc` groups (one group per `rc` type).
- Step kinds: field (stable), variant payload (unstable), element (stability declared by
  the type), split segment `[..k]`/`[k..]`, and deref (stability declared by the type).
- Stability is a property that pointer and collection types declare
  (`extern type Vec<T> { elem: unstable }`, `extern type Gc<T> { deref: stable }`).
  There is no fixed list. A future GC pointer declares a stable deref.
- Two relations compare places. "May alias" is symmetric and conservative; it decides
  invalidation and overlap. "Within" is inclusion; it decides effect coverage.
- The two sides of one split never alias. This proves `split_mut` parts disjoint.
- `mut(p..)` is equal to `mut(p)`. A Verus lemma (`lemma_deeper_mutation_weaker`) proves
  that a deeper mutation invalidates no more.
- Assignment follows the interpreter. `x = v` on a local gives the local a new value; on
  a reference local, `v` must be a reference. `c += v` (and `-=`, `*=`) on a reference
  writes through it: it mutates every place that `c` points into.

## Consequences

- Element places are not index-sensitive. A mutation of one element can invalidate a
  reference into the unstable part of another element. This is safe and conservative.
