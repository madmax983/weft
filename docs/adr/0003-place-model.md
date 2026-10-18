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
- Each owned local and each by-value parameter owns its root place (`owner(Rt, V)`). A
  move of `V` or the end of its scope frees the memory (`frees_at`), so it invalidates
  every reference into the root, also through stable steps. A block value that points
  into a local of the block is held across the end of the block, so this rule sees it.
- A move of a part (`take(p.a)`) frees that part only (`moved_part`). References into
  the other parts stay valid. For W0302 the move is still a move of the whole local:
  a later use of `p`, also of `p.b`, is a use after move. This is conservative.
- A temporary value that is not plain data has an owner too. It goes out of scope at
  the end of its statement, as in the interpreter. The value of a block is part of the
  enclosing statement, and the condition of `while` is a statement of its own.
- The locals and temporaries of a closure go out of scope at each node where the
  closure runs: a call of it, a call that takes it, a spawn. A handler clause runs at
  each operation that it handles. There it uses its captures, moves the captures that
  it moves, and its locals go out of scope.
- An `Rc` handle keeps its object alive. A place through a handle is in the group root,
  and the reference also depends on the handle place (`handle.*`, an unstable deref).
  A new value, a move or the end of the handle invalidates the reference. Dropping
  another clone does not. A call result in a group root depends on the handles of the
  arguments: their handle places, and the `Rc` handles in the values that the reference
  arguments point to. A held receiver keeps its handle places.
- A function or a closure cannot return a reference into its own locals, by-value
  parameters or temporaries (W0204). A closure call keeps the places of its result; a
  place under a reference parameter of the closure becomes the place of the argument.
- Assignment follows the interpreter. `x = v` on a local gives the local a new value; on
  a reference local, `v` must be a reference. `c += v` (and `-=`, `*=`) on a reference
  writes through it: it mutates every place that `c` points into.

## Consequences

- Element places are not index-sensitive. A mutation of one element can invalidate a
  reference into the unstable part of another element. This is safe and conservative.
