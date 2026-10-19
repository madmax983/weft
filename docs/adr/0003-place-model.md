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
- `&T in p` names the place of the reference up to stable steps below `p`. The body
  must return (or the caller must pass) a reference at `p` or below it through stable
  steps only (W0204, W0203). So a caller can treat the reference as a reference at `p`.
  `&T in p..` names any place inside `p`.
- A wildcard place (`p..`, the step `WILD`) stands for any place at or below `p`. It
  overlaps what `p` overlaps. A reference to it is invalid after any mutation or free
  that overlaps `p`, and a mutation of it invalidates every reference below `p`. The
  result of an unknown function value (a parameter of function type) points to the
  wildcard place of each reference argument.
- A returned place cannot be in a by-value parameter (W0204), also in an `extern`
  signature.
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
  writes through it: it mutates every place that `c` points into. The same holds for
  any place that holds a reference: a reference field of a `!Move` struct writes its
  declared place, and a part of a local writes what the local points into.
- A loop iteration starts with the values that the iterations before it gave. When the
  body gives a local from outside the loop a new value (a reference, a function value or
  a task), the lowering joins it into the value at the loop head and lowers the body
  again, until the values are stable. So a mutation through `cur` before `cur = b` in
  the body also mutates `b`. After eight passes the values of the last pass stay.
- A closure refers to the variables that it captures, as the interpreter captures their
  cells. A captured value of plain data stays readable after its scope ends, so such a
  closure can leave the scope. A closure that captures another value cannot outlive the
  variable (W0204, W0301), also when it moves the value: it takes the value only when it
  runs. A temporary of plain data stays readable too, as a constant does. A reference
  into a local of plain data is still invalid after the scope.
- A value points where its parts point: a tuple, a struct literal, an array literal, an
  enum payload and a call result. A local that holds such a value points into the
  places of its references, so a change there invalidates the local. A pattern, an
  element or a field can read a reference out of a local. It uses the local, and the
  reference points where the local points. A by-value binding of a reference payload
  (`Some(r)` on an `Option<&T>`) is that reference.
- A returned type can state the place of a reference inside it: `Option<&T in v[]>`.
  A top-level reference and a tuple part must state it (W0204). Another reference with
  no place is allowed: the result of the call points where the arguments can flow. An
  argument of a reference type, or of a type with a reference inside, lets the callee
  reach any place inside it (a wildcard place). An argument of a type parameter passes
  its value on as it is, so `id(&v[0])` points into `v[]`. A reference argument whose
  value holds references gives them too. The call can mutate such an argument. Then
  it can keep the references of the other arguments: `rs.push(&x)` makes `rs` point
  into `x`.
- A new value of a part of a local, such as `w.x = &b[0]`, points where it points from
  that node on. A hidden variable holds it, and each use of the local uses it. A later
  new value of the same part, of a part around it, or of the whole local replaces it.
  Each branch of an `if` or a `match` replaces only on its own path. So after the join
  the part can hold the references of each branch. On the edge from a branch, or into
  the head or the exit of a loop, a holder that the branch replaced gets a new value:
  a change of its places after it was replaced does not count after the join. A loop
  keeps the references that a pass gives for the next pass. A destructuring
  `let S(a, b) = s` gives each part the places of `s`.
- A by-value parameter that holds references, such as `o: Option<&World>`, points into
  a parameter root. The callee can mutate through it. The caller puts in the places of
  the argument. A new value of the parameter itself is local.
- A reference parameter can point to a value that holds references, such as
  `rs: &Vec<&T>`. A reference that the body reads out of it points into a root of its
  own: what the references behind `rs` point into (`*rs` in the facts). It can point
  anywhere inside that root. A signature names these places with the step `Held`: a
  caller puts in the places that the references in its argument point into, and the
  steps after them. A written `rs..` covers them, in `mut(rs..)` and in `&T in rs..`.
  So a mutation through a stored reference needs `mut(rs..)` (W0703), and a returned
  stored reference needs `in rs..` (W0204).
- Evaluation order follows the interpreter: arguments and operands run from left to
  right. A by-value argument moves when it is evaluated, so `f(v, v.len())` is a use
  after move. A hidden variable holds the value on its way to the call while the later
  arguments run: it points where the value points. A reference argument, a closure argument and the value of a named
  variable are held from the point where they are taken, so a later argument that
  invalidates or rebinds them is seen.

## Consequences

- Element places are not index-sensitive. A mutation of one element can invalidate a
  reference into the unstable part of another element. This is safe and conservative.
- A reference that goes deeper in each loop iteration (`cur = &cur.next[0]`) has the
  places of eight iterations only. A reference that a deeper change invalidates is below
  one of these places through an unstable step, so a change there invalidates it too. A
  signature check does not see the deeper places.
- `points_into` is not flow-sensitive. A reference that got a place inside a block, and
  then a place outside it before the block ends, is still invalid after the end. This
  is the same imprecision as for mutations.
- A result with no stated place points anywhere inside the reference arguments, also
  when the callee returns a reference to one element only.
- After a join, a part can hold the references of each branch. A use after the join
  uses each of them. A change of the places of a replaced holder before the join does
  not count, but a change after the join does.
- A reference read behind a reference parameter can point anywhere inside what the
  references there point into. A caller puts in each place that its argument's
  references point into, also when the callee reads only one of them. `mut(rs..)` and
  `in rs..` cover the places of `rs` and these places.
- W0605 is about written reference fields. A generic type such as `Option<&T>`,
  `Vec<&T>` or `Wrap<&T>` can hold references: the facts follow their places.
- What stays open (not checked): a reference stored behind a reference parameter of a
  closure or a clause. The value sees the outer place only (ADR 0005).
