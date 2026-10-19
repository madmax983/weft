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
  `&T in p..` names any place inside `p`. An `in` place can name a parameter that comes
  later, also one with an `in` place of its own. The lowering substitutes the `in`
  places in the order of their roots, so each parameter gets the places of its root.
  W0201 rejects a cycle.
- A wildcard place (`p..`, the step `WILD`) stands for any place at or below `p`. It
  overlaps what `p` overlaps. A reference to it is invalid after any mutation or free
  that overlaps `p`, and a mutation of it invalidates every reference below `p`. The
  result of an unknown function value (a parameter of function type) points to the
  wildcard place of each reference argument. The wildcard place of a place at or below
  `b..` is `b..` itself: `b.. ..` is the same set. So no place has two wildcard steps,
  and `cur = step(cur)` stays at `b..`. The checker compares the outermost wildcard
  bases only. The place relations are closed under prefixes, so this is exact also
  for facts with nested wildcard steps.
- A change anywhere in `b..` invalidates each reference strictly inside `b`
  (`strict_prefix(B, Path)`). A reference to `b` itself survives: a change at or below
  `b` is not a strict prefix of `b`, so rule 3 spares `b` for each place that `b..`
  can be (rule 4). So `x..` never stands for a change above `x`: a change above a place
  that the facts name by a root of their own, such as a clause parameter, is a free of
  that root (`releases_at`, ADR 0005).
- A write through a reference `R`, at the place of `R` or below it, leaves `R` valid
  (`writes_via(P, R)`). At run time `R` points to one place `c`, and the write is at
  `c` or below it. No such place is a strict prefix of `c`, so by rule 3 and rule 4 no
  mutation at the node invalidates `R`. This holds for each place that the facts give
  `R`, also a wildcard place: they are the places that `c` can be. The mutation rules
  (rule 3 and the two wildcard rules for a mutation) do not apply to `R` at such a
  node. The free rules and the lend rules still apply. Sema gives `writes_via` to an
  assignment whose target starts at a local `R` that holds one reference (`&T`, and
  `T` holds no reference), if each mutated place is at or below a place of `R`. It also
  gives it to the node of a method call on a part of `R`, if the method states no
  effect, takes and runs no function value, mutates only places of `self`, and each
  mutation at the node is at or below a place of `R` (checked at the end of the body,
  when the clauses and the stored values added their changes). Another reference into
  the same places, also a copy of `R`, is still checked.
- The result of one call with no stated place is one place inside the arguments: a
  one-place wildcard place `(b..)` (`one_place(P)`, a new instance for each call). A
  place below it, such as `(b..).items`, is a place inside that one place. A change
  and a reference below one instance compare by their steps below it, with rule 3
  (`same_one(M, Path)`). So `e.hp -= 1` does not invalidate `e`, and `e.kids.push(x)`
  invalidates a reference into `e.kids[]`. Two places inside one instance also
  overlap by their steps only (`overlaps`, for W0312 and W0405): a task that writes
  `e.hp` and a parent that reads `e.id` have separate footprints. Two instances, or
  an instance and another place, use the wildcard rules: two results can be one
  place, or one can be inside the other.
- An instance is sound only while all places below it come from one value of one
  reference, so sema makes one only where that holds:
  - The result type is `&T` or `Option<&T>`, and `T` holds no reference. A result with
    more references, such as a tuple or a `Vec<&T>`, gets the shared wildcard place.
  - The call is in the body of the function, not in a closure or a clause. One
    lowering of a closure body stands for each call of the closure, so its results
    get the shared wildcard place.
  - The code of the call cannot run again in one run of the body: it is not in the
    handled body of a handler of an effect with a `multi` operation, and the function
    cannot perform such an operation through a handler of a caller (its row has no
    such effect, no unknown `multi` call and no function parameter that can perform
    one). After a `multi` resume the code runs again, and the locals keep the results
    of the run before.
  - The call is not in a loop body. The values that an iteration gives to the next
    can hold the results of two iterations with one instance, for example after a
    rotation through the parts of a tuple. So a result in a loop gets the shared
    wildcard place. A write through the result itself still keeps it valid
    (`writes_via`).
  - A caller sees a returned instance as `..`, and makes its own instance.
  - A local that gets the results of two calls inside one base points into the shared
    wildcard place of the base for the second one. A local only gets places, so else
    `cur = step(cur)` would give `cur` one more place for each call.
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
  a task handle), the lowering joins it into the value at the loop head and lowers the
  body again, until the values are stable. So a mutation through `cur` before `cur = b`
  in the body also mutates `b`. A chain of locals (`r0 = r1; r1 = r2; ...`) needs one
  pass for each local. The join keeps the places, the function values and the tasks of
  the head and of the end of the pass, so the values only grow.
- The join widens a value that goes deeper a second time, in each pass: a new place
  below a place that an earlier pass of the loop added (a place that the value did
  not have before the loop) becomes the wildcard place of the outermost such place.
  So `cur = &cur.next[0]` gets `cur.next[]..` in the second pass, also with branches
  that go into different fields. A new place below a wildcard place `b..` (not a
  one-place instance) becomes `b..`: it is one of the places of `b..`. A local also
  points into `b..` in place of a place below it. A value whose places in one root
  are more than 16 at a loop head (64 for a local anywhere) becomes the wildcard place
  of the longest common prefix of these places. Each of these wider places includes
  the places that it replaces. So the number of places of a value does not grow with
  each pass, also in nested loops, where each entry of an inner loop starts again.
- After eight passes the join widens what still changes, so that the values become
  stable:
  - A new place below a place that the value had at the head becomes the wildcard place
    of the deepest such place.
  - After one more pass for each local outside the loop and 16 more, a new place with
    no such place above it becomes the wildcard place of its root.
  - After as many passes, a function value that still changes becomes a function value
    that the body does not know. It can still do what the joined values do. A chain of
    locals that pass function values along needs one pass for each local, as for
    places, so a chain of known closures stays known.
  - A local keeps the set of the tasks that it can hold on its own path, and the head
    joins the sets of the head, of the end of the body and of each `continue` (ADR 0006
    has the rule for a `join`).
  The widened value includes the value that it replaces: a wildcard place `q..` stands
  for each place at or below `q`, and an unknown function value can do what any
  function value can do with the places that it gets. A widened value is a value at the
  loop head, so the next pass lowers the body with it. The loop stops when a pass gives
  no value that the head does not have (by place shape, also for a root that the pass
  made again). Then the head values include the values of each iteration: those of the
  first iteration, and by induction those that the body makes from them. So the facts
  of the last pass hold for each iteration. Widened places are finite: wildcard places
  of known places and of roots, and a wildcard place of a wildcard place is itself. So
  the loop stops. If a loop is not stable after twice the number of passes before the
  root widening, and 32 more, the lowering reports W0707, an error. It never keeps the
  values of the last pass with no error.
- A closure refers to the variables that it captures, as the interpreter captures their
  cells. A captured value of plain data stays readable after its scope ends, so such a
  closure can leave the scope. A closure that captures another value cannot outlive the
  variable (W0204, W0301), also when it moves the value: it takes the value only when it
  runs. A temporary of plain data stays readable too, as a constant does. A reference
  into a local of plain data is still invalid after the scope.
- A field, an element or a part of a tuple can hold a reference. A place below it,
  such as `t.0.kids` for `t: (&Entity, &Entity)`, is a place where that reference
  points, not a place of `t`. These are the places of the references that the local
  holds (`held_refs`), so a write there invalidates the references into them.
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
  the part can hold the references of each branch. A holder that the branch replaced
  gets a new value on the edge from the branch. It gets one on the edges into the head
  and the exit of a loop too. So a change of its places after the replacement does not
  count after the join. A loop keeps the references that a pass gives for the next
  pass. A destructuring `let S(a, b) = s` gives each part the places of `s`.
- A by-value parameter that holds references, such as `o: Option<&World>`, points into
  a parameter root. The callee can mutate through it. The caller puts in the places of
  the argument. A new value of the parameter itself is local.
- A reference parameter can point to a value that holds references, such as
  `rs: &Vec<&T>`. A reference that the body reads out of it points into a root of its
  own (`*rs` in the facts). That root is what the references behind `rs` point into.
  The reference can point anywhere inside that root. Only such a parameter has this
  root. The value behind a slice reference is its elements, so `es: &[u64]` has none.
  A signature names these places with the step `Held`. A caller puts in the places
  that the references in its argument point into, and the steps after them. A written
  `rs..` covers them, in `mut(rs..)` and in `&T in rs..`. So a mutation through a
  stored reference needs `mut(rs..)` (W0703), and a returned stored reference needs
  `in rs..` (W0204).
- A function cannot put a reference behind a reference parameter if the reference
  points into its own local, a by-value parameter or a temporary. For example,
  `rs.push(&w[0])` does that. The caller keeps the reference after the return
  (W0204). This also holds for a result of an operation that points into a local of a
  clause.
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
  place one level below the place before the loop and the wildcard place below it. A
  change that overlaps the base of the wildcard place invalidates it, also through
  stable steps only, unless the change goes through the reference itself. A signature
  check sees the wildcard place, so it needs a written `in p..` or `mut(p..)`. A value
  with very many places in one root, such as a long walk in straight code or a walk
  in many branches, gets the wildcard place of their common prefix.
- A loop that needs more passes than its locals and 16 more can get a function value
  that the body does not know. A call of it lends its arguments, can abort, and
  performs its effect row.
- `writes_via` is only for a write at an assignment or at a method call that changes
  only its receiver. A call of a function, also with the reference as its only
  argument, can invalidate the reference by the wildcard rules, as before.
- `points_into` is not flow-sensitive. A reference that got a place inside a block, and
  then a place outside it before the block ends, is still invalid after the end. This
  is the same imprecision as for mutations.
- A result with no stated place points anywhere inside the reference arguments, also
  when the callee returns a reference to one element only. A change through another
  result, or through a result of an iteration before, invalidates it, also a change
  of a scalar field. In a loop body or after a `multi` operation, a result is not one
  place: a change through another reference into it invalidates each reference into
  it.
- A reference parameter with `in p..` points into the shared wildcard place `p..`, not
  into an instance. A write through it keeps it valid (`writes_via`), and so does a
  write through a local that it gives its value to, for that local. A change through
  another reference into `p..` invalidates it, also a change of a scalar field.
- A place below a part of a tuple or an element that holds a reference is a place of
  each reference that the local holds: the parts are not told apart. So a write
  through `t.0` also counts as a write where `t.1` points. A write through a part does
  not keep the part valid: `writes_via` is for a local that holds one reference.
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
  closure or a clause. The value sees the outer place only (ADR 0005). A reference to
  a local of the closure that the closure puts there is not checked either.
