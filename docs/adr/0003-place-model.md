# ADR 0003: The place model

Status: accepted. Date: 2026-10-18.

## Decision

- A place is a root and a sequence of steps. Roots are reference parameters, owned
  locals, and `rc` groups (one group per `rc` type). Phase 1 has no globals as place
  roots: the grammar has no global item. A reference local has a root for its own
  variable too (`Local::cell`): the memory that holds the reference. It has no owner.
  Only W0405 uses it (ADR 0006).
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
  The spec checks both with one rule, `inside_stated` (`arg_outside`, `ref_outside`).
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
- A move of a part (`take(p.a)`) frees that part only (`moved_part`). It leaves no
  value in the part, so it invalidates each reference that overlaps the part: a
  reference at or below the part, and a reference to a place above it, such as `&p`
  (review round 3, F3-5). A reference to the whole value reads the moved part too.
  References into the other parts stay valid. For W0302 the move is still a move of
  the whole local: a later use of `p`, also of `p.b`, is a use after move. This is
  conservative. The other parts are still in the local: a linear part stays live
  (`rest_linear`, ADR 0007), so the program must destructure the value to consume it.
- A temporary value that is not plain data has an owner too. It goes out of scope at
  the end of its statement, as in the interpreter. The value of a block is part of the
  enclosing statement, and the condition of `while` is a statement of its own. A
  handled body, a scope body and a handler clause run in frames of their own, as a
  closure does in the interpreter: the temporaries of their values go out of scope at
  their end (review round 3, O3-2, O3-3). The end of a scope body comes after the
  joins of its tasks.
- A hidden variable holds the value of such a frame from its tail to the node after
  the end of the frame (`frame_value_start`, `frame_value_end`). It points where the
  value points, and it is linear if the value is. So a reference into a temporary or a
  local of the frame is invalid there (W0301), as a block value that points into a
  local of the block is. An abort at the end of the frame sees a linear value (W0602,
  ADR 0006). A value with a variable of its own, such as a closure, goes on in that
  variable: the node that takes the value uses it. A `with_timeout` block and a `fork`
  branch are closures: a reference into their temporaries is W0204 at the return of
  the closure. A clause can also give a reference into a temporary through `resume`.
  That temporary goes out of scope at the end of the `handle`, as a local of the clause
  does: the `handle` cannot return it (W0204).
- A place of a local in statement position, such as `v`, `p.tx` or `v[i]` on its own
  line and not the value of its block, names the place only. It moves nothing and drops
  nothing. Its operands run, for example the index `i`. The interpreter compiles it as
  a place, and the checker sees a plain use. So the value is still in the local after
  the statement, and a linear value still needs a consumer (W0601).
- The tail of a block is its value, not a statement: a place there moves into the
  value of the block, as a branch of an `if` or an arm of a `match` does. This holds
  also when nothing uses the value of the block: a block statement `{ v }`, the body
  of a loop, and the branch of an `if` with no `else`. There the value goes away at
  the end of the block. So the checker sees the move and the drop: a later use is
  W0302, a reference into the value is invalid (W0301), a linear value is dropped
  (W0601), and a `!Move` value cannot move (W0604). A value that is plain data is
  copied.
- The tail of a scope body, of a handled body and of a clause moves at the tail, inside
  the frame, before the end of the frame: before the joins of the tasks of a scope,
  and before the end of the locals and the temporaries of the frame (review round 3,
  O3-1). So a task of the scope that reads into the moved place conflicts with the move
  (W0405). A scope or a `handle` in statement position drops its value at the tail, as
  a block statement does. A handled body with a `multi` operation runs its tail again
  after each `resume`, so the tail moves in each run (O3-14, ADR 0005). A sweep puts a
  tail place in each frame (a block, a `handle`, a `multi` `handle`, a scope,
  `with_timeout`, a closure, a `fork` branch, the branches of `if` and `match`, a loop
  body), in statement and in value position, with and without a task that reads into
  the place. Each run that faults gets an error (`tests/programs/150_frame_tails.wf`).
  Two forms that ran clean in the sweep stay rejected (W0302): a tail place of a
  `multi` handled body, and a tail place of an outer local in a loop body. The sweep
  runs each of them once, but a second `resume` or a second pass moves the value
  again.
- A frame tail in statement position that moves a task handle out of its local drops
  the handle: a bound handle is linear (W0601, ADR 0006), as for `{ h }`.
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
  variable (W0204, W0301). A temporary of plain data stays readable too, as a constant
  does. A reference into a local of plain data is still invalid after the scope. A
  closure that captures the scope capability `s` cannot outlive the scope: it points
  into the variable of `s`, as a closure that captures `&s` does (W0301). Else a call
  of it after the scope would start a task that no scope joins. This holds for each
  captured value that holds the capability, such as a tuple or an `Option`
  (`tests/programs/132_scope_escape.wf`).
- A closure refers to the cells of the variables that it captures by reference. So it
  reads each variable when it runs, not when it is made. The lowering of the closure
  body uses the values that the variables have where the closure is made. So each node
  where the closure runs joins the values that the variables have there. These nodes
  are a call, a call that takes the closure, a spawn, and a node that runs a stored
  value. The joins are these:
  - A variable can have a place that it did not have where the closure was made. Then
    the node uses the variable (W0301). The places of the closure below the old places
    move onto the new places. The node mutates, reads and lends them there (W0301,
    W0402).
  - A part of a captured local can get a new reference, as in `t.0 = &x`. The node
    uses the hidden variable of the part too, and the new places count as above.
  - A function variable can have another value. Then the node runs that value where the
    closure runs the variable, with the places that the closure gives it there. If that
    value runs only once, so does the closure (W0502).
  - A function variable with the same value can run a closure whose own captures have
    new values. The node joins them too, through each level of closures.
  - A variable that the closure gives to a `@ uniq` parameter must still be `@ uniq` at
    the node (W0406).
  - A task runs while its parent goes on. At the end of the body, its spawn node joins
    each value that its captured variables get. The task writes and reads what they
    reach (W0405).
- A closure that leaves the body keeps the values that its captures have later. A
  returned closure points into the places that its captures have at the return. A new
  place in a local is W0204. A new place in a parameter is part of `ret_refs` for the
  caller. A closure can go behind a reference parameter or into an `rc` object. It then
  points into the places that its captures have at the end of the body (W0204).
- A closure that moves a captured variable takes the value when the closure is made.
  This is a by-value capture, as Rust infers it. The facts move the variable at the
  node that makes the closure (`moved_at`). The interpreter moves the value into a cell
  of the closure there. Semantic analysis gives the interpreter these captures for each
  closure span (`FnFacts::by_value`). So the two sides agree by construction. A new
  value of the variable after that point stays in the variable. The closure has the
  value also if it never runs, so a use of the variable after that point is W0302. The
  closure uses its other captures after the move. So a capture that points into the
  moved value is not valid in the closure (W0301). An inner closure that moves a
  capture makes each closure around it take the value too. A capture of a handler
  clause in a closure is a capture of the closure only if the closure does not declare
  it. Such a closure still cannot leave the scope of the variable (W0204, W0301). Its
  type does not show that it runs only once or that it holds a linear value. This is
  conservative. A task closure does the same (ADR 0006).
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
- A function value in a call result points where the arguments can flow too. A
  returned closure can capture a reference argument. The body of the callee infers the
  places of its parameters that the function values in its result point into
  (`EffectSig::ret_refs`). The caller puts in the places of its arguments. A function
  argument can be in the result, so the result points where it points. A function
  with no body can capture a place anywhere inside each reference argument (its
  wildcard place). So can a function value that the body does not know. A call of the
  result
  uses these places (W0301). A function value that a callee copies out of a place
  behind a reference argument is a stored value. Each node that can run it uses what
  it captures (ADR 0005).
- The result can hold the closure in a container, a part or a field, as in
  `o.push(|| ...)` and a return of `o`. A local keeps the closures that the body puts
  into its containers. A part of a local keeps its new value in a hidden variable. A
  return of the local returns their places too. A tuple, a struct or an array literal
  points where the closures in its parts point, also through such a local. A local
  container that gets a closure does not point into its captures itself. The stored
  closure has a variable of its own from the store on (ADR 0005).
- A callee can put a closure behind a reference argument, as in `o.push(|| v.len())`
  for `o: &Vec<fn()>`. The body infers the places of its parameters that such a closure
  points into (`EffectSig::fn_store_refs`). The argument of the caller points into the
  places of its arguments there, from the call on. A local that owns the argument gets
  a hidden variable for them, as for a new value of a part. A place behind a reference
  parameter or in an `rc` object of the caller keeps them for its own caller (W0204).
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
- The same holds for a reference that a function puts into an `rc` object, at a place
  under an `rc` group root. Each function with a handle can read it after the return,
  as a global. A callee that puts a reference that a parameter gives into an `rc`
  object has that parameter in a `group_stores` part of its signature. So its caller
  checks the argument at the call, as `call_flows` does for a reference parameter. A
  foreign function that changes an `rc` type can put each argument there.
- A closure points into what it captures. A closure that goes behind a reference
  parameter or into an `rc` object counts as a reference to its captures. It can go
  there by a push into a container, by a field assignment, or by a callee. A callee
  that puts a function parameter into an `rc` object has it in `group_stores`. A
  closure or a handler clause can put its own reference parameter there. Then each node
  that runs it puts the places that it gives (`Summary::param_stores`). These nodes are
  a call, a call that takes the closure, and a node that performs the operation.
- A reference into an object behind a local `Rc` handle depends on the handle. The
  object can go away with the handle. So a store of such a reference behind a
  reference parameter is W0204. A store into an `rc` object of another type is W0204
  too. This is the same as for a returned reference. A handle of the `rc` type of the
  store can be a handle of the object itself. So a reference into that type is
  allowed.
- The borrowing proof assumes that no reference is stored in the heap. This is the
  "no back channels" assumption of `proofs/borrowing/README.md`. The checker mirrors
  it for references and closures behind reference parameters and in `rc` objects.
  They cannot point into a local of a function that has returned.
- Evaluation order follows the interpreter: arguments and operands run from left to
  right. A by-value argument moves when it is evaluated, so `f(v, v.len())` is a use
  after move. A hidden variable holds the value on its way to the call while the later
  arguments run: it points where the value points. A reference argument, a closure argument and the value of a named
  variable are held from the point where they are taken, so a later argument that
  invalidates or rebinds them is seen.

## Consequences

- Element places are not index-sensitive. A mutation of one element can invalidate a
  reference into the unstable part of another element. This is safe and conservative.
- A reference to the whole value, or to a place above a moved part, is invalid after
  the move of the part, also for a read of another part: `r = &p; take(p.a);
  print(r.b.x)` is W0301 (`tests/programs/152_part_move_refs.wf`).
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
- A node that runs a closure moves each place of the closure below an old place of a
  captured variable onto each new place. This also moves a place that comes from
  another capture that points there too. A task gets the new values of its captured
  variables also from before its spawn and after its join. A node that runs a stored
  value joins the values that the variables have at the end of the body. A stored
  closure points into each value that its captures get after the closure is made,
  also a value that a later change replaces. A returned local holds each closure that
  the body puts into a container of it, also one that a later change removes.
- A reference can go into an `rc` object through a handle of the same `rc` type. This
  is allowed, also when the handle refers to another object. Such a reference can
  dangle when that object goes away.
- A closure or a clause can put its reference parameter behind a reference parameter
  or into an `rc` object. The check covers only the nodes that run it in the body. A
  function value does not state where the references that it gets live. So the check
  does not cover unknown code that runs such a closure. It does not cover a callee
  that gives it a reference into its own local either. That case stays open until the
  core IR (F3-2, see the last item).
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
- What stays open until the core IR replaces the fact generation (review round 3).
  The checker does not enforce these rules yet. Each rule has an acceptance target in
  `tests/ir_targets` (`docs/traceability.md`):
  - A `match` that reaches its scrutinee through a reference binds a reference to a
    part, such as `e` in `match p { Some(e) => .. }` for `p: &Option<&Entity>`. A
    place below the binding is a place where the stored reference points, not a place
    of the scrutinee. The rule: a by-reference binding whose type holds references
    gets the held places of the part, as a field read through a reference does. So a
    change of these places invalidates the binding (W0301). A callee that does the
    same `match` on a reference parameter makes its caller put in these places
    (W0312) (R3RT2, `tests/ir_targets/r3rt2_match_through_ref.wf`).
  - A reference argument can point to a value that holds references, such as `&rs`
    for `rs: Vec<&Entity>`. The rule: the caller adds the places that the references
    behind the argument point into (the held places) to `call_arg`, with the root of
    the argument. It adds them to the reads of the call node, and to the reads of a
    task that makes the call. A by-value argument that holds references does this
    today (R3RT3, `tests/ir_targets/r3rt3_held_refs_at_call.wf`).
  - A closure or a clause can keep its reference parameter in an outer local, or
    store it there. A callee that runs the closure, or that performs the operation of
    the clause, can give it a reference into a local of the callee. The caller cannot
    name that place. The rule: at each node that runs a closure or a clause through a
    callee (a call that takes the closure, or a call in the handled body that can
    perform the operation), each place that the callee lends there and that the
    caller cannot name gets a root of its own. A hidden variable owns that root. It
    goes out of scope at a node right after the call, and on the abort path at the
    end of the `handle`. So a holder outside is invalid after the call (W0301). A
    store of such a place behind a reference parameter, or into an `rc` object, is
    W0204. A core IR alone does not give this rule: its fact generator must add it
    (F3-2, `tests/ir_targets/f3_2_callee_local_refs.wf`, ADR 0005).
  - A reference through a handle depends on the handle (`handle.*`). The rule: a
    place through an `Rc` handle also reads the handle place, which is the variable
    or the field that holds the handle. This is also true for the reads of a task. So
    a move of the handle, a new value of it, the end of its scope, or a move of a
    value that holds it conflicts with a task that reads through it (W0405), as for
    a `Box` (O3-6, `tests/ir_targets/o3_6_rc_handle_tasks.wf`).
