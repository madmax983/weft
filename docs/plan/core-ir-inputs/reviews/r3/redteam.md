# Review round 3, lens "redteam": targeted attacks

Source: `r3/src`, commit b073ea7 (head of `review/s5` after S5b and S5c). Binary:
`r3/target/release/weft`. I did not change the source. All files of this lens are in
`SCRATCH/r3/redteam/`
(below: `RT/`).

## Summary

- I ran the round-2 redteam probes (`r2/redteam/p/*.wf`) and the round-2 repros of all
  lenses again. I found no regression of a round-2 fix. Each mismatch in
  `RT/regress_r2p.txt` is a line shift, a known item, or a wrong mark in the old probe.
- I wrote 73 new probe files (`RT/p/`, about 500 functions) against the lens topics.
  Each probe marks the expected codes with `//~`. `RT/cmp.py` compares the marks with
  `weft check --json`. `RT/probe.sh` checks and runs a file with `--oracle`.
- I confirmed each soundness finding at run time with `weft run|test --unchecked
  --oracle`. Each false positive runs with no oracle fault.
- `weft agree` passes on each repro and probe. So the defects are in fact generation
  (`crates/weft-sema`), and for R3RT1 also in the spec rule for `live_linear`.
- I found 4 blockers, 2 majors and 5 minors. Each finding has a repro in `RT/repro/`.
  `RT/verify.txt` has the output of the checker and of the oracle for each repro.
- The compare binary `/home/user/wt-edge/target/release/weft` (328a39b, before round 2)
  gives the same result for R3RT1, R3RT2, R3RT3, R3RT5, R3RT6, R3RT7, R3RT10 and
  R3RT11. So these were there before round 2, and round 2 did not report them. For
  R3RT4 the old binary also misses the two controls: the later fix of operation
  results (S5a) does not cover a closure parameter. R3RT9 is a regression of round 2
  (one-place instances, R2a).

| Id | Severity | Statement |
| --- | --- | --- |
| R3RT1 | blocker | A move of one part of a linear aggregate ends `live_linear` for the whole local. The other linear parts leak (W0601) and are not checked at an abort (W0602). |
| R3RT2 | blocker | A `match` through a reference binds the payload slot. When the payload is a reference, the binding loses the places that the reference points into (W0301, W0312). |
| R3RT3 | blocker | A call does not give the places of the references behind a reference argument (`&Vec<&T>`, `&(&T, u64)`). W0312 and W0405 miss the overlap. |
| R3RT4 | blocker | A `resume` with a parameter of a closure in the clause gives the operation result no places. The result is never invalid (W0301). |
| R3RT5 | major | A closure that takes its capture by value is still tied to the variable. A returned maker closure is W0204; a closure that outlives a block or a loop iteration is W0301. |
| R3RT6 | major | A callee that mutates a reference argument makes it point into the wildcard place of each other reference argument, also when the types forbid it. With flow-insensitive `points_into`, a helper like `extend(&all, &some)` makes each later use of `all` W0301. |
| R3RT7 | minor | An `in` place on a parameter of an operation has no effect: the aliasing form is W0312 (false positive), and an argument outside the place is W0312, not W0203. |
| R3RT8 | minor | A parameter of type `Scope` or `&Scope` gets "type mismatch: expected `Scope`, found `Scope`". |
| R3RT9 | minor | The W0703 hint gives `mut((w..).hp)`, which does not parse. Before round 2 it gave `mut(w..)`. |
| R3RT10 | minor | A new value of a part that holds a stale reference is W0301: a program cannot refresh the part. |
| R3RT11 | minor | A `match` with no arm on an enum with no variant is W0120. |

## Blockers

### R3RT1: a partial move of a linear aggregate leaks the other parts

Repro: `RT/repro/R3RT1_partial_linear_move.wf`.

```weft
fn tuple_part() {
    let t = (begin(1), begin(2))
    rollback(t.0)
}   // expected W0601: t.1 is not consumed; found: no error
```

- A move of a part (`rollback(t.0)`, `rollback(a[0])`, `rollback(s.a)`, `let x = t.0`,
  a closure that moves `t.0`) gives `moved_at(t, n)` for the whole local and
  `moved_part(t.0, n)` (`crates/weft-sema/src/body/stmt.rs:1667` and `:1681`).
- `spec/weft.dl:229` stops `live_linear(V, Q)` at each `moved_at(V, P)`. It does not
  test `part_moved_at`. So after the part move, the other linear part is not live.
  W0601 does not fire at the end of the scope, and W0602 does not fire at an
  operation that can abort.
- ADR 0003 makes a part move a move of the whole local for W0302. So the program
  cannot consume the other part after the part move. Each partial move of a linear
  aggregate leaks the rest with no error.
- Run time: 6 of 6 tests fail with the oracle ("linear leak", or "`Lock` has no
  `on abort`"). The control (`let (x, y) = t`) passes.
- Fix: let `live_linear` go on through a part move while a linear part is left
  (`!moved_at(V, P)` only for a move of the whole value), or reject a part move out of a
  linear aggregate (W0601 at the move, "destructure it").

### R3RT2: a `match` through a reference loses the places of a held reference

Repro: `RT/repro/R3RT2_match_through_ref.wf`.

```weft
let o = Some(&world.entities[0])
let p = &o
world.entities.clear()
match p { Some(e) => print(e.hp), None => {} }   // expected W0301; found: no error
```

- `match_pattern` (`crates/weft-sema/src/body/expr.rs:1206`) gives a binding through a
  reference (`by_ref`) the places of the payload slot (`o.Some`) and the type `&T`.
  When `T` is a reference, a place below the binding is a place where the stored
  reference points (ADR 0003, `held_refs`). The facts use `o.Some.hp` instead, a place
  of `o`. A change of `world.entities` does not overlap it.
- Missed shapes (each 0 errors): a reference to an `Option`, a field of a reference
  (`match p.x`), a `Result`, an element reference (`&v[0]`), a tuple, a write through
  the binding, and the same binding in a callee (`o: &Option<&Entity>`), where the
  caller gets no W0312.
- A field read through the same reference (`p.x.hp`) and a `let` destructuring are
  found. Only the `match` binding loses the places.
- Run time: 7 of 7 tests fail with the oracle (a read of a freed cell).
- Fix: when the binding is by reference and its type holds references, give it the
  held places of the slot (as a field read through a reference does), or bind the
  stored reference by value.

### R3RT3: a call misses the references behind a reference argument

Repro: `RT/repro/R3RT3_held_refs_at_call.wf`.

```weft
fn read_both(rs: &Vec<&Entity>, w: &World) / mut(w.entities) {
    let e = rs[0]
    w.entities.clear()
    print(e.hp)
}
let rs = Vec.new()
rs.push(&world.entities[0])
read_both(&rs, world)   // expected W0312; found: no error
```

- The callee reads `e` through its own root `*rs` (ADR 0003). That root is separate from
  `w`, so the callee accepts the free. ADR 0003 says: "A caller puts in the places that
  the references in its argument point into." For `mut(rs..)` this holds (a callee that
  clears through `rs[0]` invalidates the reference of the caller).
- For W0312 and W0405 it does not hold. The call gives `call_arg` and `reads_at` for the
  places of the reference argument only (`rs`), not for the places that the references
  in it point into (`crates/weft-sema/src/body/call.rs:813` for an item,
  `call.rs:1855` for a function value). A by-value argument that holds references gets
  them (`value_refs`), and the control `read_val(Some(&world.entities[0]), world)` is
  W0312.
- Missed: W0312 for `&Vec<&T>` and for `&(&T, u64)`; W0405 for a task that calls
  `show_first(&rs)` while the parent clears `world.entities`.
- Run time: 3 of 3 tests fail with the oracle (a read of a freed cell).
- This is not the known item "a reference that a function value gets inside another
  reference" (ADR 0005): the callee here is a function with a body.
- Fix: for a reference argument whose pointee holds references, add the held places
  (`held_refs` of the argument) to `call_arg` and to the reads of the call.

### R3RT4: a `resume` in a closure with the closure parameter gives no places

Repro: `RT/repro/R3RT4_resume_closure_param.wf`.

```weft
handle Pick { fn pick() { let k = |x: &u64| resume(x); k(&v[0]) } } in {
    let r = pick()
    v.clear()
    print(r)   // expected W0301; found: no error
}
```

- A `resume` records the places of its value (`resume_refs_pending`,
  `crates/weft-sema/src/body/call.rs:2356`). `note_resumed_refs`
  (`crates/weft-sema/src/body/oprefs.rs:351`) maps a place below a clause parameter
  onto the arguments of the operation. A place below a parameter of a closure stays as
  it is: the result points into the root of `x`. No node changes that root, so the
  result is never invalid.
- Missed: a direct call of the closure, a higher-order callee that gives the reference
  (`call_with(|x| resume(x), &v[0])`), and a reference into a local of the clause that
  the body keeps after the `handle`.
- A captured reference (`|| resume(x)`) and a direct `resume(&v[0])` are found. A
  function value that a closure parameter gives is found too (stored values).
- Run time: 3 of 3 tests fail with the oracle (a read of a freed cell).
- Fix: map the places below a closure parameter onto the places that each node that
  runs the closure gives to it, as for the clause parameters. Or let the result point
  into the wildcard place of each place that the clause can reach.

## Majors

### R3RT5: a by-value capture is still tied to the variable

Repro: `RT/repro/R3RT5_byvalue_capture_scope.wf`.

```weft
fn mk_release(t: Tx) -> fn() { || release(t) }   // W0204 today; expected: no error
```

- Round 2 (R2b-1, OR2) made a closure that moves a capture take the value when it is
  made. The interpreter moves the value into a cell of the closure (ADR 0003). The
  closure owns the value.
- The checker still gives the closure the places of the variable. So the end of the
  variable invalidates the closure: W0204 for a returned closure ("the by-value parameter
  `b` goes out of scope at the return",
  `crates/weft-sema/src/body/stmt.rs:592`), and W0301 for a closure that outlives a
  block or a loop iteration.
- Run time: the program runs with the oracle and prints `0`, `release 7`, `0`, `0`,
  `0`. No fault.
- Impact: a maker that returns a closure that consumes its argument (a task, a callback
  that owns a buffer, a closure that commits a linear value) cannot be written. The
  same holds for a list of closures that each own a buffer from a loop. Rust accepts
  these with `move`.
- The round-2 probe `f_modes.wf` had these makers (`mk_eat`, `mk_tx`) and got W0204;
  the round-2 report did not record it.
- Fix: a by-value capture must not point into the root of the variable. The closure
  points where the moved value points (its references), as a by-value argument does.

### R3RT6: reference arguments flow into each other against their types

Repro: `RT/repro/R3RT6_ref_arg_flow_fp.wf`.

```weft
fn extend(dst: &Vec<&Entity>, src: &Vec<&Entity>) / mut(dst) { ... dst.push(src[i]) ... }
let all = Vec.new()
let some = Vec.new()
some.push(x)
extend(&all, &some)
print(all.len())   // W0301 today; expected: no error
```

- ADR 0003: "The call can mutate such an argument. Then it can keep the references of
  the other arguments." The caller makes `all` point into `some..`. The type of `dst`
  (`Vec<&Entity>`) cannot hold a reference into `some` (that is a `&&Entity` or a
  `&Vec<&Entity>`). Only the references in `some` can go into `dst`.
- `points_into` is not flow-sensitive. So `all` points into `some..` also before the
  call, and `some.push(x)` before the call invalidates `all`. Each use of `all` after
  the call is W0301.
- The evidence is wrong too: it says `all : &Vec<&Entity> in some..  (line 19)`, the
  line of `let all = Vec.new()`, and `all` is not a reference.
- With `move_one(&a, &b) / mut(a, b)`, both `a` and `b` become unusable.
- Run time: prints `2`, `0`, `2`. No fault.
- Fix: let a mutated argument keep only the references whose type it can hold (the
  held references of the other arguments, not the argument references themselves).
  Give the new places from the call on (a hidden variable, as `fn_store_refs` does for
  closures).

## Minors

### R3RT7: `in` on an operation parameter has no effect

Repro: `RT/repro/R3RT7_op_in_param.wf`.

- `effect Hit { fn hit_op(w: &World, a: &Entity in w.entities[]) }`. A perform
  `hit_op(world, &world.entities[0])` with a clause that writes `a.hp` gets W0312. The
  same call of a function with this signature is accepted (the ADR 0005 workaround).
- `hit_op(world, &world.other[0])` gets W0312, not W0203. A function gets W0203.
- The result is sound, because the clause also sees separate roots. But the stated
  place does not do what it does for a function, and no ADR says so.
- Fix: give the arguments of an operation `arg_at` and `param_in` facts and the root of
  the parameter that names the place, as for a call. Or reject `in` in an operation
  signature and record it.

### R3RT8: `Scope` against `Scope`

Repro: `RT/repro/R3RT8_scope_type_message.wf`.

- The binder `s` has the internal type `Ty::Scope`. A written `Scope` is the prelude
  `extern type Scope`. So `fn submit(s: Scope)` gets "type mismatch: expected `Scope`,
  found `Scope`", and `s.spawn` on a `&Scope` parameter gets "`Scope` has no method
  `spawn`".
- Fix: resolve the written `Scope` to the type of the binder, or say in the message that
  a scope cannot go to a function.

### R3RT9: the W0703 hint does not parse (regression)

Repro: `RT/repro/R3RT9_w0703_hint.wf` and `RT/repro/R3RT9_hint_applied.wf`.

- A write through the result of `find(w, id) -> Option<&Entity>` gets "add
  `mut((w..).hp)` to the effects after `/`". That text is the display of a one-place
  instance (R2a, `one_place`). It does not parse: W0001 "expected a place, found `(`".
  The JSON note has the same text, so a coding agent that applies it fails.
- Commit 328a39b gave `mut(w..)`, which parses.
- The message also names the callee `assign` for an assignment.
- Fix: show the base of the instance with `..` in hints (`mut(w..)`).

### R3RT10: a part that holds a stale reference cannot get a new value

Repro: `RT/repro/R3RT10_part_refresh_fp.wf`.

- `t.1 = &c[0]` after `b.clear()`, with `t = (&a[0], &b[0])`, is W0301 ("`t` used after
  it was invalidated"). The assignment reads nothing, and the later reads are valid.
  The run prints `1` three times.
- ADR 0003 says that a new value of a part replaces the hidden variable of the part.
  The initial value of the tuple is on the local itself, so the new value of the part
  is a use of the whole local.

### R3RT11: an empty `match` on an empty enum

Repro: `RT/repro/R3RT11_empty_enum_match.wf`.

- `enum Never {}` and `match n {}` get W0120 "does not cover every value of `Never`".
  There is no value to cover.

## Round-2 fixes and topics that hold

The probes below give the expected result. File names are in `RT/p/`.

- Owner and scope end (`j1_owner.wf`): a temporary in a `let`, a callee result, a loop
  variable, a `match` temporary, a `while` and an `if` condition, a closure local, a
  generic temporary, a closure argument, a method result and an interpolation.
- Late captures, RR7 (`c1_late.wf`): a new value in another closure, in a clause and in
  a task; a struct argument; nested closures; a loop; a tuple part; an `Option`.
- Argument order and named arguments, RR10 and RR13 (`b1_named.wf`, `b2_named_items.wf`,
  `b3_named_join.wf`, `x1_order.wf`): sema and the interpreter use the same order;
  joins of items through `if`, tuples, parts, `Option` and `Vec` give W0104.
- Function values and joins, RR2 (`t1_once.wf`): `once` through a branch, a generic
  pick, a field, a tuple swap, an `Option` and `Vec.pop`.
- Jumps (`z1_jumps.wf`): a closure and a trailing block in a loop (W0111); a `match` arm
  in a handled body, a clause, a scope and a closure around a `handle` (W0315).
- Tasks (`h1_tasks.wf`, `h2_spawn_stored.wf`, `y1_kept.wf`): references in a `Vec`, a
  closure and a clause that write, a tuple, a join in one branch, a handle in a `Vec`, a
  method read, a loop; stored spawning closures in a field, a generic and a `Vec`; kept
  variables through a closure, an inner closure, a `match`, a callee and a `for`.
- Capability escapes (`g1_cap.wf`, `f1_kesc.wf`, `f2_kesc.wf`): handler capabilities
  through an outer scope task, a scope value, `with_timeout`, a `match`, a loop, an
  `Rc` clone and a generic tuple; continuations through an `Rc`, a `Box`, a `Vec`, a
  wrapper closure, a tuple part, a nested `handle`, a maker closure and a `Weak`.
- Suspension points (`e1_multi.wf` to `e5_spared_byval.wf`): outer moves under a
  `multi` resume through a callee and a loop; `resume` in a closure called twice;
  `spared_at` with a clause that runs a function argument, an outer closure, a nested
  `handle` and an outer `multi` operation; stored closures that suspend; `body_multi` at
  a clause `resume` through a callee and a closure; by-value captures in a body.
- `resume` frees, RR5 (`v1_resume.wf`): a clause that keeps the argument, a move, a push,
  a closure, `resume` in a closure and a nested clause.
- Operation results (`w1_oprefs.wf`, `w3_opfn.wf`, `w4_opargs.wf`): a clause local, a
  tuple, a wrapper, two operations, function values from a closure parameter, and
  clauses that keep reference arguments.
- Effect identities and `pub` (`m1_ident.wf`, `m2_alias.wf`, `RT/pkgA`, `RT/pkgB`):
  module paths, the alias `log`, W0801 for root handlers, authority for an extern call,
  a clause, `sleep`, a returned closure, a generic, `fork` and `scope`; a private effect
  and a private method of a dependency.
- Modes (`o1_fork.wf`, `o2_modes.wf`): W0403 through a tuple, a wrapper, an `Option`, a
  `Vec`, a nested closure and the second branch; W0401 through nested generics, a
  `Weak` field and a raw pointer.
- `!Move` (`n1_immov.wf`): an operation argument, a `resume`, a block, a `handle`, a
  closure, a task result, an `if` and `with_timeout`.
- Generic drops and overwrites (`r1_drops.wf`, `r2_drops.wf`, `r5_lin_match.wf`,
  `r8_lin_ops.wf`, `r9_over.wf`): a generic method, a closure parameter, early return,
  `match _`, shadowing, `detach`; overwrites in a `Box`, an `Rc`, a loop, a clause, a
  task and an array.
- W0120 and W0304 (`d1_exh.wf`, `s1_unset.wf`): a reference scrutinee, nested
  literals, tuples, strings, `Result`, qualified variants; `loop` with `break`, `match`
  arms, a reference to an unset local.
- One-place instances (`k1_instance.wf`): a call in a `while` condition and in a loop
  body.
- References inside values (`i1_refs.wf`, `i3_refholder.wf`, `q2_held.wf`,
  `q4_held_ret.wf`, `q10_held_ret.wf`): generic and stated stores, `Vec` pushes,
  closure results, `Result`, interpolation, field reads through references, returned
  held references and their stated places.

## Known items that I saw again (not reported)

- A reference that a closure or a clause gets inside another reference sees the outer
  place only (ADR 0003, ADR 0005): `q6_held_closure.wf`, `w4_opargs.wf` `keep_held`.
- A function value given to a function value that the body does not know runs in the
  worst way (W0403, ADR 0006): `w3_opfn.wf` `hof_param_fn`.
- A local with no value that a closure, a clause or a task sets (W0304, ADR 0007).
- A `Vec` or an array of linear values has no consumer (W0601, ADR 0007).
- `None` from a generic callee and a struct literal with `None` are not empty values
  (ADR 0007, round 1 item).
- A part move makes the whole local moved for W0302 (ADR 0003, conservative).

## Other observations (no finding)

- A non-`pub` module does not hide its `pub` items from a dependent package
  (`RT/pkgB`). No document defines module privacy.
- A call of a private method of a dependency gives the same W0101 twice at one span.
- A struct pattern in a `match` (`P(0, A)`) gets "this value is not an enum"; `let`
  accepts the same pattern.

## Files

- Repros: `RT/repro/R3RT*.wf`. Results: `RT/verify.txt`.
- Probes: `RT/p/*.wf`, packages `RT/pkgA`, `RT/pkgB`. Regression run of the round-2
  probes: `RT/regress_r2p.txt`.
- Tools: `RT/cmp.py` (marks against `weft check --json`), `RT/probe.sh` (check, then run
  with `--oracle`).
