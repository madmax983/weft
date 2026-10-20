# Review round 2, lens "redteam": targeted attacks

Commit: 328a39b (worktree `/home/user/wt-edge`, branch `review/r2`). I did not change the
worktree. I built `target/release/weft` there. All files of this lens are in
`SCRATCH/r2/redteam/`
(below: `RT/`).

## Summary

- I wrote about 60 probe files (`RT/p/`, about 400 functions) against the round-1 fixes
  and the new features of S3 and S4. Each probe marks the expected codes with `//~`.
  `RT/cmp.py` compares the marks with `weft check --json`.
- I confirmed each unsound finding at run time. I used `weft run|test --unchecked` and
  the instrumented interpreter of the oracle lens
  (`r2/oracle/weft-inst/target/release/weft`). That binary detects dangling references,
  linear leaks and data races.
- I found 10 blockers, 1 major and 4 minors. Each finding has one repro file in
  `RT/repro/`. `RT/verify.txt` has the output of the checker and of both interpreters
  for each repro.
- `weft agree` passes on every probe file. So all the defects are in fact generation
  (`crates/weft-sema`) or in the interpreter, not in `rules.rs` or `spec/weft.dl`.
- I did not report again the known items (round1b_tasks.md "From S3/S4", the open lists
  of ADR 0003, 0005, 0006 and 0007) or the oracle findings OR1 to OR11. RR7 has the same
  cause as OR2, but it is a different shape (a new value, not a move).

| Id | Severity | Statement |
| --- | --- | --- |
| RR1 | blocker | The loop lowering stops after 8 passes. A chain of locals loses references, function values and tasks. |
| RR2 | blocker | A function type carries one closure summary. Later closures in an array, a `Vec`, an `Option` or a generic field are lost. |
| RR3 | blocker | A closure that resumes a continuation can leave its clause. A later call resumes a dropped continuation. |
| RR4 | blocker | A closure that captures the scope capability `s` can leave the scope. Its task outlives the scope and its frame. |
| RR5 | blocker | `resume` carries the mutations of the handled body to the clause, but not its frees (moves). |
| RR6 | blocker | A function value that a clause gives with `resume` is called in the handled body with no summary. |
| RR7 | blocker | A closure keeps the places, the summary and the modes of a captured variable from where it is made. A later new value is lost. |
| RR8 | blocker | `Vec.clear` drops linear elements, and no rule sees it. |
| RR9 | blocker | A generic function item given as a function value drops a linear value. Its `drops` part is not applied. |
| RR10 | blocker | Named arguments: sema binds by name, the interpreter binds by position, for a method call on a value and for a call of a function item value. |
| RR11 | major | An effect of another module or package has no name outside it. The caller cannot handle it or state it. |
| RR12 | minor | W0304 false positive: a closure, a clause or a task that gives a `let x: T` local its value. |
| RR13 | minor | Named arguments to a positional constructor and to a closure bind by position, also an unknown name. |
| RR14 | minor | The interpreter does not check the width of an unsigned local or result: `2 - 10` on `u64` gives -8. |
| RR15 | minor | An operation with the name of a prelude function cannot be called by its bare name, and nothing says so. |

## Blockers

### RR1: the loop fixpoint stops after eight passes

Repro: `RT/repro/RR1_loop_chain.wf`.

```weft
let r0 = &d[0]  ...  let r9 = &d[0]
while m < 12 {
    r0 = r1
    ...
    r8 = r9
    r9 = &world.entities[0].hp
    m += 1
}
world.entities.clear()
print(r0)            // expected W0301; no error
```

- `lower_loop` (`crates/weft-sema/src/body/stmt.rs:806`) has `MAX_LOOP_PASSES = 8`. After
  8 passes, "the values of the last pass stay". The comment says that a chain of locals
  needs one pass for each local. ADR 0003 gives a soundness argument for a reference that
  goes deeper in each pass (`cur = &cur.next[0]`). That argument does not cover a chain.
- A chain of 10 locals that rotate their values needs 10 passes. The places of `r9` do
  not reach `r0`. With 7 locals, the checker finds the error. With 8 or more, it does not.
- The same hole holds for function values (`fn_chain`: the closure that pushes reaches
  `f0` after 10 passes, W0301 is missed) and for task closures (`task_chain`: W0405 is
  missed).
- Run time: each test faults with the instrumented interpreter (a dangling reference, a
  data race).
- Fix: iterate until the carried values are stable. The values are in a finite lattice
  (the places, closures and tasks of the body), so the loop stops. If a bound must stay,
  report an error (as W0704 and W0706 do) when it is reached. Do not keep a partial value.

### RR2: a function type carries one closure summary

Repro: `RT/repro/RR2_one_summary.wf`.

```weft
let a = [|| print(1), || world.entities.clear()]
let g = a[1]
g()
print(first.hp)      // expected W0301; no error
```

- `FnTy.summary` (`crates/weft-sema/src/types.rs:75`) is one `Option<usize>`. When two
  closures unify in one type, the type keeps the first summary. A call of a value of that
  type runs only the first closure.
- Missed shapes, all with 0 errors:
  - the second element of an array literal or of a `Vec` (two `push` calls);
  - an element assignment `a[0] = || ...`;
  - a new value of an `Option` local (`o = Some(|| ...)`);
  - a new value of a field of a generic struct (`w.x = || ...`, `Wrap<T>`).
    The same assignment to a field of type `fn()` is found.
- The lost closure loses its mutations (W0301), its task writes (W0405, `task_second`),
  and its `once` mode (W0502, `once_second`: a second call eats a moved `Buf`).
- If the order changes (the mutating closure first), the checker finds the error. So the
  result depends on the order of the elements.
- Run time: 6 of 7 tests fault with the stock interpreter, all 7 with the instrumented one.
- Fix: keep a set of summaries for a function value (as `join_val` does for an `if`), or
  keep the summaries on the value (`Val`) and on each holder of a container. The modes
  (`once`, linear, nonportable, `uniq`) must join the same way.

### RR3: a continuation leaves its clause

Repro: `RT/repro/RR3_continuation_escape.wf`.

```weft
let k = || print(0)
handle Note { fn note(x) { k = || resume(()) } } in note(1)
k()                  // runtime error: a continuation was resumed after it was dropped
```

- A closure that calls `resume` is a `once` value. Nothing stops it from leaving the
  clause: through a local outside the `handle`, a field of a generic struct, an
  `Option`, or as the value of the `handle` (`as_handle_value`).
- W0313 checks capabilities of handlers only. W0501 and W0502 count calls only. The
  continuation is not a capability in the facts.
- The clause does not resume, so the handler drops the continuation and the `handle`
  ends. A later call resumes the dropped continuation. E2 (one-shot safety) and the
  design rule "a handler may resume at most once" assume this cannot happen.
- Run time: all 4 tests fault with both interpreters.
- A field of type `fn()` gets W0502 by chance (a plain-data place). That is not the
  cause.
- Fix: treat a continuation as a capability of its clause. A closure that resumes must
  not leave the clause (the W0313 rules with the clause as the body).

### RR4: the scope capability leaves the scope

Repro: `RT/repro/RR4_scope_escape.wf`.

```weft
fn escape(st: &Stats) / mut(st), async {
    let keep = || print(0)
    scope { s => keep = || { s.spawn(|| st.count += 1); () } }
    keep()           // spawns a task into a scope that ended
}
```

- A closure that captures `s` does not point into the root of `s` (see the facts of
  `escape`: the closure local points only into `st`). So the end of `s` does not
  invalidate the closure. A closure that captures `&s` gets W0301.
- The task starts after its scope ended. No scope joins it. It outlives the frame of
  `escape`, and `caller` frees `st` before the task runs.
- Run time: the stock interpreter prints "task runs, count 1" after `caller` ended (a
  write to a dead local). The instrumented interpreter reports a dangling reference.
- The same holds for the scope value (`let k = scope { s => || s.spawn(..) }`) and for a
  field of a local outside the scope.
- This breaks the design rule "children can't outlive the scope".
- Fix: a capture of `s` must point into the root of `s` (as a capture of `&s` does), or
  `Scope` must not be plain data for captures.

### RR5: `resume` does not carry frees

Repro: `RT/repro/RR5_resume_free.wf`.

```weft
handle Note {
    fn note(x) {
        let r = &world.entities[0]
        resume(())
        print(r.hp)      // expected W0301; no error
    }
} in {
    note(1)
    take_w(world)        // moves `world`
}
```

- ADR 0005: "A resume runs the handled computation." A mutation there invalidates the
  clause reference (the control `cleared_in_body` gets W0301). A move of the owner in
  the handled body does not.
- Run time: the test faults with both interpreters.
- Fix: a `resume` node must carry the `frees_at` of the handled body, as it carries its
  mutations.

### RR6: a function value that `resume` gives has no summary

Repro: `RT/repro/RR6_resume_fn_value.wf`.

```weft
handle Get { fn get() { resume(|| world.entities.clear()) } } in {
    let f = get()
    f()
    print(first.hp)      // expected W0301; no error
}
```

- The result of the operation is a function value. Its call in the handled body does
  not do what the closure does. The same holds inside a tuple (`in_tuple`).
- ADR 0005 records the open item for a reference in the result ("the clauses that give
  it are lowered after the handled body"). It claims that the result carries the
  capabilities of these function values (W0313). It does not say that their mutations,
  effects and modes are lost.
- Run time: both tests fault with both interpreters.
- Fix: lower the clauses before the handled body for the values that `resume` gives,
  or iterate (the handled body, then the clauses, then the handled body again). As a
  minimum, treat the result as an unknown function value that can run each closure of
  the clauses, and add the item to the ADR 0005 list.

### RR7: a closure keeps the old value of a captured variable

Repro: `RT/repro/RR7_late_capture.wf`.

```weft
let r = d
let f = || print(r.hp)
r = &world.entities[0]
world.entities.clear()
f()                      // expected W0301; no error
```

- ADR 0003: "A closure refers to the variables that it captures, as the interpreter
  captures their cells." The lowering takes the places, the summary and the modes of
  each capture where the closure is made. A new value of the variable after that point
  does not reach the closure.
- Missed codes, all with 0 errors:
  - W0301: a captured reference (`late_ref`), also through a higher-order callee
    (`late_ref_hof`);
  - W0405: a task reads the captured reference after the parent clears its new target
    (`late_ref_task`);
  - W0301: a captured function variable gets a closure that mutates (`late_fn`);
  - W0502: a captured function variable gets a `once` closure (`late_once`);
  - W0402: a captured reference gets a `@ shared` place (`late_shared`);
  - W0406: a captured `@ uniq` variable gets an aliased value (`late_alias`).
- OR2 (oracle lens) has the same cause for a move. This is the other side: a new value.
- Run time: 5 of 5 run-time tests fault with both interpreters.
- Fix: a closure that captures a variable must see the values of the variable at each
  node where the closure runs, not only where it is made. One way: at each node that runs
  the closure, join the current places, summaries and modes of its captured variables
  (the lowering already re-applies a closure at the nodes where it runs). Another way:
  make the variable flow-insensitive for closures that capture it (join all its values).

### RR8: `Vec.clear` drops linear values

Repro: `RT/repro/RR8_vec_clear.wf`.

```weft
fn reset(v: &Vec<Tx>) / mut(v) {
    v.clear()            // expected W0601; no error
}
```

- `clear(self) / mut(self)` in `std/prelude.wf` drops each element. It has no parameter
  of the element type, so the `drops` rules of ADR 0007 do not see it. A generic callee
  `clear_any<T>(v: &Vec<T>)` that clears has the same hole (`reset_generic`).
- `v.pop()` as a statement gets W0601 (the temporary is dropped). `clear` does not.
- The known item "a Vec of linear values has no consumer" makes a local `Vec<Tx>` W0601
  at its end. That does not cover `reset`: it is accepted, and a caller that gives the
  `Vec` on (here to an `extern fn`) is accepted too.
- Run time: the instrumented interpreter reports a linear leak in `reset`. The stock
  interpreter has no leak check.
- Fix: give `clear` (and each prelude function that drops elements) a `drops` part for
  the element type parameter. A call on a `Vec` of a linear type is then W0601.

### RR9: a generic item as a function value drops a linear value

Repro: `RT/repro/RR9_generic_item_drops.wf`.

```weft
fn sink<T>(x: T) {}
fn feed_tx(x: Tx, f: fn(Tx)) { f(x) }
feed_tx(begin(), sink)   // expected W0601; no error
```

- `sink(begin())` and `let g = sink; g(begin())` get W0601. `sink` given to a parameter
  of type `fn(Tx)` or `fn(T)`, directly or through a local, does not.
- The `drops` check runs at a direct call of the item. An item value with an inferred
  type argument that is linear does not get it.
- Run time: all 3 tests fault with the instrumented interpreter (a linear leak).
- Fix: when a generic item becomes a function value, check its `drops` part against the
  inferred type arguments (W0601 at the item value), as at a call.

### RR10: named arguments bind differently in sema and in the interpreter

Repro: `RT/repro/RR10_named_args.wf`.

```weft
fn show(e: &Entity, n: i32) { print("e.hp = {e.hp}") }
let h = show
h(n: 5, e: &y)           // checks; run time: "this value has no field `hp`"
print(x.diff(b: 10, a: 3))   // sema: 3 - 10; run time: 10 - 3
```

- Sema binds named arguments by name for a method call on a value receiver and for a
  call of a function item value. The interpreter compiles both with `args` (written
  order, by position) and `Op::CallMethod` or `Op::CallValue`
  (`crates/weft-interp/src/compile.rs`, `method_call`, `call`). A direct call of an item
  and an operation use slots by name on both sides (the RT24 fix).
- The checked program gets the wrong value in each parameter. Here an `&Entity`
  parameter gets an `i32`, and the run faults. W0301 and W0312 also reason about an order
  and a binding that the run does not use.
- Fix: compile these calls with the slot logic of `call_fn` (the callee is known for an
  item value and for a method with a known receiver type). Or reject a named argument
  where the callee is not known statically.

## Major

### RR11: an effect of another module has no name outside it

Repros: `RT/repro/RR11_module_effect.wf`, the package `RT/repro/RR11_pkg/`.

```weft
mod a {
    pub effect Note { fn note(x: u64) }
    pub fn f() / Note { note(1) }
}
fn main() {
    handle Note { fn note(x) { print(x); resume(()) } } in a.f()   // W0101, W0805
}
fn g() / Note { a.f() }                                            // W0101, W0702
```

- `handle` takes one `NAME`, a row item is one `NAME` (`docs/grammar.md`), and the lookup
  is in the current module. `handle a.Note` and `/ a.Note` do not parse.
- So code outside the module cannot handle the effect and cannot state it. A caller
  with a signature cannot call `a.f`. `main` cannot handle it (W0805). The same holds
  for a dependency: `util.noting()` in `RR11_pkg` cannot be handled.
- ADR 0005 says: "A user effect of a dependency needs a handler of the caller, not
  authority." The caller cannot write that handler.
- The hints give fixes that do not compile: "add `Note` to the effects" (W0101), "handle
  `main.a.Log` in `main`" (not syntax).
- Fix: allow a path in `handle` and in a row (`handle util.Note`, `/ util.Note`), and
  resolve it like a type path. Or record the limit in ADR 0005 and in the hints.

## Minors

### RR12: W0304 for a local that a closure, a clause or a task sets

Repro: `RT/repro/RR12_unset_closure.wf`.

- `let x: u64; let f = || { x = 1 }; f(); print(x)` gets W0304 twice: where the closure
  is made, and at `print`. The same holds for a handler clause and for a task that the
  scope joins. The program runs and prints 1, 7 and 3.
- Rust rejects the closure form too, so this can be a choice. ADR 0007 says that a
  closure reads a place field where it is made. It does not say this for a local that
  only gets its value in the closure. Document it, or make the closure an assignment at
  each node where it runs.

### RR13: named arguments to a constructor or a closure bind by position

Repro: `RT/repro/RR13_named_ctor.wf`.

- `Range(hi: 10, lo: 2)` makes `lo = 10` and `hi = 2`. `Range(nope: 2, other: 10)` is
  accepted. `f(b: 10, a: 3)` on a closure gives `a = 10`. Sema and the interpreter agree,
  so nothing faults, but the same text means another thing for a function call.
- Fix: bind by name, or reject a named argument (W0103 or W0104) where no names exist.

### RR14: the interpreter does not check integer widths in locals and results

Repro: `RT/repro/RR14_int_width.wf`.

- `print(a - b)` with `a: u64 = 2`, `b: u64 = 10` prints -8. `250 + 10` on `u8` prints
  260. The check exists only where a field or a parameter gets the value
  (`exec.rs:653`, `exec.rs:899`).
- So `weft run` does not show an overflow that the types forbid. The interpreter is a
  weaker oracle for integer code (see also OR11).

### RR15: an operation with the name of a prelude function is shadowed

Repro: `RT/repro/RR15_op_shadowed.wf`.

- `effect Nap { fn sleep(d: Duration) }`: a bare `sleep(1.ms)` calls the prelude
  `sleep` (Clock) in sema and in the interpreter. The clause never runs, and `napper`
  gets W0702 for `Clock`. `print` behaves the same way.
- Fix: W0107 for an operation that a prelude function hides, or a warning.

## Round-1 fixes that hold

I attacked each fix with new shapes. These probes give the expected result
(`RT/p/`):

- Owner and scope end (`a_owner.wf`, `a_owner2.wf`): a temporary, a loop-body local, a
  by-value match binding, moves by assignment, by destructuring, into a tuple, an
  `Option`, a `Box`, a closure and a task, the value of a block, a scope, a clause and a
  handled body, a self-reference copied out of a `!Move` struct, a `Vec` of references
  and a tuple part. All W0301 or W0204.
- Closures that give an outer reference local a place below their own locals, or below
  a place that the caller then clears (`zz_keep.wf`): all W0301.
- Reads through references for W0405 (`c_reads.wf`): interpolation, comparison,
  arithmetic, a by-value argument, a generic, a `match`, an `if` and a `while`
  condition, in the parent and in the task. All W0405.
- Argument order (`b_order.wf`, `zz_argmove.wf`, `zz_oporder.wf`): named arguments of a
  direct call and of an operation, struct literals, arrays and a reference followed by a
  move. Sema and the interpreter agree (except RR10).
- Function values (`e_fnvals.wf`, `e_fnvals2.wf`, `zz_selfrec.wf`): a field, `Vec.pop`,
  `Option` of an item, an item given to a higher-order callee, a storing callee, a
  generic, a tuple returned by a closure, an `Rc`, recursion, and a closure that calls
  itself. All W0301 (except RR2 and RR7).
- Jumps (`r_jumps.wf`): trailing blocks, `with_timeout`, a `match` arm in a clause, a
  closure in a clause, a clause in a closure, a `break` in an `if` condition in a scope,
  a `break` in a `while` condition. W0111 and W0315 are right, and the interpreter
  agrees on the target of a `break` in a `while` condition.
- Capability escapes (`t_cap.wf`): an `Rc` clone, a `Weak` upgrade, a generic field, an
  `Option`, a task result and a `Box`. All W0313. The miss `inner_clause_keeps` is the
  known open item.
- Suspension points (`h_multi.wf`, `w_susp.wf`, `y_cancel.wf`): item values, an `Option`
  of an item, a field closure, a linear closure, a typed parameter row (W0705),
  `with_timeout`, a handled body that reaches `choose` through an item, a callee or a
  field, a clause that resumes in a loop, a nested `handle` around `resume`, and task
  cancellation. All found.
- Forwarding and W0801 (`i_lib.wf`, `i_lib2.wf`): a clause that performs another standard
  effect, a clause that performs the user `Log`, a dead closure, `Async`, and `sim.run`
  through a generic. Forwarding through a callee, a called closure and a higher-order
  callee is accepted.
- Effect identities (`j_ident1.wf` to `j_ident4.wf`, `zz_ident_mod.wf`): user effects
  named `Clock`, `Log` and `Rand` with standard operation names, and a module effect
  under a root handler of the same name. Sema and the interpreter agree.
- `pub` across units (`p/pkg1/`): a private method, function, nested function and item
  value of a dependency. All W0101.
- `!Move` and the type-property table (`l_immov.wf`, `m_props.wf`): a returned local,
  `Box.new` and `Some` of a named value, a generic field, an array, an enum payload, a
  closure, a generic identity, `Vec.push` of a call result, a tuple, a field read and an
  element assignment. Linear and nonportable through a recursive generic enum, mutual
  recursion, nested generics and `Result`. A phantom type parameter stays plain.
- Closure modes (`f_modes.wf`, `zz_modes_vec.wf`, `x_uniq.wf`): `once` through a generic,
  an `Option`, a tuple and a nested closure; nonportable through a nested closure, a
  struct with an `Rc`, a `Weak` and a generic; copies of a `@ uniq` reference in fork
  branches. All found (except RR2 and RR7).
- Generic drops (`n_drops.wf`): `pop` as a statement, a branch, an early `return`, a
  loop, a generic method. All W0601 (except RR8 and RR9).
- Overwrites (`o_over.wf`): a whole struct, a nested field, a nested part, a field of a
  by-value parameter, a tuple part, an array element, a loop, a variant payload, a
  closure, a generic field and an `Rc` field. All W0601.
- W0304 (`p_unset.wf`): loops, `for`, `while`, branches, `match`, shadowing, a tuple and a
  reference. Right, except RR12.
- W0120 (`q_exh.wf`, `q_big.wf`): tuples of `bool`, nested `Option`, integers, strings,
  mixed tuples, nested `Result`, enums and references. All found. A large exhaustive
  match is accepted fast.
- References inside values (`u_refs.wf`): a generic tuple, a stated `Option` place, a
  user callee that keeps a reference, a generic choice, a generic wrapper, nested
  `Option`, `Vec` of `Option`, `Result`, `Box`, `Rc`, a closure parameter and a tuple in
  a `Vec`. All W0301 or W0312.
- References held across `resume` with a mutation in the handled body
  (`zz_resume_inv.wf`): W0301 (except RR5).

## Known items that I saw again (not reported)

- W0313: a clause of a handler inside the body that keeps its function parameter
  (ADR 0005).
- W0314: a task that gets its function value from a place behind a reference
  (`zz_taskeff.wf` `via_field`, `via_vec`; ADR 0005).
- W0402 inside a higher-order function (`zz_shared.wf` `param_cb`; ADR 0005).
- A reference in the result of an operation (`v_resume.wf` `resume_ref`; ADR 0005).
- W0701 with an empty row for a public higher-order function (`k_w0701.wf`; S5 F13).
- Whole-local accesses for W0405 (`p_unset.wf` `task_not_joined_reads`; OR8).

## Files

- Repros: `RT/repro/RR*.wf` and `RT/repro/RR11_pkg/`.
- Results of the repros: `RT/verify.txt`.
- Probes: `RT/p/*.wf`. Tools: `RT/cmp.py` (marks against `weft check --json`) and
  `RT/probe.sh` (check and run with both interpreters).
