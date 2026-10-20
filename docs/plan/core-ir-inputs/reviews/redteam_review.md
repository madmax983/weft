## Red-team report: Weft checker soundness

I found 24 distinct issues: 18 unsound (programs accepted that the design rejects), 1 crash, 4 false positives, and a few minor ones. `weft agree` says the checker and `spec/weft.dl` agree on all ~45 probe files. So none of these bugs are in `crates/weft-check/src/rules.rs`. They are in fact generation (`crates/weft-sema/src/body/*`), plus one spec gap (#1). Everything was re-run on a fresh build at 18:45, because other agents were editing sources during the review. I edited nothing in the repo and ran no git. Probe files are in `/tmp/claude-0/redteam/` (crash and nesting probes in `/tmp/claude-0/redteam/crash/`).

The programs below assume this preamble:
`struct Entity { hp: i32 }  struct World { entities: Vec<Entity> }`

### Unsound: the checker accepts what the design rejects

**1. Moving or dropping the owner does not invalidate references into it.** `a01_move_owner.wf`, `a02_scope_dangle.wf`, `a11_rc_drop.wf`, `a15_byvalue_ret.wf`
```weft
fn take(v: Vec<u64>) {}
fn f() { let v = Vec.new(); v.push(1); let r = &v[0]; take(v); print(r) }
fn g() { let r = { let v = Vec.new(); v.push(1); &v[0] }; print(r) }
```
- **Design:** W0301. The memory is freed (or moved: `let w = v; w.push(2)` reallocates).
- **Checker:** nothing.
- **Same bug, other shapes:**
  - `a = Rc.new(..)` or `take_rc(a)` on the last handle, with `r = &a.items[0]` live.
  - `fn bad(v: Vec<u64>) -> &u64 in v[] { &v[0] }`: the caller's `r` gets no places at all.
- **Cause:** the spec has no rule linking `moved_at` or `scope_end` of an owner to invalidation. `consume`/`move_var` and `end_frame` (`stmt.rs`) emit no mutation of the root. An `Rc` handle and its group have different roots. `check_returned_refs` accepts places rooted in by-value parameters. Fixing this needs a spec edit, for example "a move or scope end of V mutates V's root".

**2. Queued uses and reads are written into the wrong node.** `a13_pending.wf`, `a14_pending_branch.wf`
```weft
fn f(world: &World, c: bool) -> i32 / mut(world.entities) {
    let first = &world.entities[0]
    let x = if c { world.entities.push(Entity { hp: 1 }); first.hp } else { print(0); 1 }
    x
}
fn apply2(n: i32, f: fn()) { f() }
fn g(world: &World) / mut(world.entities) {
    let first = &world.entities[0]
    world.entities.push(Entity { hp: 1 })
    apply2(first.hp, || print(1))
}
```
- **Design:** W0301 in both.
- **Checker:** nothing. The facts show `uses(first)` on the else-branch `print` node in `f`, and on the closure's entry node in `g`.
- **Also missed:** a `match` arm whose tail read lands on the next arm's node; `handle .. in first.hp`; and a W0405 (`apply3(stats.count, || ..)` while a task writes `stats.count`).
- **Cause:** `Lower::emit` (`body/mod.rs`) drains `pend_uses`/`pend_reads` into whatever node comes next. That can be another component (`closure()` and handler clauses call `start`) or a sibling branch (`if_expr`/`match_expr` restart from `br`). Pending state needs saving and restoring at these boundaries.

**3. References lose their place through generics, containers and bindings.** `g01_generic.wf`, `a06_containers.wf`, `a07b_returns.wf`, `a05_closure_tuple.wf`, `a12_nested_ref.wf`
```weft
fn id<T>(x: T) -> T { x }
fn f() { let v: Vec<u64> = Vec.new(); v.push(1); let r = id(&v[0]); v.clear(); print(r) }
fn find(v: &Vec<u64>) -> Option<&u64> { Some(&v[0]) }   // no W0204; caller's result has no refs
```
- **Design:** W0301. W0204 for `Option<&u64>`, and also for `fn local_ref() -> Option<&u64>`, which returns a reference to a local.
- **Checker:** nothing.
- **Same bug, other shapes:**
  - `Wrap<T>{x: &v[0]}`. W0605 is also not applied to generic instances.
  - `Box.new(&v[0])`, `rs.push(&..)`, `[&..]`.
  - `let r = f()` where `f = || &world.entities[0]`.
  - A by-value `match o { Some(r) => { mutate; use r } }` on a local `Option<&T>`.
  - `let rt = &t` where `t = (&v[0], 1)`, then `let (a, _) = rt` after `v.clear()`.
- **Cause:**
  - `call_fn` attaches refs only from `sig.ret_places`.
  - `struct_lit`, `ExprKind::Array` and `call_value` return no refs.
  - In `match_pattern`, a by-value `Bind` clones `sval`, which has no refs.
  - In `bind_pattern`, a tuple pattern over `Ty::Ref(Tuple)` uses the outer refs.
  - The W0204 "state its place" check only looks at top-level `&T` and tuples of refs.

**4. An argument's reference is held from after the later arguments run.** `a04_arg_order.wf`
```weft
fn grow(w: &World) -> u64 / mut(w.entities) { w.entities.push(Entity { hp: 1 }); 0 }
fn show(e: &Entity, n: u64) { print(e.hp) }
fn f(world: &World) / mut(world.entities) { show(&world.entities[0], grow(world)) }
```
- **Design:** W0301. The reference is taken before `grow` frees the buffer.
- **Checker:** nothing. Same for `let t = (&world.entities[0], grow(world))`. It works when the reference is a named variable.
- **Cause:** `call_fn` (`call.rs`, the "argument" temporary) binds only after all arguments are evaluated. The tuple-`let` path does the same.

**5. A callee that mutates and then calls a closure argument which captured a reference.** `a10_callee_closure.wf`
```weft
fn apply(f: fn(), w: &World) / mut(w.entities) { w.entities.clear(); f() }
fn g(world: &World) / mut(world.entities) {
    let r = &world.entities[0]
    apply(|| print(r.hp), world)
}
```
- **Design:** W0312, the same as when `r` is passed directly (that case is caught).
- **Checker:** nothing.
- **Cause:** `call_fn` does not add the closure's `points_into` places as `call_arg`, and does not treat the closure as used at the call.

**6. Calling through a fn-item value ignores `mut` effects and aborts.** `a03_fn_item_value.wf`, `e04_if_item.wf`, `l01_linear.wf` (`abort_via_item`)
```weft
fn grow(w: &World) / mut(w.entities) { w.entities.push(Entity { hp: 1 }) }
fn f(world: &World) / mut(world.entities) { let first = &world.entities[0]; let g = grow; g(world); print(first.hp) }
```
- **Design:** W0301. Also W0701 on a `pub fn` doing `let g = grow; g(w)`, W0402 through `@ shared`, and W0602 for `let r = risky; r()` with a linear `Lock` live.
- **Checker:** nothing.
- **Also:** `let g = if c { pure_one } else { api.fetch }; g(1)` in a `/ clock` function hides `net`.
- **Cause:** `call_value` (`call.rs`) for `fty.item` only performs the named effects. It never substitutes `sigs[item].effects.muts` and never calls `abortive`. `if_expr` unifies the fn types and keeps only the first branch's item.

**7. Closure summaries are lost through returns, tuples, `if` and struct fields.** This also defeats the dependency authority check. `e01_effects_hidden.wf`, `a05_closure_tuple.wf`, `/tmp/claude-0/redteam/pkg`
```weft
fn mk() -> fn() { || log.info("hidden") }
fn caller() / clock { let f = mk(); f() }     // W0702 missed
```
- **Also:**
  - `let t = (|| world.entities.push(..), 1); let (h, _) = t; h()`, or a closure chosen by `if`: the mutation is lost and W0301 is missed.
  - A dependency `pub fn parse(t: String) -> fn() -> u64 { || phone_home(t) }` with `phone_home / net` passes `weft deps` with 0 authority errors.
- **Cause:**
  - `call_value` reads `loc.summary` instead of `fty.summary`.
  - `assign_local` does not carry `fn_param`.
  - `summary_to_sig` ignores the effects of closures that escape by return.
  - `package_diags` (`weft-cli/src/package.rs`) only reads pub signatures.

**8. A closure's mode does not follow from what it captures.** `l01_linear.wf`, `l02_linear_more.wf`, `e02_resume_closure.wf`, `t02_fork.wf`, `e07_multi_uniq.wf`
```weft
fn a() { let tx = begin(); let f = || rollback(tx) }                     // W0601 missed: never called
fn b() { handle Log { fn log(m) { let f = || resume(()); f(); f() } } in log("a") }   // W0501 missed
fn twice(f: fn()) { f(); f() }
fn c() { let t = begin(); twice(|| rollback(t)) }                       // linear consumed twice
```
- **Also missed:**
  - `let g = || f(); g(); g()` where `f` is `once` (W0502).
  - `let c = || print(n.v)` with `n: Rc`, then `fork(|| c(), ..)` (W0401).
  - A closure capturing a `@ uniq` part, live across `choose()` (W0503).
- **Cause:**
  - `deep_any`, `is_linear` and `is_nonportable` (`body/mod.rs`) stop at `Ty::Fn`.
  - `resume` and `call_value` push `moved_at` directly instead of calling `move_var`, so `moved_captures` and `closure_is_once` never see it.
  - There is no `once` check when a closure is passed to a `fn()` parameter.

**9. `c += 1` on a reference local is not recorded as a mutation.** `m01_write_through.wf`
```weft
fn f(s: &Stats @ shared) { let c = &s.count; c += 1 }
pub fn g(s: &Stats) { let c = &s.count; c += 1 }
fn h(c: &u64) { c += 1 }
```
- **Design:** W0402 for `f`, W0701 for `g`; `h` mutates its parameter.
- **Checker:** nothing. The interpreter's `CompoundStore` (`machine/exec.rs`) follows references, so it really does write `s.count`.
- **Cause:** `assign` (`stmt.rs`) treats any local `Name` target as a rebind and mutates only `locals[l].root`, which is `None` for references.

**10. Using a reference variable as a value is not a read.** `t01_tasks.wf`, `t04_task_dangle.wf`
```weft
fn f(v: &Vec<u64>) / mut(v), async {
    let r = &v[0]
    scope { s =>
        s.spawn(|| print(r))
        v.clear()
    }
}
```
- **Design:** W0405. The task uses `r` while the parent frees its target.
- **Checker:** nothing. Also missed: `let c = &stats.count`, then `print(c)` in the parent (or in a second task) while a task writes `stats.count`. The field form `r.hp` is caught.
- **Cause:** `name()` (`expr.rs`) records a use but no `read` of `loc.refs`.

**11. `return`/`break` inside closure, `handle` and `scope` bodies disagree with the interpreter.** `c02_return_handle.wf`, `c03_return_scope.wf`, `c01_closure_return.wf`
```weft
fn f(world: &World) / mut(world.entities) {
    let first = &world.entities[0]
    handle Log { fn log(m) { resume(()) } } in { world.entities.push(Entity { hp: 1 }); return }
    print(first.hp)
}
```
- **What happens:** the interpreter compiles closures, handled bodies, clauses and scope bodies as separate code contexts, so `return` leaves only that body and the `print` runs. The checker sends `return` to the function exit and treats the `print` as dead, so W0301 is missed. The same happens with a `scope` body.
- **Side effects:**
  - False positive: `return x` inside a closure is unified with the enclosing function's return type (W0102).
  - `break` inside a closure or scope in a loop is accepted, but the interpreter faults.
  - A `break` out of a scope gives a false W0405 after the loop.
- **Cause:** the `Return` arm in `stmt.rs` uses `exit_node()`, and `Break`/`Continue` use `self.loops`. `closure()`, `handle` and `scope` reset neither.

**12. Tasks: a spawn inside a closure is invisible, and W0314 misses fn items and fn params.** `t06_spawn_closure.wf`, `t03_items.wf`
```weft
fn f(st: &Stats) / mut(st), async {
    scope { s => let sp = || { s.spawn(|| st.count += 1); 0 }; sp(); print(st.count) }
}                                                                 // W0405 missed
fn noter() / Note { note(1) }
fn g() / async { handle Note { fn note(x) { resume(()) } } in { scope { s => s.spawn(noter) } } }   // W0314 missed
```
- **Also missed:** `fork(noter, noter)`, and `s.spawn(|| f())` where `f` is a fn param and the caller passes `|| note(1)` under its own handler.
- **Cause:** `spawned_at` is placed in the closure's component, and `apply_summary` carries no spawns. `start_task` checks W0314 only for closure summaries, and for an item its effects are resolved against the parent's handlers.

**13. A `multi` operation reached through a fn parameter skips W0503.** `e03_multi_passthrough.wf`
```weft
fn run(f: fn() -> bool) -> bool { let t = mint(); let b = f(); spend(t); b }
fn caller() -> bool / Choice { run(|| choose()) }
```
`t` is live across a perform that may resume twice, and nothing is reported. Cause: the `fn_param` branch of `call_value` never calls `multi_node`. A passthrough call should be treated as possibly `multi`.

**14. Linear values are silently dropped.** `l01_linear.wf`, `l02_linear_more.wf`
None of these report W0601:
- `let _ = begin()`
- `let (a, _) = (begin(), begin())`
- `print(begin())`
- `match begin() { _ => {} }`
- `p.tx = begin()`, which drops the old value
- `v[0] = begin()`

Cause: `bind_pattern` does nothing for `Wild`; `print` does not consume its arguments; `assign` to a place of linear type has no "overwritten" check.

**15. `!Move` is not transitive, and self-reference fields are unchecked.** `i01_immovable.wf`
```weft
struct Frame: !Move { buf: [u8; 4], cur: &u8 in self.buf[] }
struct Outer { f: Frame, n: u64 }
fn keep(o: Outer) {}
fn f() { let o = Outer { f: Frame { buf: [1, 2, 3, 4] }, n: 1 }; keep(o) }   // W0604 missed
```
- **Also accepted:**
  - `Vec<Frame>` push (the buffer can grow and move it) and `Option<Frame>` moves.
  - `f.cur = &v[0]`: points outside `self`, and is not invalidated by `v.push`.
  - `print(f.cur)` before `cur` is set; the struct literal may omit place fields.
- **Cause:** `is_immovable` checks only the top-level ADT. Assigning a place-typed field does no check.

**16. A closure can escape its handler except as the direct result.** `h02_escape.wf`
`f = || log("late")` assigned to an outer local inside `handle .. in { .. }`, then `f()` after the handler ends. Also `handle .. in (|| log("x"), 1)` and `v.push(|| log("x"))`. Only the corpus form `handle .. in || log("late")` gives W0313, because the check in `handle()` only tests whether the result type is `Fn`.

**17. `sim.run` used as a value in a library bypasses W0802.** `lib01.wf`, run with `--lib`
`let r = sim.run; r(1, body)` and `apply(sim.run)` are accepted. The check exists only in the `method_call` path to `sim_run`.

**18. A `@ uniq` borrow stays live across `multi` in the hidden loop iterator** (lower severity). `e09_multi_iter2.wf`
`for e in es[] { e.hp += 1; let b = choose() }` with `es: &[Entity] @ uniq` is accepted. The `{iterator}` variable in `for_loop` does not inherit `uniq`/`once`.

### Crash

**19. A static function called with method syntax panics the checker.** `x01_static_as_method.wf`, `x02_static_as_method_args.wf`
```weft
struct Entity { hp: u64 }
impl Entity { fn new() -> Entity { Entity { hp: 1 } } }
fn f(e: Entity) { let x = e.new() }
```
- `e.new()` panics with index out of bounds at `call.rs:298` (`ptys[i]`).
- `e.new(1)` panics with "attempt to subtract with overflow" at `call.rs:257` (`sig.params.len() - first`).
- **Cause:** `call_fn` assumes the receiver maps to parameter 0.

### False positives

**20. Integer-literal elements are forced to `i64` when indexed or iterated.** `b01_intvar.wf`, `f01_doc_vars.wf`
```weft
fn f() -> u64 { let v = Vec.new(); v.push(1); let t = 0; for x in v[] { t += x }; t }
```
This gives W0102 "expected `u64`, found `i64`"; so do `v[0]` and `Some(&v[0])` against `Option<&u64>`. Cause: `place_expr` (Index), `elem_iter` and `borrow` call `inf.resolve`, which defaults `IntVar` to `i64` before `elem_step`. They should use `shallow`.

**21. `weft check` on a package cannot see its dependencies.**
`weft check examples/package` gives W0101 "unknown name `json`/`logger`" on the shipped example, while `http.json.parse` resolves. Cause: `Collector::collect` (`program.rs:425`) inserts dependency modules into `c.prog.mods[1]`, which is the prelude's first nested module (`http`), instead of `c.prog.root`. The CLI test only runs `deps`, so nothing caught this.

**22. A tail `spawn` handle wrapped in `handle` gets W0601.** `t03_items.wf`
`handle Note {..} in { scope { s => s.spawn(..) } }` reports W0601 on `temporary : Task`. The same scope without `handle` is accepted (`noted` in `14_tasks.wf`). Cause: `handle()` rebuilds the result `Val` without its `task`, so `drop_value` sees a linear temporary.

**23. Syntax limits** (minor).
- The design's `extern fn sqlite3_step(stmt: *Stmt)` does not parse; the grammar has no `*T`.
- Nested blocks fail at about 48 levels, against the ~96 levels the grammar documents.
- A flat `1 + 1 + …` chain fails at about 380 terms with "too long or nested too deeply".

### Minor

24.
- **Ignored file markers:** `weft check FILE` ignores `// weft: library` and `// weft: no-runtime`, which only the test harness honors. So `weft check tests/programs/15_library.wf` and `19b_no_runtime_bad.wf` report 0 errors unless you pass `--lib`/`--no-runtime`.
- **W0705 and fn items:** not checked for items, e.g. `with_log(sleeper)` where `with_log` takes `fn() / log` and `sleeper` has `/ clock`.
- **Sticky `uniq`:** a local stays `uniq` after `l = &w[]`, so W0406 is missed (`m03_misc_modes.wf`).
- **Malformed calls accepted:** `s.spawn(5)` and `fork()` are accepted. Named arguments to effect operations bind by position (`op(b: 1, a: 2)`).
- **No definite-assignment or exhaustiveness checks:** `let x: u64` then `x` is accepted, and so is a non-exhaustive `match`.
- **Diagnostic text:**
  - Inferred places print coarsened: W0402 says "mutates `s`" for `s.count`, and W0701 suggests `/ mut(c)` for `c.v`, because `summary_to_sig` builds steps with empty labels.
  - `diagnose.rs:39` adds `&` to holders that are not references (`f : &fn() -> () in …`).
  - "expected `Scope`, found `Scope`".
  - `@ uniq` is not shown in holder types.

### Probes that behaved correctly
- All corpus design examples give their expected results.
- `show(first, grow(world))` with a named reference: W0301.
- A closure captures a reference, then is called after the mutation: W0301 (via the closure's `points_into`).
- References through `if`/`match` results and through destructuring a local tuple: W0301.
- Mutation on a later loop iteration, before `break`, and before `continue`: W0301.
- `-> &T in w.entities[]` callees, `v.get(0)` then `pop`: W0301.
- Box reassignment (field and local), `Rc` mutation via a clone in a struct and via a callee: W0301.
- `Gc` stable deref survives; an enum payload behind `Gc` is invalidated.
- Handler clause mutating via a callee or a closure; `resume` invalidating a clause-held reference; W0312 via a handler reached through a callee.
- A closure made outside a handler escapes to the caller (correct lexical behavior).
- Two different `split_mut` calls overlap (W0405); the two sides of one split stay disjoint.
- W0403 through a closure that captured a shared-mutable reference; W0401 for an `Rc` inside a struct.
- `@ shared` writes via a copy, a callee (declared or inferred), a closure, `get`, a loop, or a split: W0402.
- By-value `self` through a reference: W0303.
- Linear values: consumed in one arm only, skipped by `break`, dropped inside a task closure, moved in a loop: W0601/W0302.
- Recursive private functions reach a fixpoint for effects and muts; extern functions default to `blocking`.
- W0405: parent mutation while a task reads; a task spawned in a loop conflicts with itself; use after `join` is invalidated.
- Deeply nested expressions, types and closures give parser errors, not stack overflows.
- About 30 small malformed programs (`/tmp/claude-0/redteam/crash/`) gave no other panics.
