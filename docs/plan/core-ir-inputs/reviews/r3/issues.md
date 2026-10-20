# Round 3: findings for GitHub issues

Status: triage of the round-3 findings that the ship rule does not let block the PR.
Date: 2026-10-20. Source: `/home/user/wt-core`, branch `review/s5`, HEAD `b25faf0` (after R3a).
Each repro ran again at this HEAD with the release CLI. Each finding below still reproduces.

Rules (`scratchpad/ship_rule.md`): a realistic soundness blocker blocks the PR. These do not:

- `soundness-edge`: exotic combinations and contrived shapes;
- `precision`: false positives and imprecision;
- `quality`: minor items, docs, messages, speed.

The column "site" tells where the fix lives:

- `ir`: fact generation in `crates/weft-sema/src/body/`. The core IR replaces that code.
  Check the item again on the IR. Do not fix it in `body/`.
- `durable`: the interpreter, the spec, `rules.rs`, `program.rs`, `props.rs`, diagnostics,
  docs, proofs or the CLI. The IR does not change it.

R3 below is `SCRATCH/r3`.
The report of each lens is `R3/<lens>.md`. The fix proposals of the round-3 plan are in the
paragraphs.

## Index

| Id | Label | Severity | Site | Title |
| --- | --- | --- | --- | --- |
| R3RT4 | soundness-edge | blocker (edge) | ir | A `resume` inside a closure with the closure parameter gives no places |
| I3-8 | soundness-edge | minor | ir (the W0503 rule) | A `multi` operation in a scope body after a spawn |
| I3-6 | soundness-edge | minor | durable | `sim.clock.advance` moves the clock of the whole run |
| I3-7 | soundness-edge | minor | durable | The order in `sim.run` depends on `--seed` |
| R3RT5 | precision | major | ir | A by-value capture is still tied to the variable |
| R3RT6 | precision | major | ir | Reference arguments flow into each other against their types |
| O3-7 | precision | major (regression of R2d) | ir | W0312 on an operation with one closure argument |
| O3-8 | precision | major | ir | A closure with its own `multi` handler is a `multi` and abort point |
| O3-9 | precision | major | ir | Joins that the body does not see |
| Q3-3 | precision | major | durable | A bare variant name resolves to the first enum that has the name |
| O3-10 | precision | minor (regression of R2c) | ir | Two spawns of function parameters get W0503 |
| O3-11 | precision | minor | ir | A move, then a new value of a variable that a closure captures |
| O3-12 | precision | minor | ir | A clause conflicts with its own task |
| F3-11 | precision | minor | ir | A closure that gives a captured reference a new value |
| R3RT7 | precision | minor | ir | `in` on an operation parameter has no effect |
| R3RT10 | precision | minor | ir | A part that holds a stale reference cannot get a new value |
| R3RT11 | precision | minor | durable | An empty `match` on an empty enum is W0120 |
| Q3-2 | quality | major (speed) | ir | `closure_has` is exponential in closures that call closures |
| I3-5 | quality | minor | durable | `Rc` counts: a moved capture and a detached result are not dropped |
| I3-9 | quality | minor (docs) | durable | The handler at a `join`, and the time of a raise after a resume |
| I3-10 | quality | minor | durable | `http.serve` and the virtual clock |
| I3-11 | quality | minor | durable | An inline recursive enum is copied at each move |
| R3RT8 | quality | minor | durable | `Scope` against `Scope` |
| R3RT9 | quality | minor (regression of R2a) | durable | The W0703 hint does not parse |
| F3-10 | quality | minor (docs) | durable | ADR 0006 has a stale claim about the mode lattice |
| F3-12 | quality | minor (docs) | durable | ADR 0002 gives W0118 the reason of a declaration check |
| F3-13 | quality | minor (docs) | durable | Wrong tests in `docs/traceability.md` |
| F3-14 | quality | minor (docs) | durable | Design standard library items with no record |
| I3-13 | quality | minor (docs, proofs) | durable | Proof documents and the link mutation script |
| N1 | quality | minor (new at b25faf0) | ir | A second W0602 for the hidden drop variable of `detach` |

## soundness-edge

### R3RT4: a `resume` inside a closure with the closure parameter gives no places

Repro: `R3/redteam/repro/R3RT4_resume_closure_param.wf`
(`weft test --unchecked --oracle`). Site: ir (`crates/weft-sema/src/body/oprefs.rs`,
`note_resumed_refs`).

Tag: edge. The shape needs an operation that returns a reference, a closure that the clause
makes, and a `resume` inside that closure with the closure parameter. The checker accepts
three tests, and each faults with the oracle (a read of a freed cell):
`let k = |x: &u64| resume(x); k(&v[0])`, `call_with(|x| resume(x), &v[0])`, and a reference
into a local of the clause that the body keeps after the `handle`. `note_resumed_refs` maps a
place below a clause parameter onto the operation arguments. A place below a parameter of a
closure inside the clause stays in the root of that closure, and no node frees that root.
The controls (a captured reference, a direct `resume(&v[0])`) get W0301 at lines 45 and 53.
Proposal: map the places below a closure parameter onto the places that each node that runs
the closure gives it. Where that node is not known, let the operation result point into the
wildcard place of each reference place that the clause can reach. On the IR, a closure is a
body and a `resume` is a terminator, so check this shape again there (root_causes.md, INNER).

### I3-8: a `multi` operation in a scope body after a spawn

Repro: `R3/interp/repro/i3_8_multi_scope_fail.wf`. Site: ir (the W0503 rule is a
fact-generation shape). The other fix, one scope record for each copy in the interpreter, is
durable.

Tag: edge. The shape needs a `multi` operation of a handler outside a scope, performed in
the scope body after a spawn into that scope. The checker accepts it (0 errors).
`copy_frames` clones the `Scope` frame, so the two copies share one `ScopeRec`. The first copy
raises the failure of the child (`caught: child failed`). The second copy ends the scope
normally (`scope ended normally`), although its child failed. Proposal (sound): a scope with
children cannot be copied, so a `multi` node in a scope body that a spawn into that scope can
come before is W0503 for the scope, as for a task handle. Add the scope to the list of values
that are not `many` in ADR 0005 and ADR 0007.

### I3-6: `sim.clock.advance` moves the clock of the whole run

Repro: `R3/interp/repro/i3_6_sim_advance_outside.wf` (`weft test --oracle`) and
`R3/interp/repro/i3_6_advance_no_sim.wf` (`weft run --oracle`). Site: durable
(`crates/weft-interp/src/machine/natives.rs`, `SimAdvance`).

Tag: edge. `SimAdvance` adds to `Machine::now`, the clock of the run. A task outside the
simulation that sleeps 20 ms wakes at `30001ms` after the simulation advances 30 s. A
`with_timeout(1.s)` outside the simulation times out (`caught: timeout at 30s`). ADR 0010
says that a task outside a simulation sees the clock of the run. Also, `sim.clock.advance`,
`sim.net.partition` and `sim.net.heal` run outside any `sim.run` (`now 5s`, 0 errors).
Proposal: each simulation has its own clock offset, which `advance` changes, and it fires only
the timers of its own tasks. A `sim.*` call outside a simulation is a run-time fault with a
clear message.

### I3-7: the order in `sim.run` depends on `--seed`

Repro: `R3/interp/repro/i3_7_nested_sim.wf` and `R3/interp/repro/i3_7_sim_join_outside.wf`
(see `R3/interp/repro/run_all.sh`, section I3-7). Site: durable
(`crates/weft-interp/src/machine/mod.rs`, `pick`).

Tag: edge. `pick` treats each simulation with a ready task as one choice of the machine. A
`sim.run(seed: 7)` inside a task of a `sim.run(seed: 5)` gives four different orders for
`--seed 0` to `3`. A simulation that joins a task of an outer scope prints `joined` at a
place that changes with `--seed` and `--workers`. ADR 0010 says that the order inside a
simulation depends only on its seed and its workers. So a failing seed does not replay.
Proposal: the scheduler of the outer simulation schedules an inner simulation. Record in
ADR 0010 that a join of a task outside the simulation makes the order depend on the run, or
make it a run-time fault.

## precision

### R3RT5: a by-value capture is still tied to the variable

Repro: `R3/redteam/repro/R3RT5_byvalue_capture_scope.wf` (`weft run --unchecked --oracle`
runs clean). Site: ir (`crates/weft-sema/src/body/stmt.rs`, about line 592).

Tag: realistic. `fn mk_release(t: Tx) -> fn() { || release(t) }` is W0204 ("the by-value
parameter `t` of `mk_release` goes out of scope at the return"). A closure that outlives a
block or a loop iteration is W0301. Since R2b (OR2) a closure that moves a capture owns the
value, in the interpreter and in ADR 0003. So a maker that returns a closure that consumes its
argument cannot be written. At b25faf0: W0204 at 16, 17, 18 and W0301 at 27, 38. Proposal: a
by-value capture does not point into the root of the variable. The closure points where the
references of the moved value point, as a by-value argument does, and it keeps its `once` and
linear modes. Keep W0204 and W0301 for a capture by reference, and for a by-value capture
whose value holds a reference into a local. The IR has one capture rule (root_causes.md, ENV),
so check this there.

### R3RT6: reference arguments flow into each other against their types

Repro: `R3/redteam/repro/R3RT6_ref_arg_flow_fp.wf` (runs clean and prints 2, 0, 2).
Site: ir (`crates/weft-sema/src/body/call.rs`), with ADR 0003.

Tag: realistic. `extend(&all, &some)` with `/ mut(dst)` makes `all` point into `some..`, also
before the call, because `points_into` has no node. So `some.push(x)` before the call
invalidates `all`, and each later use is W0301 (line 23). `move_one(&a, &b) / mut(a, b)` makes
both locals unusable (lines 31, 32). The evidence names the line of the `let` and a type that
is not a reference. Proposal: a mutated argument keeps only the held references of the other
arguments, and a reference into another argument only if its type can hold a reference to
the pointee type. The new places hold from the call node on, in a hidden variable, as
`fn_store_refs` does for closures. Keep the ADR 0003 bad case `rs.push(&x)`;
`tests/programs/107_held_refs.wf` and `95_stated_refs.wf` must not change. A flow-sensitive
`points_into` is a change of the spec (root_causes.md, STATE).

### O3-7: W0312 on an operation with one closure argument

Repro: `R3/oracle/repro/O3-7_fp_op_closure_w0312.wf`. Site: ir (the clause footprint at a
perform). Regression of R2d (`ee68916`).

Tag: realistic. `handle Run { fn run(f) { f(); resume(()) } } in { run(|| v.push(5)) }` is
W0312 at line 16 ("`run` mutates `v` while another argument points into `v`"), but the
operation has one argument. The derivation pairs `call_mut(run, v, roots::clause)` from the
clause footprint (what the closure does) with `call_arg(run, v, roots::fn_arg)` (the closure).
The same closure given to a function is accepted. Proposal: the part of the clause footprint
that comes from a run of a function argument of the operation gets the root of that argument
(`roots::fn_arg(i)`), as for a function call (ADR 0005, `Reach::known`). The other arguments
still pair (`tests/programs/143_arg_roots.wf`).

### O3-8: a closure with its own `multi` handler is a `multi` and abort point

Repro: `R3/oracle/repro/O3-8_fp_closure_inner_multi.wf`. Site: ir (the closure summary).

Tag: edge. The shape needs a `multi` operation that a closure handles inside itself, and a
linear value that is live across the call of the closure. `let g = || { handle Pick {...} in {
if pick() {...} } }; g(); unlock(l)` gets W0503 and W0602 at line 25, and the `apply(|| ...)`
form gets them at line 31. `weft facts` shows `performs_at`, `multi_at` and `may_abort` at
`g()`. No operation can leave the closure. The block and the item forms are clean. Proposal:
remove the capabilities of the handlers inside the closure (`own_caps`) from the performs,
`multi` and abort parts of the closure summary. An operation that leaves the closure keeps
them. On the IR a closure is a body with its own handlers (root_causes.md, INNER).

### O3-9: joins that the body does not see

Repro: `R3/oracle/repro/O3-9_fp_join_not_seen.wf`. Site: ir (task sets of values), with a
`joins` part of the signature.

Tag: realistic. These forms join the task at run time, but the checker keeps the task active
to the end of the scope, so a later access is W0405: `join_it(t)` (line 25),
`let (t, _) = p; t.join()` (35), `match o { Some(t) => t.join(), ... }` (47), `id(t).join()`
(57), and `let g = || t.join(); g()` (67). A direct `t.join()` is clean. Proposal: carry the
task set of a value through tuple and `Option` patterns and through a generic call result;
add a `joins` part to the signature (the `Task` parameters that the body joins on every
normal path); let a closure that joins a captured handle on every path end its tasks where
it runs. Record a form that stays in the imprecision list of ADR 0006.

### Q3-3: a bare variant name resolves to the first enum that has the name

Repro: `R3/quality/repro/Q3_variant_name_prelude.wf`,
`R3/quality/repro/Q3_variant_name_across_modules.wf`,
`R3/quality/repro/Q3_variant_name_private.wf`. Site: durable (name resolution:
`body/call.rs:184`, `body/expr.rs:470` and `:1269`, `fip.rs:85`, and
`crates/weft-interp/src/compile.rs` about line 414; all use `prog.variants.get(name).first()`).

Tag: realistic. A user enum with a variant `None`, `Some`, `Ok` or `Err` gets the prelude
variant for the bare name: `return None` in a function that returns `Lookup` is W0102 at line
6 ("expected `Lookup`, found `Option<_>`"). Two modules with the same variant names get W0102
at line 21 ("expected `Shape`, found `Shape`"). A variant of a private enum of another module
is accepted (0 errors; W0101 expected at line 7). A pattern takes the type of the scrutinee,
so the bare form behaves differently in an expression and in a pattern. Proposal: resolve a
bare variant name in the module scope, as `Program::lookup` does for items; use the enum of
the expected type when it is known; report an ambiguous bare name (as `ambiguous_op` does)
and a private variant (W0101). Do the same in the interpreter and in `fip.rs`. Record the
rule in ADR 0009. This is name resolution, so it stays when the IR lands.

### O3-10: two spawns of function parameters get W0503

Repro: `R3/oracle/repro/O3-10_fp_spawn_param_multi.wf`. Site: ir (`multi_at` at a spawn).
Regression of R2c (`acd05a8`).

Tag: edge. It needs a `multi` operation somewhere in the program. Then
`fn both(f: fn(), g: fn()) { scope { s => s.spawn(f); s.spawn(g) } }` gets W0503 for `s`
(lines 14 and 21). A spawn does not run the parameter in this task, and W0314 keeps a task
away from the handlers of this task. Without the `effect Pick` line the file is clean.
Proposal: a spawn of a function value is not a `multi` point of the spawning task. The
whole-program `multi` test applies to calls only.

### O3-11: a move, then a new value of a variable that a closure captures

Repro: `R3/oracle/repro/O3-11_fp_move_then_refill.wf`. Site: ir.

Tag: edge. `let show = || print(v.len()); take_v(v); v = mk_v(); show()` is W0301 at line 22.
The closure reads the cell of `v` when it runs (ADR 0003), so it reads the new value. A new
value with no move before it is clean. Proposal: a move of a variable that a closure captures
by reference is not a free for the closure. Each node that runs the closure uses the
variable, so a run after the move and before a new value is W0302. The end of the scope of
the variable still invalidates the closure. Add a bad case that runs the closure between the
move and the new value (W0302).

### O3-12: a clause conflicts with its own task

Repro: `R3/oracle/repro/O3-12_fp_clause_spawn_self.wf`. Site: ir (capture reads of a clause).

Tag: edge. `handle Note { fn note(x) { s.spawn(|| { n += 1 }); resume(()) } } in { note(1);
print(7) }` is W0405 at line 11. The clause reads its captures at the operation (ADR 0006),
and the task starts at the operation too. Nothing else touches `n` while the task runs.
Proposal: leave out of the capture reads of a clause at an operation the captures that the
clause uses only inside a task that it spawns. A read in the clause after the spawn still
conflicts; add that bad case (W0405).

### F3-11: a closure that gives a captured reference a new value

Repro: `R3/fidelity/repro/F3-11_closure_rebind.wf` (`R3/triage/fid_run.sh 11`). Site: ir.

Tag: edge. `let h = || { r = grow(w) }; h(); print(r)` is W0301 at line 8. The same code with
no closure is clean, and the run with the oracle has no fault. The node that runs the closure
adds the places of the new value to `r` (ADR 0005, `keep = x`), but it does not rebind `r`, so
the change in `grow` stays. Proposal: record it in the imprecision list of ADR 0003, or rebind
at the run node when the closure gives the variable a new value on each path.

### R3RT7: `in` on an operation parameter has no effect

Repro: `R3/redteam/repro/R3RT7_op_in_param.wf` (`R3/triage/cmp.py`). Site: ir (operation
arguments), or durable if the signature check rejects `in` there.

Tag: edge. With `effect Hit { fn hit_op(w: &World, a: &Entity in w.entities[]) }`, the aliased
perform is W0312 at line 20, but a function with the same signature is accepted (the ADR 0005
workaround). An argument outside the place is W0312 at line 29, not W0203; a function gets
W0203 at line 25. The result is sound, because the clause sees separate roots. Proposal: give
the arguments of an operation the `arg_at` and `param_in` facts and the clause parameter the
root of the named parameter, as for a call; then `arg_outside` gives W0203. Or reject `in` in
an operation signature with a clear error and record that in ADR 0005.

### R3RT10: a part that holds a stale reference cannot get a new value

Repro: `R3/redteam/repro/R3RT10_part_refresh_fp.wf` (runs clean and prints 1 1 1). Site: ir.

Tag: edge. `t = (&a[0], &b[0]); b.clear(); t.1 = &c[0]` is W0301 at line 16 ("`t` used after it
was invalidated"), and the struct form at line 25. The first value of the tuple is on the
local, so a new value of a part is a use of the whole local. ADR 0003 says that a new value of
a part replaces the hidden variable of the part. Proposal: give the parts of a tuple or struct
value that a local gets hidden variables of their own. Keep a bad case that reads `t.1` before
the new value. Or record it in the imprecision list of ADR 0003.

### R3RT11: an empty `match` on an empty enum is W0120

Repro: `R3/redteam/repro/R3RT11_empty_enum_match.wf`. Site: durable
(`crates/weft-sema/src/body/exhaust.rs`; exhaustiveness is a type check, not fact generation).

Tag: edge. `enum Never {}` with `match n {}` is W0120 at line 5 ("does not cover every value of
`Never`"). There is no value to cover. Proposal: zero arms cover an enum with no variants.

## quality

### Q3-2: `closure_has` is exponential in closures that call closures

Repro: `R3/quality/repro/Q3_closure_helpers_16.wf` (4.1 s at b25faf0),
`Q3_closure_dag_18.wf` (31.7 s), `Q3_closure_chain_22.wf` (8.0 s); generator
`R3/quality/repro/Q3_exp_gen.py helpers N | chain N`. Site: ir
(`crates/weft-sema/src/body/mod.rs`, `closure_has` and `var_has`).

Tag: realistic. Local helper closures that call each other are a common style. `closure_has`
pushes and pops `h.seen`, so it searches a closure again on each path to it. `var_has` reaches
the closure of a local two times: through `ty_has_in` of its `Ty::Fn` and through
`l.summary`. So a chain of closures costs 2^n; 20 helpers take about 250 s. Proposal: the
query is existential, so keep one visited set for the whole query with no pop, and skip
`l.summary` when the type of the local names the same summary. Add a `Work` counter and a
scale test with the helper shape. The IR replaces this code: the IR fact generator must keep
closure queries linear, and the scale test belongs with the IR.

### I3-5: `Rc` counts: a moved capture and a detached result are not dropped

Repro: `R3/interp/repro/i3_5_closure_drop_weak.wf` (control `i3_5_closure_drop_weak_ctl.wf`)
and `R3/interp/repro/i3_5_detach_rc.wf`; `leaked_rc` needs the harness `R3/interp/harness`.
Site: durable (`crates/weft-interp/src/heap.rs`, `drop_value`; `machine/natives.rs`,
`TaskDetach`).

Tag: realistic. `heap.drop_value` ignores `Value::Closure`, so a value that a closure took by
value stays alive: after the closure goes out of scope, `w.upgrade()` gives `5` and
`leaked_rc=1` (the control gives `None` and `leaked_rc=0`). `Task.detach` consumes the handle
but never drops the result: `leaked_rc=1`. ADR 0007 says that `detach` drops the result.
Proposal: drop the owned cells of a closure when its last reference goes away. Drop the result
of a detached task when the task finishes, or at the end of the scope. The durable fix stage
marks the owned cells of a closure (I3-2), so this fix can use them.

### I3-9: the handler at a `join`, and the time of a raise after a resume

Repro: `R3/interp/repro/i3_9_join_handler.wf` and `R3/interp/repro/i3_9_resume_raise.wf`.
Site: durable (docs: ADR 0005, 0006, 0010, the W0504 text in `codes.rs`).

Tag: realistic. `check_interrupt` finds the scope failure first and unwinds to the scope. So
`handle Fail {...} in t.join()` never catches the failure of a scoped task
(`scope handler: task failed`), and the `TaskResult::Failed` branch of `join` cannot run for a
scoped task. After a resume, the failure comes at the next suspension point, not at the resume
(`the body goes on after the resume`, three `work` lines, then `scope handler: child
failed`). ADR 0006 says "a failure of a task goes to the task that joins it", the W0504 text
names a join as a raise point, and ADR 0010 says the resume raises it. The behavior is sound,
because W0602 treats each suspension point in a scope as abortable. Proposal: make the ADRs and
the W0504 text say what the interpreter does.

### I3-10: `http.serve` and the virtual clock

Repro: `R3/interp/repro/i3_10_http_timeout.wf`, with the harness:
`ipharness i3_10_http_timeout.wf --oracle --trace --http 127.0.0.1:18445 1` and a client
that connects at once. Site: durable (`crates/weft-interp/src/machine/mod.rs`,
`run_until_done`).

Tag: realistic. `run_until_done` calls `advance_to_next_timer` before `http_poll`. So a pending
timer moves the virtual clock before the server accepts a request: `with_timeout(60.s) {
http.serve(...) }` prints `caught: timeout at 60s` and serves nothing. A server with a sleeping
background task jumps the clock in the same way. `Machine::http` also stays set after the
server task unwinds. Proposal: poll the listener without a wait before the virtual clock moves,
and clear the server state when the server task unwinds. Record the rule in ADR 0010.

### I3-11: an inline recursive enum is copied at each move

Repro: `R3/interp/repro/i3_11_inline_list_loop.wf` (10 000 elements: 14.1 s at b25faf0) and
`R3/interp/repro/i3_11_inline_list_deep.wf` (stack overflow, exit 134). Site: durable
(`crates/weft-interp/src/heap.rs`, `is_copy` at line 207, and the drop of a value).

Tag: realistic for the loop form. `heap.is_copy` treats an enum with copy fields as copy, but
ADR 0007 says that a type that holds itself (`enum List { Cons(u64, List), Nil }`) is not plain
data. So each `l = Cons(i, l)` copies the whole list. The recursive `is_copy` and drop overflow
the stack at a depth of 8 000 000. Proposal: take the copy property of user types from sema
(`NotCopy`, as the checker does), and walk values with an explicit work list in `is_copy` and in
the drop.

### R3RT8: `Scope` against `Scope`

Repro: `R3/redteam/repro/R3RT8_scope_type_message.wf`. Site: durable (types and messages).

Tag: realistic. A written `Scope` is the prelude `extern type Scope`, but the binder of
`scope { s => ... }` has the type `Ty::Scope`. So `fn submit(s: Scope)` gets "type mismatch:
expected `Scope`, found `Scope`" (lines 11 and 12), and `s.spawn` on a `&Scope` parameter gets
"`Scope` has no method `spawn`" (line 8). Proposal (sound): in Phase 1 a scope cannot go to a
function, because a callee that spawns into the scope of its caller needs signature parts that
do not exist. Give a clear error at the parameter type that says this, and record it in ADR
0006.

### R3RT9: the W0703 hint does not parse

Repro: `R3/redteam/repro/R3RT9_w0703_hint.wf` and `R3/redteam/repro/R3RT9_hint_applied.wf`.
Site: durable (`crates/weft-check/src/diagnose.rs`, the display of a one-place instance).
Regression of R2a.

Tag: realistic. A write through the result of `find(w, id) -> Option<&Entity>` gets "add
`mut((w..).hp)` to the effects after `/`", also in the JSON note. With the hint applied, the
file is W0001 at line 8 ("expected a place, found `(`"). Commit 328a39b gave `mut(w..)`. The
message also names the callee `assign` for an assignment. Proposal: show a one-place instance
by its base with `..` in hints and messages (`mut(w..)`), also in the JSON note, and name an
assignment "assignment".

### F3-10: ADR 0006 has a stale claim about the mode lattice

Repro: `R3/fidelity/repro/F3-10_run.sh` (`R3/triage/fid_run.sh 10`). Site: durable (docs).

Tag: realistic (every reader). The first bullet of ADR 0006 says that the checker does not use
the verified mode lattice yet. ADR 0004, `docs/architecture.md` and `rules.rs`
(`modes::submode`, `join`, `bottom`, for W0406, W0403, W0401 and `pinned`) show that it does.
Proposal: delete the stale clause.

### F3-12: ADR 0002 gives W0118 the reason of a declaration check

Repro: `R3/fidelity/repro/F3-12_run.sh`. Site: durable (docs).

Tag: realistic (every reader). ADR 0002 keeps the W01xx checks in sema because they "look at
types, declarations and the syntax tree, not at the places, modes or effects of a body". W0118
reads the inferred row and the `muts`, `raises`, `reaches` and `drops` parts of the `on abort`
function. Proposal: list W0118 apart in ADR 0002 with its own reason: it checks an inferred
signature, as W0701 does.

### F3-13: wrong tests in `docs/traceability.md`

Repro: `R3/fidelity/repro/F3-13_run.sh` (`R3/triage/fid_run.sh 13`). Site: durable (docs).

Tag: realistic (every reader). The W0115 row names tests 07, 14, 61 and 132, but only
`21_types.wf` (and `cli.rs`) has W0115. The W0107 row names 64 and 141, which have none. The
W0602 cancellation row names 131, which has none. The W0315/W0111 jumps row names 80, which has
none. Proposal: name the tests that hold the codes (21_types.wf, cli.rs, units.rs, 63 and 60).

### F3-14: design standard library items with no record

Repro: `R3/fidelity/repro/F3-14_run.sh`. Site: durable (docs).

Tag: realistic (every reader). The design lists as shipped: a formatter, channels and
`select`, JSON, structured logging and tracing, and an HTTP client. Phase 1 has none of them.
ADR 0001 lists only HTTP/2, HTTP/3, TLS, SQL and the profiler as Phase 2, and the traceability
matrix has no row for that section. Proposal: add one line to ADR 0001 and one row to the
matrix.

### I3-13: proof documents and the link mutation script

Repro: `R3/interp/repro/run_all.sh`, section I3-13 (it greps the round-3 copy; at b25faf0 the
same lines are in `/home/user/wt-core`). Site: durable (docs and proof scripts). F3-15 is a
part of this item.

Tag: realistic (every reader). (1) `proofs/link/README.md` line 394 says "The interpreter must
not copy a record", but `copy_frames` (`machine/effects.rs` about line 633) gives each nested
continuation of a copied `multi` continuation a new record. Say that only the records of
`multi` continuations are copied, and why `kont_rel` holds for each copy. (2) The lifecycle
table of `crates/weft-verified/README.md` does not list `Continuation::end`
(`lifecycle.rs:107`). (3) `proofs/link/lints/unbound_use.dl` starts `unb` at the successors of
`n0`, but the hypothesis `bound_before_use` starts at `n0`; make them start at the same node or
say why not. (4) `proofs/link/mutations/run.sh` (line 45) counts a mutation as caught when
`verify.sh` fails for any reason; count it only on a Verus result line with errors, as ADR 0008
requires for borrowing and effects (expected: 26 caught, 17 link only). Run
`proofs/verify-all.sh` after the change.

### N1: a second W0602 for the hidden drop variable of `detach`

Repro: `R3/fidelity/repro/F3-6_control_detach.wf`. Site: ir (the hidden `Dropped` variable
of a generic drop). New at b25faf0: at b073ea7 the file had only the W0601.

Tag: realistic. Not a round-3 finding; triage saw it at this HEAD. `scope { s => let t =
s.spawn(|| begin()); t.detach() }` gets the correct W0601 at line 6 ("`detach` drops a value of
the linear type `Tx`"). It also gets W0602 at line 4: "linear value `detach` is live across
`scope end`, which can abort". The hidden variable that stands for the drop is rebound at the
drop node and stays live to the scope end, which can abort since R3a (F3-7). The program is
already rejected, so this is only a second message about one defect. Proposal: end the hidden
`Dropped` variable at its drop node (or exclude `Dropped` variables from W0602).
