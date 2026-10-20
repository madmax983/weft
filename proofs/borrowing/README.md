> Origin: this proof starts from
> [madmax983/group-borrowing-soundness](https://github.com/madmax983/group-borrowing-soundness)
> at commit `5dd0de3b4af29a28f1afc50c6d4ee15bbe8d0525` (Apache-2.0). Weft extends it. See `../README.md` for the extension list.

# Group Borrowing for Weft: soundness, machine-checked in Verus

A formal model of **group borrowing** (Nick Smith's proposal, written up at
<https://verdagon.dev/blog/group-borrowing>), extended for Weft, with a
[Verus](https://github.com/verus-lang/verus) proof that the checker rules out undefined behaviour.

```
verification results:: 169 verified, 0 errors     (about 22 s)
```

No `assume`, `admit`, `external_body`, extra axioms or `exec_allows_no_decreases_clause`.

## Status

| Milestone | Status | Main theorem | File |
| --- | --- | --- | --- |
| Base (upstream): straight-line programs | proved | `soundness_from_start`, `soundness` | `soundness.rs` |
| B1. Branches and loops (CFG) | proved | `cfg_soundness`, `cfg_soundness_from_start` | `cfg.rs` |
| B2. Captured references (closures, handlers, continuations) | proved | covered by all theorems; `lemma_perform_is_call` | `model.rs`, `closures.rs` |
| B5. Progress | proved | `progress`, `progress_trace`, `cfg_progress` | `progress.rs` |
| B3. Inline layout | proved, in a separate refined model | `layout_soundness`, `layout_soundness_from_start` | `layout.rs`, `layout_proof.rs` |
| B4. Task separation | proved | `task_soundness` | `tasks.rs` |

Each milestone has examples that guard against vacuity: an accepted program, a rejected
program, a concrete run of the rejected program that has UB (the rule is necessary), and
a run that meets every hypothesis of the theorem (the hypotheses are satisfiable).

## The rules

* Every reference has a **group**: a local plus a path of child-group labels, e.g.
  `d`, `d.rings*`, `d.rings*.gems*`. A child group holds anything that a mutation can
  destroy: a `Box` target, list elements, a variant payload.
* Any number of references, **mutable or not, may alias** within a group.
* A possibly-mutating use of a reference in group `G` (a `mut` argument of a call)
  **invalidates references into strict child groups of `G`, and nothing else**.
* Writing an inline primitive field invalidates nothing.
* **Joins (B1).** At a CFG join, a reference is valid only if it is valid, with the same
  group, at the end of each incoming edge (the intersection).
* **Captured references (B2).** A closure, an effect handler and a continuation are
  closure values: code plus captured `(reference, is_mut)` pairs. A closure value points
  into each group of its captures, so a call that invalidates one capture invalidates the
  closure value. A call of a closure, a `perform` that a handler handles, and a `resume`
  of a continuation are each a call whose argument list is the explicit arguments plus
  the captured references. A one-shot `resume` consumes the continuation.
* **Places (B3).** A place is a root plus a path of steps. `Field` steps are stable.
  `Variant` (an inline enum payload) and `Kid` (a child group) steps are unstable. A
  `mut(p)` invalidates a reference at place `q` iff `q` is strictly inside `p` through at
  least one unstable step. This is Weft's `strict_prefix(M, Path), crosses_unstable(M, Path)`.
  A mutable argument at an interior place `x.f` has a footprint of the inline part
  `x.f` and the kids owned under `x.f` only.
* **Tasks (B4).** No group in the mutable footprint of one task (the `mut` arguments and
  `Write` targets of its calls, invokes and writes) overlaps a group that the other task
  holds (a reference or a captured reference, at any point). Two groups overlap if they
  have the same root and one path is a prefix of the other.

## The theorems

### Base and B2 (`soundness.rs`)

```rust
pub proof fn soundness_from_start(prog: Seq<Instr>, trace: Seq<DState>)
    requires
        is_trace(prog, trace),                       // any execution: any indices, any callees
        wf(trace[0]),                                // any well-formed starting heap
        check(initial_sstate(trace[0]), prog),       // the checker accepts prog
    ensures
        forall|k: int| 0 <= k < trace.len() && k < prog.len() ==> !#[trigger] ub(trace[k], prog[k]),
```

The statement is the upstream statement. `Instr` now also has `MkClosure` and `Invoke`
(B2), so the theorem covers programs that make and call closures, handlers and
continuations. `soundness` is the same with any start state `ss0` such that
`inv(trace[0], ss0)`. The two steps of the proof are public:
`lemma_preserve` (`inv(s, ss) && instr_ok(ss, i) && step(s, i, s2) ==> inv(s2, post(ss, i))`)
and `lemma_no_ub` (`inv(s, ss) && instr_ok(ss, i) ==> !ub(s, i)`).

`ub` is a dereference of a reference whose allocation is gone, or whose address now holds
a *different* allocation or type (allocation stamps act as provenance). For `Invoke`, a
captured pointer that is not live is UB too.

### B1 (`cfg.rs`)

```rust
pub proof fn cfg_soundness(cfg: Cfg, ss0: SState, ann: Seq<SState>, path: Seq<nat>, trace: Seq<DState>)
    requires
        inv(trace[0], ss0),
        cfg_check(cfg, ss0, ann),        // the fixpoint state of each node is accepted
        is_cfg_trace(cfg, path, trace),  // the run follows CFG edges; node path[k] runs in trace[k]
    ensures
        forall|k: int| 0 <= k < trace.len() ==> !#[trigger] ub(trace[k], cfg[path[k] as int].instr),
```

`cfg_soundness_from_start` is the same with `wf(trace[0])` and `ss0 = initial_sstate(trace[0])`.
`cfg_check` requires `instr_ok(ann[n], cfg[n].instr)` at each node,
`sub_state(ann[0], ss0)`, and `sub_state(ann[m], post(ann[n], cfg[n].instr))` for each edge
`n -> m`. `sub_state(a, b)` means: same locals, and the references and closure values of
`a` are a sub-map of those of `b`.

* **Key lemma** `lemma_inv_sub`: `inv(s, ss) && sub_state(ss2, ss) ==> inv(s, ss2)`.
* `lemma_join_sub` and `lemma_join_greatest`: `join` (the intersection) is the greatest
  state that is `sub_state` of both inputs. So the fixpoint of the intersection join meets
  `cfg_check`, and so does any smaller annotation.
* `lemma_linear_cfg_check`: `check(ss0, prog)` gives `cfg_check` on the straight-line CFG.

### B2 (`closures.rs`)

```rust
pub proof fn lemma_perform_is_call(s, ss, h: CVar, args, ret, cvars: Seq<Var>, s2)
    requires
        s.clos.contains_key(h), ss.clos.contains_key(h),
        caps_in_vars(s, ss, h, cvars),   // variables cvars hold the captures of h, with their groups
    ensures
        step(s, perform(h, args, ret), s2) <==> step(s, Instr::Call { args: args + cap_args(ss, h, cvars), ret }, s2),
        ub(s, perform(h, args, ret)) <==> ub(s, Instr::Call { args: args + cap_args(ss, h, cvars), ret }),
        instr_ok(ss, perform(h, args, ret)) <==> instr_ok(ss, Instr::Call { args: args + cap_args(ss, h, cvars), ret }),
        post(ss, perform(h, args, ret)) == post(ss, Instr::Call { args: args + cap_args(ss, h, cvars), ret }),
```

This is Weft's central claim: a perform is checked, and runs, like a call with the
handler's footprint.

### B5 (`progress.rs`)

```rust
pub proof fn progress(s: DState, ss: SState, i: Instr)
    requires
        inv(s, ss),
        instr_ok(ss, i),
    ensures
        !ub(s, i),
        (exists|s2: DState| #[trigger] step(s, i, s2)) || aborts(s, i),
```

`aborts(s, i)` lists the defined, safe aborts. Each one is a failed runtime check on live data:

* `Child`: the index is out of range (the child group has no element now);
* `Read`, `Write`: the field index is out of range of the inline data. The base model has
  no static types, so the checker cannot exclude this case. B3 adds types: there an
  out-of-bounds access is UB, and the checker excludes it;
* `Call`, `Invoke` with a returned reference: no allocation exists at the requested path
  (for example `get(list, i)` with `i` out of range), so the callee aborts.

`progress_trace` (straight-line) and `cfg_progress` (CFG) lift this to runs: each accepted
run can go on, along each successor edge, until it ends or aborts safely.

### B3 (`layout.rs`, `layout_proof.rs`)

```rust
pub proof fn layout_soundness_from_start(sc: Schema, prog: Seq<LInstr>, trace: Seq<LState>)
    requires
        wf_schema(sc),                           // a consistent type schema
        lwf(sc, trace[0]),                       // ownership forest; each object has the layout of its type
        lcheck(sc, linitial(trace[0]), prog),    // the checker (Weft places) accepts prog
        is_ltrace(sc, prog, trace),
    ensures
        forall|k: int| 0 <= k < trace.len() && k < prog.len() ==> !#[trigger] lub(sc, trace[k], prog[k]),
```

`layout_soundness` is the same with any start state that satisfies `linv`. `lub` is a
use after free, a **type confusion** (a pointer path through a variant that is not active
now), or an access **outside the layout** of the type (a field index out of range, or a
non-primitive target). The key lemmas are `lemma_reads_in_region` (inline frame) and
`lemma_not_full_fp` (field-sensitive kids).

### B4 (`tasks.rs`)

```rust
pub proof fn task_soundness(p0: Seq<Instr>, p1: Seq<Instr>, ss0: SState, ss1: SState,
                            sched: Seq<nat>, trace: Seq<TState>)
    requires
        inv(tview(trace[0], 0), ss0),
        inv(tview(trace[0], 1), ss1),
        check(ss0, p0),
        check(ss1, p1),
        separated(ss0, p0, ss1, p1),
        separated(ss1, p1, ss0, p0),
        is_itrace(p0, p1, sched, trace),   // any interleaving; sched[k] picks the task of step k
    ensures
        forall|k: int, t: nat|
            0 <= k < trace.len() && t < 2 && #[trigger] task(trace[k], t).pc < prog_of(p0, p1, t).len() ==> {
                let i = prog_of(p0, p1, t)[task(trace[k], t).pc as int];
                &&& !ub(tview(trace[k], t), i)
                &&& race_free(tview(trace[k], t), i, tview(trace[k], other(t)), tss(ss0, ss1, p0, p1, trace[k], other(t)))
            },
```

`race_free` means: no allocation that the step of `i` can change or free (`writes`) is
reachable (`reach`: equal to, or below, the target) from a valid reference or a valid
captured reference of the other task. This holds at each point of each interleaving, so
it holds between any two accesses. The proof reuses the frame lemma
`lemma_ptr_survives` and adds `lemma_shared_overlap` (two valid pointers that reach the
same allocation have overlapping groups).

## The model

* **Heap (`model.rs`):** allocations with a stamp, a type, inline `data`, and labelled
  owning `kids`. Ownership is a forest rooted at the locals (`wf`).
* **Instructions:** `Borrow` (`&x`), `Child` (`&src.label[i]` with a runtime-chosen
  `i`), `Copy`, `Read`, `Write` (an inline field), `Call`, `MkClosure`, `Invoke`.
* **Calls are arbitrary.** A call passes a list of `(pointer, is_mut)` arguments, which
  may alias. Its effect is *any* new heap that keeps the ownership forest well-formed and
  changes nothing outside what the mutable arguments own (`callee_effect`). A call can
  return a reference into a child group of one of its arguments.
* **Closure values** hold copies of the captured pointers. `Invoke` passes the explicit
  argument pointers plus the captured pointers to the same `callee_effect`.
* **CFG (`cfg.rs`):** nodes with one instruction and successor edges. The model does not
  evaluate branch conditions: a run can take any edge.
* **Layout (`layout.rs`):** a type schema gives each type a size and a shape (primitive,
  struct with fields at fixed offsets, or enum with a tag slot and a payload). `data.len()`
  is the size of the type. A pointer is an allocation plus an inline path. Child-group
  labels are owned by inline paths of the type. The checker tracks places in structured
  form (hops through child groups, then an inline tail) and applies the Weft rule to the
  flat path. The checker tracks static types, so it rejects out-of-bounds accesses.
* **Tasks (`tasks.rs`):** two tasks share the heap and the locals. Each task has its own
  variables, closure values and program counter.

## The proof idea

The invariant (`inv`) says that every reference and every captured pointer that the
checker considers valid is live, and can be reached from its group's root local by a
route whose labels are exactly the group's path.

1. **Unique routes.** Ownership is a forest, so each allocation has exactly one route from
   the roots (`lemma_resolve_unique`). Anything a callee could free is a strict
   descendant of some mutable argument, so it lies in a strict child group of that
   argument's group. Those are exactly the references the checker kills (`lemma_ptr_not_below`).
2. **Frame.** Every other pointer's route avoids the callee's footprint, so both the route
   and the allocation survive the call (`lemma_route_preserved`, `lemma_ptr_survives`).
3. **Joins (B1).** The invariant holds for each subset of the valid references.
4. **Inline frame (B3).** A valid inline path reads a tag slot inside the region of another
   valid path `fp` only if it extends `fp` through a `Variant` step
   (`lemma_reads_in_region`). With unique routes, a kid that a mutable argument at `x.f`
   can free has a place `x.f ... Kid ...` (`lemma_not_full_fp`). The Weft rule kills both.
5. **Tasks (B4).** By unique routes, a write of one task and a reach of the other at the
   same allocation give overlapping groups, which the separation rule forbids.

## Sanity checks

| File | Accepted | Rejected | UB run of the rejected program | Hypotheses satisfiable |
| --- | --- | --- | --- | --- |
| `examples.rs` (base) | `damage_prefix`, `attack` (mutable aliasing, Rust rejects it), `power_up` (sibling child group) | `damage_bad` | `example_damage_bad_is_ub` | `example_soundness_applies` |
| `cfg_examples.rs` (B1) | `loop_ok` (rebinds `ring` in the loop) | `loop_bad` (binds `ring` before the loop), for every annotation | `example_loop_bad_is_ub` (second iteration) | `example_cfg_soundness_applies` (takes the back edge) |
| `closures.rs` (B2) | `handler_ok`, `closure_ok` (a closure that changes `d.rings*` keeps `d.armor*`) | `handler_bad` (perform kills `ring`), `closure_bad` (closure killed with its capture), `resume_twice` | `example_handler_bad_is_ub`, `example_closure_bad_is_ub` | `example_handler_soundness_applies` |
| `progress.rs` (B5) | `example_progress_step` (a step exists) | `example_no_progress_without_check` (no step, no abort, UB) | — | `example_progress_abort` (accepted, aborts safely) |
| `layout_examples.rs` (B3) | `fs_ok` (`&w.items[i]` survives `shuffle(mut w.players)`), `en_ok`, `stable` (`&w.score`, `&w.state` survive `update(mut w)`) | `fs_bad`, `en_bad` (payload reference after `set_state(mut w.state)`), `oob` | `example_fs_bad_is_ub` (use after free), `example_en_bad_is_ub` (type confusion), `example_oob_is_ub` | `example_layout_soundness_applies`, `lemma_wsc_ok` |
| `tasks_examples.rs` (B4) | `pa`/`pb` (`d.rings*` and `d.armor*`) | `pa_bad`/`pb_bad` (`d` and `d.rings*`; each task alone passes the checker) | `example_race_is_ub` (a data race, then a use after free) | `example_task_soundness_applies` |

## Mutation tests

Each test weakens one rule and runs `./verify.sh`. The proof fails each time.
`mutations/run.sh` runs them: each mutation is a script `mutations/NAME.py` that changes
a copy of the crate in a temporary directory. The test passes if `verify.sh` fails on
the copy. The script shows the verification results and the functions that fail. It
does not change the repository, and it takes about four minutes.

```bash
mutations/run.sh          # all mutations
mutations/run.sh b1 b4a   # some mutations
```

| Name | Milestone | Mutation | Result |
| --- | --- | --- | --- |
| `base` | Base | `strict_child` only for grandchild groups (`p.path.len() + 1 < g.path.len()`) | 165 verified, 4 errors: `lemma_ptr_not_below` fails; the base and B2 examples fail |
| `b1` | B1 | `cfg_check` checks only forward edges (`succs[j] > n`), so back edges do not join | 167 verified, 2 errors: `lemma_cfg_inv_along` fails; `example_loop_bad_rejected` fails (in `lemma_loop_bad_rejected`) |
| `b2` | B2 | `clos_survivors` keeps every closure value (no kill through captures) | 166 verified, 3 errors: `lemma_preserve_call_ptrs` fails (closure part); `example_closure_rejected` and `cfg_progress` fail |
| `b5a` | B5 | `instr_ok` accepts `Borrow` of any local | 168 verified, 1 error: `progress` fails (no step, no abort) |
| `b5b` | B5 | `aborts` has no `Child` case | 166 verified, 3 errors: `progress` fails; `cfg_progress` and `example_progress_abort` fail |
| `b3a` | B3 | `Variant` steps are stable (`unstable(st) = st is Kid`) | 167 verified, 2 errors: `lemma_kills_variant` fails; the kill facts of the examples fail |
| `b3b` | B3 | `Read` needs no static type check (only `field_only(path)`) | 167 verified, 2 errors: `lemma_lno_ub` fails; `example_oob_rejected` fails |
| `b4a` | B4 | `overlap` in one direction only (`a.path.is_prefix_of(b.path)`) | 168 verified, 1 error: `lemma_shared_overlap` fails (race freedom) |
| `b4b` | B4 | `task_soundness` without `separated(ss1, p1, ss0, p0)` | 168 verified, 1 error: `task_soundness` fails |

## Scope and limitations

* **No stored references.** References and closure values are second-class: they live in
  variables and are never stored in the heap. This is the "no back channels" assumption
  that makes the frame of `callee_effect` valid.
* **Abstract callee bodies.** The model does not check a callee's own body. The most
  general effect allowed by its signature models it.
* **One group per reference.** At a CFG join, a reference with different groups on two
  incoming edges is dropped. Weft's `points_into` can give a reference several places.
  The proof covers the one-place case. The natural extension (the pointer reaches one of
  its groups; a kill of any group kills the reference) is not done.
* **Groups that grow in a loop.** `ring = &ring.kids[i]` in a loop gives a new group on
  each iteration, so the join drops `ring`. No summary of recursive places.
* **Closure values** cannot be copied, stored, or passed to a call. An `Invoke` names one
  closure value. A call that passes several closures, or a higher-order call, is not in
  the instruction set. The call lemma `lemma_preserve_call_ptrs` accepts any list of
  argument pointers that match their groups, so the extension (one argument list with
  all the captures) is direct, but it is not done.
* **B3 is a separate model.** It covers `Borrow`, `Field`, `Variant`, `Child`, `Copy`,
  `Read`, `Write` and `Call`. It has no closures, no CFG, no tasks, and no returned
  references (calls return nothing; the base model covers returned references). A
  callee keeps the kids of other fields at their positions in the kid list. An enum
  changes its variant only through a call with a mutable argument at the enum or an
  enclosing place (an enum assignment is such a mutation). `Read` and `Write` use field
  paths only. A fixed array with a runtime index (Weft's `step_alias`) is not modelled;
  all stable steps are exact fields.
* **B4** has two tasks, each with a straight-line program, and the initial references of
  each task are given (the spawn arguments). It does not model the parent, spawn, join,
  or fork branches on other threads. The rule compares mutable footprints with *held*
  groups, at all program points of the other task.
* **Single-threaded steps.** B4 interleaves whole instructions. A callee effect is atomic.

## Notes for the production checker

These model rules must hold in `spec/weft.dl` and `crates/weft-check`:

1. A closure value, a handler and a continuation must be reference holders:
   `points_into(V, Path)` for each captured place. Then W0301 invalidates the value when
   a capture is invalidated, and a later call, perform or resume of it is an error.
2. A call of a closure, a perform and a resume must give `mutates_at(P, M)` for each
   mutable capture `M` (W0301 already has `performs_at(P, Cap), footprint(Cap, M)`). A
   call of a function that can perform an effect of an enclosing handler must also give
   the handler's footprint: a plain call can only touch its own mutable arguments.
3. Enum payload steps must be `unstable`. An assignment to an enum place must be
   `mutates_at(P, place)`. A write to a primitive field invalidates nothing.
4. The join keeps a reference only if it has the same place on each incoming edge, or the
   checker must use the multi-place extension above (not proved).
5. The task rule of the proof (B4) is reference-based: the mutable footprint (including
   `Write` targets) of one task must not overlap any place that the other task holds a
   reference into. W0405 is access-based (`task_conflict` with `accesses`) plus "spawn is a
   mutation". That rule is more permissive. This proof does not cover it.

## Running

```bash
./verify.sh          # needs `verus` on PATH
```

CI (`.github/workflows/ci.yml`, job `verus`) builds Verus at the revision in
`../VERUS_VERSION` and runs `../verify-all.sh`, which runs `./verify.sh`.
