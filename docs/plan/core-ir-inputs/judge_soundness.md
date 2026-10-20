# Judge report: the soundness lens

Status: judgement of the three core IR designs. Date: 2026-10-20. Base: commit `b073ea7`
(`ir/probes/weft`) and the R3a commit `616f99c` (`ir/work/machine/weft-r3a`). I changed
nothing in `/home/user/weft`, `/home/user/wt-core` or `/home/user/wt-edge`. All my files
are in `ir/judge_sound/` (section 8).

The designs:

- **MIR**: `docs/plan/core-ir-inputs/design_mir.md`. A CFG of basic blocks for each code unit, reference
  versions, one summary type, the interpreter runs the IR.
- **Machine**: `docs/plan/core-ir-inputs/design_machine.md`. A CFG that copies the interpreter frames and the
  proof models: node phases (`Ret`, `FrameEnd`, `AbortValue`, `Exit`, `Post`, `Landing`,
  `Copy`), cleanup chains copied for each abort destination, capability and
  continuation roots, heap slots.
- **Minimal**: `docs/plan/core-ir-inputs/design_minimal.md`. A typed tree in A-normal form. The fact generator
  of `body/` stays and walks the Core.

## Summary

| Design | Score | One line |
| --- | --- | --- |
| Machine | **8.0** | The node phases put each bind before each free that follows it. This closes the frame-boundary family (O3-2, O3-3, M1, M3 by construction; M2, M4 by the frame-root rule). The gaps are one open decision (`KeptCell`) and two under-specified clause rules. |
| MIR | **7.0** | Group A goes by construction, and versions make `points_into` flow-sensitive. But three ordering defects open holes: the abort value binds after the cleanup chain (M3), callee frame roots do not end on abort paths (M4), and `Recopy` forgets invalidations of outer places (J4). The gate does not see M3 and M4. |
| Minimal | **4.5** | Lowest migration risk. But the whole clause still runs at the perform (J1), clause and callee frames have no roots (J6, F3-2, M4), `on abort` stays atomic (F3-1), and LOOP, STATE, SUM, FNVAL, CAP and STORE keep the mechanisms of today. Those classes gave most of the round-2 and open-list blockers. |

**Recommendation.** Build the machine design. Graft these parts:

1. From the minimal design: the capture rule "`Kept` only for plain data that no body
   borrows". It closes a new realistic blocker (J5d, open at `b073ea7` and `616f99c`).
2. From MIR: the definition of a resume point ("a `Resume` call, or a call whose
   apply resumes"), and "the part after the **first** resume point". The machine text
   splits a clause "at the `Resume` nodes" only (J2).
3. From MIR: bind the `Handle` destination to the union of `_0` of the handled body
   and the values of the clauses (J3). The machine text binds `_0` at `Exit` only.
4. From MIR: the fact oracle (MIR 6.5) and the claims test (MIR 8.2, check 7).
5. From MIR, optional: reference versions. Use them only with the machine `Copy` rule
   ("rebind only a variable whose places are all in the copied frames").
6. From the minimal design: the relation table `RELS` with a test that destructures
   `FnFacts`. Apply it to the machine summary procedure, so that no new relation can
   miss a summary part.
7. Machine fixes: `Dead` always emits `scope_end` (not only for plain data); `_0` is in
   the cleanup chain of a scope body across `ScopeWait`; the gate runs the oracle on
   each accepted input, not only on inputs whose verdict differs.

Add the judge probes J1 to J6, the machine probes M1 to M4 and `ir/work/mir/postres.wf`
to the gate of each stage.

**Main findings** (section 4 has the details):

- A new unsound shape, open at `b073ea7` and `616f99c`, realistic: **J5d**. A maker
  function returns a closure that borrows a captured plain struct
  (`|| print(norm(&p))`). The oracle reports a reference into an ended local. MIR and
  the minimal design close it by their capture rules. The machine design leaves it open
  with its default `KeptCell` decision.
- A second new realistic shape, open at both commits: **J1**. A clause changes a place
  after `resume`, and the handled body stored a reference into that place after the
  operation. MIR and the machine design close it. The minimal design does not.
- J1, J5, J5d, M3 and M4 are also accepted by the newest `wt-core` release binary
  (HEAD `b25faf0`, "R3a review fixes", built at 16:15). I only ran it; I did not change
  `wt-core`.
- I checked the discriminating traces with the real spec. I wrote the facts that each
  design gives as Datalog facts, and `weft lint` evaluated them with `spec/weft.dl`
  (section 1). The results: M3 is open in MIR, J1 is open in the minimal design, J4 is
  open in MIR, and MIR and the minimal design each break `no_gen_kill` at one node kind.

## 1. Method

1. I read the three designs in full, `docs/plan/core-ir-inputs/root_causes.md`, the reports of rounds 2 and 3
   (`r2/oracle.md`, `r2/redteam.md`, `r2/fidelity.md`, `r3/oracle.md`, `r3/redteam.md`,
   `r3/fidelity.md`), `ship_rule.md`, `round1b_tasks.md`, `spec/weft.dl` and the B6
   lints (`proofs/link/lints/gen_kill.dl`, `unbound_use.dl`).
2. I took 15 blocker repros from rounds 2 and 3 (section 3). For each design I wrote
   the IR that its lowering rules give, then the facts that its templates give, and then
   the derivation of the spec. Where the design text is ambiguous, I say which reading I
   used, and I mark the verdict with `?`.
3. For the traces where the designs differ, I encoded the facts as Datalog facts. The
   command `weft lint --rules TRACE.dl empty.wf` adds them to the facts of an empty
   program and evaluates `spec/weft.dl`. Each trace has lint rules such as
   `lint("MIR M3: W0301 at print(r)", pr) :- error(rd, pr).`, and a common rule for the
   B6 hypothesis `no_gen_kill`. `ir/judge_sound/run_all.sh` runs all of them.
4. I looked for new holes in the mechanisms that each design adds or keeps. For each
   candidate I wrote a probe, and I ran it with `check` at `b073ea7` and `616f99c`, and
   with `run --unchecked --oracle`.

Verdict marks: **C** by construction (the IR has no form for the defect); **R** by one
rule (one function of the analysis or the summaries gives it); **K** by a mechanism of
today that the design keeps; **✗** the design does not remove it; **?** the design text
does not decide it.

## 2. Root-cause classes: what each design removes

The table uses my checks, not the counts of the designs. "C" for a class means that the
mechanism exists and my traces found no counterexample. A footnote names each gap that
I found.

| Class | MIR | Machine | Minimal |
| --- | --- | --- | --- |
| TEMP | C | C | C |
| TAIL | C | C | C |
| DROP | C (`on abort` as an apply) | C | C for 5 findings; ✗ for FD1, F3-1, F3-3 (`on abort` stays atomic) |
| ORDER, ACCESS, DEREF | C | C | C (place resolver, pointer word) |
| CALLS | C | C | R |
| ENV | C | C, but `KeptCell` leaves J5 open [a] | C for captures; continuation root gap [b] |
| INNER | C | C | R; clause-frame gap (J6) [c] |
| SUSP | C, but the abort value binds after the cleanup (M3) [d] | C (`AbortValue` before the cleanup) | C, with a gen-kill node |
| LOOP | C | C | ✗ (`lower_loop` stays) |
| VAL, POST, TYPES | C | C | C (POST: OL-2b stays) |
| TWO | C (stage M3) | C (stage S3a) | C (stage 6) |
| MULTI | C, but `Recopy` forgets outer invalidations (J4) [e] | C (`Copy` rule) | K (`handled_again`); OL-R2a ✗ |
| STATE | R (versions) | R (flow-sensitive state; facts stay flow-insensitive) | K |
| PART | R (move paths and the R3a rules) | R, C for V062 and Q3-1 | K |
| FNVAL | R in a body; partly across functions | R (heap slots, summaries) | K |
| SUM | R (one count query, unknown-code summary) | R | K (`EffectSig` stays) |
| STORE | R (frame roots), but not on abort paths (M4) [f] | R (callee and caller frame roots) | ✗ for F3-2, M4, OL-R2b |
| CAP | K until M9; no root for continuations [g] | R (capability and continuation roots) | K (marks); continuation root gap [b] |
| SPEC, TYPE, INF, NAMES | ✗ | ✗ | ✗ |

[a] H6. [b] H12. [c] H11. [d] H1. [e] H3. [f] H2. [g] H5.

Who removes the most classes by construction: MIR and the machine design remove each
class of group A. The machine design adds MULTI and two PART findings by construction,
and it covers the frame boundaries without a gap that I could find. MIR claims more
(114 of 180) because it counts several "one rule" mechanisms as construction (versions,
frame roots, the count query). After my checks, MIR has three ordering gaps in its own
mechanisms (H1, H2, H3). The minimal design removes most of group A, but it keeps LOOP
and all of group B as the code of today.

Why group B matters for the ship rule: in round 2, group A gave 39% of the unsound
findings and group B gave 47%. In the open lists, group B gave 72% (`root_causes.md`,
"By round"). The ship rule allows two review rounds after the IR lands. A design that
keeps the group-B mechanisms of today keeps the source of most late blockers.

## 3. Fifteen blocker repros, traced

Each subsection gives the repro, the IR of each design (short form), the facts that
decide the result, and the verdict. "Today" is `b073ea7`.

### 3.1 O3-2: a temporary of a handled body (`r3/oracle/repro/O3-2_*.wf`, `callee`)

`let r = handle Note { fn note(x) { resume(()) } } in { first(&mk_v()) }; print(r + 1)`

| Design | IR | Facts | Verdict |
| --- | --- | --- | --- |
| MIR | `handled#0: _2 = mk_v(); _3 = &_2; _0 = first(move _3); StorageDead(_3); StorageDead(_2); return`, spliced | `_0@n6` points into `t2[]`; `scope_end(S(_2), n7)`; `uses(_0@n6, n8)` at the exit | C. `error(_0, n8)` (trace `o32_mir`) |
| Machine | the same body, with `Drop(_2); Dead(_2)` at the frame end | `Exit` of the `Handle` uses `_0` of H after the free | C. Error at `Exit` (trace `o32_machine`) |
| Minimal | inline: `t1 = call mk_v(); t2 = &t1; r = call first(move t2); dead t2; dead t1` | the "handle value" node uses `r`, then binds it again | C. Error at the handle value node (trace `o32_minimal`) |

### 3.2 O3-3: a temporary of a clause (`clause_value`, `resume_value`)

| Design | IR and facts | Verdict |
| --- | --- | --- |
| MIR | Clause body: `_1 = mk_v(); _2 = &_1; _0 = first(move _2); StorageDead(_2); StorageDead(_1); return`. The `Return` node uses `_0` after the free. For `resume_value`, the resume summary gives `_0` the value of the handled body, which is the resume argument (a clause temporary). | C |
| Machine | The clause value goes to `AbortValue(h)` at the perform. Its clause-local places map to the clause-frame variable of the `Handle`, which ends at `Landing` (or `Post` for `resume_value`). `print(r + 1)` uses `r` after that end. | C |
| Minimal | Rule FRAME in the clause: `_0 = ...; dead t1; return`, and `uses(ret, exit)`. Error in the clause component. | C (but see J6, H11) |

### 3.3 O3-4: a spawn statement drops a linear task result (`fresh`)

| Design | IR and facts | Verdict |
| --- | --- | --- |
| MIR | `_h = Spawn(t)(copy _1, move _f); ScopeAdopt(move _h)`: a task-result variable with `rebound_at` at the adopt node and `scope_end` at `ScopeWait`. `unconsumed`: W0601. | C |
| Machine | `spawn site(copy s, move tf) -> None`; a `TaskResult` local that `ScopeWait` binds and `Drop` ends. W0601. | C |
| Minimal | `give h to s -> r1`; `ScopeEnd` binds `r1`; `dead r1`. W0601. | C |

### 3.4 O3-5: a task runs a closure from a struct field (`local_copy`, `in_task`, `callee`)

| Design | IR and facts | Verdict |
| --- | --- | --- |
| MIR | `h = H { f: Closure#1(&v) }`: the move path `h.f` has the function set `{c1}`. The task closure reads `(*(*_1).h).f`; at the spawn, `Capture(h)` maps to the versions of `h`, so the call applies `Σ(c1)` with the task sink: `task_writes(v)`, W0405. The `callee` form (`run_h(&h)`) runs a value behind a parameter. `SumFn` has no form for it (FNVAL partly), so the call uses the unknown-code summary, and the closure in `h.f` is not "escaped" by 3.5.23. | R for the local forms; ✗ for `callee` |
| Machine | Move paths and heap slots hold function values. `run_h` has a `runs` part for its `Held(0).f` slot, and σ maps it to `h.f`. | R |
| Minimal | The design says: the task "replays the call of the unknown value", and the stored values run there. But a closure in a struct literal is not a stored value (3.23: only an `Assign` into a place that is not a whole local). The closure set lives in types (`FnTy::closures`), and a field of a non-generic struct has a declared type. Today the same channel misses these forms. Only `field_assigned` is a store. | ? |

### 3.5 O3-6: a task reads through an `Rc` handle; the parent moves it

`let b = s.spawn(|| shared.v + 1); take(shared)`

| Design | IR and facts | Verdict |
| --- | --- | --- |
| MIR | The task reads `(*shared).v` with `Deref(Rc)`. `ptr(p)` makes the task read `shared` too. `take(move shared)` frees the root of `shared`: `task_conflict` (a free that overlaps a read). The `new_value` form is a `Store` of the whole local: `mutates_at(root(shared))`. | C |
| Machine | α of `(*h).f` names `h`, so the task reads the handle. | C |
| Minimal | The resolver reads the pointer word `shared.@`. A move or a new value of `shared` overlaps it. | C |

### 3.6 O3-14: a tail place of a `multi` handled body (`tail_place`)

| Design | IR and facts | Verdict |
| --- | --- | --- |
| MIR | `_0h = move v` (an upvar). The re-entry edge goes from the after-body node through `Recopy` back to the return point of `pick`. `v` is outside the handled body, so `Recopy` does not bind it, and the second `move v` is W0302. | C |
| Machine | The same cycle through `Post`, `Copy(P)` and `P.Ret`. `Copy` does not bind `v`. | C |
| Minimal | `handled_again` lowers the body as a loop; FRAME puts the tail move in the loop. | K |

### 3.7 R3RT2: a `match` through a reference to `Option<&Entity>`

`let o = Some(&world.entities[0]); let p = &o; world.entities.clear(); match p { Some(e) => print(e.hp) }`

| Design | IR and facts | Verdict |
| --- | --- | --- |
| MIR | `e = &(((*_p) as Some).0)` of type `&&Entity`; `e.hp` is `(*(*e)).hp`. `abs` of the inner `Deref` gives the places of the versions of the move path `o.Some`: `world.entities[]`. The read at `print` follows the clear. W0301. | C |
| Machine | α of `Deref(Ref)` of a move path gives the `refs` of the path. W0301. | C |
| Minimal | Resolver row "`Deref(Ref)` of a part of a local": the part holders, else the places of the local. W0301. | R |

### 3.8 R3RT4: `resume` inside a closure with the closure parameter

`fn pick() { let k = |x: &u64| resume(x); k(&v[0]) }`; the body clears `v` and uses the result.

| Design | IR and facts | Verdict |
| --- | --- | --- |
| MIR | Closure body: `_0 = Resume(copy (*_1).k)(copy _2)`. Its summary calls the continuation with `Param(1)`. The apply at `k(&v[0])` maps `Param(1)` to `v[]`. The clause summary gives the perform result the resume argument: `r` points into `v[]`. W0301. | R |
| Machine | The perform result comes from the resume values of the clauses, through the summary of `k` at its run node. | R |
| Minimal | The `resume` of a continuation outside the closure is a replay; σ maps `x` to `v[]`; the `OpResult` rebase moves the facts there. | R |

### 3.9 F3-1: `on abort` changes a place through a reference in the value

`body(v)` holds `r = R { o: Some(v) }` across `stop()`; the clause does not resume;
`undo_ref` pushes into `*o`; `main` holds `first = &v[0]` and prints it after the `handle`.

| Design | IR and facts | Verdict |
| --- | --- | --- |
| MIR | The cleanup chain of `body` has `Unwind(r)`. `R` has `on abort = undo_ref`, so the node applies `Σ(undo_ref)` with `RunKind::OnAbort`. Its `Held(0)` write maps to the `Param` root of `v`. The summary of `body` then writes `v`, and the call `body(&v)` in `main` invalidates `first`. | R |
| Machine | `UnwindValue(r, OnAbort(undo_ref))` applies the summary in the same way. W0118 also becomes a query over the summary ("a change through a reference in the value is a change outside it"). | R |
| Minimal | D18: `on abort` stays atomic, and W0118 stays as today. Today misses it. | ✗ |

### 3.10 F3-2: a closure or a clause keeps a reference into a local of a callee

`fn apply(f: fn(&u64)) { let x = 5; f(&x) }`; `apply(|r| last = r); print(last)`

| Design | IR and facts | Verdict |
| --- | --- | --- |
| MIR | The summary of `apply` calls `Param(0)` with a `Frame` place. The apply at the call node `C` makes the root "frame of `apply` at `C`" and the closure `assigns` part gives `last` a weak definition at the return node `R`. The frame root ends at `R` too. `invalidated_at(last, R)` holds, so `print(last)` is W0301. The same node binds and invalidates `last`: the B6 lint `gen_and_kill` fires (trace `f32_mir`). The clause form with no `resume` (`F3-2_clause_keeps_callee_ref_abort.wf`) is H2. | R (normal path) |
| Machine | `Ret` binds `last`, then `FrameEnd` frees the frame root, also on abort paths. W0301 with no gen-kill (trace `f32_machine`). | R |
| Minimal | Section 4.14: "open: a place in a local of a callee (F3-2)". | ✗ |

### 3.11 F3-7: the value of a scope body across the end of the scope

| Design | IR and facts | Verdict |
| --- | --- | --- |
| MIR | `_0 = begin(); ScopeWait -> [return, unwind]`: `_0` is live across a node with `may_abort`, so `abort_unhandled` (W0602). | C |
| Machine | The same; `ScopeWait` has an `unwind` block. | C |
| Minimal | `d = move t; scope_end s ... unwind(..)` with `d` live across it. | C |

### 3.12 RR3: a continuation leaves its clause (`to_outer_local`)

`handle Note { fn note(x) { k = || resume(()) } } in note(1); k()`

| Design | IR and facts | Verdict |
| --- | --- | --- |
| MIR | The continuation is the clause parameter `_2: Cont`. 4.3 gives roots to handler capabilities and frames, not to continuations. W0313 stays in sema until M9 and reads `AbsValue::caps`. The design does not say that a continuation is in `caps`. | ? (H5) |
| Machine | The continuation local has a root that ends at the clause `Return`. The clause stores the closure through its `ByRef` environment field; the `stores` part maps the clause-local root to the clause-frame variable of the `Handle`, which ends at `Landing`. `k()` after the `handle` is W0301, shown as W0313. My reading: the `stores` part covers a write through a `ByRef` environment field (4.5 names "behind a reference parameter"). | R |
| Minimal | D17: the continuation points into the root of the `ClauseFrame` local, and only the clause epilogue ends it. That end is in the clause component. The projection Σ(clause) drops facts about clause locals, so no node of the function component frees the root, and `k()` is accepted. The `as_handle_value` form is found (the clause `Return` uses `_0`). | ✗ (H12) |

Today rejects all RR3 forms, so the gate of each design shows the MIR and minimal
regressions as "lost error, oracle fault".

### 3.13 RR5: `resume` carries the frees of the handled body

The clause holds `r = &world.entities[0]` across `resume(())`; the body moves `world`.

| Design | IR and facts | Verdict |
| --- | --- | --- |
| MIR | The resume summary has the frees of the handled body region: `releases_at(resume node, world)`. `print(r.hp)` is W0301. | R |
| Machine | The continuation summary has `frees`. | R |
| Minimal | `Π(h)` projects `moved_at(world, ·)` (an outer local, visible) onto the `Resume` node. | R |

### 3.14 RR7: a closure reads the new value of a captured reference

`let f = || print(r.hp); r = &world.entities[0]; world.entities.clear(); f()`

| Design | IR and facts | Verdict |
| --- | --- | --- |
| MIR | D5: `r` is assigned after its declaration, so the capture is `ByRef`. At the run node `Capture(r)` maps to the versions of `r` that reach it: `r@new`, which the clear invalidates. | C |
| Machine | σ maps `Env(k)` of a `ByRef` capture to the variable itself. | C |
| Minimal | `ArgUp(B, i)` maps to the places of `r` at the run node (flow-insensitive: both values). | R |

### 3.15 OR3: a callee calls a callback twice (`via_twice`)

| Design | IR and facts | Verdict |
| --- | --- | --- |
| MIR | The summary of `twice` has `calls[0].count = Many`. The apply puts `Σ(closure)` at the call node and again at a `call again` node, so the clear of the first run invalidates `r` before the second run uses it. | R |
| Machine | `runs` = many: the summary applies at `Main` and again at `Ret`. | R |
| Minimal | The `repeats` part of `EffectSig` stays, with the R2b fix of today. | K |

### 3.16 Tally

| Design | C | R | K | ✓ total | ? | ✗ |
| --- | --- | --- | --- | --- | --- | --- |
| MIR | 8 | 6 | 0 | 14 | 1 (RR3) | 0 (but the `callee` form of O3-5 is ✗) |
| Machine | 8 | 7 | 0 | 15 | 0 | 0 |
| Minimal | 5 | 4 | 2 | 11 | 1 (O3-5) | 3 (F3-1, F3-2, RR3) |

## 4. New holes

Each hole has a probe or a trace in `ir/judge_sound/`. "Realistic" and "edge" follow
the ship rule. "Gate" says if the diff gate of the design can see the hole: a gate that
compares the old and the new verdicts sees a regression only where the old checker is
right.

| Id | Design | Shape | Probe or trace | Today | Gate sees it | Tag |
| --- | --- | --- | --- | --- | --- | --- |
| H1 | MIR | abort value binds after the cleanup chain | M3 (`m8_abort_value_into_body.wf`), trace `m3_mir` | accepted, faults | no | realistic |
| H2 | MIR | frame root does not end on an abort path | M4 (`m10_abort_value_callee_local.wf`) | accepted, faults | no | edge |
| H3 | MIR | `Recopy` gives new versions to references that point outside | `j4_multi_outer_ref.wf`, trace `j4_mir` | rejected (correct) | only with a J4 probe | realistic |
| H4 | MIR | bind and free at the `Call` return node | trace `f32_mir` | — | lint only | proof claim |
| H5 | MIR | no root for continuations | RR3 | rejected (correct) | yes (RR3 repro) | — |
| H6 | Machine | `KeptCell` capture that the closure borrows | `j5_kept_borrow.wf`, `j5d_maker_borrow.wf` | accepted, faults | no | realistic |
| H7 | Machine | clause split only at `Resume` nodes | `j2_post_resume_closure.wf` | rejected (by accident) | only with a J2 probe | realistic |
| H8 | Machine | a resuming clause value does not bind `dest` | `j3_resuming_clause_value.wf` | rejected (correct) | only with a J3-like probe | realistic |
| H9 | Machine | `Dead` emits no `scope_end` for a local that is not plain data | (design rule) | — | no (verifier does not check) | fragility |
| H10 | Minimal | the whole clause runs at the perform | `j1_post_resume_keep.wf`, trace `j1_minimal` | accepted, faults | no | realistic |
| H11 | Minimal | clause-frame and callee-frame places have no root | `j6_resume_temp_keep.wf`, F3-2, M4 | J6: `616f99c` rejects | yes for J6 (r3 sweeps) | realistic |
| H12 | Minimal | the continuation root ends only in the clause component | RR3 `to_outer_local` | rejected (correct) | yes (RR3 repro) | — |
| H13 | Minimal | abort node binds `dest` and unwinds the body at one node | trace `m3_minimal` | — | lint only | proof claim |
| H14 | Minimal | kept classes: LOOP, STATE, SUM, FNVAL, CAP, STORE; `on abort`; OL-R2a | F3-1, OL-R2a | — | partly | — |
| H15 | MIR, minimal | the gate does not block a program that both pipelines accept and the oracle faults on | M1, M3, J1, J5d | — | — | process |

### H1 (MIR): the abort value binds after the cleanup chain

MIR 4.1: "The `unwind exit` of the handled body → abort node → return node". 4.9: the
return node gives `dest` "the places of `_0` and of `clause_values`". So for M3

```weft
let r = handle Pick { fn pick(v) { &v[0] } } in { let w = Vec.new(); w.push(3); pick(&w) }
print(r)
```

the cleanup chain frees `w` (`unwound_at(S(w), u2)`) before the return node binds the
new version of `r` into `w[]`. `invalid` stops at `rebound_at`, so `print(r)` is not an
error. Trace `m3_mir`: no lint fires. The machine design binds the clause value at
`AbortValue(h)` before the cleanup copy, so the free reaches it: trace `m3_machine`
gives W0301 at `print(r)`.

Today also accepts M3, so the MIR gate puts it in the class "Same", which has no rule.
Fix: graft the machine node `AbortValue(h)` (one node for each suspending node and each
local handler that it can abort to).

### H2 (MIR): the callee frame root does not end on an abort path

MIR 4.6: the owner "frame of f at C" has `rebound_at` at the call node and `scope_end`
at the return node. A call that aborts to a local handler leaves through the abort edge
and never reaches its return node. In M4 the clause value points into a local of the
callee `body` (the operation argument), so `r` keeps a place in a frame that never
ends. M4 stays open. The machine design ends the callee frame variable "at `FrameEnd`
of `n` and on its abort paths". Fix: the same in MIR.

### H3 (MIR): `Recopy` forgets the invalidations of outer places

MIR 4.7: `Recopy(ls)` gives "a new version of each reference path of `l`, with the
places that it had at the suspension point". The new version is a definition, so it
also kills the old version (4.2). Probe J4:

```weft
handle Pick { fn pick() { resume(true); resume(false) } } in {
    let r = &o[0]          // o is outside the handled body: the copy shares it
    let b = pick()
    print(r + 1)           // the second run reads o after the first run cleared it
    o.clear()
}
```

The second run reads a dangling reference (oracle). Today rejects J4 (the `resume
again` node does not bind `r`). In MIR the clear invalidates `r`, but `invalid` stops at
the `Recopy` node, which binds the new version (trace `j4_mir`: no lint). The machine
rule binds only a variable whose places are all in the copied frames, so `r` keeps its
state (trace `j4_machine`: W0301). The corpus case `102_wild_instances.wf::twice` uses a
local outside the handled body, so it does not cover this shape. Fix: the machine
`Copy` rule. Add J4 to the gate.

### H4 (MIR): bind and free at one node breaks `no_gen_kill`

MIR D16 gives a call two nodes: the call node and the return node. The return node binds
the destination (and the weak definitions of `assigns` and `stores`), and the frame root
ends there. When a value points into the frame root, one node binds and invalidates it:
trace `f32_mir` fires the B6 lint `gen_and_kill`. The error still comes (the spec
propagates `invalidated_at` to the successors), so this is not unsound. But MIR claims
"A5 `no_gen_kill`: B" and "`no_gen_kill` follows from D16" for the proof link. The
machine phase `FrameEnd` after `Ret` keeps the two apart (trace `f32_machine`: no lint).

### H5 (MIR): continuations have no root

MIR roots (4.3) cover locals, cells, parameters, groups, `Arg` roots, callee frames and
handler capabilities. A continuation is the parameter `_2: Cont` of a clause. A closure
that captures it holds no place, so no fact ends it. RR3 and V120 then depend on W0313
in sema, which stays until stage M9 and reads `AbsValue::caps`. The design does not put
continuations in `caps`, and the M9 rules of 5.5 use `cap_root` of handler roots only.
So the claims "RR3: B9" and "V120: B9" have no mechanism. Today rejects RR3, so the gate
shows a regression. Fix: a continuation root that ends at the `Handle` return node and
at the abort node (the machine and minimal designs both have one).

### H6 (machine): a `KeptCell` capture that the closure borrows (J5, J5d)

Machine 3.1.7: "`KeptCell` if the variable is plain data and the body does not move it."
To keep V012 fixed, a `KeptCell` closure does not point into the variable. Probe J5d:

```weft
struct Point { x: u64, y: u64 }
fn norm(p: &Point) -> u64 { p.x * p.x + p.y * p.y }
fn make(a: u64) -> fn() {
    let p = Point { x: a, y: 2 }
    || print(norm(&p))
}
fn main() { let f = make(3); f() }
```

`b073ea7` and `616f99c` accept it. `run --oracle` reports "a reference into a local whose
scope ended is used". The task form (`j5c_kept_borrow_task.wf`) is W0405 today (the
V125 fix), but the closure form is not. In the machine design the reference `&p` is made
inside the closure body when `f()` runs, after `p` ended, so `invalid` never reaches it.
The design marks this "Decision needed (V125)", but its tables put the finding V125
(5.2) and the invariant F5 `kept` (4.8) under "construction". MIR (D5: a borrow makes the capture `ByRef`) and the minimal design
(rule CAPTURE: `Kept` only with no borrow) reject J5d with W0204 and keep the control
`j5b_kept_write.wf` (read and write, no borrow) accepted. Fix: the minimal rule.

### H7 (machine): the clause split only at `Resume` nodes (J2)

Machine 4.5: `pre` and `post` are "split at the `Resume` nodes". In J2 the clause
resumes through a closure:
`fn tick() { let k = || resume(()); k(); v.clear() }`. The clause has no `Resume` node,
so a literal reading puts `v.clear()` in `pre`, at the perform, before the body makes
`keep = &v[0]`. The oracle faults. Today rejects J2 only by accident: the syntax test
cannot prove that `k()` resumes, so it adds an abort edge, and the flow-insensitive
`points_into(keep, v[])` makes `keep` invalid on that path (`check --explain`). A precise
machine analysis drops that edge. MIR defines a resume point as "a `Resume` call or a
call whose apply resumes" and applies the part "after its first resume point". Fix:
take that definition, and say "after the first resume point" (a `multi` clause has
code between two resumes).

### H8 (machine): the value of a resuming clause

`semantics.md` 8.3: the value of a `handle` is the value of the outermost clause if a
clause ended at the outer level. The machine text binds `dest` at `Exit` to `_0` of the
handled body, and `Post` applies the clause code after `resume`, but no rule binds
`dest` to the clause value. Probe J3 (`fn tick() { let x = resume(()); &u[0] }`, then
`u.clear(); print(r)`) faults. Today rejects it. MIR (return node: `_0` and
`clause_values`) and the minimal design (the handle value node) bind the union. Fix:
bind `dest` at `Post` to the clause `ret` too (a weak definition), or at `Exit` to the
union.

### H9 (machine): `scope_end` only at `Drop` for a value that is not plain data

Machine 4.1: "`Dead(l)`: `scope_end(v, n)` ... only if `l` is plain data. A local that
is not plain data got its `scope_end` at its `Drop`." So the free of each owned value
depends on a `Drop` that the builder must write. The verifier (V1 to V12) checks cells,
not drops. A builder bug that omits one `Drop` loses a free, and no check sees it.
Separately, V6 lets `_0` keep its cell at `UnwindExit`. The value of a scope body is in
`_0` across `ScopeWait`, which can abort. In stage 3b the unwinder runs the cleanup
chains only, so a linear `_0` with `on abort` is not finished (a run-time leak; the
checker side is W0602 and stays right). Fix: `Dead` always emits `scope_end` (a second
free of a root changes no result), `Drop` marks only the W0601 point; put `_0` in the
cleanup chain after its assignment.

### H10 (minimal): the whole clause runs at the perform (J1)

Minimal 4.8 keeps "the order of today" and applies `Σ(clause)` at each perform. Probe J1:

```weft
let keep = &u[0]
handle Tick { fn tick() { resume(()); v.clear() } } in { tick(); keep = &v[0] }
print(keep + 1)
```

`b073ea7` and `616f99c` accept it, and the oracle faults. The trace `j1_minimal` (the
clear at the perform node, `keep` bound after it) gives no error. MIR (after-body node)
and the machine design (`Post`) give W0301 (traces `j1_mir`, `j1_machine`). The M1
probes (`m1_post_resume.wf`, `postres.wf`) are different: there the clause returns the
`resume` result, and the minimal `Π(h)` gives that result the places of the body value,
so the minimal design finds them inside the clause. J1 has no such use.

### H11 (minimal): clause and callee frames have no roots (J6, F3-2, M4)

The minimal projection drops "the locals and temporaries of B". A place in a clause
local or a callee local that leaves through a `resume` value, a store or a clause value
then has no free in the function component. Probe J6 (`resume(first(&mk_v())); ()`,
the body keeps the result in an outer local) is accepted at `b073ea7`, rejected at
`616f99c` (the R3a fix), and the oracle faults. The minimal plan deletes the R3a frame
fixes (8.4), so J6 regresses. The r3 sweeps (`sweep.py`, frame `resume`, way out
"assignment") have such programs, so the gate shows it. F3-2 and M4 have no fix in the
design at all.

### H12 (minimal): the continuation root ends in the wrong component

See 3.12. The `ClauseFrame` local ends in the clause component. A closure that the clause
stores in an outer local is used in the function component, which has no free of that
root. Fix: end the clause-frame root also at the abort node and at the end of the
`handle` in the function component (as the machine `Landing` and `Post` do).

### H13 (minimal): the abort node binds and unwinds at one node

Minimal 4.8: the abort node `A` has `unwound_at(v, A)` for the body locals and
`rebound_at(dest, A)` with the clause value. For M3 the trace `m3_minimal` gives W0301
at the handle value node (it uses `dest` before it binds it), so the design finds M3.
But `A` also fires `gen_and_kill`, and the design claims A5 "structure". The lint fires
only where an error exists, so the corpus lint stays clean; the claim is still wrong.

### H14 (minimal): the kept mechanisms

The minimal design keeps `lower_loop` and W0707 (LOOP), flow-insensitive `points_into`
and lowering state for `uniq`, task sets and part holders (STATE), `EffectSig` and its
24 parts (SUM, most of FNVAL), the capability marks of `caps.rs` (CAP), and atomic
`on abort` (FD1, F3-1, F3-3, V119). It has no re-entry edge for a `multi` operation of a
handler of a caller (OL-R2a). By `root_causes.md` ("By round"), group B gave 30 of the 64
round-2 unsound findings and 13 of the 18 open-list findings. By its own count, the
minimal design removes 15 of the 70 group-B findings by one rule; 46 go partly and 9
stay.

### H15 (gates): a program that both pipelines accept

The MIR gate (8.2) has the class "Same: `D_new = D_old`: none". The minimal gate runs the
oracle on each accepted program (check 4), but its classes block only differences. So
in both, an old hole that the new pipeline keeps (H1, H2, H10, J5d) passes each stage.
The machine gate has exit criterion 1 ("no input that `ir` accepts faults under the
oracle") and criterion 8 (a fresh sweep of 50 000 programs). But its cost paragraph says
that "the oracle runs only for the inputs whose verdict differs", which does not test
criterion 1. Fix for all three: run the oracle (all seeds of the harness) on each
accepted input, and block on each fault, also in the class "Same".

### Other notes (not holes)

- MIR and the machine design make the interpreter run the IR, and they delete
  `compile.rs` (MIR at M8, the machine design at S3a). After that, a builder defect is
  the same in the checker and in the interpreter, and only the oracle and the docs can
  show it. Keep the AST compiler behind a flag as a differential oracle until the two
  review rounds after the cut over end.
- Choice A (MIR, machine) changes the output of `x + { x = 5; 1 }`. It is consistent in
  the checker and the interpreter. The minimal ORDER-2 rule keeps the read points of
  today with early borrows; its "inert" test is a new single rule that can be wrong.
- MIR D5 gives `ByRef` to a captured integer that the function assigns. So a closure
  that changes a captured integer cannot leave the scope of the integer. The control
  `j5b_kept_write.wf` (`|| { n += 1; print(n) }`, called after the block) runs cleanly
  today, the machine and minimal rules accept it, and MIR rejects it (W0301). This is
  sound, but it is a new false positive and a language change that ADR 0012 must state.

## 5. The new probes in each design

| Probe | Today `b073ea7` | `616f99c` | Oracle | MIR | Machine | Minimal |
| --- | --- | --- | --- | --- | --- | --- |
| `postres.wf`, `m1_post_resume.wf` (M1) | accepted | accepted | faults | ✓ | ✓ | ✓ (inside the clause, through the `resume` result) |
| `m6b_resume_result_ref.wf` (M2) | accepted | accepted | faults | ✓ | ✓ | ✓ |
| `m8_abort_value_into_body.wf` (M3) | accepted | accepted | faults | ✗ (H1) | ✓ | ✓ (H13) |
| `m10_abort_value_callee_local.wf` (M4) | accepted | accepted | faults | ✗ (H2) | ✓ | ✗ (H11) |
| `j1_post_resume_keep.wf` | accepted | accepted | faults | ✓ | ✓ | ✗ (H10) |
| `j2_post_resume_closure.wf` | rejected | rejected | faults | ✓ | ? (H7) | ✓ (by the accident of today) |
| `j3_resuming_clause_value.wf` | rejected | rejected | faults | ✓ | ? (H8) | ✓ |
| `j4_multi_outer_ref.wf` | rejected | rejected | faults | ✗ (H3) | ✓ | ✓ (K) |
| `j5_kept_borrow.wf`, `j5d_maker_borrow.wf` | accepted | accepted | faults | ✓ | ✗ (H6) | ✓ |
| `j5b_kept_write.wf` (control) | accepted | accepted | clean | ✗ (W0301, stricter) | ✓ | ✓ |
| `j6_resume_temp_keep.wf` | accepted | rejected | faults | ✓ | ✓ | ✗ (H11) |

## 6. Scores

### Machine: 8.0

Strengths:

- The node phases (`Ret`, `FrameEnd`, `AbortValue`, `Exit`, `Post`, `Landing`, `Copy`)
  make "a value binds where it exists, before each free after it" a rule of
  construction. This is the exact defect of the round-3 frame findings and of M1 to M4.
  My traces found no frame-boundary gap, and no node binds and frees at once.
- It is the only design that closes all of M1 to M4, and it found them.
- Cleanup chains copied for each abort destination make `unwound_at` and `spared_at`
  facts of the CFG (SUSP, V074 to V089, V116).
- The `Copy` rule for re-entry is right for references that point outside the copied
  frames (J4), for a local handler and for a handler of a caller (OL-R2a).
- Capability and continuation roots turn W0313 into W0301 on roots (RR3, RT16), and
  callee and caller frame roots cover F3-2, M4, map N1 and N2 by one rule.
- The strongest gate: an oracle criterion on each accepted input, a fresh sweep, a fact
  oracle, a summary oracle that tests the "one rule" claims, and trace conformance.
- It is honest about verdicts: 87 by construction and 64 by one rule, with a sketch
  crate that compiles and checks that each spec input relation has a source.

Flaws:

- `KeptCell` leaves J5 and J5d open (H6), a realistic blocker, while the verdict table
  claims V125 and F5 by construction.
- Two clause rules are under-specified: the resume point (H7) and the value of a
  resuming clause (H8). The literal text gives regressions.
- `Dead` emits no `scope_end` for an owned value (H9). This makes each free hang on a
  `Drop` that the verifier does not check. `_0` is not in the cleanup chains of stage 3b.
- The gate text contradicts itself on where the oracle runs (H15).
- `points_into` stays flow-insensitive in the facts (STATE false positives stay; not a
  soundness issue).

### MIR: 7.0

Strengths:

- Each group-A class goes by construction, and the after-body node closes M1 (M-new),
  which it found. The capture rule D5 closes J5 and J5d.
- Reference versions give a flow-sensitive `points_into` with no spec change, with a
  soundness argument (4.2). The after-resume definition of the clause is the most
  precise of the three (H7 and H8 are right in MIR).
- `on abort` as an apply on the cleanup path closes FD1, F3-1 and F3-3 for the facts.
- The fact oracle (6.5) tests the B6 hypotheses on each run, and the claims test ties
  each "by construction" verdict to a repro.

Flaws:

- The abort value binds after the cleanup chain (H1): M3, realistic, and the MIR gate
  cannot see it.
- Frame roots do not end on abort paths (H2): M4.
- `Recopy` kills versions that point outside the copied frames (H3): J4 regresses.
- The return node binds and frees at once (H4): the A5 claim and the planned
  `no_gen_kill` lemma are false as written.
- Continuations have no root (H5); CAP waits for the optional stage M9.
- The count 114 "by construction" mixes construction and one-rule mechanisms; the
  versions, frame roots and count query are single points of failure like the machine
  analysis, and H1 to H3 are in exactly these mechanisms.
- The gate does not block old holes that stay (H15).

### Minimal: 4.5

Strengths:

- The smallest change and the lowest regression risk: 14 000 lines of the fact generator
  that three rounds fixed stay, and the interpreter semantics do not change (ORDER-2
  keeps the read points of today).
- Rule FRAME, ANF and explicit storage close TEMP, TAIL and most of DROP; O3-2, O3-3
  (direct forms), O3-4, F3-7 and M3 (H13) go.
- Rule CAPTURE ("`Kept` only with no borrow") is the best capture rule of the three
  (J5d closed, `j5b_kept_write.wf` accepted).
- The relation table `RELS` with a destructuring test is a good guard against a summary
  that forgets a new relation.
- Per-construct-group rollout with a per-body fallback makes each step small.

Flaws:

- The whole clause still runs at the perform (H10): J1, realistic, open today, and the
  gate cannot see it.
- No roots for clause and callee frames (H11): F3-2, M4, and a J6 regression.
- The continuation root ends in the clause component only (H12): RR3 regresses.
- `on abort` stays atomic: F3-1, F3-3, FD1 stay (H14).
- LOOP, STATE, SUM, FNVAL, CAP and STORE keep the mechanisms that gave most of the
  round-2 and open-list blockers; OL-R2a stays. With two review rounds left after the
  IR, this is the largest residual risk.
- Some verdicts are not supported by the text (O3-5, RR3, V120). 43 of its 91 "by
  construction" findings depend on one shared rule.
- The weakest gate: about 1 750 programs at each commit, and no rule for a program that
  both pipelines accept and the oracle faults on (H15).

## 7. Recommendation

Take the machine design as the base. It is the only design whose core mechanism (node
phases and frame roots) I could not break at a frame boundary, and the frame boundary
is where round 3 found its blockers. Its gaps are a decision and two text gaps, not
ordering defects in the core.

Graft these parts before stage S2 ends:

| Graft | From | Closes |
| --- | --- | --- |
| Capture rule: `Kept` only for plain data that no body borrows; else `ByRef` | minimal (rule CAPTURE) | H6 (J5, J5d), V125 family |
| Resume point = a `Resume` call or a call whose apply resumes; `post` = after the first resume point | MIR (4.6) | H7 (J2), code between two `multi` resumes |
| `dest` of a `Handle` = `_0` of the body ∪ clause values (weak definition at `Post`) | MIR (4.9), minimal (4.8) | H8 (J3) |
| `Dead` always emits `scope_end`; `_0` in the cleanup chain after its assignment | — | H9 |
| Fact oracle and claims test | MIR (6.5, 8.2 check 7) | tests the "one rule" verdicts |
| Relation table `RELS` with a field-by-field test, for the summary procedure | minimal (4.7) | a new relation that misses a summary part |
| Reference versions (optional, for precision) with the machine `Copy` rule | MIR (4.2) | STATE false positives; keep H3 closed |
| Per-construct-group rollout with a per-body fallback | minimal (8.3) | migration risk |

Change the gate: run the oracle (all seeds and worker counts of the harness) on each
input that the new pipeline accepts, and block on each fault, also when the old pipeline
accepts the input too. Add to the gate inputs: J1 to J6, M1 to M4, `postres.wf`, and the
controls `j5b_kept_write.wf` and `j5c_kept_borrow_task.wf`.

If the team prefers MIR, these fixes are required before stage M6 ends: `AbortValue`
before the cleanup chain (H1); frame roots end on abort paths (H2); `Recopy` binds only
paths whose places are all in the copied frames (H3); a third call node `FrameEnd` (H4);
a continuation root (H5); the gate change above (H15).

The minimal design does not meet the soundness lens unless it also takes the after-resume
node, clause and callee frame roots, `on abort` as an apply and a CFG fixpoint. With
those it is no longer a minimal change.

File J5d as a realistic blocker against the current code: it is open at `b073ea7`,
`616f99c` and `b25faf0`. J1 is a second one. M3 (realistic by the machine report) is
also still open at `b25faf0`.

## 8. Files

All paths are in
`SCRATCH/ir/`.

| File | Content |
| --- | --- |
| `judge_soundness.md` | this report |
| `judge_sound/run_all.sh` | runs each fact trace through `spec/weft.dl` (`weft lint`) and each probe at both commits with the oracle |
| `judge_sound/empty.wf`, `judge_sound/common.dl` | the empty program; the shared `gen_and_kill` lint |
| `judge_sound/o32_{mir,machine,minimal}.dl` | O3-2 traces |
| `judge_sound/m3_{mir,machine,minimal}.dl` | M3 traces (H1, H13) |
| `judge_sound/j1_{mir,machine,minimal}.dl` | J1 traces (H10) |
| `judge_sound/j4_{mir,machine}.dl` | J4 traces (H3) |
| `judge_sound/f32_{mir,machine}.dl` | F3-2 traces (H4) |
| `judge_sound/j1_post_resume_keep.wf` | J1: clause change after `resume`, reference kept by the body |
| `judge_sound/j2_post_resume_closure.wf` | J2: the same with a resume through a closure |
| `judge_sound/j3_resuming_clause_value.wf` | J3: a resuming clause returns another reference |
| `judge_sound/j4_multi_outer_ref.wf` | J4: a `multi` re-run with a reference into an outer place |
| `judge_sound/j5_kept_borrow.wf`, `j5d_maker_borrow.wf` | J5, J5d: a closure borrows a captured copy value after its scope |
| `judge_sound/j5b_kept_write.wf`, `j5c_kept_borrow_task.wf` | controls for J5 |
| `judge_sound/j6_resume_temp_keep.wf` | J6: a `resume` value into a clause temporary, kept by the body |
