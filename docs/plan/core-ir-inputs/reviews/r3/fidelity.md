# Review round 3, lens "fidelity": spec and design fidelity

Source: `r3/src`, commit b073ea7 (head of `review/s5` after S5b and S5c). Binary:
`r3/target/release/weft`. I did not change the source. I made a copy for the proofs and
the tests (`r3/fidelity/src`, with its own target directory). All files of this lens are
in `SCRATCH/r3/fidelity/`
(below: `FID/`). Each finding has a repro in `FID/repro/` (`F3-N_*.wf` and `F3-N_run.sh`).

## Summary

- 15 findings: 8 blockers, 7 minors.
- Agreement holds everywhere. `weft agree` agrees on each corpus, interpreter, prelude,
  example and package program under each profile, on 10 000 mutated programs, and on
  8 000 programs of the other lenses. It also agrees on each repro of this report. So
  seven blockers are in fact generation (`crates/weft-sema`) or in the interpreter, and
  one blocker (F3-5) is in a rule of `spec/weft.dl` itself.
- The proof claims hold. At the pinned Verus revision: borrowing 169, effects 122, link
  235, `weft-verified` 67 (27, 16, 9, 15 by module), all with 0 errors, as the READMEs
  say. The mutation scripts catch each mutation as their tables say: effects 8 of 8,
  borrowing 9 of 9 (each with the result line of its table), link 26 of 26 (17 "link
  only"). No proof source has `assume`, `admit`,
  `external_body` or an axiom.
- `cargo test --release --workspace` passes on the copy: 587 passed, 0 failed, 2
  ignored (performance targets).
- The round-2 fixes hold for the shapes that round 2 reported (FD1 to FD15). The new
  code has gaps at its edges: three blockers (F3-1, F3-3, F3-4) are holes in W0118,
  which R2c added for round-2 FD1. The pre-round-2 binary (328a39b) also accepts each
  blocker shape, so round 2 did not add them.
- Five blockers break a guarantee that a proof needs and that a doc says the checker
  mirrors: "`on abort` changes only its value" (F3-1), "no stored references" (F3-2),
  "each linear value is consumed or aborted exactly once" (F3-3, F3-6, F3-7, F3-8).

| Id | Severity | Statement |
| --- | --- | --- |
| F3-1 | blocker | W0118 does not see an `on abort` change through a reference that the value holds. The unwinder changes a place of the caller, and a reference dangles. |
| F3-2 | blocker | A closure or a clause keeps its reference parameter in a local outside it. A callee gives it a reference into a local of the callee. The kept reference dangles. |
| F3-3 | blocker | A generic `on abort` function drops a value of its type parameter. For `G<Tx>` the linear `Tx` leaks on each abort path. |
| F3-4 | blocker | The check of an `on abort` function ignores the type arguments of its parameter. The unwinder gives a `G<Tx>` to a function of `G<u64>`: a type confusion. |
| F3-5 | blocker | A move of a part (`take(p.a)`) does not invalidate a reference to the whole value (`r = &p`). A read through `r` reads the moved part. The spec rule is too narrow. |
| F3-6 | blocker | The runtime drops a linear task result: an abort while a `Task<Tx>` handle is live, a spawn in statement position, and a `fork` that a failure or a timeout ends. No error. |
| F3-7 | blocker | The value of a scope body is not checked across the end of the scope. A failed child aborts there, and the unwinder stops: "`Tx` has no `on abort`". |
| F3-8 | blocker | A task or a fork branch that takes a linear value by value can be cancelled before it starts. The checker gives no W0602, and the interpreter does not run `on abort` for it. |
| F3-9 | minor | The oracle does not flag a read through a reference into a local of a frame that an abort path unwound. ADR 0010 says that it does. |
| F3-10 | minor | ADR 0006 says that the checker does not use the verified mode lattice. It does (ADR 0004, `rules.rs`). |
| F3-11 | minor | A closure that gives a captured reference a new value does not rebind it where it runs: W0301 on a correct program. No ADR records it. |
| F3-12 | minor | ADR 0002 says that the W01xx checks do not look at the effects or places of a body. W0118 does. |
| F3-13 | minor | `docs/traceability.md` names tests that do not test four of its rows. |
| F3-14 | minor | Standard library items of the design (formatter, channels and `select`, JSON, tracing, HTTP client) are not in Phase 1, and no ADR or plan item records it. |
| F3-15 | minor | `proofs/link/README.md` says "The interpreter must not copy a record". `copy_frames` copies the records of nested continuations. |

## Method

1. I read CLAUDE.md, README.md, the design, the architecture, the plan, the spec, the
   eleven ADRs, `docs/traceability.md`, the four proof READMEs, the crate docs, the two
   proof reports, the reports of rounds 1 and 2, the open lists of
   `round1b_tasks.md`, and the round-3 redteam and oracle reports (to avoid
   duplicates; F3-5 and F3-6 name the overlaps).
2. Part (1): I took the matrix of `docs/traceability.md` as the start and checked each
   row with a probe, with the most attention to the guarantees that rounds R2a to S5c
   added to the ADRs (`git diff 328a39b b073ea7 -- docs spec`). About 65 probes are in
   `FID/p/`.
3. Part (2): I checked each code name of the docs against the source
   (`FID/tools/names.py`), each test name, each limit and constant, each command of the
   README with its exit code, the JSON format, the markers, the large-stack entry
   points, the verified pieces and their users, and the proof counts (Verus, by crate
   and by module). I ran the mutation scripts of the three proof crates (section
   "Proof runs").
4. Part (3): for each rule of the effects report (1 to 6, and 7 and 8 of the README)
   and of the borrowing report (notes 1 to 5 and the assumptions), I looked for its
   mirror and wrote probes. I compared `Ctx::invalidates` with the B3 kill rule, and I
   ran the B6 lints (`no_gen_kill`, `bound_before_use`) and a lint for `typed_by`
   (`FID/tools/typed.dl`) on all accepted programs that I had.
5. Part (4): `FID/tools/agree_all.sh` (each program, each profile),
   `FID/tools/mutagree.py` and `mutagree3.py` (mutations), `FID/tools/agree_list.py`
   (programs of the other lenses).
6. For each finding I confirmed the fault at run time with `weft run --oracle`, and I
   ran the pre-round-2 binary (`/home/user/wt-edge`, 328a39b) to see if the shape is
   new. Each blocker shape is accepted by that binary too. So round 2 did not add
   them, but F3-1, F3-3 and F3-4 are holes in the R2c fix of round-2 FD1 (W0118).

## Blockers

### F3-1: W0118 misses a change through a reference in the value

Repro: `FID/repro/F3-1_run.sh`.

```weft
linear struct R { o: Option<&Vec<u64>> }
    on abort = undo_ref
fn undo_ref(r: R) {
    let R(o) = r
    match o { Some(v) => v.push(7), None => {} }   // expected W0118
}
```

- ADR 0007 says: "It can change only the value that it gets: not an `rc` group, and not
  a place that a reference in the value points to (W0118)." Rule 8 of
  `proofs/effects/README.md` says the same, and the effects proof needs it (`on abort`
  is atomic).
- `check_on_abort_rows` (`crates/weft-sema/src/program.rs`) flags a mutation only if its
  root is not `Param(0)` or its steps hold `Held`. A by-value parameter that holds
  references "points into a parameter root" (ADR 0003). So the push through `o` is
  `mut(r)` (the W0703 hint of a public copy says `add mut(r)`), and the check sees a
  change of the value itself.
- `main` holds `first = &v[0]`. The abort runs `undo_ref`, which pushes into `v`. No
  node of `main` or `body` states the change. The oracle reports "a read of a freed
  cell (a dangling reference)". A tuple part `(u64, &Vec<u64>)` and a `Vec<&Vec<u64>>`
  give the same result (`F3-1_on_abort_ref_in_value_more.wf`).
- Fix: in W0118, count a change as outside when the parameter type holds a reference
  and the changed place is below that reference. Or reject `on abort` for a type that
  holds a reference.

### F3-2: a closure or a clause keeps a reference into a local of a callee

Repro: `FID/repro/F3-2_run.sh` (five programs and a control).

```weft
fn apply(f: fn(&u64)) {
    let x = 5
    f(&x)
}
fn main() {
    let y = 1
    let last = &y
    apply(|r| last = r)
    print(last)   // expected W0301; the checker accepts
}
```

- The closure keeps its parameter in `last` (`keep = x` of ADR 0005). ADR 0005 says: "At
  each node where it runs, the local then points into the place that the node gives."
  The node `apply(...)` gives a place in a local of `apply`. That place has no name in
  `main`, so `last` gets no new place. Nothing invalidates it. The oracle reports a
  dangling reference. A `Vec` outside the closure (`keep.push(r)`) is the same.
- The same holds for a handler clause: `handle Keep { fn keep(r) { last = r; resume(()) } }
  in deep()`, where `deep` performs `keep(&x)` with its own local. ADR 0005 says that
  "each `resume` of the handler frees each reference parameter of the clause" when a
  callee performs the operation. The `releases_at` fact is at the `resume` node. That
  node is in the component of the clause, which has no edge to the body
  (`weft-facts` crate doc: each clause body is one connected component). So the free
  never reaches the use after the `handle`. With no `resume`, the run reads a moved
  cell and prints `<moved>` (see F3-9).
- Control: the same operation in a closure of the handled body is W0301 (`p/st8.wf`).
- ADR 0003 says that the checker mirrors the "no stored references" assumption of the
  borrowing proof. The recorded R2b FD3 residual names a store into an `rc` object or
  behind a reference parameter. This is a new shape: a store into a local of the
  function that makes the closure or the handler. It is the simplest form.
- Fix: at a node that runs a closure or a clause through a callee, give each place that
  the callee lends and that the caller cannot name a root of its own, and free that
  root at the node (`frees_at` or `releases_at` at the call node). Then `keep = x`
  makes the local invalid after the call.

### F3-3: a generic `on abort` function drops a linear part

Repro: `FID/repro/F3-3_run.sh`.

```weft
linear struct G<T> { x: T }
    on abort = undo_g
fn undo_g<T>(g: G<T>) {
    let G(x) = g
    print("undo")
}   // drops x: a value of type parameter T
```

- `body` holds `G { x: Tx { id: 1 } }` across an operation whose clause does not resume.
  `G<Tx>` has `on abort` ("a type around the part can have it too: that `on abort`
  finishes its parts", ADR 0007). The unwinder calls `undo_g`, which drops `x`. The
  oracle reports a linear leak. A generic `forget(x)` is the same.
- `drops` of `undo_g` has `T`, but only a call checks `drops` (W0601). The unwinder
  call is not a call of the facts. So no rule checks the type argument.
- The interpreter crate doc says: "The checker (W0601, W0602) and the unwinder do that
  [each linear value finishes]." This is false here. E3 (abort safety) does not hold.
- Control: the same function with a concrete part type is W0601.
- Fix: in W0118, reject an `on abort` function with a type parameter in `drops` (or in
  `holds` at a node that can abort). Or check the `drops` part of the `on abort`
  function against the type arguments at each place where a linear value can abort.

### F3-4: the `on abort` parameter check ignores type arguments

Repro: `FID/repro/F3-4_run.sh`.

```weft
linear struct G<T> { x: T }
    on abort = undo_g
fn undo_g(g: G<u64>) {
    let G(x) = g
    print(x + 1)   // `x` is a `Tx` at run time
}
```

- `check_on_aborts` (`program.rs`) accepts a function whose one parameter is
  `Ty::Adt(b, _)` with `b == a`. It does not compare the type arguments. So `undo_g`
  takes `G<u64>` and the program has a `G<Tx>`.
- The unwinder gives the `G<Tx>` to `undo_g`. The run stops: "`Add` cannot apply to
  `Tx { id: 1 }` and `1`". With `print("{x}")` in place of `x + 1`, the run goes on, and
  the oracle reports a linear leak: `undo_g` treats the `Tx` as plain data.
- Fix: require the parameter type `G<T1, ..., Tn>` with the type parameters of the
  function in order, as for a method of `impl<T> G<T>`.

### F3-5: a part move keeps a reference to the whole value valid

Repro: `FID/repro/F3-5_run.sh`.

```weft
let p = Out { a: In { x: Vec.new() }, b: In { x: Vec.new() } }
p.a.x.push(4)
let r = &p
let n = take(p.a)
print(r.a.x.len())   // expected W0301; the run faults: "a value is used after it was moved"
```

- `frees_at(P, M) :- moved_part(M, P)` and `invalidated_at(R, P) :- points_into(R, Path),
  frees_at(P, M), prefix(M, Path)` kill only references at or below the moved part.
  `part_moved_at` stops the free of the whole root. So a reference to `p`, or to any
  place above `p.a`, stays valid. A read through it, or a call that gets it
  (`peek(r)`), reads the moved part.
- ADR 0003 says: "A move of a part frees that part only. References into the other
  parts stay valid. For W0302 the move is still a move of the whole local." W0302 sees
  a use of `p`. It does not see a use of `r`. Rule 4 of the design spares a reference
  to `p` only for a mutation, which leaves a value in `p.a`. A move leaves no value.
- `task_conflict` uses `overlaps` for a free, so W0405 sees this case. Only W0301 is
  short.
- `weft agree` agrees: the spec has the gap, and `rules.rs` mirrors it.
- Control: a move of the whole value is W0301.
- The redteam lens of this round reports the linear side of a part move (R3RT1:
  `live_linear` stops at the part move). This finding is the reference side, in another
  rule.
- Fix: add `invalidated_at(R, P) :- points_into(R, Path), moved_part(M, P),
  prefix(Path, M).` to the spec, the same to `rules.rs` (`free_kills` for a part move:
  `overlaps` in place of `prefix`), a probe for the evidence, and a corpus case. Each
  step of the checklist of ADR 0002 applies.

### F3-6: the runtime drops a linear task result

Repro: `FID/repro/F3-6_run.sh` (five programs and a control).

- The prelude declares `extern type Task<T> { linear, on_abort }`. So each `Task<T>` has
  `on abort`, also for a linear `T` with none. When a node aborts while a handle of a
  finished task is live, the unwinder runs the `on abort` of the handle: it cancels the
  task (`run_on_abort`, `Value::Task`). A finished task keeps its result, and nothing
  consumes or aborts it. For `T = Tx`, the oracle reports a linear leak. A
  `with_timeout` around the body gives the same leak (`F3-6_task_handle_timeout.wf`).
  This is the design example `profile_page` with linear results.
- A spawn in statement position (`s.spawn(|| begin())`) gives its handle to the scope.
  Nothing consumes the result. `t.detach()` of the same handle is W0601 (ADR 0007:
  `detach` drops the result), but the statement form is not
  (`F3-6_statement_spawn.wf`, control `F3-6_control_detach.wf`). The oracle lens of
  this round reports this shape too (O3-4). The other shapes of this finding are new.
- A `fork` whose other branch fails drops the value of the branch that is done
  (`fork_step` in `machine/exec.rs`). So does a `fork` that a `with_timeout` deadline
  unwinds (`F3-6_fork_failure.wf`, `F3-6_fork_timeout.wf`).
- The design says: cancellation "runs each live linear value's `on abort`, so partially
  completed work can't be silently dropped." Here completed work is dropped with no
  error. The checker accepts each program.
- Fix: `has_on_abort` of `Task<T>` holds only if `T` has no linear part or has
  `on abort`; the interpreter then runs the `on abort` of the result. A spawn in
  statement position of a closure with a linear result is W0601, as `detach` is. A
  `fork` with a linear branch value needs `on abort` for that value (W0602 at the
  `fork`), and the interpreter finishes the values of the branches that are done.

### F3-7: the value of a scope body across the end of the scope

Repro: `FID/repro/F3-7_run.sh`.

```weft
fn work() / async, fail {
    let t = scope { s =>
        s.spawn(|| boom())
        begin()           // the value of the body: a linear Tx
    }                     // the end of the scope raises the failure of the child
    commit(t)
}
```

- The run stops with "a linear value of type `Tx` has no `on abort`, so the unwinder
  cannot finish it". This is the state `err_no_on_abort` of the effects model, which E3
  excludes for a checked program.
- The facts of `work` have no `may_abort` at the end of the scope, and no variable holds
  the value of the body there. A linear local of the caller across the whole scope is
  W0602 (control `F3-7_control_outer_value.wf`), because the `scope` node can abort.
  ADR 0007 gives a hidden variable to a linear value on its way to a call; the end of
  a scope has none.
- Fix: give the value of a scope body a hidden variable from the tail to the end of
  the scope, and `may_abort` at the end of the scope if a child can fail.

### F3-8: a cancelled task that never ran drops its linear capture

Repro: `FID/repro/F3-8_run.sh`.

```weft
scope { s =>
    s.spawn(|| boom())
    let tx = begin()
    s.spawn(|| commit(tx))   // the closure takes tx by value
}
```

- The second closure takes `tx` when it is made (ADR 0003, a capture by value). The first
  task fails, and the scope cancels the second task. With some seeds and worker counts
  the second task never starts. Its closure goes away with `tx`. The oracle reports a
  linear leak in 38 of 63 runs. A `fork` branch is the same
  (`F3-8_cancelled_fork_branch_owns_linear.wf`, 25 of 63 runs).
- Checker: the closure is linear and moves into the task at the spawn, so `tx` is not
  live across a node that can abort. No rule sees that the task can be cancelled before
  it runs. W0602 must apply to the linear captures of a task closure at its spawn.
- Interpreter: with `on abort` on `Tx` the checker accepts (correct), but the leak stays
  (`F3-8_cancelled_task_on_abort.wf`): the unwinder does not run `on abort` for the
  captures of a task that never ran.
- Fix: W0602 at a spawn and at a `fork` for each linear value that the closure takes by
  value, if a sibling can fail or the scope can be cancelled. In the interpreter,
  finish the closure of a cancelled task that did not start (run `on abort` for its
  linear captures).

## Minors

### F3-9: the oracle misses a read into an unwound frame

Repro: `FID/repro/F3-9_run.sh`.

- ADR 0010: the oracle faults on "a reference into a local whose scope ended". It flags
  a read after a normal scope end (`end_cell` marks the cell). `unwind_frame`
  (`machine/effects.rs`) drops the values of a frame with `drop_value`, and does not
  mark the cells as ended. A read through a reference into such a local prints
  `<moved>` and the run goes on with exit code 0.
- The repro reads both kinds of dangling reference: the unwound one prints `<moved>`;
  the normal one faults.
- Effect: the corpus runs and the probes of the other lenses use the oracle to
  confirm soundness. They miss the abort-path shapes (the abort case of F3-2 is silent).
- A read other than `print` faults with "a value is used after it was moved", also with
  no oracle, so the gap shows mostly through `print`. The oracle lens reports that
  `print` hides a moved value (O3-13). This finding is the other cause: the unwinder
  does not end the cells.
- Fix: in `unwind_frame`, end each local and temporary cell for the oracle, as
  `end_cells` does.

### F3-10: ADR 0006 has a stale claim about the mode lattice

ADR 0006, first bullet: "The lattice is verified (`weft_verified::modes`), but the checker
does not use it yet: the mode rules use the flags." ADR 0004, `docs/architecture.md`
and the end of ADR 0006 say that the checker and sema use `modes::{submode, join}` (S5b,
F9). `rules.rs` calls them for W0406, W0403, W0401 and `pinned`. Repro:
`FID/repro/F3-10_run.sh`. Fix: delete the sentence.

### F3-11: a closure that rebinds a captured reference

`let h = || { r = grow(w) }; h(); print(r)` gets W0301. The same code with no closure
(`r = grow(w)`) is accepted. The run with the oracle has no fault. A closure adds the
places of a new value to the captured variable (ADR 0005, `keep = x`), but the node that
runs it never rebinds the variable, so the change in `grow` stays. No ADR lists this
imprecision. Repro: `FID/repro/F3-11_run.sh`. Fix: record it in ADR 0003, or rebind at
the run node when the closure gives the variable a new value on each path.

### F3-12: ADR 0002 justifies W0118 as a check of declarations

ADR 0002 keeps "Names, types and signatures: W01xx" in sema because "They look at types,
declarations and the syntax tree, not at the places, modes or effects of a body".
W0118 reads the inferred row, the `muts`, `raises` and `reaches` parts of the
signature of the `on abort` function: its effects and places. Repro:
`FID/repro/F3-12_run.sh`. Fix: list W0118 with its own reason (it checks a signature
that inference gives, as W0701 does).

### F3-13: wrong tests in `docs/traceability.md`

- "Scopes are the only way to spawn" names W0115 and tests 07, 14, 61, 132. None of
  them has W0115. Only `21_types.wf` (and `cli.rs`) tests it.
- "Each effect has one identity" names W0107 and tests 64, 141. Neither has W0107.
- "Cancellation runs `on abort`" names W0602 and test 131. Test 131 has no W0602.
- "Jumps do not leave a handled body" names W0315, W0111 and test 80. Test 80 has
  neither.

Repro: `FID/repro/F3-13_run.sh` and `FID/tools/trace.py`.

### F3-14: design standard library items with no record

The design ("Standard library", "What ships") lists one formatter, channels and
`select`, JSON, structured logging and tracing, and an HTTP client. Phase 1 has none of
them (`std/prelude.wf`, `weft help`). ADR 0001 and the plan list as Phase 2 only
HTTP/2, HTTP/3, TLS, SQL and the profiler. The traceability matrix has no row for the
section. Repro: `FID/repro/F3-14_run.sh`. Fix: one line in ADR 0001 and a row in the
matrix.

### F3-15: the link README forbids record copies that the interpreter makes

`proofs/link/README.md`, "What stays only tested": "The link assumes one exec record per
model record. The interpreter must not copy a record." `copy_frames`
(`machine/effects.rs`) gives each nested continuation of a copied `multi` continuation
a new record with the same state (`k: state`). The section "Differences" of the same
README describes this copy. So two exec records stand for one model record. This is
safe for a `multi` record (E5 keeps a fresh `once` continuation out of a `multi`
continuation), but the sentence is false as written. Repro: `FID/repro/F3-15_run.sh`.
Fix: say that the interpreter copies only the records of `multi` continuations, and
why `kont_rel` still holds for each copy.

## (1) Design rules and ADR guarantees: what enforces them

I start from `docs/traceability.md`. It is correct for each row, except the tests of
F3-13 and the claims below. This table lists only the rows where my probes found a
gap, or where a guarantee is new since round 2.

| Rule or guarantee | Enforced by | Status |
| --- | --- | --- |
| A use of an invalidated reference is an error (design rule 5) | spec `error` (W0301) | gap: a part move (F3-5); a callee local kept by a closure or a clause (F3-2) |
| No stored references (borrowing proof, ADR 0003) | W0204 for returns, stores behind reference parameters and into `rc` objects | gap: a store into a local outside a closure or a clause (F3-2) |
| `on abort` runs with the root handlers only, changes only its value (ADR 0007, effects rule 8) | sema W0118 | gap: a change through a reference in the value (F3-1); type arguments (F3-4) |
| A linear value is consumed or aborted exactly once (design, E3) | spec W0601, W0602; the unwinder | gap: generic `on abort` (F3-3); task results (F3-6); scope value (F3-7); cancelled task closures (F3-8) |
| Cancellation runs `on abort` of each live linear value (design) | W0602 at suspension points; interpreter | gap: F3-6, F3-8 |
| A `!Move`, task, scope, resource, `Rc` with references or functions is not `many` (ADR 0005, 0007) | spec `once_var`, `live_across_multi` | holds (probes `mv1.wf`, `mv2.wf`) |
| `spared_at`: a local operation suspends only its body, unless a clause performs outward (effects rule 1) | sema `spared_at` | holds, also for nested local handlers (`sp1.wf`) |
| A fresh `once` continuation is a `once` value, also in a closure, a tuple and a generic (effects rule 2) | spec W0503 | holds (`r2c.wf`) |
| A clause of `fail` cannot resume, also through the alias `fail` and a closure (effects rule 7) | sema W0504 | holds (`fr1.wf`) |
| `on abort` effects: user effects, `fail`, raises, unknown function values, no runtime (ADR 0007) | sema W0118 | holds (corpus 120, `oa3.wf`, `oa5.wf`) |
| Root handlers only in binaries and tests, also in a dependency and through an inner mock (design, W0801, W0802) | spec `root_handler_in_lib`, `sim_in_lib` | holds (`rh1.wf`, `pkg1`) |
| Public signatures state their effects (design) | sema W0701 | holds (`pub1.wf`) |
| `http.serve` runs its handler two times at one time (ADR 0006) | W0405 | holds (`hs1.wf`) |
| Fork branches and spawned tasks have separate footprints (design) | spec W0403, W0405 | holds (`fk1.wf`) |
| A returned container cannot hold a reference into a local (ADR 0003) | sema W0204 | holds (`st1.wf`) |
| Standard library items of the design | none | not in Phase 1, not recorded (F3-14) |

Rules with no enforcement and no record: only the standard library items of F3-14.
Round 2 FD10 (`env`) and FD11 (`shared`, globals) are now recorded (ADRs 0003, 0005,
0006).

## (2) Claims checked

True (I ran or read each one):

- README: each quick-start command, the example diagnostic (byte for byte), exit codes
  0, 1 and 2, option rejection for each command, `--workers` 1 to 1024, the markers and
  W0804, `--unchecked`, the package example ("`json` asks for too much"), and that `run`
  refuses a package with an authority error.
- `docs/architecture.md`: the diagrams match the spec rules; the inference limits
  (`parts_limit` = 2n + 32, `growth_limit`, `SIG_PLACE_STEPS` 8); the loop limits
  (8 passes, 16 places, 64 for a local); the large-stack entry points; the JSON format;
  "`weft deps` shows only the authority errors"; the verified pieces and their users
  (`places::concat` is unused; `modes` is used by the checker and sema); the cost claims
  that `scale.rs` asserts (at most three times the nodes).
- ADR 0002: the list of rules that moved to the spec; each test name; "a node of
  `sim_run_at`, `ref_at` and `ref_in` has no edges" (a lint on the corpus,
  `FID/tools/noedge.dl`); `corpus_exercises_every_rule` now checks each rule, not only
  the sinks (round-2 FD8 holds).
- ADR 0004, ADR 0008, ADR 0009, ADR 0010 (except F3-9).
- The spec header: each input relation of the body is in the header, and each header
  relation is used.
- `proofs/README.md`, `proofs/borrowing/README.md`, `proofs/effects/README.md`,
  `proofs/link/README.md`, `crates/weft-verified/README.md`: the counts (169, 122, 235,
  67; by module 27, 16, 9, 15 and the link table), the theorem and lemma names, the
  mutation tables of borrowing and effects (each row runs with its result line), the
  claim that only tests check the facts (round-2 FD5 holds), and "no `assume`,
  `admit`, `external_body`".

False or stale: ADR 0007 and effects README rule 8 on `on abort` changes (F3-1, part of
a blocker), the interpreter crate doc on finished linear values (F3-3, F3-6, F3-8),
ADR 0005 on `keep = x` and on `resume` freeing clause parameters (F3-2), ADR 0010 on
the oracle (F3-9), ADR 0006 (F3-10), ADR 0002 (F3-12), `docs/traceability.md` (F3-13),
`proofs/link/README.md` (F3-15).

## (3) Rules that the proofs need

Effects proof (rules 1 to 6 of the report, 7 and 8 of the README):

| Rule | Mirror | Status |
| --- | --- | --- |
| 1. Abort and multi rules at each suspension point | sema `may_abort`, `multi_at`, `clause_multi`, `body_multi`, `resumes_at`, `spared_at`; spec W0602, W0503 | mirrored for one task (`sp1.wf`, corpus 63, 124); the ends of tasks and scopes are not suspension points of the facts (F3-6, F3-7, F3-8) |
| 2. A fresh `once` continuation is a `once` value | `once_var`; a closure that holds it is not `many` | mirrored (`r2c.wf`) |
| 3. A handle body cannot return its own capability | sema W0313 | mirrored (ADR 0005 opens) |
| 4. A perform reaches the topmost handler frame | interpreter `find_handler` | mirrored (`lx1.wf`) |
| 5. The unwinder drops nested continuations | interpreter `unwind_frame` (`Frame::Clause`) | mirrored; nested `multi` records are copied (F3-15) |
| 6. Clauses run in the handle-site environment | sema clause environment | mirrored |
| 7. `fail` does not resume | sema W0504 | mirrored (`fr1.wf`) |
| 8. `on abort` is atomic | sema W0118 | not mirrored for references in the value (F3-1) |
| Model: one task | — | the multi-task paths drop linear values (F3-6, F3-8) |

Borrowing proof:

| Rule | Mirror | Status |
| --- | --- | --- |
| 1. Closures, handlers, continuations hold references | closure `points_into` | mirrored |
| 2. A call of a closure, a perform and a resume mutate the captures; a call that reaches a local handler gets its footprint | sema | mirrored (`lx1.wf`) |
| 3. Payload steps unstable; enum assignment mutates | sema | mirrored (corpus 30) |
| 4. One place per reference | multi-place `points_into` | not mirrored; recorded in `proofs/link/README.md` |
| 5. B4 is reference-based | W0405 is access-based | not mirrored; recorded in ADR 0006 |
| Assumption: no stored references | W0204 | gap: F3-2 |
| Model: no partial moves (a callee keeps a value in each field) | spec frees rule | gap: F3-5 (Weft leaves a moved part with no value) |

Models against the checker:

- B3 kill rule and `rules.rs`: `Ctx::invalidates` is "same root, then
  `places::invalidates`", as `invalidates_in_model` states. `mutation_kills` adds the
  wildcard rules and `writes_via` takes nodes out of `gen`. `writes_via` matters only
  for a reference with several places or a wildcard place, which the B1 link excludes
  (`facts_ok`), so the link statement still holds.
- `typed_by`: a lint (`FID/tools/typed.dl`) finds no two steps under one place that can
  alias with different stability, in the corpus and the interpreter programs.
- B1 CFG and the facts: the B6 lints find no `gen_and_kill` and no `use_where_unbound`
  on the 52 accepted corpus and interpreter programs, on 814 accepted programs of the
  other lenses, and on my probes (`gk1.wf`: a call result into the mutated reference,
  in a branch, a loop, a tuple, a block and a closure).
- The checker now propagates in a part of the graph (`part_of`, S5c). The link theorem
  `invalid_at` is about `propagate` on the whole CFG. The equality at the uses is
  tested (proptest), not proved; `proofs/link/README.md` covers it as "the glue".

## (4) Agreement runs

| Set | Programs | Result |
| --- | --- | --- |
| `tests/programs`, `crates/weft-interp/tests/programs`, `std/prelude.wf`, `examples/*`, `tests/packages/*`, each with no flag, `--lib`, `--no-runtime` and both | 704 runs | 700 agree; 4 runs are `examples/lints`, a directory of lint rules (exit 2, as expected) |
| Mutations that keep the braces, with inserts for closures, `resume`, `multi`, spawns, `rc` and moves (`mutagree3.py`) | 6 000 (5 207 parse) | agree, no crash |
| Line mutations (`mutagree.py`) | 4 000 (1 435 parse) | agree, no crash |
| Programs of the other lenses (random sample) | 8 000 | 6 822 agree, 204 do not parse, 974 files were gone (temporary files of the oracle lens); no disagreement, no crash |
| The probes and repros of this report | 65 + 30 | agree |
| `cargo test --release --workspace` | all suites | 587 passed, 0 failed, 2 ignored |

## Proof runs

| Run | Result |
| --- | --- |
| `proofs/verify-all.sh` | borrowing 169, effects 122, link 235, `weft-verified` 67; 0 errors |
| `weft-verified` by module | `places` 27, `dataflow` 16, `modes` 9, `lifecycle` 15 |
| `proofs/effects/mutations/run.sh` | 8 caught of 8, each with its documented result line |
| `proofs/borrowing/mutations/run.sh` | 9 caught of 9, each with its documented result line |
| `proofs/link/mutations/run.sh` | 26 caught of 26; 17 "link only", as `proofs/link/README.md` says |

## Round-2 fixes that hold

FD1 (W0118 for user effects, `fail`, raises, `rc` groups, unknown function values, no
runtime), FD2 (nested `multi` records, `multi_nested_drop.wf`), FD3 (stores into `rc`
objects, W0204), FD4 (`!Move`, tasks, scopes, resources, `Rc` across `multi`), FD5 (the
proof READMEs say what tests the facts), FD6, FD7 (counts), FD8 (each spec rule fires
on the corpus), FD9 (`sim_root`), FD10 and FD11 (recorded), FD12 (traceability), FD13,
FD14, FD15 (mutation scripts). The gaps of F3-1, F3-3 and F3-4 are at the edges of the
FD1 fix.

## Files

- Report: `FID/../fidelity.md` (this file).
- Repros: `FID/repro/F3-N_run.sh` and the `.wf` files.
- Probes: `FID/p/`. Tools: `FID/tools/`. Logs: `FID/agree_corpus.txt`,
  `FID/mutagree3_6000.txt`, `FID/mutagree_4000.txt`, `FID/agree_other_lenses.txt`,
  `FID/b6_corpus.txt`, `FID/b6_other.txt`, `FID/verify_all.log`,
  `FID/verified_modules.log`, `FID/effects_mutations.log`,
  `FID/borrowing_mutations.log`, `FID/link_mutations.log`, `FID/cargo_test.log`.
