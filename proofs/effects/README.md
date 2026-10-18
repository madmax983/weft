# Algebraic effects: soundness, machine-checked in Verus

A formal model of Weft's algebraic effects (lexical handlers, capability passing,
`once` and `multi` continuations, linear values with `on abort`, cancellation) with a
[Verus](https://github.com/verus-lang/verus) proof that the effect checker is sound.

```
verification results:: 122 verified, 0 errors     (~14 s)
```

No `assume`, `admit`, `external_body` or extra axioms. Every theorem quantifies over
all executions of all checked programs.

## Status

| Milestone | Theorem | File | Status |
| --- | --- | --- | --- |
| E1. Effect safety | `e1_effect_safety` | `src/lexical.rs` | verified |
| E2. One-shot safety | `e2_one_shot_safety` | `src/safety.rs` | verified |
| E3. Abort safety | `e3_abort_safety` | `src/safety.rs` | verified |
| E4. Lexical resolution | `e4_lexical_resolution` | `src/lexical.rs` | verified |
| E5. Multi-shot restriction | `e5_multi_shot_restriction` | `src/safety.rs` | verified |
| All errors | `soundness` | `src/safety.rs` | verified |
| No stuck state | `progress`, `no_stuck` | `src/progress.rs` | verified |
| Vacuity guards | `example_*` | `src/examples.rs` | verified |

## The model (`src/model.rs`)

A small first-order abstract machine.

* **Program.** A map from block ids to blocks. A block has a signature and a
  straight-line instruction sequence. An effect is a sequence of operations, each
  `Once` or `Multi`.
* **Signature.** `caps`: the effect of each capability parameter (the effect row).
  `rets`: the capability parameters that the block returns, as closures that capture
  them. `kmode`: `Some(m)` for a clause block, which receives a continuation of mode `m`.
* **Instructions.** `Acquire{slot, on_abort}`, `Consume{slot}`, `Call{block, caps}`,
  `Handle{eff, clauses, body}`, `Perform{cap, op}`, `Resume`, `Return`.
* **State.** A stack of frames. A code frame has a block, a pc, a capability
  environment `env` (handler ids), linear `slots` (slot to resource id), and, for a
  clause, a continuation id `k`. A handler frame holds a handler id. The state also has
  a resource table (`Live | Consumed | Aborted`, with the `on abort` flag), a
  continuation table (frames, `multi`, `used`), the handler instances (`hinfo`), and a
  pending list for the unwinder.
* **Capabilities are handler ids.** `Handle` mints a fresh id `c`, records the handler
  instance (effect, clauses, handle-site environment) in `hinfo`, and pushes a handler
  frame and the body. The body gets `env ++ [c]`. A call passes capabilities
  explicitly (`Call{caps}`). This is the elaborated form of Weft's implicit capability
  passing. A perform names a capability by index into `env`, so it reaches the handler
  that minted it, not the closest handler of the effect.
* **Perform.** The machine finds the topmost handler frame of `c`. It captures the
  frames from that handler frame up to the top as a continuation, and runs the clause
  of `c` (from `hinfo`, in the handle-site environment) in place of the handler frame.
* **Resume.** Pushes the captured frames on top of the clause frame. A `once`
  continuation becomes used. A `multi` continuation stays usable, and each resume
  pushes a copy of its frames.
* **Return.** A clause that returns with a fresh `once` continuation drops it: its
  frames go to the pending list (abort). A body that returns pops its handler frame.
* **Unwinder.** While the pending list is not empty, only the unwinder runs. It takes
  the top pending frame. If the frame holds a fresh `once` continuation, the unwinder
  drops that continuation first (its frames go on top). Then it runs `on abort` for the
  newest live linear value (largest resource id) of the frame, one per step. Then it
  removes the frame. So the order is reverse: top frame first, newest value first.
* **Cancel.** At any perform, the machine can cancel: the captured frames go straight
  to the unwinder and the handle site continues. For a task, the root handler is the
  scheduler, so this unwinds the whole task at its next suspension point.
* **Returned capabilities.** A call or a handle adds the capabilities that the callee
  or body returns to the caller's `env` when the call starts. The caller is suspended
  until the callee returns, so this is the same as adding them at the return.

**Errors.** Every stuck state that is a bug is a named predicate. `error` is their
disjunction.

| Predicate | Meaning |
| --- | --- |
| `err_unhandled` | perform with no capability, no live handler frame, or an undeclared operation (E1) |
| `err_dead_cap` | perform through a capability whose handler is gone (E4) |
| `err_resume_used` | resume of a `once` continuation that is used or dropped (E2) |
| `err_no_k` | resume in a frame with no continuation |
| `err_overwrite` | acquire into a slot that holds a linear value |
| `err_use_moved` | consume of an empty slot |
| `err_consumed_twice` | consume of a resource that is not live (E3, E5) |
| `err_leak` | normal return with a live linear value (E3) |
| `err_unwind_dead` | the unwinder finds a resource that is not live (E3, E5) |
| `err_no_on_abort` | the unwinder must abort a value whose type has no `on abort` (E3) |
| `err_dup` | a live linear resource is in two slots, or a fresh `once` continuation is in two frames, of frames that can still run (stack, pending, fresh `once` and all `multi` continuations) (E5) |
| `err_malformed` | missing block, callee, body or clause; capability index out of range |

`progress` proves that a state that is not final and not an error always has a next
state. So no error hides as a missing step.

## The checker (`src/checker.rs`)

The checker walks each block once. Its state at each pc (`SS`) holds the effect of
each capability in scope (`env`), the live linear slots with their `on abort` flags
(`lin`), and whether the continuation is usable (`k`).

| Weft rule | Checker clause in `instr_ok` |
| --- | --- |
| (a) a perform of E is in a `handle E`, or E is in the row | `Perform`: `cap < env.len()`, and the effect declares `op` |
| (a) a call needs the callee's row | `Call`: each passed capability has the effect of the callee's parameter |
| (b) `resume` consumes `k` | `Resume` needs `k`; `post` sets `k = false` for `once` |
| (c) a linear value is consumed on every normal path | `Return` needs `lin` empty; `Acquire` needs an empty slot; `Consume` needs a live slot |
| (c) a value live across an abort needs `on abort` | abort rule (`all_abortable`) at a `once` perform, and at each suspension point that passes up a capability of an effect with a `once` operation |
| `multi`: everything live across it is `many` | multi rule (`all_many`: no linear value, no usable `once` `k`) at a `multi` perform, and at each suspension point that passes up a capability of an effect with a `multi` operation |
| (d) a capability cannot escape its handle | `Handle`: each `rets` index of the body is `< env.len()`, so it is not the new capability |

A suspension point passes up capabilities. A call passes its arguments. A handle passes
the whole environment (the body and the clauses can use it). A resume passes the
clause's environment (the resumed frames can use it).

## The theorems

All theorems have the same hypotheses: `check(prog)`, `is_trace(prog, tr)`, and
`tr[0] == init(prog)`. `is_trace` means that each state steps to the next. The
execution can have any length and can stop anywhere. Below, the hypotheses and the
triggers are not repeated; see the source for the exact text.

```rust
// E1 (src/lexical.rs)
pub proof fn e1_effect_safety(prog: Prog, tr: Seq<State>)
    ensures
        forall|i: int| 0 <= i < tr.len() ==> !err_unhandled(prog, tr[i]),
        forall|i: int| 0 <= i < tr.len() ==> !err_malformed(prog, tr[i]),

// E2 (src/safety.rs)
pub proof fn e2_one_shot_safety(prog: Prog, tr: Seq<State>)
    ensures
        forall|i: int| 0 <= i < tr.len() ==> !err_resume_used(prog, tr[i]),
        // at most one step resumes a given `once` continuation
        forall|i: int, j: int, kid: KId|
            resumes(prog, tr, i, kid) && resumes(prog, tr, j, kid) && !tr[i].konts[kid].multi ==> i == j,

// E3 (src/safety.rs)
pub proof fn e3_abort_safety(prog: Prog, tr: Seq<State>)
    ensures
        // (1) no linear error
        forall|i: int| 0 <= i < tr.len() ==> !err_leak(prog, tr[i]) && !err_overwrite(prog, tr[i])
            && !err_use_moved(prog, tr[i]) && !err_consumed_twice(prog, tr[i])
            && !err_unwind_dead(tr[i]) && !err_no_on_abort(tr[i]),
        // (2) a finalized resource never changes (it is finalized at most once)
        forall|i: int, j: int, r: ResId|
            0 <= i <= j < tr.len() && tr[i].res.contains_key(r) && tr[i].res[r].st != RState::Live
                ==> tr[j].res.contains_key(r) && tr[j].res[r] == tr[i].res[r],
        // (3) `on abort` runs only from the unwinder, and only for a type that declares it
        forall|i: int, r: ResId|
            0 <= i < tr.len() - 1 && live(tr[i], r) && tr[i + 1].res[r].st == RState::Aborted
                ==> step_unwind_abort(tr[i], tr[i + 1]) && unwinding(tr[i]) && tr[i].res[r].on_abort,
        //     a consume happens only on the normal path
        forall|i: int, r: ResId|
            0 <= i < tr.len() - 1 && live(tr[i], r) && tr[i + 1].res[r].st == RState::Consumed
                ==> step_consume(prog, tr[i], tr[i + 1]) && running(tr[i]),
        //     unwinding starts only at a dropped `once` continuation or at a cancellation
        forall|i: int|
            0 <= i < tr.len() - 1 && !unwinding(tr[i]) && unwinding(tr[i + 1])
                ==> (step_return(prog, tr[i], tr[i + 1]) && holds_fresh(tr[i], tf(tr[i])))
                    || step_cancel(prog, tr[i], tr[i + 1]),
        // (4) no leak: at the end, every resource is consumed or aborted
        forall|i: int, r: ResId|
            0 <= i < tr.len() && final_state(tr[i]) && tr[i].res.contains_key(r)
                ==> tr[i].res[r].st != RState::Live,

// E4 (src/lexical.rs)
pub proof fn e4_lexical_resolution(prog: Prog, tr: Seq<State>)
    ensures
        forall|i: int| 0 <= i < tr.len() ==> !err_dead_cap(prog, tr[i]),
        // the clause that runs is the one that the unique `handle` step `m` bound
        // when it minted the capability, in the environment of that handle site
        forall|i: int|
            0 <= i < tr.len() - 1 && step_perform(prog, tr[i], tr[i + 1]) ==> exists|m: int|
                resolves_to(prog, tr, i, m)
                && forall|m2: int| minted_at(prog, tr, m2, c) ==> m2 == m,   // c: the capability at step i

// E5 (src/safety.rs)
pub proof fn e5_multi_shot_restriction(prog: Prog, tr: Seq<State>)
    ensures
        // every `multi` continuation holds only clean frames
        forall|i: int, k: KId|
            0 <= i < tr.len() && tr[i].konts.contains_key(k) && tr[i].konts[k].multi
                ==> all_clean(prog, tr[i], tr[i].konts[k].frames),
        // so each resume of a `multi` continuation pushes code frames `g` that
        // hold no resource and no fresh `once` continuation
        forall|i: int, m: int| /* step i resumes a multi continuation; g is its frame m */
            ==> !nonempty(g.slots) && !holds_fresh(tr[i], g),
        // no resource and no fresh `once` continuation has two owners
        forall|i: int| 0 <= i < tr.len() ==> b_unique_res(tr[i]) && b_unique_k(tr[i]),
        forall|i: int| 0 <= i < tr.len() ==> !err_dup(tr[i]),

// All errors, and progress (src/safety.rs, src/progress.rs)
pub proof fn soundness(prog: Prog, tr: Seq<State>)
    ensures forall|i: int| 0 <= i < tr.len() ==> !error(prog, tr[i]),
pub proof fn progress(prog: Prog, s: State)       // for any state
    requires !final_state(s), !error(prog, s),
    ensures exists|s2: State| step(prog, s, s2),
pub proof fn no_stuck(prog: Prog, tr: Seq<State>)
    ensures forall|i: int| 0 <= i < tr.len() ==> final_state(tr[i]) || exists|s2: State| step(prog, tr[i], s2),
```

`resolves_to(prog, tr, i, m)` says three things. Step `m` is the `handle` that minted the
capability `c` of the perform at step `i`. The new top frame is clause `op` of the
instance that step `m` recorded, in the handle-site environment. The captured
continuation starts at the topmost handler frame of `c`.

## The proof idea

Two invariants hold at every reachable state. Each step keeps them (`lemma_a_step`,
`lemma_b_step`).

**`inv_a`, structure** (`src/scope.rs`, `src/scope_steps.rs`):

* Each frame is well typed: its environment matches the checker's effect list through
  `hinfo`, and a clause frame links to its continuation.
* `based`: each capability that a stack frame can use has its handler frame below that
  frame. This gives E1 and the first part of E4. Rule (d) keeps it at `handle`: without
  rule (d), the handle site holds the new capability, but its handler frame is above it.
* `scoped`: for frames `i < i2`, a capability of frame `i2` is a handler between them,
  or frame `i` passed it up. A perform captures up to the *topmost* handler frame of its
  capability. So every captured frame passed that capability up, and the checker's rule
  at that frame's suspension point applies (`lemma_capture_rules`).
* `below_h`: the frame below a handler frame passes up only the capabilities of that
  handler's clauses. Continuations satisfy the same rules, relative to their clause.

**`inv_b`, ownership** (`src/own.rs`, `src/own_steps.rs`):

* A position is a stack frame, a pending frame, or a frame of a fresh `once`
  continuation. Each live resource is in exactly one slot of one position. Each fresh
  `once` continuation is held by exactly one position. A continuation inside a
  continuation has a smaller id.
* The slots of each frame match the checker state. Pending frames and frames of fresh
  `once` continuations hold only values with `on abort` (from the abort rule at
  capture). The frames of a `multi` continuation are clean (from the multi rule at
  capture).
* Each step relabels positions (`lemma_b_corr`, `lemma_b_local`). At a final state no
  stack frame and no pending frame exist. The id order then excludes a fresh `once`
  continuation (`lemma_no_fresh_at_final`), so no resource is live.

## Vacuity guards (`src/examples.rs`)

Each guard is a verified lemma.

| Milestone | Accepted program | Rejected program, and a concrete bad execution | Hypotheses satisfiable |
| --- | --- | --- | --- |
| E1 | `example_ok_checks` | `example_unhandled_rejected`, `example_unhandled_is_error`: a perform with no `handle` reaches `err_unhandled` | `example_hypotheses_satisfiable` |
| E2 | `example_ok_checks` | `example_twice_rejected`, `example_twice_is_error`: a clause resumes twice; 8 states to `err_resume_used` | `example_hypotheses_satisfiable` |
| E3 | `example_ok_checks`, `example_lex_checks` (abort path) | `example_no_abort_rejected`, `example_no_abort_is_error`: a value with no `on abort` is live across a perform whose clause drops the continuation; 5 states to `err_no_on_abort`. `example_leak_rejected`, `example_leak_is_error`: `err_leak` | `example_hypotheses_satisfiable`, `example_lexical` |
| E4 | `example_lex_checks` | `example_escape_rejected`, `example_escape_is_error`: the body returns its own capability; 4 states to `err_dead_cap` | `example_lexical` |
| E5 | `example_multi_ok_checks` | `example_multi_rejected`, `example_multi_is_error`: a linear value is live across a `multi` perform; after the first resume it is duplicated (`err_dup`), and the second resume consumes it again; 9 states to `err_consumed_twice` | `example_multi_ok` |

* `example_hypotheses_satisfiable`: a full 10-state execution of the accepted program
  (`handle`, `acquire`, `perform`, `resume`, `consume`, and the returns). It meets
  every hypothesis. All the theorems apply, and the resource ends consumed.
* `example_lexical`: two handlers of the same effect. The inner handler frame is the
  closest one, but the perform goes through the outer capability, so the outer clause
  runs. E4 names step 0 (the outer `handle`) as the step that minted the capability.
  The outer clause then aborts, and the unwinder removes the four captured frames.
* `example_multi_ok`: an accepted program resumes a `multi` continuation twice
  (11 states).

## Mutation tests

Each mutation weakens one checker rule in `src/checker.rs`. Each was run on a copy of
`src/`. Each one makes a soundness lemma fail. The `*_rejected` guard of that rule also
fails, as expected, because the weak checker accepts the bad program.

| Mutation | Result | Soundness lemma that fails |
| --- | --- | --- |
| (a) drop `cap < env.len()` at `Perform` | 120 verified, 2 errors | `lemma_no_struct_error` (E1) |
| (b) `Resume` keeps a `once` `k` usable | 119 verified, 3 errors | `lemma_b_resume` (E2: `k_sync`) |
| (c) drop the abort rule at a `once` perform | 120 verified, 2 errors | `lemma_capture_rules` (E3) |
| (c) `Return` without the empty-`lin` check | 120 verified, 2 errors | `lemma_no_own_error` (E3: `err_leak`) |
| (d) allow `rets[j] <= env.len()` at `Handle` | 119 verified, 3 errors | `lemma_a_handle` (`based`: E1, E4), `lemma_up_rule` |
| drop the multi rule at a `multi` perform | 120 verified, 2 errors | `lemma_capture_rules` (E5) |
| drop the suspension rule at `Call` | 121 verified, 1 error | `lemma_up_rule` (E3, E5) |
| drop the suspension rule at `Resume` | 121 verified, 1 error | `lemma_up_rule` (E3, E5) |

The source in this directory has no mutation. It verifies with 122 verified, 0 errors.

## Rules that the Weft checker must mirror

The proof needs these rules. Some are not obvious from the language description.

1. **The abort and multi rules apply at every suspension point, not only at the
   perform.** A perform captures every frame between it and its handler. So a call that
   passes a capability of an effect with a `once` operation is an abort point for the
   caller: its live linear values need `on abort`. A call that passes a capability of an
   effect with a `multi` operation is a copy point: the caller must hold no linear
   value and no usable `once` continuation. A `handle` passes up the whole environment
   (the body and the clauses can use it). A `resume` passes up the clause's
   environment (the resumed frames can perform through it and capture the clause
   frame). The two "suspension rule" mutations show that these checks are necessary.
2. **A usable `once` continuation is a `once` value for the multi rule.** A clause that
   holds a fresh `k` must not perform a `multi` operation through an outer capability,
   and must not call code that can. Otherwise a copy of the clause frame resumes `k`
   again.
3. **A handle body cannot return its own capability** (rule d), also not inside a
   closure. The capabilities that a body returns must come from the handle site.
4. **A perform resolves to the topmost handler frame of its capability.** With `multi`
   continuations, copies of one handler frame can exist. The proof uses "topmost" to
   show that each captured frame passed the capability up.
5. **The unwinder must drop nested continuations.** A dropped continuation can hold a
   clause frame that holds a fresh `once` continuation. The unwinder must drop that one
   too (its frames first), or its linear values leak. The no-leak proof uses the fact
   that an inner continuation is older than the one that holds it.
6. **Clauses run in the handle-site environment.** A clause does not get the new
   capability, and a clause returns no capabilities.

## Scope and limitations

* **First order.** There are no closure values. A returned closure is modelled by the
  capabilities that it captures (`rets`). Handlers and functions get capabilities
  explicitly.
* **Linear values do not move between frames.** Each linear value belongs to the frame
  that acquired it. Arguments, results, operation payloads and resume values carry no
  data.
* **Straight-line blocks.** A block has no branches or loops. Branches need a join of
  checker states (as in the borrowing proof).
* **One task.** Cancellation is a nondeterministic abort at any perform, up to the
  handler of that perform. Whole-task cancellation is the case where that handler is
  the root (scheduler) handler. `fail` is an operation whose clause does not resume.
* **`on abort` is atomic.** It cannot perform or fail.
* **Deep handlers only.** A resume puts the handler frame back.
* **Spec checker.** `check` is a Verus spec. The exec checker in
  `crates/weft-verified` is not linked to it here.
* **No interaction with group borrowing.** References are not in this model.

## Files

| File | Content |
| --- | --- |
| `src/model.rs` | machine: programs, states, steps, error predicates |
| `src/checker.rs` | static checker |
| `src/scope.rs`, `src/scope_steps.rs` | `inv_a` and its preservation |
| `src/lexical.rs` | E1, E4 |
| `src/own.rs`, `src/own_steps.rs` | `inv_b` and its preservation |
| `src/safety.rs` | E2, E3, E5, `soundness` |
| `src/progress.rs` | `progress`, `no_stuck` |
| `src/examples.rs` | vacuity guards |

## Running

```bash
./verify.sh          # needs `verus` on PATH
```

The pinned Verus revision is in `../VERUS_VERSION`.
