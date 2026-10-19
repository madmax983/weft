# Link proofs (B6)

Plan item B6 says: "Proofs link the exec core to the model". This crate
gives these proofs. Before this crate, only tests linked the exec core to the
models.

The exec core is `crates/weft-verified`. The checker and the interpreter run
it. The models are `proofs/borrowing` (group borrowing) and `proofs/effects`
(algebraic effects).

## Verify

Put Verus on `PATH`. Use the revision in `../VERUS_VERSION`. Then run:

```bash
./verify.sh            # runs ./check-copies.sh first, then Verus
```

The results must be:

```text
check-copies: 10 included source files, no shadow copies, 0 verbatim copies identical
verification results:: 230 verified, 0 errors
```

| Module | Verified | What it is |
| --- | --- | --- |
| `places`, `dataflow`, `lifecycle` | 25, 16, 14 | Included from `crates/weft-verified/src/` |
| `model`, `soundness`, `cfg` | 2, 24, 7 | Included from `proofs/borrowing/src/` (base model and B1) |
| `layout`, `layout_proof`, `layout_examples` | 5, 34, 25 | Included from `proofs/borrowing/src/` (B3) |
| `effects_model` | 0 (specs only) | Included from `proofs/effects/src/model.rs` |
| `places_link` | 29 | L1: rule 3 and the B3 model |
| `dataflow_link` | 20 | L2: `propagate` and the B1 CFG checker |
| `lifecycle_link` | 7 | L3: the lifecycle state machines and the effects machine |
| `examples` | 22 | Vacuity guards and gap witnesses |

The proofs do not use `assume`, `admit`, `external_body`, or new axioms.

### CI

`../verify-all.sh` runs this crate, and the CI job runs `../verify-all.sh`.
`verify.sh` runs `check-copies.sh` first.

## How the crate uses the sources

The crate does not copy definitions. `src/lib.rs` includes the source files
with `#[path]`. Thus each theorem is about the code that the checker runs,
and about the model definitions that the soundness proofs use. Verus
verifies the included files again in this crate.

A copy can drift from its source. An include cannot. If a change to an
included file breaks a link theorem, `verify.sh` fails.

`check-copies.sh` makes sure of these things:

1. `src/lib.rs` includes exactly the files in the list `EXPECTED` of the
   script. Each include has the form `#[path = "..."]` on a line of its own.
   Each included file exists, and its home crate declares it as a module,
   with no `cfg` attribute. Thus the link uses the files that the home crate
   verifies.
2. No file of this crate defines an item with the name of an item of an
   included file. The check finds items at each indentation and with each
   visibility.
3. Each verbatim copy is identical to its source item. A verbatim copy is a
   block between `// COPY OF <path>: <item>` and `// END COPY`. The path is
   relative to `proofs/link`. Today the crate has no verbatim copies.

## L1. Places (`src/places_link.rs`)

The exec core has rule 3 as `spec_invalidates` and `invalidates`. The B3
model (`proofs/borrowing/src/layout.rs`) has the Weft rule as `lkills`.

### The embedding

| Exec step | Model step |
| --- | --- |
| A stable step of kind `k` | `Field(kind_code(k))` |
| An unstable `Variant { id }` | `Variant(id)` |
| Another unstable step of kind `k` | `Kid(kind_code(k))` |

`kind_code` is injective. Thus the embedding is injective
(`lemma_emb_step_injective`), and the model stability of an embedded step is
the exec stability (`lemma_emb_step_unstable`).

`to_lplace` makes the structured model place from the flat path. A `Kid` step
closes a hop. Each other step goes into the tail. The B3 checker builds its
places in the same way (`lpost`). `lemma_flat_to_lplace` proves that the flat
path of the result is the input path.

For the places that sema makes: a struct field becomes `Field(id)`. A variant
becomes `Variant(id)`. An unstable element and a `Box` target become `Kid`
steps. A fixed array element and a stable pointer target become stable
`Field` steps.

### Theorems

| Theorem | Statement |
| --- | --- |
| `thm_lkills_implies_invalidates` | For all places: if `lkills` kills the embedded reference, then the roots are equal and `spec_invalidates` holds. The checker kills at least what the model kills. This is the soundness direction. |
| `thm_invalidates_exact` | If `alias_exact(m, p)`: `(rm == rp && spec_invalidates(m, p)) == lkills(lplace(rm, m), lplace(rp, p))`. |
| `lemma_typed_alias_exact` | Places without split steps, whose stability is a function of the steps before a position and the kind (`typed_by`), have `alias_exact`. Sema gives this property: the type fixes the stability. |
| `thm_invalidates_exact_typed` | The corollary: exactness for typed places without split steps. |
| `thm_split_sound` | For all places, also with split steps. `coarse` changes each split side to the elements step. If `lkills` kills the coarse reference, and no position has the two sides of one split (`no_opposite`), then rule 3 invalidates the reference. |
| `thm_split_exact`, `thm_split_exact_typed` | Let the coarse places have `alias_exact` (for example, typed coarse places). Then rule 3 is exactly `lkills` on the coarse places and `no_opposite`. |
| `thm_rcheck_lcheck` | Put rule 3 into the B3 checker in place of `lkills` (`rcheck`). Read each model step as an exec step through a decoding `d` that keeps the stability (`keeps_stab`). If `rcheck` accepts a program, the B3 checker accepts it. |
| `thm_rule3_layout_sound`, `thm_rule3_layout_sound_from_start` | With `layout_soundness`: if `rcheck` accepts a program, no run of it has UB. There is no use after free, no type confusion, and no access outside the layout of a type. |
| `invalidates_in_model` | The exec comparison of the checker (`Ctx::invalidates`: the same root, then `invalidates`). Its result is rule 3. If the model kills, the result is true. With `alias_exact`, the result is the model predicate. The same holds for the coarse places of split places. The proof uses only the postcondition of `invalidates`. |

### Split steps

The B3 model has no split steps. A split side `[..k]` or `[k..]` names a part
of the elements at the same position (`spec_step_within`). The link reads
each split side as the elements step with the same stability (`coarse`).
Sema gives a split side the stability of the elements step of its type.

The model cannot express that the two sides of one split are disjoint. Rule
3 adds exactly this fact. `thm_split_sound` and `thm_split_exact` fix the
alias table of split steps. `Elem` aliases each side. Sides of different
splits alias. The same side of one split aliases itself. Only the two sides
of one split do not alias. A change to this table breaks the theorems.

The plain embedding (without `coarse`) gives the two sides different labels.
Then `alias_exact` is false, and the plain exactness fails
(`ex_split_alias_not_in_model`). No embedding can make split places exact:
step aliasing is not transitive (`[..1]` aliases `[2..]`, and `[2..]`
aliases `[1..]`, but `[..1]` does not alias `[1..]`). The model compares
steps by equality, and equality is transitive.

## L2. Dataflow (`src/dataflow_link.rs`)

The checker computes W0301 for one reference `v` with `propagate`. The B1
model (`proofs/borrowing/src/cfg.rs`) accepts a CFG with each annotation that
passes `cfg_check`. The model treats `v` as invalid at node `n` if `v` is not
in `ann[n].vars`.

### The facts of a B1 CFG

| Checker fact | Link definition |
| --- | --- |
| `rebound_at(v, n)` | `binds`: a `Borrow`, `Child` or `Copy` into `v`, or a `Call` or `Invoke` whose result goes to `v` |
| `uses(v, n)` | `uses`: the source of `Child`, `Copy`, `Read` and `Write`, and each argument of a `Call` |
| `points_into(v, Path)` | The static group `g[v]`. `gsteps` gives its weft steps: label `l` becomes `.l[]`, a stable field and an unstable element step. |
| `invalidated_at(v, n)` | `invalidated_at`: a mutable argument `a` of the `Call` at `n` has `grp_invalidates(g[a], g[v])`, that is the same root and `spec_invalidates` |
| `invalid(v, n)` | `lfp`: `spec_in_lfp` with `gen = invalidated_at` and `kill = binds` |

`lemma_grp_invalidates` proves that `grp_invalidates` is the B1 kill rule
(`strict_child`).

`spec/weft.dl` has more `invalidated_at` rules: a free of an owner
(`frees_at`), a wildcard place (`wild_at`) and a place that a call lends
(`lends_mut`). The link definition has only the call rule. So the theorems
apply to `v` only when these other rules do not fire for `v`. The other rules
only add nodes to `gen`, so the checker set gets larger and the checker
rejects more. The link does not prove this step.

### Hypotheses

The link does not prove these hypotheses. Tests check them.

* `facts_ok`. Sema must give these facts: the CFG is well formed for
  `propagate`, each binding gives the static group that the model gives,
  the labels fit into a step id, and each borrowed local exists. The CFG has
  no closure instructions.
* `facts_ok` also has `ret_ok`. This is not a sema fact. It is a B1
  acceptance condition: a returned reference comes from an argument that the
  call does not kill. No rule in `spec/weft.dl` states it directly. W0312
  (no mutable argument overlaps another argument) probably gives it, but the
  link does not prove that.
* `w0301_ok`: the checker accepts. No node uses a reference in the fixpoint.
* `bound_before_use`: `unb` covers each node where a reference can be unbound,
  and no node uses a reference there. Sema gives this through lexical scope.

### Theorems

| Theorem | Statement |
| --- | --- |
| `thm_lfp_annotation_checks` | Soundness: the annotation `lfp_ann` passes `cfg_check`. It keeps `v` valid exactly outside the fixpoint and outside `unb`. |
| `thm_w0301_no_ub` | With `cfg_soundness`: if W0301 accepts, no run that follows the CFG edges has UB. |
| `thm_must_invalid_in_lfp` | The soundness direction as sets. Let W0301 accept. At a node where every accepted annotation marks `v` invalid, the fixpoint or `unb` holds. |
| `thm_model_invalid_contains_lfp` | Minimality: each annotation that passes `cfg_check` with the static groups marks `v` invalid on the fixpoint of `gen` minus `kill`. This holds for each B1 CFG, also with closures. |
| `lemma_lfp_contains_eff` | The checker fixpoint (all of `gen`) contains the fixpoint of `gen` minus `kill`. |
| `thm_dataflow_exact` | Let no node both invalidate and rebind `v` (`no_gen_kill`). Then `lfp_ann` passes `cfg_check`, and each accepted annotation marks `v` invalid on the whole fixpoint. |
| `invalid_at` | The exec `propagate` on the CFG edges with the `gen` and `kill` vectors of `v` returns `lfp`. The proof uses only the postcondition of `propagate`. |

### Which direction

Let `must` be the set of nodes where each accepted model annotation with the
static groups marks `v` invalid.

* Soundness needs `must` inside the checker set. If `facts_ok`, `w0301_ok`
  and `bound_before_use` hold, `must` is inside the checker set plus `unb`
  (`thm_must_invalid_in_lfp`). `thm_w0301_no_ub` gives soundness directly.
  `facts_ok` excludes closures.
* For each B1 CFG, the fixpoint of `gen` minus `kill` is inside `must`
  (`thm_model_invalid_contains_lfp`).
* If no node both invalidates and rebinds `v`, that fixpoint is the checker
  fixpoint. Then, with the hypotheses above, the checker set and `must` are
  equal outside `unb` (`thm_dataflow_exact`).
* A B1 `Call` that mutates `r` and returns `v` into `r` both invalidates and
  rebinds `v`. There the checker marks `v` invalid after the node, but the
  model keeps the new `v` valid (`ex_gen_and_kill`). Thus the checker set is a
  strict superset on such nodes. Sema binds the result of a call at a separate
  `let` node after the call (`weft-cli facts` shows `mutates_at` at the call
  node and `rebound_at` at the next node). Thus sema CFGs do not have this
  shape.

## L3. Lifecycle (`src/lifecycle_link.rs`)

The interpreter keeps one exec record per continuation (`Continuation`) and
per linear value (`Linear`). The effects model keeps a `Kont` record per
continuation and a `Res` record per linear resource.

### The relations

| Exec state | Model record (`kont_rel`) |
| --- | --- |
| `Fresh` | the same mode, `used == false` |
| `Resumed` | the same mode, `used == !multi` (the model never marks a `multi` record used) |
| `Dropped` | `multi || used` |

`lin_rel` maps `Live`, `Consumed` and `Aborted` to the same model states.

### Theorems

Each function calls one exec operation. Its proof uses only the postcondition
of that operation. Each model step is the model function itself.

| Function | Exec operation | Statement |
| --- | --- | --- |
| `perform_linked` | `Continuation::new` | `do_perform` adds a model record. The new exec record and that record satisfy `kont_rel`. |
| `resume_linked` | `resume` | A success is the model step `step_resume`, and the records stay related. If the model state is `err_resume_used`, the exec resume fails and does not change the record. Before a drop, the exec succeeds exactly when the model allows the resume. After a drop, the exec resume fails. |
| `return_linked` | `drop_now` at a clause return | The step is `step_return`, and the records stay related. For a `once` continuation, the exec aborts exactly when the model sends the captured frames to the unwinder. |
| `unwind_drop_linked` | `drop_now` in the unwinder | If the model drops (`holds_fresh`), the exec aborts and the step is `step_unwind_drop`. Else the records stay related. |
| `acquire_linked` | `Linear::new` | `do_acquire` adds a model resource. The new exec record and that resource satisfy `lin_rel`. |
| `consume_linked` | `consume` | A success is the model step `step_consume`. If the model state is `err_consumed_twice`, the exec consume fails and does not change the record. |
| `unwind_linked` | `unwind` | The exec runs `on abort` exactly when the model resource is live. With `on abort`, the step is `step_unwind_abort`. If the exec does not run it, the model state is `err_unwind_dead`. |

Each function requires the relation and gives it again after a model step.
Thus the relations hold along each sequence of these operations, while each
exec operation is a model step. The link has no separate theorem for whole
sequences.

For `once` continuations and for linear values, each exec transition is a
model transition. The exec API refuses each transition into the model
errors `err_resume_used`, `err_consumed_twice` and `err_unwind_dead`. For
`multi` continuations, see the differences below.

### Differences

The link states these differences in the theorems. It does not hide them.

* `drop_now` on a fresh `multi` continuation reports an abort. The model does
  not unwind a `multi` continuation (`holds_fresh` is false), and its record
  does not change (`ex_multi_drop`). E5 says that such a continuation holds
  no linear value and no fresh `once` continuation. Thus the unwind of the
  interpreter has nothing to finalize. The link does not prove this
  consequence.
* After that abort, the exec record is `Dropped`, and an exec resume fails.
  The model record does not change, and the model allows the resume
  (`ex_multi_dropped_resume`). The interpreter copies the `Clause` frames of
  a `multi` continuation with the same record
  (`crates/weft-interp/src/machine/effects.rs`, `copy_frames`). Thus, if one
  copy returns without a resume and another copy then resumes, the
  interpreter faults where the model continues.
* `Linear` has no `on abort` flag. If the type of a live value has no
  `on abort`, the exec unwind still succeeds, but the model state is the error
  `err_no_on_abort`. The checker rule (W0602, E3) must exclude this case.
* After an abort, the postcondition of `drop_now` does not keep the mode of
  the record. Thus `kont_rel` does not use the mode of a `Dropped` record.

## Examples (`src/examples.rs`)

| Example | What it shows |
| --- | --- |
| `ex_push_kills_element_refs` | Rule 3 and the model agree on `mut(world.entities)` and `&world.entities[]`. The typed hypotheses hold. |
| `ex_split_alias_not_in_model` | Gap witness: rule 3 kills a reference into `v[j..]` after `mut(v[..i])`. The plain embedding gives no model kill. `alias_exact` is false. |
| `ex_split_coarse` | The coarse model kills both `v[j..]` (another split) and `v[i..]` (the other side). Rule 3 kills only the first. Both pairs meet the hypotheses of `thm_split_exact_typed`. |
| `ex_rule3_layout_applies` | Vacuity guard: a run of the B3 example `en_ok` meets each hypothesis of `thm_rule3_layout_sound_from_start`, for each decoding that keeps the stability. Its mutable call kills a reference. |
| `ex_rule3_layout_rejects` | The B3 checker with rule 3 rejects `en_bad`. |
| `ex_accepted` | Vacuity guard. A CFG has a borrow, a child reference, a mutating call and a read. It meets the static hypotheses of `thm_w0301_no_ub` (`facts_ok`, `w0301_ok`, `bound_before_use`). |
| `ex_accepted_run` | Vacuity guard: a concrete run of that CFG up to the call meets the run hypotheses (`inv` at the start and `is_cfg_trace`). The theorem then shows that the call gets no dangling argument. |
| `ex_loop_accepted` | Vacuity guard with a back edge. A call in a loop invalidates `e`. A rebind of `e` at the loop head stops the propagation. The CFG meets the static hypotheses. |
| `ex_rejected` | W0301 rejects a read of the child reference after the call. No model annotation with the static groups passes `cfg_check`. |
| `ex_gen_and_kill` | Gap witness for `no_gen_kill` (see "Which direction"). |
| `ex_double_resume` | A second exec resume of a `once` continuation fails where the model state is `err_resume_used`. |
| `ex_once_drop`, `ex_multi_drop` | The abort at a clause return, for `once` and for `multi`. |
| `ex_multi_dropped_resume` | Gap witness: an exec resume after the `multi` abort fails, and the model allows it. |
| `ex_consume_twice` | Vacuity guard for `Linear`: acquire and consume are the model steps. A consume from a duplicated frame fails where the model state is `err_consumed_twice`. |
| `ex_unwind_once` | The unwinder runs `on abort` once (`step_unwind_abort`). A duplicated pending frame then finds a dead value (`err_unwind_dead`), and the exec unwind does not run `on abort` again. |

## Mutation tests

`mutations/run.sh` runs the mutation tests. Each mutation changes a copy of
the sources in a temporary directory. The test passes if `verify.sh` fails on
the copy. The script does not change the repository. The script needs
`python3` and `verus`. It takes about ten minutes. All 24 mutations make
`verify.sh` fail. For 16 of them, `crates/weft-verified` still verifies
alone.

```bash
mutations/run.sh          # all mutations
mutations/run.sh m3b l2   # some mutations
```

The column "Core verifies" says if `crates/weft-verified` still verifies
alone on the copy. If it does, only the proofs in `proofs/` find the change.
For d1 and d2, only the lemma in `dataflow.rs` fails. The link uses the
postcondition of `lemma_step_sound`, and a failed lemma body does not change
that postcondition.

| Mutation | What it changes | Core verifies | Fails in |
| --- | --- | --- | --- |
| m1 | Rule 3 without the unstable step (spec and exec). | no | `weft-verified places.rs`, `places_link.rs` |
| m1b | As m1, and the lemmas of `places.rs` that need the unstable step change too. | yes | `places_link.rs` |
| m2 | Rule 3 needs two steps after `m` (spec and exec). | no | `weft-verified places.rs`, `examples.rs`, `places_link.rs` |
| m11 | Rule 3 needs the unstable step after the first step past `m` (spec and exec). | yes | `examples.rs`, `places_link.rs` |
| m3 | `Elem` and `Seg` do not alias (spec and exec). | no | `weft-verified places.rs`, `places_link.rs` |
| m3b | As m3, and `Seg` is not within `Elem` (spec and exec). | yes | `places_link.rs` |
| m4 | `Deref` does not alias `Deref` (spec and exec). | no | `weft-verified places.rs`, `places_link.rs` |
| m5 | Field steps alias without equal ids (spec and exec). | yes | `dataflow_link.rs`, `places_link.rs` |
| m8 | Sides of different splits do not alias (spec and exec). | yes | `examples.rs`, `places_link.rs` |
| m9 | The same side of one split does not alias itself (spec and exec). | no | `weft-verified places.rs`, `places_link.rs` |
| m10 | The two sides of one split alias (spec and exec). | no | `weft-verified places.rs`, `examples.rs`, `places_link.rs` |
| m6 | Model: `lkills` without the unstable step. | yes | `borrowing layout_examples.rs`, `places_link.rs` |
| m7 | Model: only `Kid` steps are unstable. | yes | `borrowing layout_examples.rs`, `borrowing layout_proof.rs`, `examples.rs`, `places_link.rs` |
| d1 | Spec only: the fixpoint does not enter a kill node (`spec_closed`). | no | `weft-verified dataflow.rs` |
| d2 | Spec only: `spec_closed` has no propagation rule. | no | `weft-verified dataflow.rs` |
| d3 | `propagate` and `spec_edge` follow only the first successor (spec and exec). | yes | `dataflow_link.rs` |
| d4 | Model: the B1 `killed` also kills through shared arguments. | yes | `dataflow_link.rs` |
| d5 | Model: `strict_child` also holds for the group itself. | yes | `dataflow_link.rs`, `examples.rs` |
| l1 | A dropped `multi` continuation can resume (spec and exec). | yes | `lifecycle_link.rs` |
| l2 | `consume` accepts an `Aborted` value (spec and exec). | yes | `lifecycle_link.rs` |
| l3 | `drop_now` does not abort a fresh `multi` continuation (spec and exec). | yes | `lifecycle_link.rs` |
| l4 | Model: a used `once` continuation can resume. | yes | `lifecycle_link.rs` |
| l5 | Model: `do_return` does not mark the dropped `once` record used. | yes | `lifecycle_link.rs` |
| l6 | `unwind` also runs `on abort` for a consumed value (spec and exec). | yes | `lifecycle_link.rs` |

## What stays only tested

* The fact generation in sema (`crates/weft-sema/src/body/`): `points_into`,
  `mutates_at`, `rebound_at`, `uses`, `cfg_edge` and lexical scope. The link
  takes them as hypotheses (`facts_ok`, `bound_before_use`).
* The B1 condition `ret_ok` in `facts_ok` (see "Hypotheses").
* The glue in `crates/weft-check/src/rules.rs` that builds `succ`, `gen` and
  `kill` from the facts, and the evidence search. `invalid_at` and
  `invalidates_in_model` state what the glue must compute.
* The places of sema in the B3 link. `thm_rule3_layout_sound` reads model
  places through a decoding of steps. The link does not prove that sema
  builds those exec places.
* A reference with more than one place. The checker allows a list of places
  per reference. The B1 model has one group per reference.
* Stability that does not come from the type.
* Closures, handlers and continuations in the dataflow link. Soundness
  (`thm_lfp_annotation_checks`) excludes `MkClosure` and `Invoke`. The
  `gen` of the link has no effect footprints (`performs_at`, `footprint`).
* `spec_overlaps` and `spec_within` (W0405 and signature cover). The link has
  no model predicate for them.
* The other analyses that use `propagate`: moves, linear liveness, `multi`.
  The effects model has its own checker. The link does not connect the two.
* The interpreter glue around the exec records. For example, `consume_lin`
  (`crates/weft-interp/src/machine/exec.rs`) ignores a failed consume of an
  `Aborted` value. The model calls that consume `err_consumed_twice`. The
  link proves that the exec API refuses it, but not that the interpreter
  stops.
* `Continuation` and `Linear` derive `Copy`. The link assumes one exec record
  per model record. The interpreter must not copy a record.
* `modes.rs`.
