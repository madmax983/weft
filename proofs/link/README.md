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
./verify.sh
./check-copies.sh
```

The results must be:

```text
verification results:: 143 verified, 0 errors
check-copies: 8 included source files, no shadow copies, 0 verbatim copies identical
```

| Module | Verified | What it is |
| --- | --- | --- |
| `places`, `dataflow`, `lifecycle` | 25, 16, 14 | Included from `crates/weft-verified/src/` |
| `model`, `soundness`, `cfg`, `layout` | 2, 24, 7, 5 | Included from `proofs/borrowing/src/` |
| `effects_model` | 0 (specs only) | Included from `proofs/effects/src/model.rs` |
| `places_link` | 13 | L1: rule 3 and the B3 kill predicate |
| `dataflow_link` | 18 | L2: `propagate` and the B1 CFG checker |
| `lifecycle_link` | 7 | L3: the lifecycle state machines and the effects machine |
| `examples` | 12 | Vacuity guards and gap witnesses |

The proofs do not use `assume`, `admit`, `external_body`, or new axioms.

`../verify-all.sh` does not run this crate yet. To run it there, add `link`
to the list of crates in its loop.

## How the crate uses the sources

The crate does not copy definitions. `src/lib.rs` includes the source files
with `#[path]`. Thus each theorem is about the code that the checker runs, and
about the model definitions that the soundness proofs use. Verus verifies the
included files again in this crate.

A copy can drift from its source. An include cannot. If a change to an
included file breaks a link theorem, `verify.sh` fails.

`check-copies.sh` makes sure of three things:

1. Each included file exists, and its home crate declares it as a module.
   Thus the link uses the files that the home crate verifies.
2. No own file of this crate defines an item that an included file defines.
3. Each verbatim copy is identical to its source item. A verbatim copy is a
   block between `// COPY OF <path>: <item>` and `// END COPY`. The path is
   relative to `proofs/link`. Today the crate has no verbatim copies.

## L1. Places (`src/places_link.rs`)

The exec core has rule 3 as `spec_invalidates` and `invalidates`. The B3 model
(`proofs/borrowing/src/layout.rs`) has the Weft rule as `lkills`.

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
| `invalidates_in_model` | The exec comparison of the checker (`Ctx::invalidates`: the same root, then `invalidates`). Its result is rule 3. If the model kills, the result is true. With `alias_exact`, the result is the model predicate. The proof uses only the postcondition of `invalidates`. |

`alias_exact(m, p)` says: at each position where the steps before are equal,
two steps that can alias are equal. Split steps break it (`[..i]` can alias
`[j..]`). `ex_split_alias_not_in_model` proves that exactness fails for such
a pair. An informal argument shows that each embedding fails: step aliasing
is not transitive (`[..1]` aliases `[2..]`, and `[2..]` aliases `[1..]`, but
`[..1]` does not alias `[1..]`). The model compares steps by equality, and
equality is transitive.

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

### Hypotheses

Sema must give these facts. The link does not prove them. Tests check them.

* `facts_ok`: the CFG is well formed for `propagate`, each binding gives the
  static group that the model gives, the labels fit into a step id, each
  borrowed local exists, and each returned reference comes from an argument
  that the call does not kill. The CFG has no closure instructions.
* `w0301_ok`: the checker accepts. No node uses a reference in the fixpoint.
* `bound_before_use`: `unb` covers each node where a reference can be unbound,
  and no node uses a reference there. Sema gives this through lexical scope.

### Theorems

| Theorem | Statement |
| --- | --- |
| `thm_lfp_annotation_checks` | Soundness: the annotation `lfp_ann` passes `cfg_check`. It keeps `v` valid exactly outside the fixpoint and outside `unb`. |
| `thm_w0301_no_ub` | With `cfg_soundness`: if W0301 accepts, no run that follows the CFG edges has UB. |
| `thm_model_invalid_contains_lfp` | Minimality: each annotation that passes `cfg_check` with the static groups marks `v` invalid on the fixpoint of `gen` minus `kill`. This holds for each B1 CFG, also with closures. |
| `lemma_lfp_contains_eff` | The checker fixpoint (all of `gen`) contains the fixpoint of `gen` minus `kill`. |
| `thm_dataflow_exact` | If no node both invalidates and rebinds `v` (`no_gen_kill`): `lfp_ann` passes `cfg_check`, and each accepted annotation marks `v` invalid on the whole fixpoint. |
| `invalid_at` | The exec `propagate` on the CFG edges with the `gen` and `kill` vectors of `v` returns `lfp`. The proof uses only the postcondition of `propagate`. |

### Which direction

The link proves both directions on the closure-free fragment:

* The checker set contains the model must-invalid set. The model
  must-invalid set is the set where each accepted annotation marks `v`
  invalid. This is the direction that soundness needs. `thm_w0301_no_ub`
  gives soundness directly.
* If no node both invalidates and rebinds `v`, the two sets are equal,
  outside the unbound nodes.
* A B1 `Call` that mutates `r` and returns `v` into `r` both invalidates and
  rebinds `v`. There the checker marks `v` invalid after the node, but the
  model keeps the new `v` valid (`ex_gen_and_kill`). Thus the checker set is a
  strict superset on such nodes. Sema binds the result of a call at a separate
  `let` node after the call. Thus sema CFGs do not have this shape.

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
| `perform_linked` | `Continuation::new` | The new record is related to the record that `do_perform` adds. |
| `resume_linked` | `resume` | A success is the model step `step_resume`, and the records stay related. If the model state is `err_resume_used`, the exec resume fails and does not change the record. Before a drop, the exec succeeds exactly when the model allows the resume. |
| `return_linked` | `drop_now` at a clause return | The step is `step_return`, and the records stay related. For a `once` continuation, the exec aborts exactly when the model sends the captured frames to the unwinder. |
| `unwind_drop_linked` | `drop_now` in the unwinder | If the model drops (`holds_fresh`), the exec aborts and the step is `step_unwind_drop`. Else the records stay related. |
| `acquire_linked` | `Linear::new` | The new record is related to the resource that `do_acquire` adds. |
| `consume_linked` | `consume` | A success is the model step `step_consume`. If the model state is `err_consumed_twice`, the exec consume fails and does not change the record. |
| `unwind_linked` | `unwind` | The exec runs `on abort` exactly when the model resource is live. With `on abort`, the step is `step_unwind_abort`. If the exec does not run it, the model state is `err_unwind_dead`. |

Thus each exec transition is a model transition, and the exec API refuses
each transition into the model errors `err_resume_used`,
`err_consumed_twice` and `err_unwind_dead`.

### Differences

The link states these differences in the theorems. It does not hide them.

* `drop_now` on a fresh `multi` continuation reports an abort. The model does
  not unwind a `multi` continuation (`holds_fresh` is false), and its record
  does not change (`ex_multi_drop`). E5 says that such a continuation holds no
  linear value and no fresh `once` continuation. Thus the unwind of the
  interpreter has nothing to finalize. The link does not prove this
  consequence.
* `Linear` has no `on abort` flag. If the type of a live value has no
  `on abort`, the exec unwind still succeeds, but the model state is the error
  `err_no_on_abort`. The checker rule (W0602, E3) must exclude this case.
* After an abort, the postcondition of `drop_now` does not keep the mode of
  the record. Thus `kont_rel` does not use the mode of a `Dropped` record.

## Examples (`src/examples.rs`)

| Example | What it shows |
| --- | --- |
| `ex_push_kills_element_refs` | Rule 3 and the model agree on `mut(world.entities)` and `&world.entities[]`. The typed hypotheses hold. |
| `ex_split_alias_not_in_model` | Gap witness: rule 3 kills a reference into `v[j..]` after `mut(v[..i])`. The model does not kill. `alias_exact` is false. |
| `ex_accepted` | Vacuity guard: a CFG with a borrow, a child reference, a mutating call and a read meets each hypothesis of `thm_w0301_no_ub`. |
| `ex_rejected` | W0301 rejects a read of the child reference after the call. No model annotation with the static groups passes `cfg_check`. |
| `ex_gen_and_kill` | Gap witness for `no_gen_kill` (see "Which direction"). |
| `ex_double_resume` | A second exec resume of a `once` continuation fails where the model state is `err_resume_used`. |
| `ex_once_drop`, `ex_multi_drop` | The abort at a clause return, for `once` and for `multi`. |

## Mutation tests

Each mutation below makes `verify.sh` fail. I ran them on scratch copies.
The delivered sources do not have them.

| Mutation | Fails in |
| --- | --- |
| Exec rule 3 without the unstable step (code and spec) | `places` (its own lemmas), `places_link` |
| Exec resume lets a `once` continuation resume twice (code and spec) | `lifecycle_link` |
| Exec unwind also aborts a consumed value (code and spec) | `lifecycle_link` |
| Exec `drop_now` also aborts a resumed continuation (code and spec) | `lifecycle_link` |
| The fixpoint spec (`spec_closed`) ignores `kill` | `dataflow`, `dataflow_link` |
| The embedding makes element steps stable | `places_link` |
| A `Copy` is not a rebind | `dataflow_link` |
| A `Copy` does not use its source | `dataflow_link` |
| `kont_rel` forgets the state of a dropped record | `lifecycle_link` |
| The model resume does not mark a `once` record used | `lifecycle_link`, `examples` |
| `lkills` without the unstable step | `places_link` |
| The B1 `killed` spares the groups with one label | `soundness` (borrowing), `dataflow_link` |

## What stays only tested

* The fact generation in sema (`crates/weft-sema/src/body/`): `points_into`,
  `mutates_at`, `rebound_at`, `uses`, `cfg_edge` and lexical scope. The link
  takes them as hypotheses (`facts_ok`, `bound_before_use`).
* The glue in `crates/weft-check/src/rules.rs` that builds `succ`, `gen` and
  `kill` from the facts, and the evidence search. `invalid_at` and
  `invalidates_in_model` state what the glue must compute.
* A reference with more than one place. The checker allows a list of places
  per reference. The B1 model has one group per reference.
* Split steps (`Seg`), and stability that does not come from the type.
* Closures, handlers and continuations in the dataflow link. Soundness
  (`thm_lfp_annotation_checks`) excludes `MkClosure` and `Invoke`. The
  `gen` of the link has no effect footprints (`performs_at`, `footprint`).
* `spec_overlaps` and `spec_within` (W0405 and signature cover). No model
  predicate is linked to them.
* The other analyses that use `propagate`: moves, linear liveness, `multi`.
  The effects model has its own checker. The link does not connect the two.
* `Continuation` and `Linear` derive `Copy`. The link assumes one exec record
  per model record. The interpreter must not copy a record.
* `modes.rs`.
