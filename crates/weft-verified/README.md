# weft-verified

This crate is the verified core of the Weft checker. Verus proves the code.
A normal `cargo build` compiles the same code. The `verus!` macro removes the
specs and the proofs. The production checker and the interpreter call most of
these functions. `places::concat` and the `modes` functions are verified but not
yet used.

## Verify

Put Verus on `PATH`. Use the revision in `proofs/VERUS_VERSION`.

From the workspace root, run:

```bash
verus crates/weft-verified/src/lib.rs --crate-type=lib
```

The result must be:

```text
verification results:: 64 verified, 0 errors
```

| Module | Verified |
| --- | --- |
| `places` | 25 |
| `dataflow` | 16 |
| `modes` | 9 |
| `lifecycle` | 14 |

To verify one module, add `--verify-module <name>`.

To test and lint the compiled code, run:

```bash
cargo test -p weft-verified
cargo clippy -p weft-verified --all-targets -- -D warnings
```

The proofs do not use `assume`, `admit`, `external_body`, or new axioms. Each
loop has a `decreases` clause. Thus each exec function terminates.

## `places`: the place algebra

A place is a root and a sequence of steps. Each exec function returns exactly
the value of its spec function.

| Exec function | Ensures |
| --- | --- |
| `step_alias` | `r == spec_step_alias(*a, *b)` |
| `step_within` | `r == spec_step_within(*a, *b)` |
| `may_prefix` | `r == spec_may_prefix(m@, p@)` |
| `crosses_unstable` | `r == spec_crosses_unstable(from as int, p@)` |
| `invalidates` | `r == spec_invalidates(m@, p@)` (rule 3) |
| `within` | `r == spec_within(p@, d@)` |
| `overlaps` | `r == spec_overlaps(p@, q@)` |
| `concat` | `r@ == a@ + b@` (not yet used; sema substitutes signature places with its own code) |

| Lemma | Statement |
| --- | --- |
| `lemma_step_alias_symmetric` | Step aliasing is symmetric. |
| `lemma_no_self_invalidation` | Rule 4: a mutation of `p` does not invalidate a reference to `p`. |
| `lemma_stable_suffix_survives` | Rule 4: if all steps of `p` after `m` are stable, a mutation of `m` does not invalidate `p`. |
| `lemma_disjoint_no_invalidation` | A mutation does not invalidate a place that it does not overlap. |
| `lemma_deeper_mutation_weaker` | A mutation of `m + s` invalidates only places that a mutation of `m` invalidates. This makes the wildcard `mut(w..)` sound. |
| `lemma_step_within_alias` | Step inclusion gives step aliasing. |
| `lemma_within_overlaps` | If `p` is in `d`, then `d` can be a prefix of `p`. |
| `lemma_cover_invalidates_more` | Signature soundness: if `m` is in the declared place `d`, then `d` invalidates each place that `m` invalidates. |
| `lemma_within_transitive` | Inclusion is transitive. |
| `lemma_split_sides_disjoint` | The two sides of one split do not overlap. |

## `dataflow`: gen/kill propagation

`propagate` computes the least set that is closed under the two gen/kill rules.
The checker analyses use it. The theorem is the postcondition:

```text
forall i. out[i] == spec_in_lfp(spec_view(succ), gen@, kill@, i)
```

Node `i` is marked if and only if each closed set contains `i`.

The proof has three parts:

1. Soundness. Each marked node is in each closed set. `lemma_step_sound` shows
   one marking step. The loop invariant `spec_work_inv` keeps the property.
2. Completeness. At the end, the marked set is closed (`lemma_marked_closed`).
   Thus the least fixpoint is in the marked set (`lemma_done`).
3. Termination. The measure `2 * spec_count_unmarked(out) + work.len()`
   decreases on each worklist iteration (`lemma_count_unmarked_mark`).

| Lemma | Statement |
| --- | --- |
| `lemma_step_sound` | A successor of a `gen` node, or of a non-`kill` node in the least fixpoint, is in the least fixpoint. |
| `lemma_marked_closed` | If the successors of each `gen` node and of each marked non-`kill` node are marked, the marked set is closed. |
| `lemma_done` | When the worklist is empty, the marked nodes are exactly the least fixpoint. |
| `lemma_mark_and_push` | To mark a node of the least fixpoint and push it keeps the invariant. It removes one unmarked node. |
| `lemma_pop` | To pop a node keeps the invariant. The popped node becomes the active node. |
| `lemma_count_unmarked_mark` | To mark an unmarked node decreases the unmarked count by 1. |
| `lemma_marked_contains` | A node is in `spec_marked(out)` if and only if `out` marks it. |
| `lemma_push_contains` | A push keeps each element and adds the pushed element. |
| `lemma_pop_contains` | A pop removes only the last element. |

Note: in this Verus version, `Set<int>` contains only finite sets. The least
fixpoint is a subset of the nodes, so it is finite. The theorem is the same.

## `modes`: the mode lattice

Not yet used: the checker decides the mode rules with flags in the facts
(`nonportable`, `uniq`, `shared`). A later stage can use these functions.

| Exec function | Ensures |
| --- | --- |
| `bottom` | `r == spec_bottom()` |
| `submode` | `r == spec_submode(*a, *b)` |
| `join` | `r == spec_join(*a, *b)` |

| Lemma | Statement |
| --- | --- |
| `lemma_submode_reflexive` | Submoding is reflexive. |
| `lemma_submode_transitive` | Submoding is transitive. |
| `lemma_submode_antisymmetric` | Submoding is antisymmetric. Thus it is a partial order. |
| `lemma_join_is_lub` | The join is the least upper bound. |
| `lemma_bottom_crosses` | Plain immutable data can go to each mode (mode crossing). |

## `lifecycle`: continuations and linear values

The interpreter uses these state machines at run time.

| Exec function | Ensures |
| --- | --- |
| `Continuation::new` | The state is `Fresh`. |
| `Continuation::resume` | The resume succeeds only if the state is `Fresh`, or `Resumed` for a `multi` continuation. A second resume of a `once` continuation fails with `AlreadyResumed`. A resume after a drop fails with `AlreadyDropped`. A failure does not change the state. |
| `Continuation::drop_now` | The drop aborts only a `Fresh` continuation. Otherwise it does not change the state. |
| `Linear::new` | The state is `Live`. |
| `Linear::consume` | The consume succeeds only for a `Live` value. A failure does not change the state. |
| `Linear::unwind` | `on abort` runs only for a `Live` value. Otherwise the state does not change. |
| `Linear::is_finished` | `r == (state != Live)` |

| Lemma | Statement |
| --- | --- |
| `lemma_finish_once` | A finished value is `Consumed` or `Aborted`. |

Together, these specs show that a `once` continuation resumes at most one time.
They also show that a linear value finishes (consume or abort) at most one time.
