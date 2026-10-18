# Proofs

Verus proofs for Weft Phase 1. The pinned Verus revision is in `VERUS_VERSION`.

| Crate | Content |
| --- | --- |
| `borrowing/` | Soundness of group borrowing (places, calls, captured references, tasks). |
| `effects/` | Soundness of algebraic effects (effect safety, one-shot, abort, lexical handlers). |
| `link/` | B6: the exec core agrees with the models (places, dataflow, lifecycle). |

The exec core that the checker runs is in `crates/weft-verified`. It is verified too.

Run all proofs:

```bash
./verify-all.sh        # needs `verus` on PATH
```

## The link crate

`link/` includes the source files of `crates/weft-verified`, `borrowing/` and
`effects/` with `#[path]`. It does not copy them. It proves three links:

1. Places: for all places, if the B3 model kills a reference, rule 3 (the
   exec `invalidates`) invalidates it. For typed places without split steps,
   the two are equal. The model has no split steps. For split places, the
   link reads a split side as the elements step. Then, for typed places,
   rule 3 is the model predicate, minus the pairs with the two sides of one
   split. The B3
   checker with rule 3 as its kill rule has no UB.
2. Dataflow: on B1 CFGs without closures, if W0301 accepts, the result of
   `propagate` gives an annotation that passes the B1 CFG checker. Thus no
   run has UB. Each accepted model annotation marks at least the fixpoint of
   `gen` minus `kill` invalid.
3. Lifecycle: each operation of `Continuation` and `Linear` is a step of the
   effects machine, with two differences for `multi` continuations. Each
   operation fails where the model step is an error.

Run it with `link/verify.sh`. It runs `link/check-copies.sh` first.

`verify-all.sh` and CI do not run the link yet. Until they do, a change to an
included file can break the link, and CI does not see it. To fix this,
change the loop in `verify-all.sh` to `for crate in borrowing effects link; do`.
`link/README.md` gives the theorems and the gaps.

Rules for proof crates: no `assume`, no `admit`, no `external_body`, no new axioms.
