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
   exec `invalidates`) invalidates it. Without split steps, the two are equal.
2. Dataflow: if W0301 accepts, the result of `propagate` gives an annotation
   that passes the B1 CFG checker. Thus no run has UB. Each accepted model
   annotation marks at least the fixpoint invalid.
3. Lifecycle: each operation of `Continuation` and `Linear` is a step of the
   effects machine. Each operation fails where the model step is an error.

Run it with `link/verify.sh` and `link/check-copies.sh`. `verify-all.sh` does
not run it yet. `link/README.md` gives the theorems and the gaps.

Rules for proof crates: no `assume`, no `admit`, no `external_body`, no new axioms.
