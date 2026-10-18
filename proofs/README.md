# Proofs

Verus proofs for Weft Phase 1. The pinned Verus revision is in `VERUS_VERSION`.

| Crate | Content | Status |
| --- | --- | --- |
| `borrowing/` | Soundness of group borrowing: places, calls, branches and loops, captured references, inline layout, task separation, progress. | B1-B5 proved (169 verified). See `borrowing/README.md`. |
| `effects/` | Soundness of algebraic effects: effect safety, one-shot, abort, lexical handlers, multi-shot restriction, progress. | E1-E5 proved (122 verified). See `effects/README.md`. |
| `link/` | B6: the exec core agrees with the models (places, dataflow, lifecycle). | Proved (230 verified). See `link/README.md` for the gaps. |

The link (`link/`) covers the exec core. The facts that sema emits and the glue in
`rules.rs` are hypotheses of the link: tests check them (agreement with the Datalog spec).

The exec core that the checker runs is in `crates/weft-verified`. It is verified too
(64 verified). See `crates/weft-verified/README.md` for the parts that the checker and
the interpreter use.

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
   split. The B3 checker with rule 3 as its kill rule has no UB.
2. Dataflow: on B1 CFGs without closures, if W0301 accepts, the result of
   `propagate` gives an annotation that passes the B1 CFG checker. Thus no
   run has UB. Each accepted model annotation marks at least the fixpoint of
   `gen` minus `kill` invalid.
3. Lifecycle: each operation of `Continuation` and `Linear` is a step of the
   effects machine, with two differences for `multi` continuations. Each
   operation fails where the model step is an error.

Run it with `link/verify.sh`. It runs `link/check-copies.sh` first.

`link/README.md` gives the theorems and the gaps.

`verify-all.sh` verifies `borrowing`, `effects`, `link` and `crates/weft-verified`. It
fails if one of them is missing, so the gate cannot pass without its proofs.

Rules for proof crates: no `assume`, no `admit`, no `external_body`, no new axioms.
