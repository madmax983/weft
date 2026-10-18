# Proofs

Verus proofs for Weft Phase 1. The pinned Verus revision is in `VERUS_VERSION`.

| Crate | Content |
| --- | --- |
| `borrowing/` | Soundness of group borrowing (places, calls, captured references, tasks). |
| `effects/` | Soundness of algebraic effects (effect safety, one-shot, abort, lexical handlers). |

The exec core that the checker runs is in `crates/weft-verified`. It is verified too.

Run all proofs:

```bash
./verify-all.sh        # needs `verus` on PATH
```

Rules for proof crates: no `assume`, no `admit`, no `external_body`, no new axioms.
