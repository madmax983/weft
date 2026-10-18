# Proofs

Verus proofs for Weft Phase 1. The pinned Verus revision is in `VERUS_VERSION`.

| Crate | Content | Status |
| --- | --- | --- |
| `borrowing/` | Soundness of group borrowing: places, calls, branches and loops, captured references, inline layout, task separation. | B1-B5 proved for the model (169 verified). See `borrowing/README.md`. |
| `effects/` | An abstract machine for algebraic effects and its static checker. | E1 (effect safety, `e1_effect_safety`) and E4 (lexical resolution, `e4_lexical_resolution`) proved (48 verified). E2 (one-shot), E3 (abort safety) and E5 (multi-shot restriction) are defined in `model.rs` but not proved yet. |

Not done: B6, a proof that links the exec core and the Datalog rules to these models.
The proofs cover models, not the checker that ships: tests link the checker to the rules
of the models.

The exec core that the checker runs is in `crates/weft-verified`. It is verified too
(64 verified). See `crates/weft-verified/README.md` for the parts that the checker and
the interpreter use.

Run all proofs:

```bash
./verify-all.sh        # needs `verus` on PATH
```

`verify-all.sh` verifies `borrowing`, `effects` and `crates/weft-verified`. It fails if
one of them is missing, so the gate cannot pass without its proofs.

Rules for proof crates: no `assume`, no `admit`, no `external_body`, no new axioms.
