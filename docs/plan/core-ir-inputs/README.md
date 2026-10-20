# Core IR: design inputs

The inputs of ADR 0012 (`docs/adr/0012-core-ir.md`), the specification `docs/ir.md` and the
plan `docs/plan/core-ir.md`.

- `map_lowering.md`: how `crates/weft-sema/src/body/` lowers each construct to facts today.
- `semantics.md`: the run-time semantics of the interpreter and the proof models.
- `root_causes.md` and `findings.py`: each review finding of rounds 1 to 3, sorted by root cause.
- `design_machine.md`, `design_mir.md`, `design_minimal.md`: the three designs.
- `judge_soundness.md`, `judge_feasibility.md`, `judge_proofs.md`: the three judge reports.
- `reviews/`: the review records of rounds 1 to 3 and the results of the fix stages.

The records name a session scratch directory as `SCRATCH`. That directory is not kept. Stage
G2 of the plan copies the probe programs that the records name into `tests/gate/probes/`.
