# Round 1 part B: open items

## S3: control flow, tasks, handlers, effects-proof rules
- RT11: return/break/continue across closure, handle body, handler clause, scope body.
- RT12: spawn inside a closure is invisible; W0314 for fn items and fn params.
- Interp report: false W0314 for a task closure that performs a std effect directly inside a sim.run body.
- RT16: closure escapes its handler (outer local, tuple, struct, container) -> W0313.
- RT22: tail spawn handle wrapped in handle gives false W0601.
- Effects proof rules: (1) abort and multi rules at every suspension point (call: live values vs effects of the caps it passes; handle: vs all outer caps; resume: vs the clause's caps); (2) a fresh once continuation counts as a once value under the multi rule; (3) a handle body cannot return its own capability, also inside a closure; (6) clauses run in the handle-site environment and return no capabilities.
- F6: forwards computed from handler clauses that perform the effect outward (spec rule).
- RT24: s.spawn(5), fork() arity; named arguments to effect operations bind by name.
- RT21 follow-up: enforce pub across units (dependency modules).

## S4: modes, linear, values with references
- RT8 / F5: closure mode follows captures (linear, once, nonportable, uniq); resume and call_value use move_var; once check for a closure passed to a fn() parameter.
- F5: tuple has_on_abort is the AND over its linear parts.
- RT14: linear dropped by let _, tuple wildcard, print, match _, field/element overwrite; captured linear overwritten inside a closure or a clause.
- RT15: !Move transitive (fields, tuples, arrays, Option/enum payloads, Vec elements); self-reference field assignments must point within self; reads of unset place fields.
- RT3: references through generics (id(&x)), containers ([&x], Box.new(&x), push), struct literals (Wrap{x: &v[0]}), by-value match on Option<&T>, fn item params of type Option<&T>; W0204 for nested reference types (Option<&T>, structs with reference fields).
- RT18 / RT24: uniq on the hidden for-loop iterator; uniq is not sticky after a rebind.
- QR7 / QR8: per-ADT fixpoint cache for linear, nonportable, copy, on_abort, immovable (no depth cutoff, no exponential walk).
- QR12 (body parts): duplicate struct-literal initialisers, duplicate closure params, literal range checks, fork() arity, messages for f(y: 1) and f(x: 1, x: 2).
- QR11 (body part): the W0701 hint lowercases user effects (call.rs).
- RT24: definite assignment (let x: u64 then use), non-exhaustive match.

## S5: refactor and spec fidelity
- F8: move W0203/W0204/W0314/W0406/W0705/W0802/W0803 into Datalog where feasible.
- F9: use weft_verified::modes::{submode, join} for mode checks (or keep claims corrected).
- F7: compare Report.invalidations / Report.conflicts with the spec; completeness guards.
- F13: perform-site W0301 shows the footprint; JSON notes keep line refs; derivation linked to its diagnostic; W0701 empty row.
- QR17: newtype ids in weft-sema (FnId, ModId, EffectId, AdtId); Code enum; magic numbers (900 + adt, 800 + i, split_base * 64).
- QR15 / QR16: show() adt_names per variable; hot-path clones.
- QR19 (body parts): local_ty duplicate, multi_node twice, let _ = &self.loops.
- QR22: a proptest that feeds mutated corpus programs to check_source plus agreement on a 2 MiB thread.

## From the quality lane (out of lane, body/), exact changes in quality_results.json
- VarInfo flags (linear, has_on_abort, immovable, nonportable, once, ty) are set at the `let` before inference resolves the type; recompute them in Lower::finish from the resolved type (repros bare_vec.wf, multi_vec.wf: a linear value in an unannotated Vec gets 0 errors and faults at run time). -> S4
- QR4: body/mod.rs `use std::rc::Rc` -> `std::sync::Arc as Rc`; types.rs Ty::Fn(Arc<FnTy>); program.rs Arc::new; run weft_sema::analyze on a scoped large-stack thread (move on_large_stack/STACK from weft-cli to weft-sema). -> S5
- Field of a literal (`1.sleep`, `500.x`) is accepted: W0104 in Lower::expr. -> S4
- `loop { return xs }` as a fn tail gives a false W0102: type a loop with no break as Never. -> S3
- Shadowed standard effect names: facts name effects by string; a user `Log` that shadows the standard `Log` cannot be told apart. Needs effect identity in the facts (design examples shadow Log on purpose). -> S3 (decide: qualified name for a user effect that shadows a std one)
- QR11 W0701 lowercase (stmt.rs:149, call.rs:402, call.rs:765 -> effects::written_name). -> S4
- QR19 VarInfo.callable set in var_info; drop the `fn(` text default. -> S4
- QR12 body checks: duplicate struct-literal initialisers, duplicate closure params, literal ranges (IntTy bound helper), fork arity, named-argument messages. -> S4
- QR19 dead code: `let _ = &self.loops;`, local_ty/local_ty_pub duplicate. -> S5

## From the quality merge (2712a80), for S5
- W0301 cost grows with the square of the number of references (one invalidated_at pass + one first_reaching search per reference). Move pattern takes ~1.8 s at n=1000 in debug. Share work across references (one pass per points_into set already; extend to one search per gen set).
- Duplicate corpus numbers 31-34 (two files each): renumber the edge ones (31_raw_pointers, 32_overwritten, 33_stealable, 34_alias_in_one_task) and update ADR 0005/0006 and docs/design.md references.
- W0901 docs and `weft explain W0901`: say that only standard effects need authority.
- diagnose.rs comment on W0301 grouping is stale (group key is (reference, invalidating node)).
- agreement_random each_invalid_use_has_the_first_evidence: check against all gen nodes, not only evidence nodes.

## From S3/S4 (round1b_results.json), open and recorded in ADRs; S5 decides fix or keep
- ADR 0005: a task that runs a function value from a store (field or container); a callee that copies a fn value out of a reference argument; a clause that keeps its fn parameter; operation results that hold references; Local.caps only grows (false W0313 after a reassignment).
- ADR 0006: a stored spawning closure at a reach node starts one copy of its task; a clause that runs a parameter of a finished closure as a task.
- ADR 0007: overwriting None/empty Vec of an inferred local is W0601 (needs an 'empty value at bind' input relation); generic callees that abort or are multi while they hold a linear T; a Vec of linear values has no consumer; a return/break in a later operand that leaves a linear value.
- ADR 0003: references stored behind a reference parameter; stale holder after a join on a continue path.
- W0304 read inside a handler clause is reported on the resume line.
- Effects-proof rule 2 through closures: check S4 covers a closure that holds a fresh once continuation (63_suspension cases).

## Open after R2a/R2b (for the final issue)
- R2a: a multi operation of a CALLER's handler can re-run the rest of a function body with locals from the run before (only local handlers are modelled as loops). Unsound.
- R2b FD3 residual: a closure or clause that stores its own reference parameter into an rc object, or behind a reference parameter, is checked only against stated places; a function value does not state where the references it receives live. Unsound.
- R2b FD3 precision: a reference stored into an rc object through a handle of the same rc type is allowed even when the handle refers to another object (group places). Unsound by design choice (design example c.refs.push(&c.data[0])).
- Pre-existing FP: a local that receives a reference from a callee through `holds` (reg_ref(&h, ...)).

## Open after S5a and R2c-R2e (for the final issue)
- S5a 3b kept: a Vec of linear values has no consumer; the sound rule rejects too much (ADR 0007, corpus 88 known gap).
- S5a residuals (ADR 0005): a node that runs a clause and that only the stored-value pass finds gets no abort edge; a value the body cannot follow that goes to a caller's operation is not checked for W0314; a reference stored behind a closure or clause parameter is seen as the outer place only.
- R2c imprecisions (sound): an operation in a closure/clause inside a handled body spares nothing; a callee that performs the operation makes each resume free every reference parameter of the clause; a generic wrapper holding Rc<T> is never many across a multi operation.
- R2d: Box borrow through an unstable deref does not read the Box (c2_box_borrow_nouse.wf); a clause that spawns its fn parameter into an outer scope then resumes (imprecision); fn values in a struct a callee returns, called later by an unknown value outside a task (pre-existing gap).
- R2e: no root-anchored effect path form (language change); `let g = diff; g = rdiff` loses parameter names (W0104 imprecision).

## Open after S5b/S5c (for the final issue)
- S5b F8 partial: W0204 forms with a root that ends at an exit (a local, a by-value parameter or a temporary at a return; a closure or clause local; a store behind a reference) stay in sema; ADR 0002 says why.
- S5c: long functions in body/ not split (loop_head, rewind, handle ~176 lines, match_pattern, expr, stmt, eval_i...).
- S5c: one W0301 shape stays quadratic in the checker: n references, each live across most of the function, invalidated one after the other.
- S5c imprecision: a stored value that a callback can be still pairs with a different known closure at parameter 0 (sound side).
- Pre-existing FP: a local handler clause that runs its callback parameter gets W0312 (handle Run { fn run(g) { g() } } in { run(|| st.count += 1) }).
