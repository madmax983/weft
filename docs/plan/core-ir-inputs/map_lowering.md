# Map of the current lowering: typed AST to facts

Commit: `b073ea7` (`/home/user/weft`, read-only). All paths are relative to
`crates/weft-sema/src/` unless the text says otherwise. A citation `file:N` names the
first line of the function or of the statement.

This document has six parts and two appendixes:

1. The architecture of the lowering: the state, the nodes, the components, the
   post-passes, the roots, the hidden variables and the hidden nodes.
2. The map of each surface construct: the functions that lower it, the facts that it
   emits, the variables and nodes that it invents, and its special cases with the
   reason for each one.
3. The cross-cutting mechanisms: which constructs must remember each one, and how
   the mechanisms interact.
4. The places where the facts and the interpreter disagree today: the round-3
   blockers, and two new blockers that I found while I made this map (N1, N2).
5. The invariants that the facts must satisfy for the rules of `spec/weft.dl` to be
   sound, with the hypotheses of `proofs/link/README.md`.
6. A short list of what this map tells the design of a core IR.

Appendix A lists the producers of each input relation. Appendix B lists the files.

Sources that I read: `CLAUDE.md`, `README.md`, `docs/design.md`,
`docs/architecture.md`, `docs/traceability.md`, ADR 0002, 0003, 0005, 0006, 0007,
0010, 0011, `spec/weft.dl`, `crates/weft-facts/src/lib.rs`, all of `body/`
(19 097 lines), `program.rs` (`EffectSig`, `field_step`, `elem_step`,
`in_place_order`), `infer.rs` (header), `props.rs` (header), `lib.rs` (driver),
`crates/weft-check/src/bridge.rs` (`each_fact`), `crates/weft-interp/src/compile.rs`
and `machine/exec.rs` (statements, temporaries, frames), the B1 model
(`proofs/borrowing/src/cfg.rs`, `model.rs`), the B6 hypotheses
(`proofs/link/src/dataflow_link.rs`, `proofs/link/lints/*.dl`), the effects README,
the review reports of rounds 1 to 3, `round1b_tasks.md`, and the stage issues list
(`ir/work/stage_issues.txt`). I ran `target/debug/weft facts` on small programs
(`ir/work/map/ex1.wf`) to confirm the shapes of the facts.

---

## 1. Architecture of the lowering

### 1.1 One walk does everything

`Lower` (`body/mod.rs:1160`) walks the AST of one function once. In that one walk it:

- infers types (`Infer`, unification in `Lower::unify`, `mod.rs:1565`);
- computes places and the places that each value points into (`Val::refs`);
- tracks function values (closure summaries), tasks, capabilities and modes;
- writes the CFG nodes and the facts (`FnFacts`);
- reports type, name and many check diagnostics (W01xx, W0204, W0313, W0314,
  W0315, W0502, W0504, W0605, W0701, W0707).

There is no intermediate form. A `Val` (`mod.rs:908`) is the abstract value of an
expression. It has a type, the places that it points into (`refs`), the variable that
holds it (`var`), its local (`local`), its place (`place: LVal`), a closure summary,
an item, a function parameter, task ids, capability marks, the parts of a tuple, and
an `empty` flag. An `LVal` (`mod.rs:929`) is a place expression: the places, the type,
the owner local, a `through_ref` flag, the `Rc` handle places on the way (`deps`), and
the capabilities that the place can hold.

The lowering is not one pass in practice:

- A loop body is lowered again until the values of the outer locals are stable
  (`loops::lower_loop`, `loops.rs:188`). Each pass rewinds all facts to the loop head
  (`FactMark`, `FnFacts::rewind`) and restores the locals (`Locals::begin/end/restore`,
  `mod.rs:867`).
- A handled body of an effect with a `multi` operation is lowered as a loop
  (`handled_again`, `expr.rs:2518`).
- The clauses of a `handle` are lowered after the handled body (`handle`,
  `expr.rs:1823`). So a clause sees the places that the body gave to its operation.
  The facts of the clause at the nodes of the body come later (`run_handler`).
- 17 post-passes rewrite the facts after the walk (section 1.4).
- Effect inference (`infer.rs`) lowers each body again until the signatures are
  stable. A body reads the signatures of its callees (`EffectSig`, `program.rs:286`):
  24 parts, most of them "always inferred" (`lent`, `ret`, `stores`, `reaches`,
  `reach_given`, `reach_repeats`, `multi`, `tasks`, `task_runs`, `pins`, `op_fns`,
  `op_effects`, `task_effects`, `repeats`, `fn_stores`, `ret_refs`, `group_stores`,
  `fn_store_refs`, `drops`, `holds`, `raises`). Each part is a summary of a fact
  pattern of the callee that the caller must replay.

### 1.2 Nodes and the pending queue

| Primitive | Where | What it does |
| --- | --- | --- |
| `emit(span, label, detail)` | `mod.rs:1667` | Adds a node, an edge from the current node, and moves the pending uses (`pend_uses`) and reads (`pend_reads`) onto the new node. The new node is the current node. |
| `start(span, label)` | `mod.rs:1700` | Starts a new CFG component: a node with no predecessor. |
| `flush(span)` | `mod.rs:1708` | Writes the pending queue into a `use` node. It must run before control leaves a branch, a loop body or a component. |
| `take_pending`, `restore_pending` | `mod.rs:1722` | Saves the queue across a closure or a clause, which start their own components. |
| `insert_after(n, ...)` | `mod.rs:1684` | Adds a node after an existing node `n`, and moves the out-edges of `n` to the new node. Post-passes use it (`restart_after`, `apply_stored`). |
| `facts.add_node` with no edge | `stmt.rs:631`, `stmt.rs:1425`, `expr.rs:928`, `call.rs:3309` | Nodes of `ref_at`, `ref_in` and `sim_run_at`. Only one rule reads them (ADR 0002). |
| `cur = None` | many | The code after a `return`, `break`, `continue` or a node that never returns cannot run. Most emitters return early when `cur` is `None`. |

A node "uses its inputs before it mutates places" (`mod.rs:1` doc). The spec puts a
mutation at node `P` in effect at the successors of `P` (`invalid(R, Q) :-
invalidated_at(R, P), cfg_edge(P, Q)`). So a use and a mutation can share a node, and a
use that comes after a mutation at run time needs a node of its own. The lowering adds
such nodes by hand: "call again" (`repeat.rs:60`), "spawn again" (`repeat.rs:207`),
"given back by the callee" (`call.rs:1480`), "task end" (`late.rs:585`).

### 1.3 CFG components and summaries

Each function body, each closure body and each handler clause is one connected
component of the CFG (`weft-facts/src/lib.rs:1`). There are more components: the check
of a generic item that is used as a value (`check_item_value`, `drops.rs:41`), and the
edge-less nodes of section 1.2.

A closure or a clause does not get edges to the code that runs it. Its own component
checks only the code inside it. At each node that runs it (a "run node"), the lowering
copies what the body does into the facts of that node. This is the summary mechanism:

- A closure or a clause has a `Summary` (`mod.rs:272`): 42 fields. Examples: `muts`,
  `reads`, `lends`, `escapes`, `performs`, `captures`, `moved_captures`, `dropped`,
  `ret_refs`, `param_roots`, `binds`, `spawns`, `op_args`, `cap_runs`, `uniq_needs`,
  `param_stores`.
- `apply_summary` (`fnval.rs:538`) runs a summary at a node. It maps each place below
  a parameter root of the body onto the places that the node gives (`places_of`,
  `through`, `fnval.rs:486`), and copies `mutates_at`, `call_mut`, `reads_at`,
  `lends_mut`, `escapes_at`, `performs_at`, `may_abort`, `multi_at`, `scope_end` (of
  the locals of the body), `spawned_at` and more.
- `run_handler` (`expr.rs:2341`) does the same for the clauses of a `handle` at each
  node that performs through the handler.
- `apply_value` (`fnval.rs:434`) dispatches over what a function value can be: a
  closure summary, a function item (`apply_item`, `fnval.rs:692`), a function
  parameter (`call_param`, `fnval.rs:752`), or a value that the body does not know
  (`call_unknown`, `fnval.rs:778`).
- `late_join` (`late.rs:206`) adds, at a run node, the new values that the captured
  variables got after the closure was made.

So the facts of one closure appear twice: once in its own component, and once at each
run node in the places of the caller. The spec sees only facts. It does not know that
the second copy is a summary.

### 1.4 Post-passes

`lower_fn` (`stmt.rs:16`) and `finish` (`stmt.rs:182`) run these passes after the walk,
in this order. Each pass reads the facts of the earlier ones and adds or removes facts.

| Order | Pass | Where | What it adds or changes |
| --- | --- | --- | --- |
| 1 | `finish_values` | `fnval.rs:1185` | Sets `lowered`. Runs `finish_task_values` (the new values of task captures, `late.rs:664`), `apply_stored` (each stored function value at each node that can reach it, `fnval.rs:1042`), and `run_handler` again for the new nodes that perform. |
| 2 | `finish_aborts` | `aborts.rs:23` | Adds an "abort" node and an edge from each node that runs a clause that can end with no `resume`, to the end of the `handle`. Adds `unwound_at`, `joined_at`, "task end" nodes. Runs the W0313 check of outer locals. |
| 3 | `finish_task_ends` | `late.rs:605` | Gives each "task end" node `lends_mut` of each place that the task writes. |
| 4 | `finish_task_marks` | `tasks.rs:471` | `opaque`, `spawns_in`, the `pins` and `task_runs` parts. |
| 5 | `op_refs` | `oprefs.rs:388` | Moves every fact below the root of an operation result onto the places that the `resume`s give (`points_into`, `mutates_at`, `reads_at`, `call_mut`, `call_arg`, `lends_mut`, `task_reads`, `task_writes`, and summary parts). |
| 6 | `finish_op_env` | `oprefs.rs:59` | `lends_mut` of the root "a place of a caller" at each node that runs code of a caller. |
| 7 | `check_returns` | `oprefs.rs:113` | W0204, `ref_at`, `ref_in` for returned references, after `op_refs`. |
| 8 | `check_stored_behind` | `oprefs.rs:124` | W0204 for stores behind reference parameters and into `rc` objects; `fn_store_refs`, `group_stores`. |
| 9 | `summary_to_sig` | `stmt.rs:374` | The `EffectSig` of the body. |
| 10 | `finish_resume_runs` | `expr.rs:2688` | Copies `mutates_at`, `lends_mut`, `releases_at` of each `resume` onto each node that runs a closure that resumes. |
| 11 | `finish_spared` | `aborts.rs:105` | `spared_at` for the operations of local handlers. |
| 12 | `check_int_lits`, `finish_int_ops` | `stmt.rs:272` | W0102 and `int_ops`. |
| 13 | `settle_moves` | `stmt.rs:256` | Removes `moved_at` and `moved_part` of a value whose final type is plain data (`tentative`). |
| 14 | `finish_via_calls` | `stmt.rs:1382` | `writes_via` for method calls through a one-reference local, after all mutations of the node are known. |
| 15 | flag pass | `stmt.rs:196` | Sets `linear`, `has_on_abort`, `immovable`, `nonportable`, `once`, `callable`, `ty` of each local and hidden variable from the type that the whole body infers. |
| 16 | `dropped_params`, `held_params` | `drops.rs:95`, `drops.rs:180` | The `drops` and `holds` parts of a generic body: a small W0601 and W0602 analysis that sema runs itself on the facts. |
| 17 | `normalize` | `weft-facts` | Sorts and deduplicates. |

Hazards of this design:

- A pass can see facts that a later pass changes. Example: `body_frees` (`expr.rs:2592`)
  reads `moved_at` while a `handle` is lowered, and `settle_moves` (pass 13) can remove
  some of these moves later. The result is conservative, but it shows that the order
  matters.
- Some passes add nodes after the walk (`insert_after`, abort nodes, "task end"). Other
  passes find "the nodes of a closure" by a range of node numbers
  (`Summary::nodes`, `expr.rs:1473`; used by `spawned_inside` `tasks.rs:541`,
  `finish_task_marks`, `kept_roots`, `finish_resume_runs`, `finish_spared`). A node
  that a post-pass adds is outside every range. `reaches_without` (`expr.rs:2970`)
  assumes that each edge comes after its source node in `cfg_edge`, except for
  `insert_after`.
- `retire_stale` (`mod.rs:2805`) changes the target of an existing edge.

### 1.5 Roots and places

`FnFacts::add_root` makes a root of one of four kinds (`weft-facts/src/lib.rs:117`):
`Param` (needs a declaration), `Local` (owned), `Group` (an `rc` type), `Arg` (the
pointee of a parameter of a closure or a clause, or of a place of a caller). The
lowering makes these roots:

| Root | Kind | Made by | Owner fact |
| --- | --- | --- | --- |
| a reference parameter `p` | `Param` | `lower_fn`, `stmt.rs:36` | none |
| a by-value parameter `p` | `Local` | `stmt.rs:42` | `owner(p, v)` |
| a by-value parameter that holds references (`Option<&T>`) | `Local` and a second `Param` root with the same name | `stmt.rs:47` | `owner` for the first only |
| what the references behind reference parameter `i` point into (`*rs`) | `Param` | `held_root`, `flow.rs:119` | none |
| a local that holds an owned value | `Local` | `assign_local`, `mod.rs:2590`; `place_expr`, `expr.rs:554` | `owner` |
| the cell of a reference local (`Local::cell`) | `Local` | `assign_local`, `mod.rs:2594` | none. Only W0405 uses it. |
| a temporary | `Local`, name `temporary` | `temp_root`, `mod.rs:2173` | `owner` only if the value can free memory |
| an `rc` group of a type | `Group` | `group_root`, `mod.rs:2213` | none |
| a reference parameter of a closure | `Arg` | `bind_closure_params`, `expr.rs:1515` | none |
| a reference parameter of a clause | `Arg` | `bind_clause_params`, `expr.rs:2160` | none |
| a reference parameter of a returned function value | `Arg`, name `argument` | `ret_summary`, `fnval.rs:1561` | none |
| the result of an operation of a local handler | `Local`, name `operation result` | `op_result_refs`, `oprefs.rs:34` | none. `op_refs` moves the facts away at the end. |
| a place of a caller that a caller handler can give | `Arg`, name `a place of a caller` | `env_ref`, `oprefs.rs:47` | none |

Steps (`weft_verified::places::Step`): a field (stable), a variant (unstable), an
element (stability from the type, `elem_step`, `program.rs:2183`), a split side
(`[..k]`, `[k..]`, `seg_split`, `mod.rs:2235`), a deref (stability from the type; a
`Box` deref is unstable, `field_step` `program.rs:2163`), the wildcard step `WILD`, and
a one-place instance `wild_one(k)`. A handle place `h.*` (an unstable deref below an
`Rc` handle) marks a dependence on the handle (`handle_deps`, `mod.rs:2292`). The set
`dep_places` keeps these places apart, and `split_deps` (`mod.rs:2413`) separates them
from the places that a reference names.

Special place shapes:

- Wildcard places: `FnFacts::wildcard` keeps at most one wildcard step on a path. The
  result of a call of an unknown function value, a joined place in a loop after the
  widening, a place of a closure parameter that a callee gives with no position, the
  places that a handler of a caller gives.
- One-place instances (`one_result`, `flow.rs:19`): a call result that is one
  reference, in the function body (not in a closure or a clause), not in a loop, and not
  where a `multi` operation can re-run the code (`may_run_again`, `flow.rs:41`). A
  local that gets two results inside one base points into the shared wildcard place
  instead (`two_results`, `mod.rs:2946`).
- `below_shared_wild` (`mod.rs:2933`): a place below a shared wildcard `b..` becomes
  `b..`.
- `collapse_places` (`loops.rs:500`): a value with more than 16 places in one root at a
  loop head (64 for a local anywhere, `LOCAL_PLACES_MAX`, `mod.rs:730`) becomes the
  wildcard place of their common prefix.

### 1.6 Hidden variables

The facts name about 20 kinds of variables that are not locals of the source. Each one
exists to make a spec rule see a value at a node where no local holds it.

| Hidden variable | `VarKind` | Made by | Facts | Why |
| --- | --- | --- | --- | --- |
| held operand (`argument`, `receiver`, `operand`, `tuple part`, `element`, `field`) | `Temp` | `hold_as` via `hold`, `hold_later`, `hold_operand`, `hold_part` (`mod.rs:1740`) | `rebound_at` at a new node, `points_into` the value places, `uses` at the consumer | A later operand can invalidate the reference (ADR 0003, evaluation order). Not linear, `has_on_abort` true. |
| value on its way (`argument`, ...) | `Temp` | `hold_moved`, `mod.rs:1768` | `rebound_at`, `points_into`, `uses` and `moved_at` at the node that takes it (`take_held`), `scope_end` at a jump that leaves it (`leave_in_flight`) | A by-value operand moves when it is evaluated. A later operand can abort or jump (ADR 0007, W0602, W0601). |
| block value | `BlockValue` | `hold_out`, `stmt.rs:670` | `rebound_at`, `points_into`, `uses` at a "block value" node after the frame end | The end of the block frees its locals. A value that points into them must be invalid after it. |
| temporary owner | `Temp` | `temp_root`, `mod.rs:2173` | `owner`, `scope_end` at "end of statement", or at a run node through `Summary::dropped` | A temporary goes away at the end of its statement (ADR 0003, interpreter `StmtEnd`). |
| part holder `value in p` | `Temp` | `part_holder`, `stmt.rs:1311`; `hold_in_part`, `mod.rs:2847` | `rebound_at` at the assignment, `points_into`, `uses` at each use of the local | `points_into` is not flow-sensitive. A new value of a part points somewhere new from that node on. |
| stale part holder | the same | `retire_stale`, `mod.rs:2805` | `rebound_at` at a "stale part" node on an edge into a join | A branch replaced the holder. A change after the replacement must not count after the join. |
| unset place field | `Local`, with the place as name | `unset_fields`, `mod.rs:2608` | `unset_at` at the binding node, `rebound_at` at the assignment of the field, `uses` at each read (`touch_unset`) | W0304 for a place field of a `!Move` struct with no value. |
| hidden iterator `{iterator}` | `Iterator` | `for_loop`, `stmt.rs:1057` | `points_into` the elements, `uses` at the loop head | Each iteration reads through it. It is `@ uniq` if the source is. |
| closure value `{closure}` | `Closure` | `closure_value`, `expr.rs:1624` | `rebound_at` at the "closure" node, `points_into` the places of the captures and the roots of the captures that are not plain data | A closure is a reference holder of its captures. |
| stored closure `{stored closure}` | `Closure` | `escape`, `fnval.rs:933` | `rebound_at` at the store node, `points_into` the captures, `uses` at each node that can run it | The body does not follow the stored value. |
| continuation `resume` | `Continuation` | `bind_clause_cont`, `expr.rs:2213` | `rebound_at` at the clause entry, `moved_at` at a `once` resume, `once` flag | W0501: a `once` continuation resumes at most once. |
| dropped linear value | `Temp` or `Dropped` | `drop_linear_as`, `drops.rs:21` | `rebound_at` at one "drop" node, `scope_end` at the next "drop" node | Makes `unconsumed` fire for a linear value that goes away (W0601): `_`, a statement value, a temporary, a callee `drops`, `detach`. |
| value that a generic callee holds | `Temp` | `hold_generic`, `call.rs:1439`; `check_item_value`, `drops.rs:41` | `rebound_at` at "held by the callee", `uses` and `moved_at` at "given back by the callee" | W0602 and W0503 for a type argument in `holds`. |
| moved temporary | `Temp` | `move_temp`, `drops.rs:283` | `moved_at` | W0604 for a `!Move` temporary that a type parameter moves. |
| task handle | a local | `spawn`, `call.rs:3092` | none of its own; `Local::tasks` is lowering state | `joined_at` and the task sets. |

Some facts on source locals are also invented:

- `rebound_at(v, entry)` of a captured linear variable at the entry of a closure or a
  clause (`captures_live_at`, `expr.rs:1643`): so a new value inside the closure is
  `overwritten` (W0601, issue S002).
- `rebound_at` and `empty_at` of each local of a handled body at the "resume again"
  node (`again_node`, `expr.rs:2561`): the copy of a `multi` resume.
- `uses` of a captured variable at a run node (`late_join`, `late.rs:228`).
- `scope_end` of the locals of a closure at each run node (`apply_summary`,
  `fnval.rs:645`), and of the locals of a clause at each perform node (`run_handler`,
  `expr.rs:2407`).
- `moved_at` of a closure variable at a call that runs it once (`call_value`,
  `call.rs:1889`; `give_fn`, `repeat.rs:251`; `start_task`, `call.rs:2861`).
- `unset_at` in place of `rebound_at` for `let x: T` (`stmt.rs:879`).

### 1.7 Hidden nodes

| Label | Where | Why |
| --- | --- | --- |
| `entry`, `exit` | `stmt.rs:26`, `stmt.rs:100` | The function component. `return` jumps to `exit`. Parameters end at `exit`. |
| `closure entry`, `closure exit`, `closure end` | `expr.rs:1385`, `expr.rs:1678`, `expr.rs:1465` | The closure component. `closure end` gives `scope_end` to each linear capture that the closure moves. |
| `handler clause` | `expr.rs:2047` | The clause component. Its detail names the capability. |
| `let`, `assign`, `x =`, `move`, `drop`, `print`, `assert`, `return`, `jump`, `use`, `value` | `stmt.rs`, `mod.rs` | One node for each statement effect. `value` takes the held parts of a literal (`take_held_here`, `mod.rs:1811`). |
| call node (callee name), operation node (operation name), value call node (local name) | `call.rs:801`, `call.rs:2577`, `call.rs:1848` | One node for each call. |
| `held by the callee`, `given back by the callee` | `call.rs:1470`, `call.rs:1484` | Around a call of a generic callee in `holds`. |
| `branch`, `join` | `expr.rs:989`, `expr.rs:1018`, `expr.rs:828` | `if`, `&&`, `\|\|`. |
| `match`, `arm`, `end match` | `expr.rs:1105`, `expr.rs:1106`, `expr.rs:1119` | `match`. |
| `while`, `loop`, `for`, `for binding`, `iterator`, `end while`, `end loop`, `end for` | `stmt.rs:977` and after | Loops. |
| `end of statement`, `end of block` | `mod.rs:2207`, `stmt.rs:763` | `scope_end` of temporaries and of locals. |
| `block value` | `stmt.rs:700`, `stmt.rs:715` | A block value held across its frame end, or a move of a local that a block tail names. |
| `closure` | `expr.rs:1615` | Binds `{closure}`. |
| `end handle` | `expr.rs:2001` | The end of a `handle`. Abort edges go here. |
| `abort` | `aborts.rs:53` | `unwound_at` on the way to `end handle`. |
| `resume`, `resume again` | `call.rs:2363`, `expr.rs:2564` | A resume; the start of a re-run of a `multi` handled body. |
| `scope`, `scope end` | `expr.rs:2898`, `expr.rs:2923` | `scope` binds its binder; the end joins its tasks. |
| `spawn`, `fork branch`, `fork join`, `join`, `detach` | `call.rs:2856`, `call.rs:3288`, `call.rs:3170` | Tasks. |
| `task end` | `late.rs:589`, `aborts.rs:70` | After a task ends: `lends_mut` of what it writes. |
| `task of the callee` | `tasks.rs:320` | A chain of nodes after a call whose callee runs a function argument as a task. |
| `call again`, `spawn again` | `repeat.rs:65`, `repeat.rs:182`, `fnval.rs:1131` | A callee can run a value twice: the second run uses the captures after the changes of the first run. |
| `stale part` | `mod.rs:2826` | Rebinds a stale part holder on an edge into a join. |
| `return`, `field`, `sim.run` with no edges | `stmt.rs:631`, `stmt.rs:1425`, `expr.rs:928`, `call.rs:3309` | Only `ref_outside` or `sim_in_lib` reads them. |
| `test` | `stmt.rs:166` | The entry of a test body. |

---

## 2. The map of each construct

Each section has four parts:

- **Lowered by:** the functions, in the order that they run.
- **Facts:** the relations of `spec/weft.dl` that the construct emits, and at which node.
- **Invents:** the hidden variables, roots and nodes.
- **Special cases:** each case, why it exists, and the review item that made it
  (round 1: RTn, Fn; round 1b: S3, S4; round 2: RRn, ORn, FDn, QAn, IPn, S5a; round 3:
  R3RTn, O3-n, F3-n, I3-n, Q3-n; stage issues: Snnn in `ir/work/stage_issues.txt`).
  Each known gap at `b073ea7` is marked **Gap**.

### 2.1 Function body, parameters and the exit

**Lowered by:** `lower_fn` (`stmt.rs:16`); `finish_return` (`stmt.rs:519`);
`check_returned_refs` (`stmt.rs:547`, called by `check_returns`, `oprefs.rs:113`);
`summary_to_sig` (`stmt.rs:374`); `finish` (`stmt.rs:182`). A test body:
`lower_test` (`stmt.rs:161`).

**Facts:**

- `rebound_at(param, entry)` and `points_into(param, root)` for each parameter
  (`assign_local` at the entry node).
- `owner(root, param)` for each by-value parameter (`set_root`, `mod.rs:2512`).
- `shared_root` for each `@ shared` parameter (`stmt.rs:89`).
- `has_signature()`, `declared_mut` (the stated places, substituted, `stmt.rs:92`),
  `declared_effect` (closed under implication).
- `scope_end(local, "end of block")` for the body locals (`end_frame`, `stmt.rs:755`),
  `scope_end(param, exit)` (`stmt.rs:121`), `cfg_edge(…, exit)`.
- At a return: `ref_at`, `ref_in` on an edge-less "return" node, if the signature states
  returned places (`stmt.rs:631`).
- `library()`, `started()`, `no_runtime()` come from the driver (`lib.rs:283`).

**Invents:** the `entry` and `exit` nodes; one `Param` root for each reference
parameter; one `Local` root for each by-value parameter, and a second `Param` root with
the same name for a by-value parameter that holds references (`stmt.rs:47`).

**Special cases:**

- A parameter with `in p` gets no root of its own. Its places are the substituted
  places of `p`. The lowering substitutes the parameters in the order of their roots
  (`in_place_order`, `program.rs:2249`), because an `in` place can name a later
  parameter (QA3).
- A by-value parameter that holds references points into a `Param` root: the callee can
  change what the references point into, and the caller sees that change (ADR 0003).
  `summary_to_sig` removes the changes of the parameter's own value (`stmt.rs:405`).
- A parameter that can hold a function value gets the mark `Held::Param(i)` in its
  capability set (`stmt.rs:79`). W0314 and the `tasks` part use it.
- The value of the body moves into the result (`consume` in `finish_return`). A unit
  result is dropped instead (`drop_value`).
- The temporaries of the tail of the body get no `scope_end`: `lower_fn` pops their
  statement record with no close (`stmt.rs:110`). The exit ends everything. W0204 for a
  returned reference into a temporary covers the only way out.
- `check_returned_refs` runs after `op_refs`, so that an operation result has its final
  places (S5a 1d, S079, S092). It reports W0204 for a place in a local, a by-value
  parameter or a temporary (an exit that ends a root), and emits `ref_at` / `ref_in`
  for the stated-place check (S5b F8).
- A test body is a component with a `test` start node. It has no signature, so it
  skips `check_returns` and `check_stored_behind`. `library()` is false for it.

### 2.2 `let` and patterns in `let`

**Lowered by:** `stmt` `StmtKind::Let` (`stmt.rs:853`) → `expr` of the value →
`consume` (`stmt.rs:1632`) → `check_binders` (W0107) → `emit("let")` →
`bind_pattern` (`stmt.rs:1457`) → `new_local` (`mod.rs:2462`) and `assign_local`
(`mod.rs:2528`) → `flush` → `wild_drops` and `drop_linear` (`drops.rs:343`,
`drops.rs:15`).

**Facts:**

- From `consume`: a "move" node with `uses(v, n)` and `moved_at(v, n)` for a value that
  is not plain data. For a part of a local (`let x = p.a`), also `moved_part(p.a, n)`.
- At the "let" node: `rebound_at(x, n)` for each binder, `points_into(x, p)` for each
  place of the value (after `point_local`, `mod.rs:2887`), `empty_at(x, n)` for a value
  with no linear part (`None`), `owner(root, x)` at the first owned value.
- `unset_at(h, n)` for each place field of a value that is built in place
  (`unset_fields`, `mod.rs:2608`).
- `let x: T` with no value: the `rebound_at` facts of the binders become `unset_at`
  (`stmt.rs:879`). W0304 follows.
- A pattern `_` over a linear part: `drop_linear` makes a hidden variable with
  `rebound_at` at one "drop" node and `scope_end` at the next (W0601).

**Invents:** the "let" node; "move" and "drop" nodes; the unset field variables; the
root of each owned local (made when the local first gets a value, `mod.rs:2590`); the
cell root of a reference local (`mod.rs:2594`).

**Special cases:**

- A tuple pattern uses the parts of a tuple literal if the value has them
  (`Val::parts`). Else each part points where the whole value points. Behind a
  reference to a tuple, a part that is a reference also points where the held
  references point (`held_refs`, `stmt.rs:1496`).
- `let S(a, b) = s` consumes `s` (it is the consumer of a linear struct, ADR 0007).
  Each field that holds references points where `s` points.
- A fresh task handle under `_` does not drop: the scope owns the handle
  (`stmt.rs:883`). **Gap** (O3-4, I3-1, F3-6): the scope then drops the result of the
  task, also a linear result.
- `assign_local` does many things at once: it retires the part holders of the local,
  adds capability marks (W0313 bookkeeping), joins function values (old and new), sets
  the task set, joins `@ uniq` (`join_uniq`), and gives the variable `once` if the
  value is not `many`. Each of these is lowering state, not a fact, but later facts
  depend on it.
- A local that gets a result of a call with no stated place points into a one-place
  instance; a second result inside the same base widens to the shared wildcard place
  (`point_local`, `mod.rs:2887`, R2a).
- The binding is a node of its own, after the nodes of the value. So a call result
  never gets `rebound_at` at the call node. The B6 hypothesis `no_gen_kill` needs this.
- **Gap** (O3-2): `let r = handle … in { first(&mk_v()) }` frees the temporary at the end
  of the handled body, before the "let" node. `rebound_at(r, let)` then stops
  `invalid(r, _)`, so the free never reaches a use of `r`.

### 2.3 Expression statements and place statements

**Lowered by:** `block_inner` (`stmt.rs:730`) wraps each statement that is not the tail
in `open_stmt` / `close_stmt` (`mod.rs:2193`, `mod.rs:2199`). `stmt`
`StmtKind::Expr` (`stmt.rs:898`) → `expr` → `discard_block_value` (`stmt.rs:829`) for a
block, or `drop_value` (`stmt.rs:804`) unless `local_place` (`stmt.rs:791`).

**Facts:** `scope_end(t, "end of statement")` for each temporary of the statement that
can free memory. A dropped linear value: the "drop" pair of nodes. A block whose tail
names a place: a "move" node (`uses`, `moved_at`, `moved_part`).

**Special cases:**

- A place of a local in statement position (`v`, `p.tx`, `v[i]`) names the place only.
  It moves nothing and drops nothing (ADR 0003, round 2 OR6). The interpreter compiles
  it as a place (`compile.rs:473`).
- The tail of a block statement is a value: a place there moves, and the value goes away
  at the end of the block (`discard_block_value`, OR6, S118, S122).
- `drop_value` returns early for a value with a variable (`v.var`) or with tasks. A
  closure that moves a linear capture and that no local holds is dropped: a "drop" node
  with `scope_end` (W0601).
- **Gap** (O3-1): `scope { s => v }` in statement position. `scope` returns a value with
  `var`, so `drop_value` does nothing. The interpreter moves `v` into the value of the
  scope and drops it.
- **Gap** (O3-4, I3-1): `s.spawn(…)` in statement position. The value has a task set,
  so `drop_value` does nothing. The result of the task is dropped at the end of the
  scope with no check.

### 2.4 Assignment to a local: `x = v`

**Lowered by:** `assign` (`stmt.rs:1137`) → `assign_name` (`stmt.rs:1236`) → `expr` of
the value → `unify` → `consume` → `emit("x =")` → `mutate(n, var_place(x))` →
`note_capture` → `assign_local`.

**Facts:** at the "x =" node: `mutates_at(n, cell or root of x)` (a write of the
variable, for W0405), `rebound_at(x, n)`, `points_into(x, …)`, `empty_at` if the value
has no linear part. A linear `x` that is live there gets `overwritten` from the spec
rule `overwritten(V, P) :- live_linear(V, P), rebound_at(V, P)`.

**Special cases:**

- `assign_name` takes `x = v` on any local, and `x op= v` on a local that is not a
  reference. `c += v` on a reference local takes the general path (2.6): it writes
  through the reference, as the interpreter does (`CompoundStore` follows references).
- The value runs first, then the target. The interpreter does the same
  (`compile.rs:481`).
- A local of a function type joins the old and the new function value: a later call can
  run either (ADR 0005). This is flow-insensitive on purpose.
- The places of `x` only grow (`Local::refs`). `points_into` is flow-insensitive.
- **Gap** (F3-11, precision): a closure that gives a captured reference a new value does
  not rebind it at the node that runs the closure.

### 2.5 Assignment to a place: `p.f = v`, `v[i] = x`, through a reference

**Lowered by:** `assign` (`stmt.rs:1137`): `expr` of the value → `place_expr` of the
target (`expr.rs:527`) → `check_self_ref` (`stmt.rs:1416`) → `drop_replaced_uses`
(`stmt.rs:1275`) → `assigned_places` (`stmt.rs:1295`) → `unify`, `keep_modes`
(`drops.rs:298`) → `note_stored_fn` / `note_stored_behind` (`oprefs.rs:270`,
`oprefs.rs:261`) → `escape` (`fnval.rs:899`) → `store_into`, `note_fn_store` →
`consume` → `part_holder` (`stmt.rs:1311`) → `drop_linear` or `overwrites` →
`emit("assign")` → `mutate` → `writes_via`.

**Facts:**

- At the "assign" node: `mutates_at(n, p)` for each target place; `rebound_at(h, n)` for
  the part holder and for each unset place field below the target; `overwrites(x, n)` if
  the old value of a part of a live linear local `x` goes away; `writes_via(n, r)` if the
  target is at or below the one place of a one-reference local `r` (QA6).
- The uses of the target base (`use_local`) and the reads of index places wait in the
  pending queue. They go onto the next node: the "move" node of the value if the value
  moves, else the "assign" node.
- A self-reference field of a `!Move` struct: `ref_at` and `ref_in` on an edge-less
  "field" node (W0605, S5b F8).
- A linear old value behind a reference: a "drop" pair (W0601: a borrowed place always
  has a value).

**Invents:** a part holder variable `value in p` (`Temp`) with `points_into` the places
of the new value; the "assign" node; edge-less "field" nodes.

**Special cases:**

- A new value of a part of a local points somewhere new from this node on. A hidden
  holder keeps that, because `points_into` of the local itself is flow-insensitive
  (ADR 0003). A use of the local uses each live holder (`use_local`, `mod.rs:1913`).
  A new value of a part, or of the whole local, retires the holders below it
  (`retire_holders`, `mod.rs:2836`). A join of branches can keep a holder that one
  branch retired; a "stale part" node rebinds it on that edge (`retire_stale`,
  `mod.rs:2805`). S069 (quadratic facts and false W0301) made this.
- The target does not read the references that the new value replaces
  (`drop_replaced_uses`).
- A reference that goes behind a reference parameter or into an `rc` object is kept by
  the caller: W0204 at the end of the body (`check_stored_behind`, FD3).
- A function value in a field or an element is stored where the body does not follow
  it (`escape`): it gets a `{stored closure}` variable and runs at each node that can
  reach it (2.23).
- `c op= v` on a place that holds a reference writes where the reference points
  (`assigned_places` with `field_referents` or the places of the local).
- **Gap** (R3RT10, precision): a new value of a part that holds a stale reference is
  W0301, because the first value of the tuple is on the local itself, and the target
  uses the whole local.

### 2.6 Compound assignment: `x += v`

**Lowered by:** `assign_name` for a local that is not a reference (`use_local`, `arith`,
`int_ops`); else `assign` with `AssignOp::Add` (`read` of each place, `arith`,
`int_ops`).

**Facts:** `uses(x, n)` (the old value is read: W0304), `reads_at(n, p)`, then the facts
of 2.4 or 2.5. A compound assignment on a reference local or on a place that holds a
reference mutates the places that the reference points into, with `writes_via`.

**Special case:** the interpreter checks the integer width at the span of the value
(`FnFacts::int_ops`, RR14). This is not a spec fact.

### 2.7 Names, field places, index places, slices

**Lowered by:** `name` (`expr.rs:375`), `place_expr` (`expr.rs:527`), `field_of`
(`expr.rs:628`), `deref_lval` (`expr.rs:711`), `place_value` (`expr.rs:731`),
`field_referents` (`expr.rs:757`), `place_or_temp` (`stmt.rs:1598`), `held_refs`
(`flow.rs:60`), `field_step` (`program.rs:2118`), `elem_step` (`program.rs:2183`).

**Facts:**

- `uses(x, n)` for the local, and for each live part holder of it (`use_local`).
- `reads_at(n, cell or root of x)` for a use of a local as a value (`read_var`, W0405,
  OR8). For a reference local used as a value: `reads_at(n, p)` for each place that it
  points into.
- An index: `reads_at(n, base place)` for each indexed place (the length and the buffer,
  W0405, OR5). The index expression runs after the base.
- `uses(h, n)` for each unset place field at or below a read place (`touch_unset`,
  W0304).
- The move of the value is not here. A consumer moves it later (`consume`).

**Special cases:**

- A place through a reference local is a place of what it points into
  (`LVal::through_ref`). A move out of it is W0303 (`consume`, `stmt.rs:1652`).
- A part of a tuple, a field or an element of type `&T` holds a reference. A place below
  it is a place where that reference points, not a place of the value that holds it
  (`deref_lval`, `held_refs`, ADR 0003, round 2 S098).
- An `Rc` handle: a field through it is a place in the `Group` root of the inner type.
  The reference also points into the handle place `h.*` (`handle_deps`, ADR 0003).
- A `Box` adds an unstable deref step (`field_step`, `program.rs:2163`).
- An enum variant name as a field (`o.Some`) is an unstable variant step.
- A reference parameter whose pointee holds references: a reference read out of it
  points into the wildcard place of the root `*p` (`held_root`, `flow.rs:119`, ADR
  0003).
- A self-reference field of a `!Move` struct points into the place that the struct
  declares (`field_referents`).
- **Gap** (O3-6): a task that reads a group place through an `Rc` handle does not read
  the handle variable. A move of the handle while the task runs is not a conflict.

### 2.8 Borrow: `&p`, `&p[]`, `&value`

**Lowered by:** `borrow` (`expr.rs:773`).

**Facts:** no node of its own. The value of the borrow is a `Val` with `refs` = the
places (and the handle places). The facts appear where a consumer binds it: a "let"
node (`points_into`), a held operand (`hold_*`), a call (`call_arg`, `reads_at`).
`uses(h, n)` for unset place fields below the place (`touch_unset`).

**Invents:** for `&value`: a temporary root with an owner variable that ends at the end
of the statement (`temp_root`, `mod.rs:2173`; S007 made this).

**Special cases:**

- `&x[]` is a slice of all elements: the element step of the type.
- `&value` first moves the value into the temporary (`consume`, `drop_value`).
- **Gap** (round 2 R2d, precision): a borrow through a `Box` (`&b.items`) does not read
  `b` (W0405).

### 2.9 Temporaries and statements

**Lowered by:** `temp_root` (`mod.rs:2173`), `open_stmt` (`mod.rs:2193`), `close_stmt`
(`mod.rs:2199`), `place_or_temp` (`stmt.rs:1598`), `Summary::dropped`.

**Facts:** `owner(root, t)` for a temporary that can free memory; `scope_end(t, "end of
statement")`; inside a closure or a clause, `scope_end(t, run node)` (through
`dropped`); `temp_refs` (lowering state) lets a read of the temporary give the places
that its value points into.

**Where a temporary ends, by frame:**

| Code | In sema | In the interpreter |
| --- | --- | --- |
| A statement that is not a tail | its "end of statement" node | `StmtEnd` (`exec.rs:412`) |
| The tail of a block | the enclosing statement | the enclosing statement |
| The condition of `while` | its own statement (`stmt.rs:980`) | its own `StmtBegin` / `StmtEnd` |
| The value of a function body | no `scope_end` (the exit ends all) | the `Return` of the frame |
| A closure body | each run node (`dropped`) | the `Return` of the closure frame |
| A handled body | its own statement record (`expr.rs:1863`), closed after the body | the `Return` of the `HandleBody` frame |
| A clause body | each perform node (`dropped`) | the `Return` of the clause frame |
| A scope body | the enclosing statement | the `Return` of the `ScopeBody` frame (`compile.rs:963`) |

**Special cases and gaps:**

- The handled body got its own statement record in R2c, as the interpreter runs it in a
  frame. **Gap** (O3-2): the value of the body leaves after that free with no holder, so
  a reference into the temporary is valid in the facts after the `handle`.
- **Gap** (O3-2, scope form): the temporaries of a scope body end later in sema than in
  the interpreter.
- **Gap** (O3-3): a clause value or a `resume` argument that points into a temporary of
  the clause leaves the clause after the free.

### 2.10 Blocks and tails

**Lowered by:** `block` / `block_with` (`stmt.rs:647`, `stmt.rs:653`) → `push_frame` →
`block_inner` (`stmt.rs:730`) → `hand_out` (`stmt.rs:706`) → `hold_out` (`stmt.rs:670`)
→ `end_frame` (`stmt.rs:755`) → `pop_frame` → `use_held` (`stmt.rs:696`).

**Facts:**

- `hand_out`: if the tail names a local of this block that is not plain data, a "block
  value" node with `uses` and `moved_at` (S059: a local named as an arm tail was not
  moved).
- `hold_out`: if the value points into a local of this block, a `BlockValue` holder with
  `rebound_at` at a node before the end, and `points_into` the value places.
- `end_frame`: an "end of block" node with `scope_end` for each local of the block.
- `use_held`: a "block value" node with `uses(holder)` after the end. The free at the end
  reaches the holder, so a value that points into a local of the block is W0301
  (round 1 RT1/F1).

**Special cases:**

- A closure body uses `block_with(hold = false)`: a returned reference into a closure
  local is W0204 instead (`closure_ret_refs`).
- `hold_out` and `use_held` are called by `block_with`, `match` arms and `scope`. They
  are not called for a handled body, a clause value or a `resume` argument (O3-2, O3-3).
- The tail of a block is not a statement (2.9).

### 2.11 `if`, `&&`, `||`

**Lowered by:** `if_expr` (`expr.rs:985`); `binary` for `&&` and `||`
(`expr.rs:823`).

**Facts:** a "branch" node after the condition; edges from the ends of both branches to a
"join" node (`add_node`, `expr.rs:1018`); the moves of the branch values (`consume`), or
the drop of the value of a branch with no `else` (`discard_block_value`); "stale part"
nodes on the edges into the join (`retire_stale`).

**Lowering state:** `branch_state` (`mod.rs:2709`) saves the `@ uniq` set, the task
sets and the part holders. Each branch starts from the saved state (`set_branch`). The
join takes the join of the ends (`joined`, `mod.rs:2764`): `@ uniq` with the verified
`modes::join` (`join_uniq`), the union of the task sets, the union of the holders.

**Special cases:**

- The value of a branch moves into the value of the `if` (S059, ADR 0007).
- A branch of type `Never` gives no places to the value.
- A task set of the value is only for a new task handle (RT22).
- Two function values join into a new summary (`join_val`, `fnval.rs:337`).
- `&&` and `||` get their own "branch" and "join" nodes for the short circuit.

### 2.12 `match` and its patterns

**Lowered by:** `match_expr` (`expr.rs:1070`) → `place_expr` of the scrutinee, or
`expr` and `temp_root` → `read` of each place → `emit("match")` → for each arm:
`set_branch`, `push_frame`, `emit("arm")`, `match_pattern` (`expr.rs:1187`), `consume`
of the scrutinee if a binding moves it, `match_drops` (`drops.rs:325`), the arm body,
`hand_out`, `consume` of the arm value, `hold_out`, `end_frame`, `use_held`, edge to
"end match" → `join_branches`, `retire_stale` → `check_exhaustive` (W0120,
`exhaust.rs:25`).

**Facts:** `reads_at` of the scrutinee places at the "match" node; at each "arm" node,
`rebound_at` and `points_into` of each binder; a "move" node for a by-value binding
(once for the arm); "drop" pairs for `_` over linear parts of a value that the arm
takes; the arm locals end at the arm's "end of block".

**Special cases:**

- A binding through a reference (the scrutinee is behind a reference) binds a
  reference to the payload slot: type `&T`, places = the slot places and the handle
  places (`match_deps`).
- A scalar payload binds by value and reads the place.
- A by-value binding of a reference payload is that reference: it takes the places of
  the scrutinee value (`sval`, round 1 RT3).
- A tuple step is stable; a variant step is unstable; a variant with more than one field
  adds a field step.
- An arm that matches a value with no linear part (`None`) consumes a linear local
  scrutinee (ADR 0007 `empty`).
- The interpreter compiles the scrutinee with `place_or_temp` and binds in `Op::Match`
  (`compile.rs:894`).
- **Gap** (R3RT2): a binding through a reference to a payload that is itself a reference
  points into the slot (`o.Some.hp`), not where the stored reference points. W0301 and
  W0312 miss changes there.
- **Gap** (R3RT11, precision): a `match` with no arm on an enum with no variant is
  W0120.

### 2.13 Loops: `while`, `loop`, `for`, `break`, `continue`

**Lowered by:** `stmt` `While` (`stmt.rs:973`), `Loop` (`stmt.rs:991`), `for_loop`
(`stmt.rs:1031`), `elem_iter` (`stmt.rs:1093`), `loop_body` (`stmt.rs:1014`),
`lower_loop` (`loops.rs:188`), `next_carry` (`loops.rs:312`), `retire_loop_stale`
(`loops.rs:625`), `stmt` `Break | Continue` (`stmt.rs:931`), `end_frames_above`
(`stmt.rs:772`), `leave_in_flight` (`mod.rs:1801`).

**Facts:**

- `while`: a "while" header; the condition as its own statement; a "branch" node; an
  "end while" exit with an edge from the branch; the body; a back edge to the header.
- `loop`: a "loop" header and an "end loop" exit. The exit is the current node only if a
  `break` reaches it (else the loop has type `Never`).
- `for`: a hidden `{iterator}` local bound at an "iterator" node, with `points_into` the
  element places; `reads_at` of the element places; a "for" header with
  `uses(iterator)`; an "end for" exit with an edge from the header; a "for binding" node
  in each pass that binds the pattern; the iterator ends at the end of the loop frame.
- `break` / `continue`: a "jump" node with `scope_end` of each local and statement
  temporary deeper than the loop, `scope_end` of the values on their way
  (`leave_in_flight`), and an edge to the exit or the header.

**The lowering fixpoint.** `lower_loop` lowers the body again until the values of the
outer locals are stable. Each pass starts from `LoopHead` (`loops.rs:85`, 61
fields; each new field of `Lower` needs a decision there), rewinds the facts
(`FnFacts::rewind`, the tables of roots, places and variables stay), and restores the
locals (`Locals::restore`). The join of the back edges (the head, the end and each
`continue`) gives the next head (`next_carry`). It widens:

- a place that goes deeper a second time becomes the wildcard place of the outermost
  place that an earlier pass added (`widen_deeper`);
- after 8 passes (`LOOP_WIDEN_AFTER`), a new place below a known place becomes the
  wildcard place of the deepest one (`widen_place`);
- after `outer + 16` passes (`loop_roots_after`), a new place becomes the wildcard place
  of its root, and a function value that still changes becomes an unknown function
  value;
- more than 16 places in one root become the wildcard place of their common prefix
  (`collapse_places`).

A loop that is not stable after `2 * (outer + 16) + 32` passes gets W0707
(`loop_pass_bound`). The part holders of outer locals carry to the next pass. The
stale holders on the edges into the head and the exit get "stale part" nodes
(`retire_loop_stale`).

**Special cases:**

- A loop body is a block that nothing uses: a tail place moves and goes away
  (`discard_block_value`, OR6).
- A `for` element of scalar type binds by value; another element binds by reference.
  An element that holds references also points where they point. The iterator is
  `@ uniq` if its source is (RT18).
- A call result in a loop gets the shared wildcard place, not a one-place instance
  (`one_result`, R2a): the values of two iterations can meet.
- A local keeps the set of tasks that it can hold; the head joins the sets (RR1, S096,
  S100).
- `break` and `continue` cannot leave a handled body, a clause or a scope body (W0315,
  `Jump::Fence`), and cannot cross a closure (the closure saves `loops`).
- The widening came from RR1 (loop-carried references), QA4 and QA7 (exponential growth),
  S101 and S102 (false positives and blow-up), and QA1 (W0707 in place of partial
  facts).

Note: there are two fixpoints. The lowering fixpoint computes the abstract values of the
locals (places, function values, tasks). The spec fixpoint (`invalid`, `moved`,
`live_linear`, `live_in`) runs over the CFG cycle of the last pass.

### 2.14 `return`

**Lowered by:** `stmt` `Return` (`stmt.rs:908`); `finish_return` (`stmt.rs:519`) in a
function; `closure_return` (`expr.rs:1653`) in a closure.

**Facts:** the move of the value (`consume`); a "return" node; `scope_end` of each local
and statement temporary above the function frame (`end_frames_above(1, n)`) or above
the closure frame; `scope_end` of the values on their way (`leave_in_flight`); an edge
to the exit (the closure exit is made at the first `return`, `expr.rs:1678`).

**Special cases:** W0315 for a `return` inside a handled body, a clause or a scope body;
W0204 for a closure that returns a reference into its own local
(`closure_ret_refs`, `expr.rs:1699`).

### 2.15 Operators and literals

**Lowered by:** `binary` (`expr.rs:823`), `expr` `Unary` (`expr.rs:131`), `lit`
(`expr.rs:347`), `arith` (`stmt.rs:1436`).

**Facts:** an operand that holds references is held while the right operand runs
(`hold_later(a, "operand")`): `rebound_at`, `points_into`, `uses` at the next node. A
comparison drops its temporaries (`drop_value`). A string interpolation reads the whole
value of each part (`touch_unset`, W0304).

**Special cases:** the operands are values, not moves (the interpreter keeps a place as a
place, `operand`, `compile.rs:1109`). `-128` is one literal (W0102 range,
`int_lits`). A range is valid only in `for` (W0114).

### 2.16 Aggregates: tuple, array, struct literal, positional struct, enum variant

**Lowered by:** `expr` `Tuple` (`expr.rs:153`), `elements` (`expr.rs:256`),
`struct_lit` (`expr.rs:869`), `positional_struct` (`call.rs:2444`), `variant_ctor`
(`call.rs:2504`), `path_member` and `unit_variant` for a unit variant (`expr.rs:287`,
`expr.rs:469`), `hold_part` (`mod.rs:1822`), `take_held_here` (`mod.rs:1811`).

**Facts:** each part: its own facts, then `consume`; each part but the last is held
while the later parts run: a moving part through `hold_moved` (a holder that is linear if
the part is, `moved_at` at the "value" node), another part with references through
`hold_later`; a "value" node that takes the moved parts. A struct literal that gives a
place field a reference: `ref_at` on an edge-less "field" node with no `ref_in`
(W0605: a literal has no place yet).

**Invents:** the held-part variables; the "value" node; the "field" nodes.

**Special cases:**

- A tuple part that can hold a function value gets a type variable of its own, so two
  closures that meet in the part join (`expr.rs:174`, RR2).
- An array element, a field and a payload store their function values where the body
  does not follow them (`escape`), and keep the modes of a `once` or linear closure
  (`keep_modes`, W0502, W0601, S056).
- A struct literal evaluates its fields in the written order; a positional struct in the
  order of the fields (ADR 0009). The interpreter does the same (`compile.rs:1135`,
  `compile.rs:1165`).
- A unit variant is an `empty` value: the binding gets `empty_at`.
- A missing field that is not a place field is W0115. A place field with no value gets
  an unset variable at the binding (W0304).
- This "consume, hold, take" loop is written out five times (tuple, array, struct
  literal, positional struct, variant), and again in `print`, `binary`, the arguments of
  item calls, value calls and operations (round 1 note: "the hold loop is written out at
  each operand site").

### 2.17 Calls of function items

**Lowered by:** `call` (`call.rs:160`) or `method_call` (`call.rs:236`) → `call_fn`
(`call.rs:442`) → `call_fn_as` (`call.rs:480`), in eight phases:

1. `item_arg_slots` (`call.rs:568`): the order of the arguments, by name (ADR 0009). It
   exports `arg_order` for a method of a value or an item in a local.
2. `eval_item_args` (`call.rs:597`): each argument in parameter order.
3. `item_call_node` (`call.rs:756`): the call node.
4. `check_arg_places` (`call.rs:848`): `in` places and `@ uniq`.
5. `item_call_effects` (`call.rs:914`): the effects.
6. `item_fn_args` (`call.rs:961`): the function arguments.
7. `item_call_keeps` (`call.rs:1082`): what the callee keeps; abort and `multi`.
8. `item_call_result` (`call.rs:1129`): the result.

**Facts, by phase:**

- Phase 2, before the call node:
  - a receiver that a by-reference `self` borrows: its places, or a temporary root for a
    value; `touch_unset`; a held "receiver" variable if later arguments follow;
  - a reference argument: `arg_places` = its places; a held variable if later
    arguments follow (`hold_operand`);
  - a by-value argument: a "move" node (`consume`, the move happens at evaluation); a
    `hold_moved` holder if later arguments follow; a held variable for its references
    if it does not move. A closure at a parameter of function type does not move here:
    the callee borrows it, and `give_fn` moves a `once` closure at the call node;
  - a `!Move` temporary that goes to a type parameter: a "move" node with a moved hidden
    variable (`move_temp`, W0604, FD4);
  - a generic callee in `holds`: a "held by the callee" node before the call
    (`hold_generic`).
- Phase 3, at the call node `n` (label = callee name, detail = `mut(…)` and effects):
  - `uses(h, n)` for each held variable; `uses` and `moved_at` for each moved holder
    (`take_held`);
  - `mutates_at(n, m)` and `call_mut(n, m, root)` for each `mut` place of the signature,
    substituted with the argument places and a fresh split id (`subst_place`,
    `mod.rs:2241`); a by-value parameter that does not hold references is skipped;
  - `reads_at(n, p)` and `call_arg(n, p, root_of(i))` for each reference argument place;
    a parameter with `in` shares the root of its place (`sig_root`, `call.rs:455`);
  - `call_arg(n, p, fn_arg(i) | STORED | root)` for the references inside a by-value
    argument (`roots`, `body/roots.rs`);
  - a "given back by the callee" node right after, with `uses` and `moved_at` of the
    `holds` variables (`release_generic`);
  - a "drop" pair for each type parameter in the callee's `drops` that gets a linear type
    (`callee_drops`, `call.rs:1384`).
- Phase 4: `param_in`, `arg_at` (W0203); `uniq_param`, `arg_aliased` (W0406); for a
  `@ uniq` argument that is a captured local, a `uniq_needs` record for the closures
  around the call (`note_cap_uniq`, `late.rs:108`).
- Phase 5, for each named effect of the callee (`perform_at`, `fnval.rs:811`):
  - a local handler: `performs_at(n, cap)`, a `cap_calls` record, the abort context
    (`note_abort_ctx`), `callee_ops`, and `give_op` of each reference argument with any
    position and any operation;
  - a handler of a caller: `escapes_at(n, e)`; `multi_at` if the effect has a `multi`
    operation; `lends_mut` and `call_mut` of each reference argument if an operation of
    the effect takes a reference;
  - `raises` and `pins` bookkeeping; W0314 checks of the callee's tasks
    (`check_callee_tasks`).
- Phase 6, for each function argument at a parameter of function type:
  - `fn_arg_effect`, `param_effect` (W0705);
  - `apply_value(n, value, row, fn_arg(i), given)`: the closure, item, parameter or
    unknown value runs at the call node, with the places that the callee lends to it
    (`lent_to`: the `lent` part of the callee, or any place inside each reference
    argument for a callee with no inferred body, `fnval.rs:1219`);
  - if the callee runs the argument as a task (`task_runs`): a chain of "task of the
    callee" nodes after the call with `spawned_at`, `task_reads`, `task_writes`,
    `joined_at`, `lends_mut`, `reads_at` (`arg_tasks`, `tasks.rs:362`, OR7);
  - if the callee can run it more than once: a "call again" node with `uses` of the
    closure variable (`run_again`, `repeat.rs:60`), and `repeats` bookkeeping;
  - a `once` closure moves at `n` (and again at "call again", W0502); a linear closure
    gets `scope_end` at `n` unless the callee runs it exactly once (`give_fn`,
    `repeat.rs:251`; only `with_timeout`).
- Phase 7: a function argument that the callee stores is escaped (2.23); an argument that
  holds a function value lets the callee run stored values (`reach`); `may_abort(n)` if
  the callee has a named effect (`abortive`); `multi_at(n)` if the callee's `multi` part
  is set.
- Phase 8, the result (a `Val`, no node):
  - the stated places (`ret_places`, substituted), with the handle places of the
    arguments for a group place (`group_arg_deps`) and of the receiver;
  - an unstated reference: the wildcard place of each reference argument, or a one-place
    instance (`call_flows`, `flow_refs`, `one_result`);
  - a type parameter in the result passes the places of the arguments on;
  - a function value in the result: a summary from the callee's `ret` part
    (`ret_summary`, `fnval.rs:1542`) and the places of its `ret_refs`;
  - a mutated reference argument whose pointee holds references gets the places of the
    other arguments: `points_into` of the owner local (`point_local`), or a store behind
    a parameter (`note_stored_behind`);
  - `fn_store_refs`: a part holder or a store behind a parameter (`fn_stores_of`);
  - `group_stores`: a store into an `rc` object (`group_stores_of`);
  - the root of "a place of a caller" if the callee can get a reference from a handler
    of a caller; the operation result root if it performs through a local handler.

**Special cases** (each one is an ADR sentence): F3 (a perform and a call that reaches a
local handler give `call_arg`), RT5 (a closure argument points into its captures),
F4 (mutations through closure parameters), RT6 and RT7 (function items and returned
closures), RR2 (joins of function values), OR7 and S126 to S133 (callee task runs),
FD3 (stores behind references and into `rc` objects), RR10 and RR13 (named arguments),
S056 (a closure at a type parameter keeps its modes), S072 (a linear value on its way
when a later argument aborts), QA17 (distinct roots for `call_arg` kinds).

**Gaps:**

- R3RT3: a reference argument whose pointee holds references gives `call_arg` and
  `reads_at` only for its own places (`call.rs:814`), not for the places of the held
  references. W0312 and W0405 miss the overlap.
- R3RT6 (precision): a mutated reference argument gets the wildcard place of each other
  reference argument, also when the types forbid it, and from the `let` on (flow
  insensitive).
- F3-2: a closure argument that keeps its reference parameter in an outer local gets a
  place in a local of the callee. The caller cannot name that place, so nothing frees
  it.
- O3-9 (precision): a callee that takes a `Task` by value does not end its task.

### 2.18 Method calls

**Lowered by:** `method_call` (`call.rs:236`), `method_on_path` (`call.rs:353`),
`note_via_call` (`call.rs:325`).

**Special cases:**

- A path receiver: a module function, a type function or constructor, an effect
  operation (`perform_op`), or `sim.run` (`call.rs:370`).
- A value receiver is a place first (`place_expr`): the call decides to borrow it (a
  by-reference `self`) or to move it (a by-value `self`).
- `s.spawn(…)` on a `Scope` and `t.join()`, `t.detach()` on a `Task` are built-ins
  (`call.rs:279`). Their arguments are lowered too, so their moves are in the facts
  (S136).
- `note_via_call`: a method that states no effect, takes no function value, runs no
  stored value and mutates only `self`, called on a part of a one-reference local, can
  get `writes_via` at the end of the body (`finish_via_calls`, `stmt.rs:1382`, QA6).

### 2.19 Generic calls and type parameters

**Lowered by:** `item_call_types` (`call.rs:547`), `callee_drops` (`call.rs:1384`),
`hold_generic` (`call.rs:1439`), `release_generic` (`call.rs:1480`), `consume`
(tentative moves), `settle_moves` (`stmt.rs:256`), `new_var` (`mod.rs:2452`),
`dropped_params` (`drops.rs:95`), `held_params` (`drops.rs:180`), `check_item_value`
(`drops.rs:41`), `flow_refs` (`flow.rs:142`), `mentions_param` (`flow.rs:194`).

**Facts:** the "held by the callee" and "given back by the callee" nodes around a call
(W0602, W0503); "drop" pairs for `drops`; tentative `moved_at` facts that `settle_moves`
removes when the final type is plain data.

**Special cases:**

- The lowering infers types while it emits facts. A value whose type is not known yet
  moves for now (`tentative`), and `settle_moves` removes the move later (S4 "Ty::Var
  move").
- In a generic body, a value of a type parameter counts as linear where a linear value
  can go away (`Lower::generic`, `Has::params`, `maybe_linear`). These hidden variables
  have no `linear` flag in the facts. Sema runs its own small W0601 and W0602 analysis
  on the facts (`dropped_params`, `held_params`) to compute the `drops` and `holds`
  parts (S057, S058, S065).
- A generic function item used as a value gets a check of its own in a separate
  component: "held by the callee", the item node with `may_abort` and `multi_at`, and
  "given back by the callee" (`check_item_value`, S081, S094).
- A by-value argument of a type parameter passes its places on to the result (`id(&x)`
  points into `x`, round 1 RT3).
- `Box.new` and `Rc.new` build a `!Move` argument in place (`builds_in_place`,
  `call.rs:1374`). Another type parameter can move it (W0604).
- The flags of each variable are set again at the end from the inferred type
  (`finish`, `stmt.rs:196`; round 1 quality item on `let v = Vec.new()`).
- **Gap** (F3-3): an `on abort` function with a type parameter in `drops`. **Gap**
  (Q3-1): a place field below a second use of one generic type gets no unset variable.

### 2.20 Calls of function values

**Lowered by:** `call_value` (`call.rs:1802`) → `eval_value_args` (`call.rs:1938`) →
the call node → `apply_value` (`fnval.rs:434`) → `value_fn_args` (`call.rs:2014`) →
`value_call_result` (`call.rs:2145`), `value_call_refs` (`call.rs:2230`),
`result_summary` (`fnval.rs:282`).

**Facts:** at the node (label = the local name): `uses` of the local and of the held
arguments; `reads_at` and `call_arg(n, p, param(i))` of the reference arguments;
`call_arg(n, p, STORED)` for an argument that holds function values; then what the value
does (`apply_value`):

- a closure summary: `apply_summary` (1.3) with root `STORED`;
- a function item: `apply_item` (`fnval.rs:692`): `mutates_at`, `call_mut` of its `mut`
  places in the given places; `perform_at` for its effects; `may_abort`;
- a function parameter: `call_param` (`fnval.rs:752`): `lends_mut` and `call_mut` of each
  given place; the `lent` part; a `caller_runs` record (`finish_op_env` lends the root
  "a place of a caller" there, but only if the body made that root: see N2, 4.2);
- an unknown value: `call_unknown` (`fnval.rs:778`): `lends_mut` of each given place; a
  `reach` record (stored values can run here);
- for a parameter and an unknown value: `escapes_at` or `performs_at` for its row,
  `may_abort`, and `multi_at` if a `multi` operation can reach it.

A `once` closure moves at the node (`moved_at`, W0502). A value that runs a held value
again gets a "call again" node.

**Special cases:**

- A function item in a local is a call of the item with the types of the value
  (`call_fn_as` with `inst`).
- A closure, a parameter and a join have no parameter names: no named arguments (RR13).
- The result: a closure gives its `ret_refs` moved onto the arguments, and the places of
  the new values of its captures (`closure_call_refs`, `late_ret_refs`); an unknown
  value gives the wildcard place (or a one-place instance) of each reference argument
  (round 1 S011).
- The `multi` test for a value with no row looks at the whole program
  (`may_be_multi`, round 1 RT13). **Gap** (O3-10, precision).

### 2.21 Closures

**Lowered by:** `closure` (`expr.rs:1359`) → `bind_closure_params` (`expr.rs:1489`) →
the body → `closure_ret_refs` → `captures_live_at` (`expr.rs:1643`) → `close_scope` →
`closure_value` (`expr.rs:1553`) → `note_cap_values` (`late.rs:52`). Captures:
`note_capture` (`mod.rs:1928`) from `use_local`, and `move_var` (`mod.rs:1980`) for
`moved_captures`.

**Facts in the closure's own component:** a "closure entry" start node; `rebound_at` and
`points_into(param, Arg root)` for each parameter that holds references; the facts of the
body; `scope_end` of the closure locals at its "end of block"; `rebound_at(c, entry)` for
each linear capture (S002); a "closure end" node with `scope_end` of each linear capture
that the closure moves.

**Facts where the closure is made:** `uses(h, n)` of unset place fields that the body
reads (W0304 at creation, ADR 0007); a "move" node with `moved_at` of each capture that
the closure takes by value, and the export `FnFacts::by_value` for the interpreter (OR2);
`uses` of the other captures at the "closure" node; `rebound_at({closure}, n)` and
`points_into({closure}, p)` for the places of each capture, and the root of each capture
that is not plain data or that holds a scope capability (RR4).

**Facts where the closure runs** (`apply_summary`, `fnval.rs:538`): see 1.3. Plus
`late_join` (`late.rs:206`): a captured variable with a new place since the closure was
made gives `uses` of the variable and its part holders, and the closure's mutations,
reads, lends and operation arguments below the old places moved onto the new places
(RR7); a captured function variable with another value runs that value; a captured local
that the closure gives to a `@ uniq` parameter gives `uniq_param` (index
`CLOSURE_ARG + k`) and `arg_aliased` if it is not `@ uniq` here.

**Run nodes:** `call_value`, `item_fn_args`, `value_fn_args`, `op_fn_values`,
`start_task`, `sim_run`, `apply_stored`, `late_join` (a captured function variable), and
`run_handler` for clauses.

**Special cases:**

- A capture that the closure moves is taken when the closure is made (by-value capture,
  as Rust infers it). The interpreter moves the value into a cell of the closure
  (`MakeClosure { owned }`, `compile.rs:870`).
- A closure that moves a value that is not plain data runs only once (`once`, W0502).
  A closure that moves a linear value is linear (W0601).
- A closure is not plain data: a branch value, a variable and a type-parameter argument
  move it.
- A closure that returns a function value also does what the result does
  (`union_ret`, `mod.rs:647`).
- A captured copy value stays readable after its scope (the interpreter keeps the cell),
  so a closure that captures only copy values can leave the scope (round 1 S012).
- A parameter of unknown type is treated as a function parameter: the body can run it
  (`expr.rs:1543`).
- An inner closure that moves a capture makes each closure around it move it too.
- **Gap** (R3RT5, precision): a by-value capture still points into the variable. A
  returned maker closure is W0204, a closure that outlives a block or an iteration is
  W0301.
- **Gap** (F3-2): a closure that keeps its own reference parameter in an outer local
  (`last = r`) gives the local the places that each run node gives; a callee can give a
  place in its own local, which has no name here.
- **Gap** (O3-8, precision): a closure with its own `multi` handler inside it keeps the
  capability in `performs` of its summary, so the call of the closure is a `multi` and
  abort node.
- **Gap** (O3-11, precision): a move and then a new value of a captured variable
  invalidates the closure.

### 2.22 Function items as values, and joins of function values

**Lowered by:** `item_value` (`expr.rs:436`), `fn_info` (`fnval.rs:178`), `join_fn`
(`fnval.rs:216`), `add_fn` (`fnval.rs:231`), `value_summary` (`fnval.rs:260`),
`join_val` (`fnval.rs:337`), `unify` with `fn_joins` (`mod.rs:1565`, `mod.rs:1611`),
`assign_local` (function values join), `ret_sig` (`fnval.rs:1347`), `ret_summary`
(`fnval.rs:1542`).

**Facts:** none of their own. An item value of `sim.run` gives `sim_run_at` on an
edge-less node (RT17). A generic item value gives the check of 2.19.

**Special cases:**

- `Ty::Fn` carries the value: `FnTy::summary` and `FnTy::item`. Type unification joins
  two function values that meet in one type variable (the elements of a `Vec`, the parts
  of a tuple, a generic field) into a new summary (`fn_joins`, RR2). So the inference
  table is also a value-flow table.
- A join makes a new `Summary` in `closures`. Joins are not deduplicated by content.
- A function that returns a function value has a `ret` part (`RetFn`). The caller makes a
  summary from it with fresh `Arg` roots for the parameters of the value.

### 2.23 Stored function values

**Lowered by:** `escape` (`fnval.rs:899`), `escape_all` (`fnval.rs:952`), `keep`,
`store_into` (`caps.rs:401`, `caps.rs:411`), `reach` (`fnval.rs:965`), `apply_stored`
(`fnval.rs:1042`), `known_at` (`fnval.rs:1013`).

**Facts:** a `{stored closure}` variable with `rebound_at` at the store and
`points_into` the captures. After the body, for each stored value and each node that can
reach it after the store: the facts of `apply_value` at that node, `uses` of the stored
variable, `call_arg(n, p, root)` of its captures, and, if the node can run it again, a
"call again" node (`insert_after`) with another use.

**Special cases:**

- A node can reach a stored value if it calls an unknown function value, a callee that
  can run a stored value (`reaches` part, or a function with no body), or a function value
  with an argument that holds a function value.
- A node before the store, and not after it, does not run the stored value (`is_after`,
  `fnval.rs:1073`).
- A stored value that a value at the node is known to be gets the root of that value, so
  one closure does not pair with itself in W0312 (`Reach::known`, QA17, S5c review).
- A node in a closure passes the stored values on to each run node of the closure.
- New nodes that perform through a lowered handler run its clauses again
  (`finish_values`).
- **Gap** (O3-5): a task that runs a closure from a struct field does not get the writes
  and reads of the stored value (W0405, W0403).

### 2.24 `handle`, clauses and the handled body

**Lowered by:** `handle` (`expr.rs:1823`): `handled_effect` → a new capability →
`HandlerInfo` → `HandlerFrame` → a new `Summary` → `Jump::Fence("handled body")` → a
statement record for the body → `handled_again` (2.25) or `expr` → `close_stmt` →
`body_frees`, `inner_frees` (`expr.rs:2592`, `expr.rs:2618`) → `check_cap_escape`
(W0313) → `merge_summary` (`expr.rs:2845`) → for each clause `lower_clause`
(`expr.rs:2012`) → the facts of the handler → `run_handler` (`expr.rs:2341`) →
`run_clause_caps` (`expr.rs:2421`) → "end handle" → `end_clause_locals`
(`expr.rs:2250`) → `join_clause_vals` (`expr.rs:2285`). After the body:
`finish_values`, `finish_aborts`, `op_refs`, `finish_resume_runs`, `finish_spared`.

`lower_clause` (`expr.rs:2012`): a new `Summary` and frame → a "handler clause" start
node → `bind_clause_params` (`expr.rs:2147`, an `Arg` root for each parameter that holds
references) → `bind_clause_cont` (`expr.rs:2213`, the local `resume`) →
`Jump::Fence("handler clause")` → the body → `check_cont_escape` (W0313) → `consume` of
the clause value → `end_frame` → `reaches_without` (`expr.rs:2970`: can the clause end
with no `resume`?) → `captures_live_at` → `note_resumed_refs` (`oprefs.rs:351`) →
`clause_refs_onto_args` (`expr.rs:2308`) → `clause_performs` → footprint and lends →
`merge_summary`.

**Facts:**

- `handler(h, e)` (`HandlerInfo`).
- In the handled body (inline in the outer component): the body facts; `performs_at(n,
  cap)` at each node that runs a clause; the body temporaries end at an "end of
  statement" node at the end of the body.
- In each clause component: the clause facts; `rebound_at(resume, entry)`;
  `rebound_at(c, entry)` for each linear capture.
- `footprint(cap, m)` for each place outside the clauses that a clause mutates.
- `clause_multi(cap)` if a clause can resume more than once; `body_multi(cap)` if the
  body can.
- `clause_performs(h, e)` for each effect that a clause performs through a handler
  outside (F6).
- At each `resume` of the handler: `resumes_at(n, cap)`, `mutates_at(n, m)` for the
  footprint and for the body mutations, `lends_mut(n, l)` for the lends, `releases_at`
  (2.26).
- At each node that runs a clause (`run_handler`): `call_mut(n, m, clause(cap))` for the
  footprint and the lends; `lends_mut` of the lends; the clause mutations and reads
  through its parameters, mapped onto the places that the node gives
  (`clause_through_params`, `expr.rs:2433`: `mutates_at`, `call_mut`, `reads_at`,
  `point_local` for clause binds, stores behind parameters, `lends_mut`); `uses` of the
  clause captures; `reads_at` of the clause reads; `moved_at` of the captures that a
  clause moves; `scope_end` of the clause locals (`dropped`); `spawned_at` of the tasks
  that a clause spawns into an outer scope; `performs_at` of the outer local handlers
  that a clause performs through (`run_clause_caps`).
- An "end handle" node; `scope_end` there of each clause local that a result can point
  into (`end_clause_locals`, W0204 if the `handle` returns one).
- After the body (`finish_aborts`): for each node that runs a clause of a handler whose
  clause can end with no `resume`, an "abort" node with an edge from the node,
  `unwound_at` of the values of the body in scope there, `joined_at` of the tasks of the
  scopes that the body opened, a "task end" node, and an edge to "end handle"
  (S5a 6a).
- `spared_at(v, n)` for an operation of a local handler and each value outside the body
  (`finish_spared`, OR4).

**Special cases:**

- The handled body is inline in the outer component; the interpreter runs it in a frame
  of its own (`CodeKind::HandleBody`, `compile.rs:951`). The lowering mimics the frame
  for temporaries only (2.9).
- The clauses are lowered after the body. So the facts of a clause at a perform node are
  added later, by `run_handler`, at nodes that were emitted before the clause existed.
- A clause runs in the environment of the `handle`: its operations go to the handlers
  outside (effects rule 6). A clause parameter of function type is the join of the values
  that the operations give (`clause_fns`, ADR 0006).
- A reference parameter of a clause has an `Arg` root. A mutation through it is a
  mutation of the argument at each node that gives places to the operation (F3). A call
  that reaches the handler gives any place inside each reference argument
  (`pos: None`).
- The value of a clause is the value of the `handle`; a reference in it below a clause
  parameter points into the operation arguments (`clause_refs_onto_args`, S053). The
  value is `empty` only if each clause value and the body value is (S073, 6b).
- An operation in a closure or a clause inside the handled body spares nothing
  (`outside_vars`, `mod.rs:2047`, S116).
- A clause that resumes only in a closure counts as a clause that can end with no
  `resume` (ADR 0005).
- **Gap** (O3-7, precision): the clause footprint at the perform node holds what the
  closure argument of the operation does, so the closure conflicts with itself (W0312).
- **Gap** (O3-12, precision): a clause conflicts with the task that it spawns (W0405).
- **Gap** (R3RT7): an `in` place on a parameter of an operation has no effect.
- **Gap** (ADR 0005, open): a stored function value that runs inside a clause; a
  function value that the body cannot follow and that goes to a caller's operation.

### 2.25 A `multi` handled body (re-runs)

**Lowered by:** `handled_again` (`expr.rs:2518`) with `lower_loop`; `again_node`
(`expr.rs:2561`); `resumes_at_most_once` (`expr.rs:3003`, a syntax count of `resume`).

**Facts:** the body is lowered as a loop. After each pass, a "resume again" node with
`rebound_at` and `empty_at` of each local of the body that points only into places of the
body (the copy), an edge from the end of the body to it, and edges from it to the
successors of each node of the body that runs a clause of this handler.

**Special cases:**

- Only if the effect has a `multi` operation and a clause can name `resume` more than
  once, or in a loop, a closure or a clause of another handler.
- One-place instances are off here (`may_run_again`, S097).
- **Gap** (O3-14): a place as the tail of a `multi` handled body moves once for each
  resume in the interpreter; the facts count one move.
- **Gap** (round 2 R2a, ADR 0005 open): a `multi` operation of a handler of a caller
  re-runs the rest of the function with the locals of the run before. The CFG has no
  edge for that.

### 2.26 Perform (an operation call)

**Lowered by:** `call` (bare name, `ops_named`, W0107 if ambiguous) or `method_on_path`
(effect path) → `perform_op` (`call.rs:2563`) → `op_slots` (`call.rs:2808`) →
`eval_op_args` (`call.rs:2606`) → the node → `perform_effect` (`mod.rs:2137`) →
`note_abort_ctx` and `note_op_fn` (local handler) or `give_held_to_op` (handler of a
caller) → `op_arg_places` (`call.rs:2672`) → `op_fn_values` (`call.rs:2706`) →
`op_suspends` (`call.rs:2763`) → `op_result` (`call.rs:2785`).

**Facts:** at the node (label = operation name, detail = effect):

- `uses` of the held arguments, `uses` and `moved_at` of the moved ones;
- a local handler: `performs_at(n, cap)`; `multi_at(n)` if the effect has a `multi`
  operation; a `cap_calls` record (the clauses run here, 2.24);
- a handler of a caller: `escapes_at(n, e)`; `multi_at(n)` if the effect has a `multi`
  operation;
- `reads_at(n, p)` and `call_arg(n, p, param(i))` for each reference argument; a local
  handler gets `give_op` (the clause parameter points there); a handler of a caller gets
  `lends_mut` and `call_mut`;
- `call_arg(n, p, fn_arg(i))` for the references in a by-value argument;
- each function argument runs at the node with any place inside the reference arguments
  (`apply_value`, `any_arg`); a handler of a caller runs it as a task in the worst way
  (`arg_tasks` with `worst_runs`); a "call again" node (`run_again`); a `once` closure
  moves;
- `may_abort(n)` (`abortive_local` for a local handler, `abortive` else);
  `local_performs` (for `spared_at`).

**The result:** a local handler: a reference result points into a root "operation
result" that `op_refs` replaces with the places that the `resume`s give (S5a 1d). A
handler of a caller: the wildcard place of each parameter base and the root "a place of
a caller" (`env_ref`, S078), which `finish_op_env` lends at each node that runs code of a
caller. **Gap** (N1, section 4.2): the result does not get the places of the reference
arguments of the operation itself.

### 2.27 `resume`

**Lowered by:** `call` → `resume` (`call.rs:2308`).

**Facts:** at a "resume" node in the clause component: `uses(resume, n)`; `moved_at(resume,
n)` for a `once` continuation (W0501); `mutates_at(n, m)` for each place that the
handled body mutates (`ContInfo::muts`); `releases_at(n, m)` for each place that the body
frees (`ContInfo::frees`, RR5); `may_abort(n)` (`abortive_local`). Then `handle` adds
`resumes_at`, the footprint and the lends; `run_handler` adds `lends_mut` of the clause
changes and, through `resume_through_params` (`expr.rs:2634`), `mutates_at` and
`releases_at` for a clause parameter whose argument the body changes (`onto_param`,
`expr.rs:2762`; QA6(a), S095, S099). If a callee performs the operation, each `resume`
releases each reference parameter of the clause. `finish_resume_runs`
(`expr.rs:2688`) copies these facts onto each node that runs a closure that resumes.

**Special cases:**

- The argument of `resume` is the result of the operation in the body: its places go to
  `resume_refs_pending`, and `op_refs` moves the operation result onto them.
- A function value in the argument is stored where the body does not follow it
  (`escape_all`); a closure that resumes cannot go to the body (W0313, RR3, OR9).
- A clause of `Fail.fail` cannot resume (W0504).
- **Gap** (F3-2): the `releases_at` fact is in the clause component. A use after the
  `handle` does not see it.
- **Gap** (R3RT4): `resume(x)` where `x` is a parameter of a closure in the clause: the
  result keeps the root of `x`, which no node changes.

### 2.28 `scope`, `spawn`, `join`, `detach`, `fork`

**Lowered by:** `scope` (`expr.rs:2896`); `spawn` (`call.rs:3092`) → `closure_arg`
(`call.rs:2829`) → `task_ret` (`call.rs:3231`) → `start_task` (`call.rs:2846`) →
`task_captures` (`tasks.rs:69`); `join` (`call.rs:3168`); `fork` (`call.rs:3270`);
`end_tasks` (`late.rs:585`). After the body: `finish_task_values` (`late.rs:664`),
`finish_task_ends` (`late.rs:605`), `finish_task_marks` (`tasks.rs:471`).

**Facts:**

- `scope`: a "scope" node that binds the binder (a `Scope`, nonportable), with
  `escapes_at` or `performs_at` of `Async` and `may_abort`; the body in an inner frame; a
  "scope end" node with `joined_at` of each task of the scope; a "task end" node; the
  locals of the body end after the join; the binder ends at the outer "end of block".
- `spawn`: a "spawn" node with `uses` of the closure variable, `spawned_at(t, n)`,
  `moved_at` of a `once` closure, the summary of the closure applied at the node with
  root `TASK` (a spawn is a mutation at the spawn node), `task_writes` and `task_reads`
  (the summary's mutations, lends and reads, minus its own roots and the roots of the
  captures that it moves), `captures`, `mut_through`, `kept`, `Async`, `may_abort`; the
  value is a task handle with the task set `{t}`.
- `join`: a "join" node with `uses` and `moved_at` of the handle variable, `joined_at(t,
  n)` for each task that no other local can hold (a must fact, RR1, S100), `Async`,
  `may_abort`, a "task end" node.
- `detach`: a "detach" node with `moved_at`, and a "drop" pair for a linear result
  (ADR 0007).
- `fork`: one "fork branch" node for each branch (each one a task of kind `Fork`), a
  "fork join" node with `joined_at`, `Par`, `may_abort`, a "task end" node. The value is a
  tuple of the branch values.
- `finish_task_ends`: `lends_mut(e, m)` at each "task end" node for each place that the
  task writes, except the writes of an inner task that is still active there (S130).
- `finish_task_marks`: `opaque`, `spawns_in`; the `pins` and `task_runs` parts, with the
  verified `modes::submode`.

**Special cases:**

- The tasks of a scope join before the locals of the scope body end (ADR 0006).
- A spawn inside a closure or a clause into a scope outside it starts the task at each
  run node (`Summary::spawns`, RT12).
- A closure that a callee can run more than once starts its tasks again at a "spawn
  again" node (`restart_after`, `repeat.rs:207`).
- A task keeps a copy variable that it captures and does not borrow (`kept`, S125,
  S131).
- A capture of the scope binder points into the root of the binder (RR4, S134).
- Each task gets, at its spawn node, the values that its captured variables get later in
  the body (`finish_task_values`).
- **Gaps:** O3-4, I3-1, F3-6 (a linear task result is dropped: a spawn statement, an
  abort before the join, a `fork` that a failure ends; `Task<T>` has `on abort` for each
  `T`); F3-7 (the value of a scope body across the end of the scope); F3-8 (a cancelled
  task that never ran drops its linear by-value capture); O3-1 (a scope statement with a
  tail place); O3-9 (precision: a join through a callee, a tuple, an `Option`, `id` or a
  closure does not end the task).

### 2.29 `sim.run`

**Lowered by:** `method_on_path` (`call.rs:370`) → `sim_run` (`call.rs:3314`);
`note_sim_run` (`call.rs:3308`).

**Facts:** `sim_run_at(n)` on an edge-less node (W0802); `handler(h, e)` with
`sim_root(h)` for each standard effect; a "sim.run" node with the summary of the body
(`apply_summary` with root `STORED`).

**Special cases:** the root handlers are in `root_caps`. They do not count for abort
contexts, `spared_at`, W0314 (`cap_on_this_stack`) or `task_effects`. `seed` and
`workers` bind by name or by position. `sim.run` as a value also gives `sim_run_at`
(RT17).

### 2.30 `with_timeout`

`with_timeout<T>(d: Duration, f: fn() -> T) -> T / async, fail` is an `extern` prelude
function (`std/prelude.wf:123`). A call takes the normal item path (2.17). Two special
cases: it runs its function argument exactly once (`item_runs_once`, `repeat.rs:275`), so
a linear closure is not dropped at the call; and it does not run the argument more than
once (`item_repeats`, `repeat.rs:448`). Its effects `async` and `fail` make the call node
`may_abort`. **Gap** (F3-6, I3-4): a `fork` or a finished task in the block when the
deadline fires.

### 2.31 `on abort`

`on abort` is not a construct of a body. The facts see it only as the flag
`has_on_abort(v)` (from `Prop::NoOnAbort`, `props.rs`). W0118 checks the `on abort`
function at the program level (`check_on_abort_rows`, `program.rs`). The spec rule
`abort_unhandled` uses the flag at each `may_abort` node; `unwound_at` stops
`live_linear` on an abort path.

**Gaps:** F3-1 (a change through a reference in the value), F3-3 (a generic `on abort`
drops a part), F3-4 (the type arguments of the parameter), I3-1 (`Task<T>` claims
`on abort` for a linear `T`).

### 2.32 `Rc`, `Box`, `Weak`

- `Rc<T>`: `deref: group, nonportable` (prelude). A field through a handle is a place in
  the `Group` root of the inner type (`field_of`, `expr.rs:641`). Each reference through
  a handle also points into the handle place `h.*` (`handle_deps`). A call result in a
  group root depends on the handle places of the arguments and on the handles inside the
  values that the reference arguments point to (`group_arg_deps`,
  `inner_handle_deps`, `mod.rs:2309`, depth limit 4). A mutation of a group place needs a
  declaration (`param_rooted`). A store of a reference that depends on a local handle is
  W0204 (`check_stored_behind`, `handle_of`). An `Rc` to an object that can hold a
  function value or a reference is not `many` (`Prop::Resource`, `mod.rs:3027`, FD4).
- `Box<T>`: an unstable deref step (`field_step`). `Box.new` builds in place. A `Box`
  does not pass `!Move` on.
- `Weak<T>`: nonportable, no elements.
- **Gap** (O3-6): see 2.7. **Gap** (FD3 precision, by design): a reference into an `rc`
  object through a handle of the same `rc` type is allowed, also when the handle refers
  to another object.

### 2.33 `print` and `assert`

`print` (`call.rs:2416`): no names; each argument: its facts, `touch_unset` (the whole
value is read, W0304), `reads_at` of its places, a held copy while the later arguments
run; a "print" node; the temporaries are dropped (`print` only reads). `assert`
(`stmt.rs:1003`): the expression, a `bool`, an "assert" node.

### 2.34 Effects at calls and at handlers of a caller

- `perform_effect` (`mod.rs:2137`): the innermost local handler of the effect takes it
  (`performs_at`), else it escapes (`escapes_at`).
- `perform_at` (`fnval.rs:811`): the same for a callee, a value with a row, or a summary
  row, with the reference arguments as given places.
- `effect_lends` (`fnval.rs:861`): a caller's operation that takes a reference lends the
  reference arguments.
- `raise_here` (`mod.rs:2010`): a node that can raise a runtime failure (a `join`, a scope
  end, a `fork`) sets the `raises` part unless a local `Fail` handler takes it.
- `callee_ops`: the local handlers whose operations a callee performs. Their `resume`s
  release each clause reference parameter (2.27).
- `may_run_again` (`flow.rs:41`): the body can re-run after a `multi` operation of a
  caller. It turns off one-place instances only.

---

## 3. Cross-cutting mechanisms

Each mechanism below is a rule that each construct must remember to call. The count is
the number of call sites in `body/` at `b073ea7` (`grep -o -F`). A construct that does
not call a mechanism gets no error from the compiler: the facts are short, and only a
probe or a review finds it.

| Mechanism | Helper | Call sites | Constructs that must call it | Failures when a construct forgot it |
| --- | --- | --- | --- | --- |
| Move a value that is not plain data | `consume` | 24 | `let`, assignment values, `return`, branch values, arm values, clause values, closure tails, handle values, block tails (`hand_out`), item arguments, value-call arguments, operation arguments, `resume` arguments, literal parts, `match` by-value bindings, discarded tails | S059 (arm tails), O3-1 (scope statement tail), O3-14 (tail of a `multi` body) |
| Drop a value that nothing keeps | `drop_value`, `discard_block_value`, `drop_linear` | 10 + 2 + 11 | statement values, comparisons, `print`, borrowed temporaries, temporary receivers, `_` patterns, `keep_modes`, `detach`, callee `drops`, `match` arms | O3-4 and I3-1 (spawn statement), RT14 (several `_` forms, round 1) |
| Hold an operand while later operands run | `hold`, `hold_later`, `hold_operand`, `hold_moved`, `hold_part`, `hold_as` | 2 + 4 + 6 + 4 + 5 + 3 | item calls, value calls, operations, tuples, arrays, struct literals, positional structs, variants, binary operators, `print` | S072 (a linear value on its way when a later argument aborts); round 1 note: the loop is written out at each operand site |
| End a temporary | `temp_root`, `open_stmt`, `close_stmt`, `Summary::dropped` | 4 + 2 + 2 | each statement, the condition of `while`, the handled body, closures and clauses through `dropped` | S007 (no owner for temporaries), O3-2, O3-3 |
| Hold a value across the end of a frame | `hold_out`, `use_held` | 3 + 3 | blocks, `match` arms, `scope` | O3-2, O3-3, F3-7 (handled body, clause value, `resume` argument, scope value) |
| Bind a new value | `bind`, `assign_local` | 12 + 8 | `let`, `x =`, parameters, patterns, closure and clause parameters, holders | — |
| Keep the places of a part | `part_holder`, `hold_in_part`, `retire_holders`, `retire_stale` | 1 + 1 + 1 + 3 | assignment to a part, callee `fn_store_refs`, joins of `if`, `match`, loops | S069, R3RT10 |
| Run code of another body at a node | `apply_value`, `apply_summary`, `apply_item`, `run_handler`, `late_join` | 6 + 4 + 2 + 2 + 3 | value calls, item calls with callbacks, value calls with callbacks, operations, spawns, `sim.run`, stored values, clauses | each new `Summary` field needs a mapping at each site: O3-8 (`own_caps` in `performs`), F3-2 (a callee-local place), R3RT4 (a closure parameter in `resume`) |
| Record an abort context | `note_abort_ctx` | 4 | operations, callees that perform, summaries, stored-value reach nodes | S089 (a node that only the stored-value pass finds) |
| Give places to an operation | `give_op` | 6 | operations, callees, summaries, late joins | S093 (`lent` and `op_args` not rebased by `op_refs`) |
| Suspension points | `abortive`, `abortive_local`, `multi_node`, `multi_local` | 9 + 3 + 5 + 3 | operations, callees, function values, summaries, `scope`, `spawn`, `join`, `fork`, `resume` | F3-7 (the end of a scope), F3-8 (a task cancelled before it starts), O3-10 (a spawn of a parameter) |
| Store a function value | `escape`, `escape_all`, `keep`, `store_into`, `note_fn_store` | 7 + 5 + … | fields, elements, payloads, callees that store, `resume` values, operation arguments, by-value arguments | O3-5 (a task runs a stored value), round 2 OR1, OR3 |
| A use at a later node | `run_again`, `insert_after` | 5 + 2 | callbacks that run twice, stored values that run twice, spawns that start again | — |
| Read for W0405 | `read`, `read_var`, `touch_unset` | 8 + 5 + 6 | names, places, indexes, borrows, `print`, interpolation, closures, receivers | O3-6 (a read through an `Rc` handle does not read the handle) |
| `@ uniq`, `once`, nonportable marks | `mark_modes`, `keep_modes`, `closure_not_many` | 6 (`keep_modes`) | every place where a closure goes into a place | S061, S071 |

### 3.1 State that one walk carries

`Lower` has 105 fields. `LoopHead` (`loops.rs:85`) has 61 fields, because a
loop pass must restore each one. The comment at `loops.rs:75` says: "a new field needs a
decision there". The state falls into these groups:

- the value of each local: `Local` (places, cell, tasks, summary, function parameter,
  continuation, capability marks, `@ uniq`);
- the CFG cursor and the pending queue (`cur`, `pend_uses`, `pend_reads`);
- the stacks of the syntax: frames, summaries, handlers, loops, jumps, scopes, statement
  temporaries, values on their way (`in_flight`);
- the tables of function values: `closures` (all summaries, also joins), `rets`,
  `escaped`, `reaches`, `applied`, `cap_values`, `held_fns`;
- the tables of handlers: `handled`, `cap_calls`, `op_args`, `resumes`, `op_results`,
  `resumed_refs`, `resume_refs_pending`, `abort_ctx`, `local_performs`, `out_suspends`,
  `clause_fns`, `clause_conts`, `cont_caps`, `resumed`, `op_fn_args`, `callee_ops`;
- the tables of tasks: `task_runs`, `task_scope`, `task_ends`, `param_nodes`,
  `pin_calls`, `task_run_places`;
- the tables of stores and signature parts: `stored_behind`, `late_stores`,
  `fn_store_places`, `group_stores`, `via_calls`, `returned`, `kept`, `bind_caps`;
- the type state: `inf`, `late_vars`, `tentative`, `maybe_linear`, `int_lits`.

Many of these tables exist only to let a post-pass (1.4) add facts at nodes that the walk
already emitted. Each one is a place where two features meet.

### 3.2 Interactions that broke

These pairs of features made the blockers of the three rounds. Each row names one shape.

| Features | Shape | Items |
| --- | --- | --- |
| frame × value | the value of a handled body, a clause, a `resume` or a scope body leaves its frame after its temporaries end | O3-2, O3-3, F3-7 |
| frame × tail place | a tail place of a scope statement or of a `multi` body | O3-1, O3-14 |
| closure × loop | a closure made in a loop; its captured variable gets new values in later iterations | RR7, S109, S110 |
| closure × handler | an operation in a closure inside the handled body; a `resume` in a closure; a closure with its own handler | S116, R3RT4, O3-8 |
| closure × callee local | a closure that keeps its reference parameter; the callee gives a place in its own local | F3-2 |
| clause × callee local | a clause that keeps its reference parameter; a callee performs with its own local | F3-2 |
| handler × abort edges × nested handlers | a local outside an inner `handle`; an abort to an outer `handle` | S088, S089, S090 |
| handler × `multi` × one-place instances | code after a `multi` operation runs again | S097 |
| handler of a caller × reference arguments | the result of an operation points into an argument of the operation | new, section 4.2 (N1) |
| function parameter × caller locals | the result of a call of a function parameter points into a local of the caller | new, section 4.2 (N2) |
| part move × linear | a move of one part of a linear aggregate | R3RT1 |
| part move × reference to the whole | a reference to `p` after `take(p.a)` | F3-5 |
| `match` × reference payload | a binding through a reference to a payload that is a reference | R3RT2 |
| call × references behind a reference argument | `&Vec<&T>` at a call | R3RT3 |
| task × stored value | a task that runs a closure from a struct field | O3-5 |
| task × `Rc` handle | a task reads through a handle; the parent moves the handle | O3-6 |
| task × linear result | a spawn statement; an abort before the join; a `fork` that fails | O3-4, I3-1, F3-6 |
| task × cancellation × by-value capture | a task that never started drops its linear capture | F3-8 |
| generic × `on abort` | a generic `on abort` function drops a part; type arguments | F3-3, F3-4 |
| loop × task handles | a `join` of a handle that can hold several tasks | S096, S100 |
| loop × places | walks that go deeper in each pass, branching walks | RR1, QA4, QA7, S101, S102 |

The pattern: a feature adds a mechanism at the sites that its author knew. A shape that
combines two features reaches a site that the mechanism of the other feature does not
cover.

---

## 4. Where the facts and the interpreter disagree today

### 4.1 Round 3 blockers, by the mechanism that misses them

All round-3 lenses confirm that `weft agree` holds on each repro: the checker equals the
spec on the facts. So each blocker is in fact generation (sema), in a spec rule, or in
the interpreter. Another workflow fixes some of them now in `/home/user/wt-core` (task
list R3a-4 to R3a-8: O3-1, O3-14, O3-2, O3-3, F3-7, F3-5, R3RT1, Q3-1, Q3-4). This
document maps `b073ea7`, before those fixes.

| Item | What the run does | What the facts miss | Mechanism (section) | Invariant (section 5) |
| --- | --- | --- | --- | --- |
| O3-1 | a scope statement moves its tail place | the move | `drop_value` returns early (2.3) | D1 |
| O3-14 | each `multi` resume moves the tail place again | the move in each pass | `handled_again` (2.25) | D1, A1 |
| O3-2 | the handled body and the scope body free their temporaries at their end | a holder of the value across the free | 2.9, 2.10 | C2 |
| O3-3 | a clause frees its temporaries before the `handle` gives its value | the same | 2.9, 2.24 | C2 |
| F3-7 | the end of a scope can abort while it holds the body value | a holder and `may_abort` | 2.28 | D4, D5 |
| O3-4, I3-1, F3-6 | the scope or the unwinder drops a finished task's linear result | a linear holder of the result | 2.3, 2.28 | D5, D6 |
| F3-8 | the scope cancels a task that never ran; its by-value linear capture goes away | `may_abort` at the spawn for the captures | 2.28 | D4 |
| O3-5 | a task runs a stored closure | the task footprint of the stored value | 2.23 | F3 |
| O3-6 | the parent moves an `Rc` handle while a task reads through it | a read of the handle variable | 2.7 | F3, F4 |
| F3-1, F3-3, F3-4 | `on abort` changes a place through a reference, drops a part, gets another type | (signature checks, W0118) | 2.31 | D6 |
| F3-2 | a closure or a clause keeps a reference into a local of the callee | a root and a free for the callee local | 2.21, 2.27 | C4 |
| F3-5 | a move of a part; a read through a reference to the whole | the spec rule (`prefix(M, Path)` only) | 2.2 | C7 |
| R3RT1 | the other linear parts after a part move | `live_linear` stops at `moved_at` | 2.2 | D1 |
| R3RT2 | a `match` binding through a reference to a reference payload | the held places | 2.12 | C1, C8 |
| R3RT3 | a callee frees what a held reference of an argument points into | `call_arg`, `reads_at` of the held places | 2.17 | C8, G2 |
| R3RT4 | `resume(x)` with a closure parameter `x` | a mapping of the closure parameter onto the given places | 2.27 | C1 |
| Q3-1 | a read of a place field with no value | an unset variable for a second use of a generic type | 2.19 | D7 |

### 4.2 New findings while mapping

I wrote two probes from the invariants of section 5. Both are accepted by the checker at
`b073ea7` and fault with `weft run --oracle` (debug binary `target/debug/weft`, built
from `b073ea7`). The files are in `ir/work/map/`.

**N1 (blocker, realistic). The result of an operation of a handler of a caller does not
point into the reference arguments of the operation.** File `ir/work/map/opres.wf`:

```weft
effect Pick { fn pick(v: &Vec<u64>) -> &u64 }

fn body() / Pick {
    let v = Vec.new()
    v.push(1)
    let r = pick(&v)
    v.clear()
    print(r)          // accepted; oracle: a read of a freed cell
}

fn main() {
    handle Pick { fn pick(v) { resume(&v[0]) } } in body()
}
```

- `op_result` (`call.rs:2785`) calls `op_result_refs(cap, Some(op))` (`oprefs.rs:24`).
  For a handler of a caller, `cap` is `None`, and the function gives the wildcard
  place of each parameter base of `body` and the root "a place of a caller". It does
  not give the places of the reference arguments of the operation. `body` has no
  parameters, so `r` points only into `a place of a caller..` (`weft facts`:
  `points_into(v3, p2)`, `wildcard(p2)`).
- `v.clear()` mutates the root of `v`. That root is not a prefix of `r`'s place. No rule
  fires.
- A local handler is correct: `op_refs` moves the result onto the places that the
  `resume`s give, and `clause_refs_onto_args` maps a place below a clause parameter onto
  the operation arguments. A callee that performs is correct too: `call_flows` gives an
  unstated result the places of the arguments.
- Fix: give an operation result of a handler of a caller also the places that
  `flow_refs` gives for the reference arguments of the operation (as `call_flows` does
  for a callee with no stated place). Invariant C1.

**N2 (blocker, plausible). The result of a call of a function parameter with no
reference argument has no places.** File `ir/work/map/fnres2.wf`:

```weft
fn body(f: fn(bool) -> &u64) {
    let r = f(false)
    let s = f(true)    // the closure pushes into the caller's `v`
    print(r)           // accepted; oracle: a read of a freed cell
    print(s)
}

fn main() {
    let v = Vec.new()
    v.push(1)
    body(|b| { if b { v.push(2) }; &v[0] })
}
```

- `value_call_refs` (`call.rs:2230`) gives the result of an unknown function value the
  wildcard place of each reference argument (`call.rs:2276`). With no reference argument
  the result has no places: `weft facts` shows no `points_into` for `r` and `s`.
- A function parameter is code of a caller. Its result can point into a place of the
  caller, as the result of a caller's operation can (S078 fixed that case with
  `env_ref`). `call_param` adds the node to `caller_runs`, but `finish_op_env` lends the
  root only if `env_root` exists, and nothing makes it here.
- In `main`, the one call node `body(...)` runs the whole closure summary at once, and
  W0312 has only one argument, so the caller does not see the order inside `body`.
  With two closures (a getter and a mutator) W0312 in `main` rejects the program
  (`ir/work/map/fnres.wf`), so the gap needs one closure that does both.
- Fix: give the result of a call of a function parameter, or of a value that the body
  does not know, the place `env_ref()` too (then `finish_op_env` lends it at each
  `caller_runs` node). Invariant C1, C5.

### 4.3 Model differences that are not bugs today

- The handled body and the scope body are inline in the outer CFG component, but the
  interpreter runs each one in a frame of its own (`CodeKind::HandleBody`,
  `CodeKind::ScopeBody`). The lowering copies only some effects of the frame boundary:
  the temporaries of the handled body (2.9). Each other effect of a frame boundary needs
  its own special case.
- A closure body and a clause body are separate CFG components, and the interpreter runs
  them in frames too. Their effects reach the caller only through summaries (1.3).
- Named arguments run in parameter order in both (`order_args`, `arg_order`).
- A struct literal runs its fields in written order in both.
- A by-value capture moves at the closure in both (`by_value` export).
- `print` of a moved value prints `<moved>` in the stock interpreter (O3-13); the R3a
  oracle fix makes it a fault.

---

## 5. Invariants that the facts must satisfy

The rules of `spec/weft.dl` are sound only if the facts are true and complete for the
program. The proofs take the facts as hypotheses: `proofs/link/README.md` calls them
`facts_ok`, `bound_before_use` and `no_gen_kill`, and says that "only tests check the
facts". Agreement (`weft agree`) does not check them either: the checker and the spec
read the same facts. This section states the hypotheses as invariants of the facts,
against the run-time semantics of the interpreter.

"Sound" means: if the checker accepts a body, no run of it gets an oracle fault of the
class that the rule covers (a dangling read, a use after a move, a linear leak or a
double finish, a data race, a stealable task that reaches a nonportable value).

### 5.0 The abstraction

To state the invariants, fix a map `α` from run-time objects to fact objects:

- a run of a frame (the function, a closure, a clause, a task) → a path of nodes in one
  CFG component; a closure or a clause also maps to its run node in the code that runs
  it;
- a step of the interpreter that moves, frees, changes, reads or uses → a node;
- a memory location (a cell and a path) → a place: a root and steps. The root of a cell
  of a local or a temporary is its `Local` root. Memory of the caller maps to a `Param`
  root (through a parameter), a `*p` root (behind a reference parameter), a `Group` root
  (an `rc` object), an `Arg` root (given by a run node) or the root "a place of a caller";
- a run-time value that holds pointers → a variable (a local or a hidden holder).

`α` can map one location to several places. Two different roots never alias in the spec
(`alias` follows `parent` down to one root). So two roots name disjoint memory, unless a
run node relates them by substitution.

Each invariant has: the statement; the spec rules that need it; the mechanism of the
current lowering; the known violations at `b073ea7`.

### 5.1 Control flow

**A1. Path cover.** For each run of a frame, the steps map to a path of `cfg_edge` that
starts at the start node of the component. This holds for branches, loops, short
circuits, `break`, `continue`, `return`, each abort exit of a handled body to the end of
its `handle` (a clause with no `resume`, a failure, a timeout, a cancellation), each
re-run of a handled body after a `multi` resume, and each second run of a callback.

- Needed by: every flow rule (`invalid`, `moved`, `unset`, `live_linear`, `live_in`,
  `live_out`, `active`).
- Mechanism: `emit`; the edges of 2.11 to 2.14; `finish_aborts`; `handled_again`;
  `run_again`; `insert_after`.
- Violations: a `multi` operation of a handler of a caller re-runs the rest of the body
  with no edge (ADR 0005, open since R2a); the end of a scope can abort the code that
  holds the scope value (F3-7).

**A2. Components.** Each component has one start node and no edge to another component.
An edge-less node is read by one rule only (`ref_outside`, `sim_in_lib`).

- Needed by: the soundness of summaries (A3); `bound_before_use`.
- Mechanism: `start`, `take_pending`, `restore_pending`; `flush` before control leaves.

**A3. Run-node cover.** Let node `P` run code `C` of another component (a closure, a
clause, a stored value, a task start, or a callee through its signature). Then the facts
at `P` hold each effect of `C` on the memory and the variables of the component of `P`,
in the places of `P`: changes (`mutates_at`, `lends_mut`, `footprint`), frees
(`scope_end` of the owners of `C`, `moved_at` of the captures that `C` moves,
`releases_at`), reads (`reads_at`), uses of captured variables (`uses`), effects
(`performs_at`, `escapes_at`), suspensions (`may_abort`, `multi_at`), spawns
(`spawned_at`), new places of outer locals (`points_into`), stores behind references,
and the places of its result.

- Needed by: W0301, W0302, W0601, W0602, W0503, W0405, W0702, W0703 at the run node.
- Mechanism: `apply_summary`, `apply_item`, `call_param`, `call_unknown`, `run_handler`,
  `late_join`, `apply_stored`, `finish_resume_runs`, `finish_task_values`, and the 24
  parts of `EffectSig`.
- Violations: F3-2 (a place in a local of a callee has no name at `P`, so its free is not
  at `P`); R3RT4 (a closure parameter in `resume`); N1 and N2 (the places of a result,
  section 4.2); O3-8 (precision: the capability of a handler inside the closure).

**A4. Order inside a node.** The spec puts the change of node `P` at the successors of
`P`, and the uses of `P` before it. So a use that happens at run time after a change of
the same step must be at a later node. A binding (`rebound_at`) must come after the uses
and changes that make its value.

- Needed by: W0301, W0302 (a use after a change or a move at one node is not seen).
- Mechanism: "call again", "spawn again", "given back by the callee", "task end"; the
  separate "let" node.

**A5. `no_gen_kill` (B6).** No node both invalidates and rebinds one reference.

- Needed by: `thm_dataflow_exact` (exactness, not soundness).
- Mechanism: a call result binds at a later node. Lint: `proofs/link/lints/gen_kill.dl`,
  run on the corpus by `crates/weft-check/tests/hypotheses.rs`.

**A6. `bound_before_use` (B6).** On each path from the entry, a reference variable is
bound before a use.

- Needed by: `thm_w0301_no_ub`.
- Mechanism: lexical scope. Lint: `proofs/link/lints/unbound_use.dl`. The lint starts at
  `n0`, so it covers only the function component. A closure or a clause component uses
  captured variables that another component binds.

### 5.2 Places

**B1. Interned tree.** Each place has its parent in the table, before it. `steps` are all
steps from the root, and `display` is the text.

**B2. Typed stability (`typed_by`, `alias_exact`).** The stability of a step is a
function of the steps before it and of its kind: the type decides it. A split side has
the stability of the element step of its type.

- Needed by: `thm_invalidates_exact_typed`, `thm_split_exact_typed`.
- Mechanism: `field_step`, `elem_step`, `subst_place`. Lint: `FID/tools/typed.dl` of
  round 3 (no violation in the corpus).

**B3. Root truth.** A `Param` or a `Group` root names memory of a caller (a change of it
needs a declaration). A `Local` root names memory that this body owns. An `Arg` root
names memory that a run node gives. Two roots name disjoint memory, except where a run
node maps one onto the other (A3).

- Needed by: every rule that compares places (`alias`, `prefix`, `overlaps`, `within`).
- Violations: R3RT3 (in the callee, `*rs` and `w` can name the same memory); F3-2.

**B4. Wildcards.** A path has at most one wildcard step (`FnFacts::wildcard`). A
one-place instance stands for one place of one reference value, in code that runs once
(ADR 0003: one reference type, in the function body, not in a loop, not after a `multi`
operation).

- Needed by: `same_one`, the wildcard rules of `invalidated_at` and `overlaps`.
- Violations: S097 (round 2, fixed); R3RT9 (a hint shows `(w..).hp`, minor).

**B5. Split ids.** Each split has one id for each call and parameter (`seg_split`, QA17).

**B6. Handle places.** A reference through an `Rc` handle also points into the handle
place `h.*`, so a new value, a move or the end of the handle invalidates it.

- Violation: O3-6 (a task read through a handle does not read the handle variable).

### 5.3 References (W0301)

**C1. Points-into cover.** For each reference variable `R` and each node `P` where `R` is
used, each pointer that `R` can hold at `P` is at or below `α` of a place of
`points_into(R, _)`, with the meaning of wildcard places. `points_into` is the union over
all nodes (it is not flow-sensitive).

- Needed by: `invalidated_at` (each rule starts with `points_into(R, Path)`).
- Mechanism: `Val::refs` through each construct; `point_local`; `held_refs`;
  `flow_refs`; `call_flows`; `op_refs`; `late_join`.
- Violations: R3RT2, R3RT4, N1, N2; R3RT3 at the call (see C8).

**C2. Holder cover.** From the step that makes a pointer to its last use, a variable of
the facts holds it at each node, and each node that reads, copies or passes the pointer
uses that variable. A value in transit is held by a hidden variable over the whole
interval: an operand, a part of a literal, a tail value, the value of a frame (a block, a
handled body, a scope body, a clause, a closure), a `resume` argument, an operation
result, a call result, a task result.

- Needed by: W0301 (a free that comes before the transfer must reach a use).
- Mechanism: `hold_*`, `hold_out` and `use_held`, part holders, `{closure}`,
  `{stored closure}`, `{iterator}`.
- Violations: O3-2, O3-3, F3-7.

**C3. Rebind hygiene.** `rebound_at(R, P)` only where `R` gets a value whose pointers come
from holders that `P` (or a later node) uses, or from a borrow at `P` of memory that is
live at `P`. A rebind must not hide an invalidation of the source.

- Needed by: W0301 (`invalid` stops at `rebound_at`).
- Violation: O3-2 (the "let" node rebinds after the free of the source temporary, and no
  holder of the source is used at or after the free).

**C4. Free cover.** Each run-time free has a `frees_at` fact at its node, on each path:
`scope_end` of each owner (a local, a temporary, a by-value parameter, the locals of a
closure or a clause at the run node, a value on its way at a jump); `moved_at` of a moved
owner; `moved_part` of a moved part; `unwound_at` on an abort path; `releases_at` for what
a `resume` can free; `lends_mut` for code that can free (unknown code, the end of a
task). Each owned root has `owner(Rt, V)`, also a temporary that can free memory.

- Needed by: the free rules of `invalidated_at`; `task_conflict`.
- Violations: F3-2 (the local of a callee); O3-6.

**C5. Change cover.** Each run-time change that can move or free memory behind an
unstable step has `mutates_at` (or `performs_at` with `footprint`, or `lends_mut`) at its
node: an assignment, a callee row, a closure, a clause, a `resume`, the end of a task,
code of a caller (the root "a place of a caller").

- Needed by: rule 3 and the wildcard rules of `invalidated_at`; `task_conflict`.
- Violation: N2 (no place of the caller for the result of a call of a function
  parameter, so no change can reach it).

**C6. `writes_via` exactness.** `writes_via(P, R)` only if `R` holds one reference at `P`
and each change of `P` is at or below the place of that reference.

- Needed by: `invalidated_at` (`!writes_via(P, R)` takes `R` out of the mutation rules).
- Mechanism: `writes_through` (`stmt.rs:1349`), `finish_via_calls` (`stmt.rs:1382`).

**C7. Part moves.** After a move of part `M`, each reference to a place above `M` is
invalid: a read through it reads the moved part. Today the spec frees only the places
at or below `M` (`frees_at(P, M) :- moved_part(M, P)` with `prefix(M, Path)`).

- Violation: F3-5 (a spec rule; the facts are as ADR 0003 says).

**C8. References behind references.** A reference whose pointee holds references gives
the places of the held references (`held_refs`) at each step that reads through it: a
call that passes it (`call_arg`, `reads_at`), a `match` binding by reference, a task
that reads it.

- Violations: R3RT3 (calls), R3RT2 (`match`).

### 5.4 Values, moves and linear values

**D1. Move cover.** `moved_at(V, P)` for each move of the whole value of `V`: an argument
at its evaluation, a `let`, a `return`, a tail of a block, a branch, an arm, a clause, a
`handle` or a scope, a by-value capture at the closure, a `once` closure at a call, a
`once` continuation at `resume`, a task handle at `join`. A part move gives
`moved_part(M, P)`, and the rules must treat `V` as holding its other parts. `moved_at`
of an immovable `V` only at a real move (W0604 fires at each one).

- Needed by: W0302, W0501, W0502 (`moved`), W0601, W0602 (`live_linear` stops at
  `moved_at`), W0604.
- Violations: O3-1, O3-14 (missing moves); R3RT1 (a part move gives `moved_at` of the
  whole local, so `live_linear` stops and the other linear parts leak).

**D2. New values.** `rebound_at(V, P)` at each new value of `V`; `empty_at(V, P)` only if
the new value has no linear part; `overwrites(V, P)` at each new value of a part of `V`
that drops an old part.

- Needed by: `live_linear`, `overwritten`, `moved`, `unset`, `invalid`.
- Mechanism: `assign_local`, `assign`. Invented facts: `captures_live_at`, `again_node`.

**D3. Normal ends.** `scope_end(V, P)` at each normal-path end of the life of `V`: the end
of its block, statement or function, each run node of its closure or clause, a jump that
leaves it, the end of `handle` for a clause local that a result can point into.

- Needed by: `unconsumed` (W0601); the free rules.

**D4. Suspension cover.** `may_abort(P)` at each node where the run can abort the code
that holds a live value: an operation, a call that can perform, a call of a function
value, a `resume`, `scope`, the end of a scope with a child that can fail, `spawn`,
`join`, `fork`, and a spawn of a task that can be cancelled before it starts while it
owns a by-value capture. `multi_at(P)` at each node that can resume more than once.

- Needed by: W0602, W0503.
- Violations: F3-7 (the end of a scope); F3-8 (a cancelled task).

**D5. Linear holders.** Each live linear value is held by a variable with the `linear`
flag from its creation to its consumption on each normal path, and that variable has
`scope_end` where the value can go away: a temporary (`drop_linear`), a value on its way
(`hold_moved`), a value that a generic callee holds (`hold_generic`), the result of a
task, the value of a scope body, the captures of a task that can be cancelled.

- Needed by: W0601, W0602.
- Violations: O3-4, I3-1, F3-6 (task results); F3-7 (scope value); F3-8.

**D6. Flags.** `linear`, `has_on_abort`, `once_var`, `immovable`, `nonportable` and
`uniq` of a variable are true for each value that the variable can hold. The lowering
takes them from the type that the whole body infers (`finish`, `stmt.rs:196`) and from
the capability marks (`mark_modes`, `caps.rs:319`). `has_on_abort(V)` must hold only if
the unwinder finishes each linear part of `V`.

- Needed by: W0601, W0602, W0503, W0604, W0401, W0403, W0406, `stealable`.
- Violations: I3-1 (`Task<T>` claims `on abort` for each `T`); F3-1, F3-3, F3-4 (the
  `on abort` function, checked by W0118 outside the facts).

**D7. Unset values.** `unset_at` for each declaration with no value, and for each place
field of a value that is built in place; a use of the hidden field variable at each read
or borrow of the field.

- Needed by: W0304.
- Violation: Q3-1 (a second use of one generic type).

### 5.5 `multi` and suspension

**E1.** `multi_at`, `clause_multi`, `body_multi` and `resumes_at` cover each node that can
resume more than once (effects rule 1).

**E2. Re-runs.** The code after a `multi` node of a local handler has a path back to the
successors of the node (`handled_again`). The locals of the body get their copy there
(`rebound_at`, `empty_at`). For a handler of a caller there is no such path (open).

**E3. `spared_at` precision.** `spared_at(V, P)` only if each handler that `P` suspends to
is a local handler, `V` lives outside its handled body, nothing else at `P` suspends,
and no clause of the handler suspends the outer code.

- Mechanism: `outside_vars` (`mod.rs:2047`), `finish_spared` (`aborts.rs:105`).
- Violation history: S116 (round 2, fixed: a closure or a clause that took the value by
  value).

**E4.** `once_var` for each value that a `multi` copy cannot keep: a `!Move` value, a
resource, a task handle, a scope, an `Rc` to an object with function values or
references, a `once` continuation, a `@ uniq` value, a `once` closure.

### 5.6 Tasks

**F1.** `spawned_at(T, P)` at each node where `T` can start: a spawn, a fork branch, a
run node of a closure that spawns into an outer scope, a "spawn again" node, a task of a
callee (`ARG_TASK`).

**F2.** `joined_at(T, P)` only where `T` is finished on each run (a must fact). `active`
must cover each step of the run while `T` runs.

- Violation history: S100 (round 2, fixed by the task sets).

**F3.** `task_reads` and `task_writes` cover each access of `T`: through its captures,
through the stored function values that it runs, through callees, and through the
handle variables of `Rc` places.

- Violations: O3-5, O3-6.

**F4.** The parent has `reads_at` at each read (also of a variable cell and of an index
buffer) and `mutates_at`, `frees_at` or `lends_mut` at each change.

**F5.** `kept(T, Rt)` only for a copy variable that `T` captures and that no reference of
`T` points into.

- Violation history: S125, S131 (round 2, fixed).

**F6.** `captures`, `mut_through`, `nonportable`, `uniq`, `opaque` and `spawns_in` cover
the facts that `pinned` needs.

### 5.7 Effects and signatures

**G1.** `escapes_at(P, E)` at each node that can perform `E` with no local handler;
`performs_at(P, Cap)` with a local handler; `declared_effect` closed under implication;
`std_effect`, `handler`, `clause_performs`, `sim_root` and `sim_run_at` complete.

**G2.** `call_arg` and `call_mut` give each place that a call passes or changes, with one
root for each kind (`body/roots.rs`). The parts of one argument share a root.

- Violations: R3RT3; O3-7 (precision: the clause footprint and the function argument
  have two roots for one closure).

**G3.** Each change of memory of a caller (a `Param` or a `Group` root) is a `mutates_at`
fact, also inside a closure component (`needs_decl`).

**G4.** `arg_at`, `param_in`, `ref_at`, `ref_in`, `uniq_param`, `arg_aliased`,
`fn_arg_effect` and `param_effect` for each call, also an operation.

- Violation: R3RT7 (an `in` place on an operation parameter, minor).

### 5.8 The hypotheses of the proof link

| Hypothesis (`proofs/link/README.md`) | What it asks of the facts | Invariants | Status at `b073ea7` |
| --- | --- | --- | --- |
| `facts_ok`: `cfg_wf` | a well-formed CFG for `propagate` | A1, A2 | tested |
| `facts_ok`: `instr_groups_ok` | each binding gives the group that the B1 model gives (borrow, child, copy, call result) | C1, C3 | tested; closures are out of the fragment |
| `facts_ok`: `fits`, borrowed locals | labels fit in a step id; each borrowed local exists | B1 | tested |
| `ret_ok` | a returned reference comes from an argument that the call does not kill | none | false for the `in` form (documented) |
| `w0301_ok` | the checker accepts | — | the assumption of the theorem |
| `bound_before_use` | A6 | A6 | lint on the function component only |
| `no_gen_kill` | A5 | A5 | lint |
| `typed_by`, `alias_exact` | B2 | B2 | tested by a round-3 lint |
| one group for each reference | the B1 model has one group; the facts allow a list | C1 | not mirrored (documented) |
| no `MkClosure`, no `Invoke` in the dataflow link | closures, handlers and continuations are outside the link | A3 | not proved; summaries are only tested |
| no stored references (borrowing proof) | a reference never lives in the heap past its owner | C4 | mirrored by W0204; gap F3-2 |
| B4 is reference-based | W0405 is access-based | F3, F4 | documented difference (ADR 0006) |
| effects model: one task, explicit capability passing, atomic `on abort` | the facts of tasks and of `on abort` | D4, D5, D6, G1 | gaps F3-6, F3-8, F3-1, F3-3, F3-4 |

### 5.9 Which invariants a core IR can give by construction

| Invariant | By construction in an IR? | How |
| --- | --- | --- |
| A1, A2, A4, A5, A6 | yes | the IR is a CFG of simple statements; one fact template for each statement kind; a use and a change of one statement are in a fixed order |
| B1, B2, B5, B6 | yes | places are typed projections; a deref of a reference is a projection of its own |
| C2, C3, D1, D3, D5 | yes | explicit temporaries with an explicit end; explicit moves and copies; explicit drops; an explicit result slot for each frame (block, handled body, scope body, clause, closure); task results as values of the IR |
| D2, D7 | yes | explicit assignment of a local or a projection; explicit "declare with no value" |
| C1, C4, C5, C8, A3, F3 | no, but uniform | a points-to analysis and the summaries run over the IR, not over each surface form; one rule for "a run node applies the summary of a body" |
| D4, E1, E2, F1, F2, G1 | mostly | each suspension point is an explicit IR statement (perform, call, resume, spawn, join, scope end, fork); the abort and re-run edges are IR edges |
| C7, D1 (part moves) | no | a spec change (F3-5, R3RT1) |
| D6 (`on abort`, `Task<T>`) | no | a type rule (props, W0118) |

---

## 6. What this map tells the design of a core IR

1. **Frames must be explicit.** The interpreter runs a closure, a clause, a handled body
   and a scope body each in a frame of its own, with its own temporaries and its own
   result. Sema inlines the handled body and the scope body, and copies the frame rules
   one by one (2.9, 2.10). Six of the round-3 blockers (O3-1, O3-2, O3-3, O3-14, F3-7,
   and part of I3-1) are frame-boundary rules that one construct forgot. An IR body for
   each frame, with an explicit result slot and an explicit end of its temporaries, gives
   these rules once.
2. **Moves, copies, drops and temporaries must be explicit, after type inference.** Today
   the lowering decides a move while the type is not known (`tentative`, `settle_moves`),
   and 24 call sites of `consume` and 23 of the drop helpers decide case by case. An IR
   built after inference has `Move`, `Copy`, `Drop` and `StorageEnd` statements.
3. **One evaluation-order rule.** The "hold the operand while the later operands run"
   rule is written at about 24 sites. In an IR each operand is a temporary, so the rule
   is the def-use of temporaries.
4. **Places as projections, with a deref of a stored reference as a step of its own.**
   R3RT2, R3RT3 and R3RT6 come from the ad-hoc `held_refs` rule: "a place below a part
   that holds a reference is a place of the reference". A typed projection `(*t.0).f`
   makes it uniform.
5. **One summary mechanism.** Closures, clauses, stored values, tasks and callees each
   have their own way to put facts at a run node (`apply_summary`, `run_handler`,
   `apply_stored`, `start_task`, `late_join`, `EffectSig` parts). An IR can compute one
   summary for each body (closure, clause, function) and apply it with one substitution
   rule at each IR call statement.
6. **Elaborated effects.** The effects proof already uses an elaborated form:
   `Handle`, `Perform{cap}`, `Resume`, `Call{caps}` with explicit capability passing
   (`proofs/effects/README.md`). An IR with these statements makes the footprint, the
   abort edges and the re-run edges of a `multi` handler explicit CFG facts, not
   post-passes.
7. **Two fixpoints should be one.** The loop fixpoint of the lowering
   (`lower_loop`, 61 fields of saved state, widening, W0707) exists because the lowering
   computes the places of locals while it walks. In an IR, the places are the result of a
   dataflow analysis over a fixed CFG, and the loop needs no re-lowering.
8. **Function values in types.** `Ty::Fn` carries closure summaries, and unification
   joins them (`fn_joins`). An IR should keep value flow (which closures a value can be)
   out of the type table.
9. **Post-passes that add nodes after the walk.** `insert_after`, abort nodes and "task
   end" nodes are added after the closure node ranges are fixed. An IR that has these
   nodes from the start removes the range assumptions (1.4).

---

## Appendix A. Producers of each input relation

Direct push sites in `body/` (`grep self.facts.<relation>.push|extend`), and the helpers
that write the relation for most constructs.

| Relation | Helper | Direct sites |
| --- | --- | --- |
| `cfg_edge` | `emit` (`mod.rs:1667`) | 22: `aborts.rs:54,68,71,72`; `expr.rs:834,1021,1158,1432,1466,1680,2541,2543`; `mod.rs:1670,1692,2828`; `stmt.rs:114,926,972,987,1026,1080`; `tasks.rs:321` |
| `points_into` | `point_local` (`mod.rs:2887`), `hold_as` | 11: `expr.rs:1630`; `fnval.rs:937`; `loops.rs:263,272`; `mod.rs:1781,1857,2859,2896,2911`; `oprefs.rs:475`; `stmt.rs:1331` |
| `mutates_at` | `mutate` (`mod.rs:1867`, 7 callers) | 8: `call.rs:2371`; `expr.rs:1935,2469,2675,2751`; `mod.rs:1868`; `oprefs.rs:479`; `repeat.rs:237` |
| `reads_at` | `read`, `read_var` (pending queue) | 12: `call.rs:816,1858,2682`; `expr.rs:2400,2476`; `fnval.rs:564`; `late.rs:244`; `mod.rs:1677`; `oprefs.rs:484`; `repeat.rs:240`; `tasks.rs:329,412` |
| `uses` | `use_local`, `pend_uses` (13 sites) | 16: `call.rs:806,1486,1851`; `drops.rs:72`; `expr.rs:2397`; `fnval.rs:1087,1134,1139`; `late.rs:228,230`; `mod.rs:1674,1791,1981`; `repeat.rs:67`; `stmt.rs:701,1077` |
| `rebound_at` | `bind` (`mod.rs:1976`, 12 callers) | 3: `expr.rs:1646,2581`; `mod.rs:1977` |
| `moved_at` | `move_var` (`mod.rs:1980`, 11 callers) | 5: `call.rs:1487`; `drops.rs:73,290`; `mod.rs:1792,1982` |
| `moved_part` | `consume` | 1: `stmt.rs:1681` |
| `scope_end` | `end_frame`, `close_stmt`, `drop_linear_as` | 12: `drops.rs:30`; `expr.rs:1469,2267,2408`; `fnval.rs:646`; `mod.rs:1804,2209`; `repeat.rs:265`; `stmt.rs:121,766,785,812` |
| `owner` | `set_root`, `temp_root` | 2: `mod.rs:2182,2520` |
| `overwrites` | `assign` | 1: `stmt.rs:1216` |
| `unset_at` | `unset_fields`, `let` | 2: `mod.rs:2633`; `stmt.rs:880` |
| `empty_at` | `assign_local`, `again_node` | 2: `expr.rs:2582`; `mod.rs:2534` |
| `unwound_at` | `finish_aborts` | 2: `aborts.rs:56,80` |
| `releases_at` | `resume`, `run_handler` | 4: `call.rs:2375`; `expr.rs:2388,2678,2753` |
| `lends_mut` | `lend` (`fnval.rs:531`, 7 callers) | 10: `expr.rs:1938,2355,2368,2500,2752`; `fnval.rs:532`; `late.rs:632`; `oprefs.rs:68,496`; `tasks.rs:409` |
| `call_mut` | `lend` | 8: `call.rs:812`; `expr.rs:2471,2501`; `fnval.rs:533,559,731`; `late.rs:240`; `oprefs.rs:488` |
| `call_arg` | — | 9: `call.rs:818,831,1860,1876,2072,2684,2694`; `fnval.rs:1142`; `oprefs.rs:492` |
| `performs_at` | `perform_effect`, `perform_at` | 3: `expr.rs:2424`; `fnval.rs:597`; `mod.rs:2141` |
| `escapes_at` | `perform_effect` | 2: `fnval.rs:593`; `mod.rs:2147` |
| `footprint`, `clause_multi`, `body_multi`, `resumes_at`, `clause_performs` | `handle`, `lower_clause` | `expr.rs:1911,1916,1919,1933,2119` |
| `may_abort` | `abortive`, `abortive_local` (12 callers) | 2: `drops.rs:66`; `mod.rs:2002` |
| `multi_at` | `multi_node`, `multi_local` (8 callers) | 2: `drops.rs:69`; `mod.rs:2033` |
| `spared_at` | `finish_spared` | 1: `aborts.rs:134` |
| `spawned_at` | `start_task` and others | 7: `call.rs:2857`; `expr.rs:2412`; `fnval.rs:653,668`; `tasks.rs:383,396,442` |
| `joined_at` | `join`, `fork`, `scope`, aborts, arg tasks | 6: `aborts.rs:61`; `call.rs:3200,3290`; `expr.rs:2925`; `tasks.rs:430,458` |
| `task_reads`, `task_writes` | `start_task`, `task_places_from`, `arg_task`, `op_refs` | 4 + 4 |
| `captures`, `mut_through`, `kept` | `task_captures` | `tasks.rs:71,90,94` |
| `opaque`, `spawns_in` | `finish_task_marks` | `tasks.rs:505,533` |
| `writes_via` | `assign`, `finish_via_calls` | `stmt.rs:1228,1408` |
| `arg_at`, `param_in`, `uniq_param`, `arg_aliased` | `check_arg_places`, `closure_uniq_need` | `call.rs:883,885`, `late.rs:131,133` and the `extend` calls in `check_arg_places` |
| `fn_arg_effect`, `param_effect` | `check_fn_arg_effects` | `call.rs:1764` (`extend`) |
| `ref_at`, `ref_in` | `check_returned_refs`, `check_self_ref`, `struct_lit` | `stmt.rs:633,634,1426,1427`; `expr.rs:929` |
| `shared_root`, `declared_mut`, `declared_effect`, `has_signature` | `lower_fn` | `stmt.rs:89,96` |
| `sim_run_at`, `handler` | `note_sim_run`, `handle`, `sim_run` | `call.rs:3310,3369`; `expr.rs:1842` |

The bridge (`crates/weft-check/src/bridge.rs:64`) derives `place`, `parent`, `unstable`,
`wildcard`, `one_place`, `param_rooted`, `step_alias` and `step_within` from the place
table, and the variable relations (`linear`, `has_on_abort`, `once_var`, `immovable`,
`nonportable`, `uniq`) from `VarInfo`.

## Appendix B. Files of this map

- `docs/plan/core-ir-inputs/map_lowering.md`: this document.
- `ir/work/map/ex1.wf`: the small programs for the fact shapes of 1.3 and 2.24.
- `ir/work/map/opres.wf`: N1. `ir/work/map/fnres2.wf`: N2. `ir/work/map/fnres.wf`: the
  control of N2 (W0312 with two closures).
