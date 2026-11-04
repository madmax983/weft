# ADR 0013: What the facts criterion of the core IR counts

Status: accepted (plan stage C1.4, issue #62). Date: 2026-11-04.

## Context

The common exit of the plan (`docs/plan/core-ir.md` §2.7, item 4) says: "the facts of
each function are at most 3 times as many" as the facts of the old pipeline. The plan
did not say which rows count. At stage C1, 10617 of 37667 functions of tier 1 had more
than 3 times the rows that `weft facts` prints.

- Each relation that the fact generators write is an input relation of the spec, and a
  rule of the spec reads each of the 74 input relations. So "all relations" and "the
  input relations that the spec reads" name the same set. The difference is at the level
  of rows. Many rows of the `ir` facts could not join a rule that gives a violation: the
  `rebound_at`, `empty_at`, `uses` and `scope_end` rows of a temporary of plain data,
  the `reads_at` and `owner` rows of a place that no reference and no task can reach,
  the `cfg_edge` rows through a node with no other row.
- The old lowering gives some functions almost no rows: 1 row for a function of 100
  operators on `bool` (`edge/n100.wf`), 2 rows for a struct literal with place fields
  (`tests/programs/154_unset_nested.wf`, `mk_chain`). The IR keeps one node for each
  statement with a row, and the variables that a rule can read (the place fields of the
  literal, W0304). A ratio of such small numbers measures the old lowering, not the cost
  of the check.

## Decision

1. A counted row is a fact of an input relation of the spec that the checker reads for
   the function: each fact of `weft_check::bridge::each_fact`, with the place table and
   `cfg_edge`. The old facts count as they are.
2. The `ir` pipeline does not give the checker a row that no rule can read:
   `factgen::prune` (`docs/ir.md` 6.2, "As built (plan stage C1.4)") removes such rows,
   with a written argument for each step, and the property test
   `pruned_facts_give_the_same_violations` checks it on random facts against the
   checker and the spec. So the count of the `ir` facts is the count of the rows that
   the checker receives. A row that no rule can read does not count, because it is not
   there.
3. The bound for each function is `3 × old + 64` rows. The factor 3 bounds the growth;
   the 64 rows are a fixed part for each function (the largest fixed part on tier 1 at
   stage C1.4 is 58 rows, `q31rec.wf` `mk_list`). A quadratic pattern passes the fixed
   part at a small size: the `match` of stage C1 had 14 times the old rows at 200
   arms. `crates/weft-check/tests/scale.rs` checks the plain factor 3 (no fixed part)
   on its large shapes.
4. The time criterion does not change: the total `check` time of the `ir` pipeline on
   tier 1 is at most 2 times the old time.

## Consequences

- The measurement of the gate record (`docs/plan/core-ir.md` §5, stage C1.4) counts the
  rows of `weft facts --facts=both` for each function of the single-file programs of
  tier 1 in scope.
- A derivation of `weft check --explain` can take a shorter path, another witness, or
  other place ids. The verdicts and the diagnostics do not change.
- The fact oracle reads the facts before the prune: it checks the facts of the
  generator, and the prune keeps each row that a rule can read.
- Plan stage C1.4b (issue #62): the prune can also move rows to new nodes when the
  rules give the same facts at each old node. The nodes that lead to one node and give
  nested sets of variables new values (`rebound_at` at the aborts to a local handler)
  share one chain of new nodes (`factgen::prune`, `docs/ir.md` 6.2). The criterion
  counts the rows that the checker receives, so it counts the rows of the chain.
