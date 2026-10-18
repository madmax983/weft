# TDD log

This log records the SPEC, PROOF, RED, GREEN, REFACTOR loop for each work package. The
commits on the branch show the order.

| Work package | SPEC | PROOF | RED | GREEN | REFACTOR |
| --- | --- | --- | --- | --- | --- |
| Place algebra | `spec/weft.dl` place rules | `places.rs` lemmas (Verus) | unit tests on rule 3 and 4 | exec fns verify and pass | `concat`, triggers |
| Dataflow | `invalid`/`moved`/`live_*`/`active` rules | `propagate` equals least fixpoint (Verus) | proptest against a naive fixpoint | worklist proof | measure in benches |
| Datalog engine | language in the agent brief | n/a | tests against `todo!()` stubs | semi-naive with provenance | iterative drop and display |
| Parser | `docs/grammar.md` | n/a | snippet and unit tests first | parser and lexer | pretty-printer round trip |
| Checker | each rule group of the spec | uses verified core | 21 rule tests on hand-written facts | `rules.rs` | random agreement test found a std-effect mismatch; fixed |
| Sema | fact schema | n/a | corpus programs with `//~` markers | lowering | duplicate items, scalar bindings, match moves |
| CLI | usage text | n/a | `tests/cli.rs` | commands | package diagnostics per unit |

Each corpus program in `tests/programs` was written before its fix. The first corpus run
failed 13 of 13 programs (prelude clash, callee roots, destructuring); later runs failed
5 of 20 and 3 of 27 before the fixes in the following commits.
