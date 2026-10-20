## Weft compiler quality review (weft-interp skipped; no repo files edited, no git)

**Baseline.** `cargo fmt --check` is clean. `cargo clippy --workspace --exclude weft-interp --all-targets -- -D warnings` is clean. All tests pass. Line coverage is 92.6%.

**Fuzzing.** I ran two harnesses against `check_source`, with `agreement()` on and `--explain` on part of the runs:
- 440k mutated corpus programs (line and token mutations).
- 36k generated, mostly well-formed programs (12k of them also through `--explain`).

They found 1 crash family and **no checker/spec disagreements**. Hand-written probes found the other crashes.

**Scratch files.**
- Harness: `/tmp/claude-0/qualityreview/harness/src/bin/{fuzz,batch,perf,stack,codes,rounds}.rs`
- Generators: `/tmp/claude-0/qualityreview/{gen_deep,gen_perf,genprog}.py`
- Minimal repros: `/tmp/claude-0/qualityreview/repro/`

### Findings, most severe first

1. **crash** – `crates/weft-sema/src/body/call.rs:298` (`ptys[i]`) and `:257` (`sig.params.len() - first`).
   - Calling a method that has no `self` with method syntax panics in every build. The fuzzer hit it 30 times.
   - Repro (`repro/01_method_without_self.wf`): `struct S {}` / `impl S { fn m() {} }` / `fn f(s: S) { s.m() }`. Panic: "index out of bounds: the len is 0 but the index is 0". `s.m(1)` also overflows the subtraction in debug.
   - Fix: in `method_call`/`call_fn`, if `recv.is_some()` and the first param is not `self`, emit a W0104 such as "`m` is not a method; call `S.m()`" and return `Ty::Error`. Use `ptys.get(i)` and `saturating_sub` here.

2. **crash** – `crates/weft-cli/src/lib.rs:274` (`t[0]`), with the arity check missing at `:257`.
   - `weft lint --rules repro/02_lint_nullary.dl FILE`, where the file holds `lint() :- has_signature().`, panics: index out of bounds.
   - Arity 1 and 3 are accepted silently and print junk (`lint p0` at 1:1).
   - Fix: after parsing, reject unless `lint` has arity 2. Use `t.first()`.

3. **crash (stack overflow)** – `crates/weft-check/src/bridge.rs:360`. `render` recurses once per derivation premise.
   - `weft check --explain repro/03_explain_deep.wf` (one ref, one push, 10 000 `print(1)`, then a use): the debug CLI aborts with "stack overflow" even on its 8 MB main stack. Release aborts at 40 000 statements on a 2 MB thread.
   - At 10 000 statements the output is already **302 MB**, because `"  ".repeat(depth)` makes it grow quadratically.
   - Fix: make `render` iterative, like `Derivation`'s `Display` in `weft-datalog/src/provenance.rs:224`. Cap the indent, and fold long chains of one relation ("… 9 998 more `invalid` steps …").

4. **crash (stack overflow)** – sema recursion in `Lower::expr`, `binary`, `method_call`, `borrow`, `if_expr` (`weft-sema/src/body/expr.rs`).
   - The parser's depth budget (`weft-syntax/src/parser.rs:1-8, 37-40`) claims that code walking the tree "has enough stack too". This is false.
   - Parser-accepted inputs overflow a 2 MB thread (the default for spawned threads and test threads) in debug: a 377-term `1 + 1 + …` (`repro/04_sum_377_terms.wf`), 369 `else if`s, 376 chained `.m()` calls, 376 `&`s.
   - Fix: run `analyze`/`check_source` on a thread with a fixed large stack, or make chains iterative in sema. Lower `CHAIN_COST`'s effective limit to match sema. Add a test that runs the deepest accepted inputs on a 2 MB thread.

5. **crash in debug / wrong result in release** – `crates/weft-sema/src/fip.rs:296,300` (`b.1 * 2`).
   - 64 or more nested loops in a `fip fn` (`repro/05_fip_64_loops.wf`) panic with "attempt to multiply with overflow" in debug.
   - In release the count wraps to 0, so W1002 silently disappears. With 3 loops it reports "found 1 to 9".
   - Fix: use `saturating_mul` and `saturating_add`, or clamp `hi` to 2, since only `== 1` matters.

6. **correctness (unsound)** – `crates/weft-sema/src/lib.rs:98` (`rounds >= 32`). Effect inference stops after 32 rounds with no diagnostic.
   - A call chain of 33 or more functions, declared caller first, loses its effects: `repro/06_effect_chain_33.wf` (`fn quiet() / par { f0() }`, where f0→…→f33 performs `Log2`) is accepted. With 31 links W0702 fires.
   - Each round also re-lowers every inferred body: a 3 200-function chain takes 827 ms in sema, against about 40 ms for one round.
   - Fix: infer bottom-up over call-graph SCCs (Tarjan), iterating only inside an SCC. Or use a worklist that re-lowers only the callers of changed signatures. Never cap silently; report an internal error if a bound is hit.

7. **correctness (unsound)** – `crates/weft-sema/src/body/mod.rs:546` (`depth > 6` in `deep_any`) and `:596` (in `is_copy_d`).
   - A linear type nested 7 levels deep is not linear: `repro/07_linear_depth_7.wf` (`struct W0 { t: Tok }` … `W7`, `fn f(w: W7) {}`) gives no W0601. At depth 3 W0601 fires. `is_nonportable` and `has_on_abort` share this cut-off.
   - Fix: compute `linear`, `nonportable` and `copy` once per ADT after collection, as a fixpoint over the type graph with a visited set. Cache the results in `AdtDef`.

8. **perf (exponential)** – the same `deep_any` walk (`body/mod.rs:546-560`) branches on every field down to depth 6, so it costs O(fields^7). It runs about 3 times per variable (`var_info`).
   - Measurement (release) for `struct A { f0: A, …, f{k-1}: A }` with `fn f(x: A) { let y = x }`:

     | k | time |
     |---|---|
     | 4 | 0.03 s |
     | 8 | 0.9 s |
     | 10 | 4.2 s |
     | 12 | 15.3 s |
     | 14 | 43 s |

     The repro is `repro/08_wide_cyclic_struct.wf`.
   - Fix: the cache from finding 7.

9. **perf (cubic)** – `crates/weft-check/src/rules.rs:204-216`. W0301 evidence runs one `forward()` per (use, mutation) pair.
   - The pattern `let r = &v[0]; v.push(1); print(r)`, repeated n times (shadowing), measures in check (release):

     | n | time |
     |---|---|
     | 250 | 0.13 s |
     | 500 | 1.06 s |
     | 1000 | 7.96 s |
     | 2000 | 59 s |

     The Datalog spec does n=250 in 67 ms, faster than the "fast" checker. The repro is `repro/09_rebind_1000.wf`.
   - Fix: one multi-source BFS that labels each node with the first gen (in gens order) that reaches it, stopping at nodes that already have a label. This is O(N+E) per variable. Also drop the `gen.to_vec()`/`kill.to_vec()` copies in `Ctx::forward`/`backward` (`rules.rs:125-132`).

10. **correctness (wrong file and line)** – `crates/weft-sema/src/program.rs:436-439`.
    - This leftover loop calls `declare_unit_mark(&mut seen, 0)` and resets every pass-1 diagnostic to unit 0.
    - So W0107 (duplicate struct, enum, effect or mod) and W0108 point into `prelude.wf` with nonsense positions: `repro/10_dup_struct_prelude.wf` reports "--> prelude.wf:1:23", and a far-down duplicate reports "prelude.wf:137:17074". This also affects `--json`.
    - Fix: delete the loop. Pass 1 already sets `d.unit`. Add a test that asserts `d.unit == 1`.

11. **correctness (wrong fix hint)** – `crates/weft-check/src/diagnose.rs:174` (`e.to_lowercase()`).
    - For user effect `Log2`, W0702 says "add `log2` to the effects". Doing that gives W0101 "unknown effect `log2`" (`repro/11_user_effect_hint.wf`).
    - Fix: lowercase only standard effects (`effects::is_std`). The W0701 text in `call.rs:398` has the same issue.

12. **correctness (missing checks)** – these were all accepted with no diagnostic (cases in `/tmp/claude-0/qualityreview/hand.txt`, output from `htarget/release/codes`):
    - Infinite-size `struct A { a: A }`.
    - Duplicate struct fields, duplicate enum variants, duplicate field initialisers `S { a: 1, a: 2 }`, duplicate closure params `|a, a|`.
    - `let x: u8 = 300` (no literal range check).
    - `on abort = nope` (unknown function) and `on abort = g` with the wrong signature.
    - `@ uniq uniq shared once many` (contradictory modes).
    - `x: &u32 in x` and cyclic `in` places.
    - `fork()` with fewer than two closures.
    - Misleading messages:
      - `f(y: 1)` and `f(x: 1, x: 2)` both say "`f` takes 1 arguments, found 1" (`call.rs:257`).
      - `weft check missing.wf` says "cannot read missing.wf/weft.toml".
      - `weft explain` with no code says "missing PATH".
      - Parse errors print "error: f.wf:1:1: error[W0001]".
    - Fix: add the checks in `define_items`/`resolve_one`, and a W0103 "no parameter named `y`" / "argument `x` given twice".

13. **robustness (CLI and manifest)** – `crates/weft-cli/src/package.rs`:
    - No `#[serde(deny_unknown_fields)]` on `Manifest`, `PackageTable` or `DepTable` (`:41,57,67`). `runtim = "none"` is ignored, so the embedded profile is silently off.
    - A broken dependency `weft.toml` is swallowed by `.ok()` (`:166`), which skips the W0902 `gc` check.
    - A dependency named like a root item (for example `main`) silently loses the name clash (`program.rs:426`). The result is "`fn() -> ()` has no method `f`".
    - In `crates/weft-cli/src/lib.rs`:
      - A syntax error bypasses `--json` (stderr text, exit 2) instead of emitting a JSON W0001 with exit 1.
      - `weft facts FILE nosuchfn` prints nothing and exits 0.
      - Extra positional args are ignored.
    - Fix: deny unknown fields, propagate dependency manifest errors, emit W0107 on a name clash, emit parse errors as diagnostics, and error on an unknown function or extra args.

14. **perf (quadratic)** – `crates/weft-check/src/bridge.rs:66-81`. The pairwise `step_alias`/`step_within` loop allocates two `to_string()`s per pair, even when nothing is emitted.
    - A struct with 3 200 fields, all assigned: `each_fact` takes 877 ms against 0.4 ms for check. 400 fields take 29 ms.
    - Fix: build `pv`/`qv` only inside the `if`. Better, index by step kind so only aliasing pairs are visited.

15. **perf (quadratic)** – `crates/weft-sema/src/body/mod.rs:218-219`. `show()` calls `prog.adt_names()`, which copies every ADT name, once per variable (`var_info`).
    - 3 200 types with 3 200 locals: sema takes 715 ms (1 600 take 244 ms, 400 take 17 ms).
    - Fix: build the name table once in `Lower::new`, or make `Display` take `&Program`.

16. **perf (other)**:
    - Per-variable propagation is O(V·N). One function with 8 000 blocks: check 1.56 s, sema 552 ms (2 000 blocks: 97 ms and 48 ms).
    - `call_mut × call_arg` is a nested loop over the whole function (`rules.rs:337-343`). Group it by node.
    - Clones in hot paths:
      - `def.decl.body.clone()` (`stmt.rs:17`): the whole body, every inference round.
      - `self.sigs[f].clone()` per call (`call.rs:218`).
      - `self.closures[s].clone()` (`expr.rs:1106`).
      - `adts[a].kind.clone()` (`call.rs:683,715`, `expr.rs:653,903`).
    - `sort_by_key` with a `String` clone per comparison (`driver.rs:55`, `cli/lib.rs:110`, `diagnose.rs:268`): use `sort_by`.
    - Measured and fine:
      - `FnFacts::child` interning is O(1) amortised plus O(depth) step copies.
      - The parser rejects every 2 000-level nesting in about 10 ms.
      - The cloning of the whole `Program` in `local_ty` has been fixed: it now uses `TyResolver`.

17. **standards (panics and ids)**:
    - `pub fn agreement` panics on spec failure (`driver.rs:126`). Return `Result`, or add the error to `Disagreement`.
    - `bridge::spec()` panics (`bridge.rs:25`). This is acceptable for an `include_str!` invariant, but document it (`# Panics`) and add a parse test.
    - `prelude_unit()` silently uses an empty prelude on a parse failure (`lib.rs:59`).
    - `SourceFile::snippet` (`source.rs:48`) panics on a non-char boundary and is unused.
    - Ids in weft-sema are `usize` aliases, not newtypes: `FnId`, `ModId`, `EffectId` (`program.rs:16-20`) and `AdtId` (`types.rs:63`). `PathRef::Adt(usize)` and `groups: BTreeMap<usize, _>` mix them freely. Use the `id_type!` macro from weft-facts.
    - Diagnostic codes are bare strings. 9 emitted codes have no `weft explain` entry: L0001 and W0108–W0115. Use a `Code` enum and add a test that every emitted code is in `CODES`.
    - Magic numbers: `900 + adt` and `800 + i` call indices (`call.rs:380,478`), `split_base * 64` (`mod.rs:406`, which collides when there are more than 64 params), and unit `1` (`driver.rs:69`, `lib.rs:80`).

18. **standards (lint allows)**:
    - `weft-verified/src/lib.rs:9-10` has a blanket `allow(clippy::all, pedantic, nursery)` and `allow(missing_docs)` with no comment. Removing it shows 46 warnings, including 4 undocumented pub fields (`places.rs:17,19,23`: `id`, `split`, `hi`). Only `ptr_arg`, `len_zero` and `missing_const_for_fn` are forced by Verus; allow just those, with a comment.
    - `bridge.rs:39` `#[allow(clippy::too_many_lines)]` is redundant, since the workspace already allows it.
    - The global `too_many_lines` allow hides `call_fn` (324 lines, `call.rs:210`), which is not grammar-shaped and contains finding 1. `diagnose` (253 lines) is the same.
    - `missing_panics_doc` is allowed although public functions panic.
    - The bench's `significant_drop_tightening` allow has no comment.
    - `RUSTDOCFLAGS=-D warnings cargo doc` fails on a redundant explicit link at `rules.rs:4`.

19. **code smells (dead and duplicated code)**:
    - Dead closure `pairs` plus `let _ = pairs` (`bridge.rs:239-306`).
    - `let p = Program::default(); let _ = p;` (`package.rs:196-197`), and `canonical_std` duplicates `effects::canonical`.
    - `let _ = &self.loops;` (`stmt.rs:94`).
    - `local_ty` (`stmt.rs:760`) and `local_ty_pub` (`expr.rs:1090`) are identical; `_pub` is also a misleading name.
    - `multi_node` is applied twice per named effect (`call.rs:460`, already done in `perform_effect`), and `handlers.iter().any()` is followed by the same `find`.
    - Closure-ness is inferred from the type text: `info.ty.starts_with("fn(")` (`diagnose.rs:59`).
    - The empty test module `weft-sema/src/tests.rs`.
    - `bridge::violations` silently drops tuples that fail to parse, which could hide a disagreement.

20. **style (diagnostic flood)** – W0602 fires once per abort node. 4 calls give 4 identical errors, and the generated programs averaged 28 W0602 errors each. Report once per variable: the first site plus "and N more".

21. **docs (ASD-STE100 and accuracy)** – the style is mostly compliant: no banned words, and only 10 sentences over 25 words. Places to fix:
    - Long sentences:
      - `weft-verified/src/dataflow.rs:87` (61 words).
      - `dataflow.rs:1` (38 words).
      - `places.rs:6` (31 words).
      - `weft-datalog/src/lib.rs` "Range restriction…" and "Provenance…" (26 words each).
    - Passives:
      - "It is parsed once." (`bridge.rs:20`)
      - "is rejected when the project loads it" (`package.rs:4`)
      - "The program is rejected/accepted" (`diag.rs:11,13`)
      - "The open token is consumed" (`parser.rs:287,307`)
      - "Each interpolation is parsed" (`parser.rs:1769`)
    - Inaccurate docs:
      - The parser's stack-safety claim (finding 4).
      - The `Diagnostic::render` example has no `-->` line (`diag.rs:84-89`).
      - "It does not copy the program" (`program.rs:1032`) describes history, not behaviour.
      - README:36-37 lists `weft run` and `weft test`, which are not in `USAGE`.

22. **tests** – coverage gaps:

    | file | lines | other |
    |---|---|---|
    | `fip.rs` | 73% | 66% regions |
    | `driver.rs` | 74% | `agreement` `Err` path untested |
    | `package.rs` | 84% | 65% functions |
    | `expr.rs` | 81% | |
    | `main.rs` | 0% | |

    - weft-sema has only 3 unit tests.
    - There are no tests for:
      - effect inference rounds, recursion or long chains
      - deep or cyclic types
      - the unit index of diagnostics
      - lint arity
      - manifest errors or unknown keys
      - `--json` on a syntax error
    - There is no fuzz test of sema or the checker; only the parser is fuzzed.
    - CLI tests use `assert!(run(..).is_err())` without checking the message (`cli/tests/cli.rs:107-113`), and `library_cannot_enable_gc` only checks a substring.
    - Suggest a proptest that feeds mutated corpus programs to `check_source` plus `agreement`, running on a 2 MB thread. My `harness/src/bin/fuzz.rs` is a starting point.
