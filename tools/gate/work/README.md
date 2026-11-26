# Work tools of the R0z stages

These scripts compare a build of a stage with a build of main. They are not
part of the gate. The handoff (`docs/plan/handoff.md`) tells how to use them
in each stage.

Build the binaries in release mode (`cargo build --release -p weft-cli -p weft-gate`).
Keep one binary for main and one for the stage. Run the scripts in the root of
the repo.

| Script | Use |
|---|---|
| `ev.sh` | `WEFT=<weft> bash ev.sh FILE...`: one TSV row for each program. Column 8 is the verdict. |
| `evcmp.py` | `python3 evcmp.py MAIN.tsv STAGE.tsv`: the rows of `ev.sh` that change, and each new `HOLE` and `FP-IR`. |
| `fo.sh` | `WEFT=<weft> bash fo.sh FILE...`: the fact oracle and the memory oracle in 3 (seed, workers) configurations. It runs only on files that the IR checks. |
| `census.sh` | `bash census.sh <weft> BASE LIST OUT`: `check --reasons` on each path of LIST. One TSV row for each path: the fallback note, or `-`. |
| `census-t2-fb.txt` | The list of tier-2 files of the census (relative to `target/gate/probes-tier2`). |
| `gates-t1.sh` | `bash gates-t1.sh <weft-gate> OUT`: the tier-1 gates (manifest, oracle caches, gate, sigdiff, fact oracle). |
| `gates-t2.sh` | `bash gates-t2.sh <weft-gate> OUT`: the tier-2 gate. Run it alone. |

The verdicts of `ev.sh` ("in scope" means that the IR checks the program, not the
fallback):

| Verdict | Errors | Fault at run time |
|---|---|---|
| `HOLE` | none, in scope | yes |
| `held` | the fallback rejects | yes |
| `both-reject` | both pipelines reject, in scope | yes |
| `oldmiss` | only the IR rejects, in scope | yes |
| `fb-miss` | none, in the fallback | yes |
| `FP-IR` | the IR rejects, in scope | no |
| `fb-reject` | the fallback rejects | no |
| `nofault` | none | no |

A time-out of `check` gives 0 errors. A new `HOLE` or a new `FP-IR` (from
`nofault` on main) is a blocker of the stage, unless the ship rule of the
handoff makes it an exception.

The tier-1 list for `census.sh` is the path column of the manifest:

```bash
cut -f2 tests/gate/manifest-tier1.tsv | tail -n +2 > /tmp/census-t1.txt
```
