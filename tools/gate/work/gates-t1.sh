#!/usr/bin/env bash
# gates-t1.sh GATE OUT: the tier-1 gates with the release weft-gate binary GATE.
# Run it in the root of the repo. The reports and logs go to OUT.
# The order: manifest, the oracle caches (ir, ast), the gate with
# --write-baseline, the gate, sigdiff, the fact oracle. Each log ends with
# "exit N". The gate needs 0 blockers, sigdiff 0 rows with no entry, and the
# fact oracle 0 failures.
set -u
G=${1:?usage: gates-t1.sh GATE OUT}
O=${2:?usage: gates-t1.sh GATE OUT}
mkdir -p "$O"
step() { local name=$1; shift; "$@" > "$O/$name.log" 2>&1; echo "exit $?" >> "$O/$name.log"; }
step manifest "$G" manifest --tier 1
step oracle-ir "$G" oracle --tier 1 --engine ir --workers 2
step oracle-ast "$G" oracle --tier 1 --engine ast --workers 2
step run-wb "$G" run --tier 1 --workers 2 --write-baseline --report "$O/report-t1-wb.md"
step run "$G" run --tier 1 --workers 2 --report "$O/report-t1.md"
step sigdiff "$G" sigdiff --tier 1 --workers 2 --report "$O/sigdiff-t1.md"
step fact-oracle "$G" fact-oracle --tier 1 --workers 2 --report "$O/fact-oracle-t1.md"
echo done > "$O/t1.done"
