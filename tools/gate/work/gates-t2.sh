#!/usr/bin/env bash
# gates-t2.sh GATE OUT: the tier-2 gate with the release weft-gate binary GATE.
# Run it in the root of the repo, and run it alone (no other cargo or gate).
# The reports and logs go to OUT. The gate needs 0 blockers.
set -u
G=${1:?usage: gates-t2.sh GATE OUT}
O=${2:?usage: gates-t2.sh GATE OUT}
mkdir -p "$O"
step() { local name=$1; shift; "$@" > "$O/$name.log" 2>&1; echo "exit $?" >> "$O/$name.log"; }
step oracle-ir-t2 "$G" oracle --tier 2 --engine ir --workers 2
step run-t2 "$G" run --tier 2 --workers 2 --report "$O/report-t2.md"
echo done > "$O/t2.done"
