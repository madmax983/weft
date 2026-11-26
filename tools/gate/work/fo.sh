#!/usr/bin/env bash
# fo.sh FILE...: the fact oracle (with the memory oracle) for three (seed,
# workers) pairs: (1,1), (2,4), (3,2). Only files that the IR checks (not in
# the fallback). One line for each file: the first failure of each run, or ok.
# Usage: WEFT=<weft binary> bash fo.sh FILE...
set -u
Z=${WEFT:?set WEFT to the weft binary}
for f in "$@"; do
  if "$Z" check --facts=ir "$f" 2>&1 | grep -q 'old pipeline checks'; then continue; fi
  r=""
  for cfg in "1 1" "2 4" "3 2"; do
    read -r s w <<<"$cfg"
    o=$(timeout 20 "$Z" run --unchecked --fact-oracle --oracle --seed "$s" --workers "$w" "$f" 2>&1)
    e=$(grep -m1 -E 'fact oracle|runtime error' <<<"$o")
    n=$(grep -m1 -o 'fact-oracle: [0-9]* frame' <<<"$o")
    r="$r [$s/$w: ${e:-ok} ${n}]"
  done
  echo "$(basename "$f"):$r"
done
