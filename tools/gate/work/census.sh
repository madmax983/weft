#!/usr/bin/env bash
# census.sh BIN BASE LIST OUT: `check --reasons` on each path of LIST (relative
# to BASE), 2 jobs. One TSV row: path, fallback note (or -), reasons.
BIN=$1 BASE=$2 LIST=$3 OUT=$4
cd "$BASE" || exit 1
export BIN
one() {
  for f in "$@"; do
    out=$(timeout 150 "$BIN" check --reasons "$f" 2>&1); rc=$?
    fb=$(grep -m1 -o 'the old pipeline checks the program: .*' <<<"$out" | sed 's/^the old pipeline checks the program: //')
    rs=$(grep -o 'note: --reasons: .*' <<<"$out" | sed 's/^note: --reasons: //' | tr '\n' '|' | sed 's/|$//')
    [ $rc = 124 ] && fb="TIMEOUT"
    printf '%s\t%s\t%s\n' "$f" "${fb:--}" "${rs:--}"
  done
}
export -f one
xargs -d "\n" -a "$LIST" -n 20 -P 2 bash -c 'one "$@"' _ > "$OUT.part"
sort "$OUT.part" > "$OUT" && rm -f "$OUT.part"
echo done > "$OUT.done"
