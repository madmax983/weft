#!/usr/bin/env bash
# Run the mutation tests of this proof crate (ADR 0008). Requires `verus` on
# PATH and `python3`.
#
# Each mutation is a script NAME.py in this directory. Its first line is
# `# DESC: <what it changes>`, and its second line is `# EXPECT: N verified, M
# errors`, the result in the README of the crate (Verus writes `1 errors`; the
# check compares the numbers). The script changes a copy of
# the sources. This script copies the crate to a temporary directory, applies
# one mutation, and runs `verify.sh` there. The test passes only if Verus gives
# a result line with at least one error, and that line is the expected one. A
# failure with no result line (Verus did not run, or the patch breaks the
# build) does not pass. The script shows the functions that fail.
#
# Usage: mutations/run.sh [NAME...]    (no NAME: all mutations)
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
crate="$(cd "$here/.." && pwd)"

names=("$@")
if [ "${#names[@]}" -eq 0 ]; then
    for f in "$here"/*.py; do
        n="$(basename "$f" .py)"
        case "$n" in _*) ;; *) names+=("$n") ;; esac
    done
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
caught=0
bad=0
for n in "${names[@]}"; do
    d="$work/$n"
    cp -r "$crate" "$d"
    rm -rf "$d/mutations"
    desc="$(sed -n '1s/^# DESC: //p' "$here/$n.py")"
    want="$(sed -n '2s/^# EXPECT: //p' "$here/$n.py")"
    if ! python3 -I -B "$here/$n.py" "$d" > "$d/patch.log" 2>&1; then
        echo "$n: PATCH DOES NOT APPLY: $(cat "$d/patch.log")"
        bad=$((bad + 1))
        continue
    fi
    if (cd "$d" && ./verify.sh > "$d/verify.log" 2>&1); then
        echo "$n: NOT CAUGHT ($desc)"
        bad=$((bad + 1))
        continue
    fi
    result="$(grep -m1 -oE '[0-9]+ verified, [0-9]+ errors?' "$d/verify.log")"
    errors="$(printf '%s' "$result" | sed -nE 's/.* ([0-9]+) errors?$/\1/p')"
    at="$(python3 -I -B "$here/_where.py" "$d" < "$d/verify.log")"
    if [ -z "$errors" ] || [ "$errors" -eq 0 ]; then
        echo "$n: NO RESULT ($desc): verify.sh fails, but Verus gives no error count: $(tail -n 3 "$d/verify.log" | tr '\n' ' ')"
        bad=$((bad + 1))
    elif [ -n "$want" ] && [ "${result%error*}" != "${want%error*}" ]; then
        echo "$n: caught, but NOT AS DOCUMENTED ($desc): $result, expected $want. Fails in: $at"
        bad=$((bad + 1))
    else
        echo "$n: caught ($desc): $result. Fails in: $at"
        caught=$((caught + 1))
    fi
done
echo "mutations: $caught caught, $bad not caught or not applied"
[ "$bad" -eq 0 ]
