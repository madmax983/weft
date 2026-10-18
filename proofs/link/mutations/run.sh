#!/usr/bin/env bash
# Run the mutation tests of the link crate. Requires `verus` on PATH and `python3`.
#
# Each mutation is a script NAME.py in this directory. Its first line is
# `# DESC: <what it changes>`. The script changes a copy of the sources.
# This script copies `proofs/` and `crates/weft-verified/` to a temporary
# directory, applies one mutation, and runs `proofs/link/verify.sh` there.
# The test passes if `verify.sh` fails. The script also verifies
# `crates/weft-verified` alone on the copy: "link only" means that it still
# verifies, so only the link finds the change.
#
# Usage: mutations/run.sh [NAME...]    (no NAME: all mutations)
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../../.." && pwd)"

names=("$@")
if [ "${#names[@]}" -eq 0 ]; then
    for f in "$here"/*.py; do
        n="$(basename "$f" .py)"
        [ "$n" = _lib ] || names+=("$n")
    done
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
caught=0
bad=0
for n in "${names[@]}"; do
    d="$work/$n"
    mkdir -p "$d/crates"
    cp -r "$root/proofs" "$d/"
    cp -r "$root/crates/weft-verified" "$d/crates/"
    desc="$(sed -n '1s/^# DESC: //p' "$here/$n.py")"
    if ! python3 -I -B "$here/$n.py" "$d" > "$d/patch.log" 2>&1; then
        echo "$n: PATCH DOES NOT APPLY: $(cat "$d/patch.log")"
        bad=$((bad + 1))
        continue
    fi
    if (cd "$d" && verus crates/weft-verified/src/lib.rs --crate-type=lib > "$d/core.log" 2>&1); then
        only="link only"
    else
        only="weft-verified fails too"
    fi
    if (cd "$d/proofs/link" && ./verify.sh > "$d/link.log" 2>&1); then
        echo "$n: NOT CAUGHT ($desc)"
        bad=$((bad + 1))
    else
        at="$(grep -E '^ *--> ' "$d/link.log" | sed -E 's/^ *--> //; s/:[0-9]+:[0-9]+$//; s|^src/\.\./\.\./\.\./|| ; s|^src/\.\./\.\./|proofs/|; s|^src/|proofs/link/src/|' | sort | uniq -c | awk '{ print $2 " (" $1 ")" }' | tr '\n' ' ')"
        [ -n "$at" ] || at="$(grep -m1 -E '^FAIL' "$d/link.log")"
        echo "$n: caught, $only. Fails at: $at"
        caught=$((caught + 1))
    fi
done
echo "mutations: $caught caught, $bad not caught or not applied"
[ "$bad" -eq 0 ]
