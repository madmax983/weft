#!/usr/bin/env bash
# Verify all Weft proof crates and the verified exec core.
# A missing proof crate is an error: the gate must not pass without its proofs.
set -euo pipefail
cd "$(dirname "$0")"
EXPECTED=(borrowing effects link)
for crate in "${EXPECTED[@]}"; do
    if [ ! -x "$crate/verify.sh" ]; then
        echo "error: proofs/$crate/verify.sh is missing or not executable" >&2
        exit 1
    fi
done
if [ ! -f ../crates/weft-verified/src/lib.rs ]; then
    echo "error: crates/weft-verified/src/lib.rs is missing" >&2
    exit 1
fi
for crate in "${EXPECTED[@]}"; do
    echo "== proofs/$crate"
    (cd "$crate" && ./verify.sh "$@")
done
echo "== crates/weft-verified"
verus ../crates/weft-verified/src/lib.rs --crate-type=lib "$@"
