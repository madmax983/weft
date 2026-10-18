#!/usr/bin/env bash
# Verify all Weft proof crates and the verified exec core.
set -euo pipefail
cd "$(dirname "$0")"
for crate in borrowing effects; do
    echo "== proofs/$crate"
    (cd "$crate" && ./verify.sh "$@")
done
echo "== crates/weft-verified"
verus ../crates/weft-verified/src/lib.rs --crate-type=lib "$@"
