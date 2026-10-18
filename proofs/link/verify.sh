#!/usr/bin/env bash
# Verify the link between the exec core and the proof models. Requires `verus` on PATH.
# First check that the crate includes its sources and has no shadow copies.
set -euo pipefail
cd "$(dirname "$0")"
./check-copies.sh
verus src/lib.rs --crate-type=lib "$@"
