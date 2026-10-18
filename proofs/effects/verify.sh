#!/usr/bin/env bash
# Verify the effects development. Requires `verus` on PATH.
set -euo pipefail
cd "$(dirname "$0")"
verus src/lib.rs --crate-type=lib "$@"
