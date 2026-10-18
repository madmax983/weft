#!/usr/bin/env bash
# Verify the whole development. Requires `verus` on PATH (see README).
set -euo pipefail
cd "$(dirname "$0")"
verus src/lib.rs --crate-type=lib "$@"
