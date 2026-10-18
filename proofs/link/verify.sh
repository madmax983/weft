#!/usr/bin/env bash
# Verify the link between the exec core and the proof models. Requires `verus` on PATH.
set -euo pipefail
cd "$(dirname "$0")"
verus src/lib.rs --crate-type=lib "$@"
