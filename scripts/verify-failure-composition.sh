#!/usr/bin/env bash
# Verify the maintained library using already installed, pinned dependencies.
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
exec bash "$script_dir/../Lean/FailureOfComposition/verify.sh" "$@"
