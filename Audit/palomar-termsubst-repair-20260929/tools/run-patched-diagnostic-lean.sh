#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 2 ]]; then
  echo "usage: $0 DIAGNOSTIC_OLEAN_DIR LEAN_ARGS..." >&2
  exit 64
fi

diagnostic_olean_dir=$1
shift

repository=/home/flengyel/src/FailureOfComposition-port
patched_foundation="$repository/.codex-work/palomar/termsubst-repair/20260929T021106Z/foundation/overlay/lib/lean"
project="$repository/Lean"
pinned_prefix=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2
base_lean_path=$(cd "$project" && "$pinned_prefix/bin/lake" env printenv LEAN_PATH)

exec env LEAN_PATH="$diagnostic_olean_dir:$patched_foundation:$base_lean_path" \
  "$pinned_prefix/bin/lean" "$@"
