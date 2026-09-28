#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 2 ]]; then
  echo "usage: $0 DIAGNOSTIC_OLEAN_DIR LEAN_ARGS..." >&2
  exit 64
fi

diagnostic_olean_dir=$1
shift

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repository=$(cd -- "$script_dir/../../.." && pwd)
pinned_prefix=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2
base_lean_path=$(cd -- "$repository/Lean" && \
  "$pinned_prefix/bin/lake" env printenv LEAN_PATH)

exec env LEAN_PATH="$diagnostic_olean_dir:$base_lean_path" \
  "$pinned_prefix/bin/lean" "$@"
