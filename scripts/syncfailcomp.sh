#!/usr/bin/env bash
# Synchronize the maintained failure-of-composition development into a persistent
# Linux workspace, then verify it using the existing pinned PCats dependencies.
set -euo pipefail
command -v python3 >/dev/null 2>&1 || {
  echo 'syncfailcomp: Python 3.9 or later is required' >&2
  exit 1
}
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
export PYTHONDONTWRITEBYTECODE=1
exec python3 "$script_dir/sync_failcomp.py" "$@"
