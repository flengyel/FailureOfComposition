#!/usr/bin/env bash
# Create an independent Linux checkout for the Lean version port.
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: bash scripts/setup-codex-wsl.sh [DESTINATION]

Clone FailureOfComposition main into a new Linux directory and create the branch
codex/lean-4.35.0-rc2. The default is $HOME/src/FailureOfComposition-port.
Existing destinations and destinations inside the source checkout, PCats, or the
existing execution environment are refused. No tools or Lean dependencies are
installed, and no build is run.
EOF
}
if [[ ${1:-} == --help || ${1:-} == -h ]]; then
  usage
  exit 0
fi
if (( $# > 1 )); then
  usage >&2
  exit 2
fi
for required in git python3; do
  command -v "$required" >/dev/null 2>&1 || {
    printf 'setup-codex-wsl: %s is required\n' "$required" >&2
    exit 1
  }
done
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
destination=${1:-"$HOME/src/FailureOfComposition-port"}
destination=$(python3 - "$destination" "$script_dir/.." \
  "$HOME/src/PCats" "${PCATS_DST:-$HOME/src/PCats}" \
  "$HOME/src/FailureOfComposition" \
  "${FAILCOMP_DST:-$HOME/src/FailureOfComposition}" <<'PY'
import os
import re
import sys

raw, *protected = sys.argv[1:]
raw = os.path.abspath(os.path.expanduser(raw))
target = os.path.realpath(raw)
reason = None
if os.path.lexists(raw) or os.path.lexists(target):
    reason = "destination already exists (including a symbolic link)"
elif re.match(r"^/mnt/[A-Za-z](?:/|$)", target):
    reason = "destination is on a Windows-mounted drive; choose a Linux directory"
else:
    for root in protected:
        root = os.path.realpath(root)
        if os.path.commonpath([target, root]) == root:
            reason = "destination is inside the source checkout or a protected execution environment"
            break
if reason:
    sys.exit(f"setup-codex-wsl: {reason}: {raw}")
print(target)
PY
)
canonical_url=https://github.com/flengyel/FailureOfComposition.git
mkdir -p -- "$(dirname -- "$destination")"
# Keep the ordinary all-branch fetch mapping. A --single-branch clone prevents
# later published review branches from being fetched and recognized for tracking.
git clone --branch main -- "$canonical_url" "$destination"
if [[ $(git -C "$destination" config --get remote.origin.url) != "$canonical_url" \
  || $(git -C "$destination" symbolic-ref --quiet --short HEAD) != main \
  || $(git -C "$destination" rev-parse --show-toplevel) != "$destination" ]]; then
  printf 'setup-codex-wsl: cloned repository identity check failed: %s\n' "$destination" >&2
  exit 1
fi
git -C "$destination" switch -c codex/lean-4.35.0-rc2
printf 'Starting commit: %s\n' "$(git -C "$destination" rev-parse HEAD)"
printf '\nIndependent checkout ready. After installing and signing in to Codex:\n'
printf 'cd %q\n' "$destination"
printf '%s\n' \
  'mkdir -p .codex-work/logs .codex-work/tmp' \
  'export TMPDIR="$PWD/.codex-work/tmp"' \
  'export LEAN_NUM_THREADS=1 FAILCOMP_STYLE_JOBS=1' \
  'codex "Read AGENTS.md and docs/CODEX_PORT_TASK.md. Carry out the first porting milestone described there."'
printf '\nSetup guide: docs/CODEX_WSL_SETUP.md\n'
