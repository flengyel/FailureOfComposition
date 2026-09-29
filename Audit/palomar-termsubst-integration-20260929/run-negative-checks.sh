#!/usr/bin/env bash
set -euo pipefail

repository_root=/home/flengyel/src/FailureOfComposition-port
evidence_root="$repository_root/.codex-work/palomar/termsubst-integration/20260929T062653Z"
negative_root="$evidence_root/analysis/negative"
lean_root="$repository_root/Lean"
lean_bin=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean
checker="$lean_root/FailureOfComposition/Palomar/CheckThreeInterface.lean"

cd "$lean_root"
lake_path=$(lake env printenv LEAN_PATH)
negative_path="$negative_root:$lake_path"

/usr/bin/env LEAN_PATH="$negative_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$negative_root" \
  -o "$negative_root/ThreeResultNegativeChallenge.olean" \
  "$negative_root/ThreeResultNegativeChallenge.lean"
/usr/bin/env LEAN_PATH="$negative_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$negative_root" \
  -o "$negative_root/ThreeResultNegativeSolution.olean" \
  "$negative_root/ThreeResultNegativeSolution.lean"
/usr/bin/env LEAN_PATH="$negative_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$lean_root" --run "$checker" \
  --negative-shared-definition \
  ThreeResultNegativeChallenge ThreeResultNegativeSolution \
  ThreeResultNegative.selected ThreeResultNegative.shared

/usr/bin/env LEAN_PATH="$lake_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$lean_root" --run "$checker" \
  --negative-selection-count

check_rejected_override() {
  local label=$1
  shift
  set +e
  /usr/bin/env LEAN_PATH="$lake_path" LEAN_NUM_THREADS=1 \
    "$lean_bin" --root="$lean_root" --run "$checker" "$@" \
    >"$evidence_root/analysis/${label}.stdout" \
    2>"$evidence_root/analysis/${label}.stderr"
  local status=$?
  set -e
  if (( status == 0 )); then
    echo "$label module override was unexpectedly accepted" >&2
    exit 1
  fi
  printf '%s\n' "$status" >"$evidence_root/analysis/${label}.exit"
}

check_rejected_override legacy-selection \
  FailureOfComposition.Palomar.Challenge FailureOfComposition.Palomar.Solution
check_rejected_override one-only-selection \
  FailureOfComposition.Palomar.ChallengeOne FailureOfComposition.Palomar.SolutionOne
check_rejected_override two-only-selection \
  FailureOfComposition.Palomar.ChallengeTwo FailureOfComposition.Palomar.SolutionTwo

echo "PASS three-result command rejects legacy, One-only, and Two-only module overrides"
