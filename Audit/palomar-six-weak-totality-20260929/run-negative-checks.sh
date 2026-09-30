#!/usr/bin/env bash
set -euo pipefail

repository_root=/home/flengyel/src/FailureOfComposition-port
lean_root="$repository_root/Lean"
fixtures="$repository_root/Audit/palomar-six-weak-totality-20260929/negative"
output=$(realpath -m "${1:?usage: run-negative-checks.sh OUTPUT_DIRECTORY}")
lean_bin=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean
checker="$lean_root/FailureOfComposition/Palomar/CheckSixInterface.lean"

mkdir -p "$output"
cd "$lean_root"
lake_path=$(lake env printenv LEAN_PATH)
negative_path="$fixtures:$output:$lake_path"

/usr/bin/env LEAN_PATH="$negative_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$fixtures" -o "$output/SixResultNegativeChallenge.olean" \
  "$fixtures/SixResultNegativeChallenge.lean"
/usr/bin/env LEAN_PATH="$negative_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$fixtures" -o "$output/SixResultNegativeSolution.olean" \
  "$fixtures/SixResultNegativeSolution.lean"
/usr/bin/env LEAN_PATH="$negative_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$lean_root" --run "$checker" \
  --negative-shared-definition SixResultNegativeChallenge SixResultNegativeSolution \
  SixResultNegative.selected SixResultNegative.shared \
  >"$output/changed-definition.stdout" 2>"$output/changed-definition.stderr"

/usr/bin/env LEAN_PATH="$lake_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$lean_root" --run "$checker" --negative-selection-count \
  >"$output/incomplete-selection.stdout" 2>"$output/incomplete-selection.stderr"

check_rejected_override() {
  local label=$1
  shift
  set +e
  /usr/bin/env LEAN_PATH="$lake_path" LEAN_NUM_THREADS=1 \
    "$lean_bin" --root="$lean_root" --run "$checker" "$@" \
    >"$output/${label}.stdout" 2>"$output/${label}.stderr"
  local status=$?
  set -e
  if (( status == 0 )); then
    printf '%s module override was unexpectedly accepted\n' "$label" >&2
    exit 1
  fi
  grep -q "accepts no module overrides" "$output/${label}.stderr"
  printf '%s\n' "$status" >"$output/${label}.exit"
}

check_rejected_override legacy-selection \
  FailureOfComposition.Palomar.Challenge FailureOfComposition.Palomar.Solution
check_rejected_override one-only-selection \
  FailureOfComposition.Palomar.ChallengeOne FailureOfComposition.Palomar.SolutionOne
check_rejected_override two-only-selection \
  FailureOfComposition.Palomar.ChallengeTwo FailureOfComposition.Palomar.SolutionTwo
check_rejected_override three-only-selection \
  FailureOfComposition.Palomar.ChallengeThree FailureOfComposition.Palomar.SolutionThree
check_rejected_override four-only-selection \
  FailureOfComposition.Palomar.ChallengeFour FailureOfComposition.Palomar.SolutionFour
check_rejected_override five-only-selection \
  FailureOfComposition.Palomar.ChallengeFive FailureOfComposition.Palomar.SolutionFive

printf 'PASS Six checker rejects changed shared bodies, incomplete selection, and legacy/One/Two/Three/Four/Five overrides\n'
