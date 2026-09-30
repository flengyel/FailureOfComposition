#!/usr/bin/env bash
set -euo pipefail

repository_root=/home/flengyel/src/FailureOfComposition-port
lean_root="$repository_root/Lean"
fixtures="$repository_root/Audit/palomar-nine-generated-quotient-20260930/negative"
output=$(realpath -m "${1:?usage: run-negative-checks.sh OUTPUT_DIRECTORY}")
lean_bin=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean
checker="$lean_root/FailureOfComposition/Palomar/CheckNineInterface.lean"

mkdir -p "$output"
cd "$lean_root"
lake_path=$(lake env printenv LEAN_PATH)
negative_path="$fixtures:$output:$lake_path"

/usr/bin/env LEAN_PATH="$negative_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$fixtures" -o "$output/NineResultNegativeChallenge.olean" \
  "$fixtures/NineResultNegativeChallenge.lean"
/usr/bin/env LEAN_PATH="$negative_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$fixtures" -o "$output/NineResultNegativeSolution.olean" \
  "$fixtures/NineResultNegativeSolution.lean"
/usr/bin/env LEAN_PATH="$negative_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$lean_root" --run "$checker" \
  --negative-shared-definition NineResultNegativeChallenge NineResultNegativeSolution \
  NineResultNegative.selected NineResultNegative.shared \
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
check_rejected_override six-only-selection \
  FailureOfComposition.Palomar.ChallengeSix FailureOfComposition.Palomar.SolutionSix
check_rejected_override seven-only-selection \
  FailureOfComposition.Palomar.ChallengeSeven FailureOfComposition.Palomar.SolutionSeven
check_rejected_override eight-only-selection \
  FailureOfComposition.Palomar.ChallengeEight FailureOfComposition.Palomar.SolutionEight

/usr/bin/env LEAN_PATH="$negative_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$fixtures" -o "$output/NineWrongRouteSolution.olean" \
  "$fixtures/NineWrongRouteSolution.lean"
/usr/bin/env LEAN_PATH="$negative_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$fixtures" "$fixtures/NineWrongRouteAudit.lean" \
  >"$output/wrong-route.stdout" 2>"$output/wrong-route.stderr"
grep -q "PASS exact-type wrong-route fixture is rejected" "$output/wrong-route.stdout"

printf 'PASS Nine checker rejects changed shared bodies, incomplete selection, legacy/One/Two/Three/Four/Five/Six/Seven/Eight overrides, and the exact-type Gödel-route substitution\n'
