#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repository_root=$(CDPATH= cd -- "$script_dir/.." && pwd)
lean_root="$repository_root/Lean"
output=$(realpath -m "${1:?usage: run-palomar-nine-focused.sh OUTPUT_DIRECTORY}")
submission=${PALOMAR_SUBMISSION_CHECKOUT:?set PALOMAR_SUBMISSION_CHECKOUT to current pinned verifier}
palomar_python=${PALOMAR_PYTHON:-python3}
dependency_checkout=${PALOMAR_DEPENDENCY_CHECKOUT:-$repository_root}
results="$output/focused-gates.tsv"

mkdir -p "$output"
printf 'gate\texit_status\telapsed_seconds\n' >"$results"

run_gate() {
  local label=$1 started status
  shift
  started=$(date +%s)
  printf 'command=' >"$output/$label.command"
  printf '%q ' "$@" >>"$output/$label.command"
  printf '\n' >>"$output/$label.command"
  set +e
  timeout --signal=TERM --kill-after=30s 300s "$@" \
    >"$output/$label.stdout" 2>"$output/$label.stderr"
  status=$?
  set -e
  printf '%s\t%s\t%s\n' "$label" "$status" "$(( $(date +%s) - started ))" >>"$results"
  (( status == 0 )) || return "$status"
}

cd "$repository_root"
run_gate submission-layout python3 scripts/check-palomar-submission-tree.py .
run_gate portable-config python3 scripts/validate-palomar-nine-config.py \
  Lean/FailureOfComposition/Palomar/comparator-nine.json

cd "$lean_root"
run_gate build-selected-modules env LEAN_NUM_THREADS=1 lake build \
  FailureOfComposition.Palomar.ChallengeNine \
  FailureOfComposition.Palomar.SolutionNine
for module in \
  ArithmeticInterface EvaluatorInterface GeneratedCongruenceInterface \
  GeneratedCongruenceBridge GeneratedQuotientInterface GeneratedQuotientBridge \
  WeakTotalityBridge RangeInterface RangeBridge RangeProductiveBridge SolutionNine; do
  run_gate "strict-$module" env LEAN_NUM_THREADS=1 lake env lean \
    -DwarningAsError=true "FailureOfComposition/Palomar/$module.lean"
done
run_gate challenge-nine env LEAN_NUM_THREADS=1 lake env lean \
  FailureOfComposition/Palomar/ChallengeNine.lean
run_gate exact-nine-interface env LEAN_NUM_THREADS=1 lake env lean \
  -DwarningAsError=true --run FailureOfComposition/Palomar/CheckNineInterface.lean
run_gate nine-dependency-route-audit env LEAN_NUM_THREADS=1 lake env lean \
  -DwarningAsError=true FailureOfComposition/Palomar/Checks/NineDependencyAudit.lean
run_gate challenge-src-deps env LEAN_NUM_THREADS=1 lake env lean --src-deps \
  FailureOfComposition/Palomar/ChallengeNine.lean

cd "$repository_root"
run_gate challenge-source-policy env PYTHONDONTWRITEBYTECODE=1 "$palomar_python" \
  scripts/check-palomar-challenge-policy.py --repository "$repository_root" \
  --dependency-checkout "$dependency_checkout" --submission "$submission" \
  --source-deps "$output/challenge-src-deps.stdout" \
  --output "$output/challenge-source-policy.json"
run_gate negative-regressions env LEAN_NUM_THREADS=1 \
  bash scripts/run-palomar-nine-negative.sh "$output/negative"

printf 'PASS all focused cumulative-Nine module-port gates\n'
