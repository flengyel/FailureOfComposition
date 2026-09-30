#!/usr/bin/env bash
set -euo pipefail

repository_root=/home/flengyel/src/FailureOfComposition-port
lean_root="$repository_root/Lean"
audit_root="$repository_root/Audit/palomar-nine-generated-quotient-20260930"
output=$(realpath -m "${1:?usage: run-focused-gates.sh OUTPUT_DIRECTORY}")
lake=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lake
results="$output/focused-gates.tsv"

mkdir -p "$output"
[[ ! -e $results ]] || { printf 'result already exists: %s\n' "$results" >&2; exit 2; }

run_gate() {
  local label=$1
  shift
  local started status
  started=$(date +%s)
  {
    printf 'cwd=%q\n' "$PWD"
    printf 'command='
    printf '%q ' "$@"
    printf '\n'
  } >"$output/$label.command"
  set +e
  timeout --signal=TERM --kill-after=30s 180s "$@" \
    >"$output/$label.stdout" 2>"$output/$label.stderr"
  status=$?
  set -e
  printf '%s\t%s\t%s\n' "$label" "$status" "$(( $(date +%s) - started ))" >>"$results"
  (( status == 0 )) || { printf 'gate failed: %s\n' "$label" >&2; return "$status"; }
}

printf 'gate\texit_status\telapsed_seconds\n' >"$results"
cd "$lean_root"
run_gate strict-arithmetic-interface env LEAN_NUM_THREADS=1 "$lake" env lean \
  -DwarningAsError=true FailureOfComposition/Palomar/ArithmeticInterface.lean
run_gate strict-evaluator-interface env LEAN_NUM_THREADS=1 "$lake" env lean \
  -DwarningAsError=true FailureOfComposition/Palomar/EvaluatorInterface.lean
run_gate strict-generated-interface env LEAN_NUM_THREADS=1 "$lake" env lean \
  -DwarningAsError=true FailureOfComposition/Palomar/GeneratedCongruenceInterface.lean
run_gate strict-generated-bridge env LEAN_NUM_THREADS=1 "$lake" env lean \
  -DwarningAsError=true FailureOfComposition/Palomar/GeneratedCongruenceBridge.lean
run_gate strict-generated-quotient-interface env LEAN_NUM_THREADS=1 "$lake" env lean \
  -DwarningAsError=true FailureOfComposition/Palomar/GeneratedQuotientInterface.lean
run_gate strict-generated-quotient-bridge env LEAN_NUM_THREADS=1 "$lake" env lean \
  -DwarningAsError=true FailureOfComposition/Palomar/GeneratedQuotientBridge.lean
run_gate strict-weak-totality-bridge env LEAN_NUM_THREADS=1 "$lake" env lean \
  -DwarningAsError=true FailureOfComposition/Palomar/WeakTotalityBridge.lean
run_gate strict-range-interface env LEAN_NUM_THREADS=1 "$lake" env lean \
  -DwarningAsError=true FailureOfComposition/Palomar/RangeInterface.lean
run_gate strict-range-bridge env LEAN_NUM_THREADS=1 "$lake" env lean \
  -DwarningAsError=true FailureOfComposition/Palomar/RangeBridge.lean
run_gate strict-range-productive-bridge env LEAN_NUM_THREADS=1 "$lake" env lean \
  -DwarningAsError=true FailureOfComposition/Palomar/RangeProductiveBridge.lean
run_gate strict-solution-nine env LEAN_NUM_THREADS=1 "$lake" env lean \
  -DwarningAsError=true FailureOfComposition/Palomar/SolutionNine.lean
run_gate challenge-nine env LEAN_NUM_THREADS=1 "$lake" env lean \
  FailureOfComposition/Palomar/ChallengeNine.lean
run_gate exact-nine-interface env LEAN_NUM_THREADS=1 "$lake" env lean \
  -DwarningAsError=true --run FailureOfComposition/Palomar/CheckNineInterface.lean
run_gate preserve-eight-contracts env LEAN_NUM_THREADS=1 "$lake" env lean \
  -DwarningAsError=true --run FailureOfComposition/Palomar/CheckNinePreservesEight.lean
run_gate nine-dependency-route-audit env LEAN_NUM_THREADS=1 "$lake" env lean \
  -DwarningAsError=true "$audit_root/NineDependencyAudit.lean"

cd "$repository_root"
run_gate checker-negative-regressions env LEAN_NUM_THREADS=1 /usr/bin/bash \
  "$audit_root/run-negative-checks.sh" "$output/negative"
run_gate portable-config env PYTHONDONTWRITEBYTECODE=1 /usr/bin/python3 \
  "$audit_root/validate_nine_config.py" \
  "$lean_root/FailureOfComposition/Palomar/comparator-nine.json"

printf 'PASS all focused cumulative Nine gates\n'
