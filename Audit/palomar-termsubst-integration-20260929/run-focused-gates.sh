#!/usr/bin/env bash
set -euo pipefail

repository_root=/home/flengyel/src/FailureOfComposition-port
evidence_root="$repository_root/.codex-work/palomar/termsubst-integration/20260929T062653Z"
analysis="$evidence_root/analysis"
lean_root="$repository_root/Lean"
lake=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lake
results="$analysis/focused-gates.tsv"

[[ ! -e $results ]] || {
  printf 'focused gate result already exists: %s\n' "$results" >&2
  exit 2
}

run_gate() {
  local label=$1
  shift
  local started finished status
  started=$(date +%s)
  {
    printf 'cwd=%q\n' "$PWD"
    printf 'command='
    printf '%q ' "$@"
    printf '\n'
  } >"$analysis/$label.command"
  set +e
  "$@" >"$analysis/$label.stdout" 2>"$analysis/$label.stderr"
  status=$?
  set -e
  finished=$(date +%s)
  printf '%s\t%s\t%s\n' "$label" "$status" "$((finished - started))" >>"$results"
  (( status == 0 )) || {
    printf 'focused gate failed: %s (status %s)\n' "$label" "$status" >&2
    return "$status"
  }
}

cd "$lean_root"
printf 'gate\texit_status\telapsed_seconds\n' >"$results"

run_gate strict-godel-bridge \
  "$lake" env lean -DwarningAsError=true \
  FailureOfComposition/Palomar/GodelQuotientBridge.lean
run_gate strict-solution-three \
  "$lake" env lean -DwarningAsError=true \
  FailureOfComposition/Palomar/SolutionThree.lean
run_gate exact-three-interface \
  "$lake" env lean -DwarningAsError=true --run \
  FailureOfComposition/Palomar/CheckThreeInterface.lean
run_gate challenge-three \
  "$lake" env lean FailureOfComposition/Palomar/ChallengeThree.lean

set +e
source_started=$(date +%s)
"$lake" env lean --src-deps FailureOfComposition/Palomar/ChallengeThree.lean \
  >"$analysis/challenge-three-source-deps.txt" \
  2>"$analysis/challenge-three-source-deps.stderr"
status=$?
source_finished=$(date +%s)
set -e
printf '%s\t%s\t%s\n' challenge-three-source-deps "$status" \
  "$((source_finished - source_started))" >>"$results"
(( status == 0 )) || exit "$status"

run_gate challenge-three-source-policy \
  /usr/bin/python3 "$analysis/run_source_policy.py"
run_gate three-dependency-route-audit \
  "$lake" env lean "$analysis/ThreeDependencyAudit.lean"
run_gate checker-negative-regressions \
  /usr/bin/bash "$evidence_root/run-negative-checks.sh"
run_gate portable-config \
  /usr/bin/python3 "$analysis/validate_three_config.py" \
  "$lean_root/FailureOfComposition/Palomar/comparator-three.json"

{
  wc -c FailureOfComposition/Palomar/ChallengeThree.lean
  wc -l FailureOfComposition/Palomar/ChallengeThree.lean
  sha256sum FailureOfComposition/Palomar/ChallengeThree.lean \
    FailureOfComposition/Palomar/SolutionThree.lean \
    FailureOfComposition/Palomar/comparator-three.json \
    FailureOfComposition/Palomar/CheckThreeInterface.lean
} >"$analysis/three-input-identities.txt"

printf 'PASS all focused Three gates\n'
