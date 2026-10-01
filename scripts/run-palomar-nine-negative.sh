#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repository_root=$(CDPATH= cd -- "$script_dir/.." && pwd)
lean_root="$repository_root/Lean"
output=$(realpath -m "${1:?usage: run-palomar-nine-negative.sh OUTPUT_DIRECTORY}")
checker=FailureOfComposition/Palomar/CheckNineInterface.lean

mkdir -p "$output"
cd "$lean_root"
lean_bin=$(lean --print-prefix)/bin/lean
lake_path=$(lake env printenv LEAN_PATH)
fixture_build="$output/olean"
fixture_module_dir="$fixture_build/FailureOfComposition/Palomar/Tests"
mkdir -p "$fixture_module_dir"
fixture_path="$fixture_build:$lake_path"

env LEAN_PATH="$fixture_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$lean_root" \
  -o "$fixture_module_dir/NineResultNegativeChallenge.olean" \
  FailureOfComposition/Palomar/Tests/NineResultNegativeChallenge.lean
env LEAN_PATH="$fixture_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$lean_root" \
  -o "$fixture_module_dir/NineResultNegativeSolution.olean" \
  FailureOfComposition/Palomar/Tests/NineResultNegativeSolution.lean

env LEAN_PATH="$fixture_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$lean_root" --run "$checker" --negative-shared-definition \
  FailureOfComposition.Palomar.Tests.NineResultNegativeChallenge \
  FailureOfComposition.Palomar.Tests.NineResultNegativeSolution \
  NineResultNegative.selected NineResultNegative.shared \
  >"$output/changed-definition.stdout" 2>"$output/changed-definition.stderr"
env LEAN_PATH="$lake_path" LEAN_NUM_THREADS=1 \
  "$lean_bin" --root="$lean_root" --run "$checker" --negative-selection-count \
  >"$output/incomplete-selection.stdout" 2>"$output/incomplete-selection.stderr"

check_rejected_override() {
  local label=$1 left=$2 right=$3 status
  set +e
  env LEAN_PATH="$lake_path" LEAN_NUM_THREADS=1 \
    "$lean_bin" --root="$lean_root" --run "$checker" "$left" "$right" \
    >"$output/${label}.stdout" 2>"$output/${label}.stderr"
  status=$?
  set -e
  (( status != 0 )) || {
    printf '%s override was unexpectedly accepted\n' "$label" >&2
    return 1
  }
  grep -q "accepts no module overrides" "$output/${label}.stderr"
  printf '%s\n' "$status" >"$output/${label}.exit"
}

check_rejected_override legacy-selection \
  FailureOfComposition.Palomar.Challenge FailureOfComposition.Palomar.Solution
for stage in One Two Three Four Five Six Seven Eight; do
  lower=${stage,,}
  check_rejected_override "$lower-only-selection" \
    "FailureOfComposition.Palomar.Challenge$stage" \
    "FailureOfComposition.Palomar.Solution$stage"
done

env LEAN_NUM_THREADS=1 lake build \
  FailureOfComposition.Palomar.Tests.NineWrongRouteSolution
env LEAN_NUM_THREADS=1 lake env lean \
  FailureOfComposition/Palomar/Tests/NineWrongRouteAudit.lean \
  >"$output/wrong-route.stdout" 2>"$output/wrong-route.stderr"
grep -q "PASS exact-type wrong-route fixture is rejected" "$output/wrong-route.stdout"

python3 - "$repository_root/Lean/FailureOfComposition/Palomar/comparator-nine.json" \
  "$output/eight-only.json" <<'PY'
import json
import pathlib
import sys

source = pathlib.Path(sys.argv[1])
target = pathlib.Path(sys.argv[2])
value = json.loads(source.read_text(encoding="utf-8"))
value["theorem_names"] = value["theorem_names"][:-1]
target.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
PY
set +e
python3 "$repository_root/scripts/validate-palomar-nine-config.py" \
  "$output/eight-only.json" \
  >"$output/eight-only-config.stdout" 2>"$output/eight-only-config.stderr"
status=$?
set -e
(( status != 0 )) || {
  printf 'Eight-only configuration was unexpectedly accepted\n' >&2
  exit 1
}
grep -q "nine-result theorem selection or order is wrong" \
  "$output/eight-only-config.stderr"
printf '%s\n' "$status" >"$output/eight-only-config.exit"

printf 'PASS Nine negatives reject changed bodies, incomplete/legacy selections, an Eight-only config, and the exact-type wrong route\n'
