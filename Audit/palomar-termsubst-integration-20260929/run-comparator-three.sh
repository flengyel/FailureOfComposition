#!/usr/bin/env bash
set -euo pipefail

repository_root=/home/flengyel/src/FailureOfComposition-port
evidence_root="$repository_root/.codex-work/palomar/termsubst-integration/20260929T062653Z"
run="$evidence_root/runs/comparator-three-termsubst-01"
inputs="$evidence_root/analysis/comparator-inputs"
prefix=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2
gnu_time="$repository_root/.codex-work/tmp/gnu-time/usr/bin/time"
challenge="$evidence_root/exports/comparator-three-challenge.ndjson"
solution="$evidence_root/exports/comparator-three-solution.ndjson"

cp "$inputs/portable-comparator-three.json" "$run/portable-comparator-three.json"
cp "$inputs/protected-comparator-three.json" "$run/protected-comparator-three.json"
cp "$inputs/identity.json" "$run/identity.json"

exec "$gnu_time" -v -o "$run/time.log" \
  "$prefix/bin/lake" comparator \
  --config "$run/protected-comparator-three.json" \
  --challenge-from-export "$challenge" \
  --solution-from-export "$solution" \
  >"$run/comparator.log" 2>&1
