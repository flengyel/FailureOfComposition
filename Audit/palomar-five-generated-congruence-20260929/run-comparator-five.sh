#!/usr/bin/env bash
set -euo pipefail

repository_root=/home/flengyel/src/FailureOfComposition-port
evidence_root="$repository_root/.codex-work/palomar/five-generated-congruence/20260929T224214Z"
run="$evidence_root/runs/comparator-five-01"
inputs="$evidence_root/inputs/comparator"
prefix=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2
gnu_time="$repository_root/.codex-work/tmp/gnu-time/usr/bin/time"
challenge="$evidence_root/exports/comparator-five-challenge.ndjson"
solution="$evidence_root/exports/comparator-five-solution.ndjson"

cp "$inputs/portable-comparator-five.json" "$run/portable-comparator-five.json"
cp "$inputs/protected-comparator-five.json" "$run/protected-comparator-five.json"
cp "$inputs/identity.json" "$run/identity.json"

exec "$gnu_time" -v -o "$run/time.log" \
  "$prefix/bin/lake" comparator \
  --config "$run/protected-comparator-five.json" \
  --challenge-from-export "$challenge" \
  --solution-from-export "$solution" \
  >"$run/comparator.log" 2>&1
