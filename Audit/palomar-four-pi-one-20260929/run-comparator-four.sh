#!/usr/bin/env bash
set -euo pipefail

repository_root=/home/flengyel/src/FailureOfComposition-port
evidence_root="$repository_root/.codex-work/palomar/four-pi-one/20260929T203116Z"
run="$evidence_root/runs/comparator-four-01"
inputs="$evidence_root/inputs/comparator"
prefix=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2
gnu_time="$repository_root/.codex-work/tmp/gnu-time/usr/bin/time"
challenge="$evidence_root/exports/comparator-four-challenge.ndjson"
solution="$evidence_root/exports/comparator-four-solution.ndjson"

cp "$inputs/portable-comparator-four.json" "$run/portable-comparator-four.json"
cp "$inputs/protected-comparator-four.json" "$run/protected-comparator-four.json"
cp "$inputs/identity.json" "$run/identity.json"

exec "$gnu_time" -v -o "$run/time.log" \
  "$prefix/bin/lake" comparator \
  --config "$run/protected-comparator-four.json" \
  --challenge-from-export "$challenge" \
  --solution-from-export "$solution" \
  >"$run/comparator.log" 2>&1
