#!/usr/bin/env bash
set -euo pipefail

repository_root=/home/flengyel/src/FailureOfComposition-port
evidence_root="$repository_root/.codex-work/palomar/six-weak-totality/20260929T234633Z"
run="$evidence_root/runs/comparator-six-01"
inputs="$evidence_root/inputs/comparator"
prefix=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2
gnu_time="$repository_root/.codex-work/tmp/gnu-time/usr/bin/time"
challenge="$evidence_root/exports/comparator-six-challenge.ndjson"
solution="$evidence_root/exports/comparator-six-solution.ndjson"

cp "$inputs/portable-comparator-six.json" "$run/portable-comparator-six.json"
cp "$inputs/protected-comparator-six.json" "$run/protected-comparator-six.json"
cp "$inputs/identity.json" "$run/identity.json"

python3 "$repository_root/Audit/palomar-six-weak-totality-20260929/record_input_hashes.py" \
  "$run/export-hashes-before.json" "$challenge" "$solution" \
  "$run/portable-comparator-six.json" "$run/protected-comparator-six.json"

set +e
"$gnu_time" -v -o "$run/time.log" \
  "$prefix/bin/lake" comparator \
  --config "$run/protected-comparator-six.json" \
  --challenge-from-export "$challenge" \
  --solution-from-export "$solution" \
  >"$run/comparator.log" 2>&1
comparator_status=$?
set -e

python3 "$repository_root/Audit/palomar-six-weak-totality-20260929/record_input_hashes.py" \
  "$run/export-hashes-after.json" "$challenge" "$solution" \
  "$run/portable-comparator-six.json" "$run/protected-comparator-six.json"
set +e
python3 "$repository_root/Audit/palomar-six-weak-totality-20260929/compare_input_hashes.py" \
  "$run/export-hashes-before.json" "$run/export-hashes-after.json" \
  >"$run/export-hash-equality.stdout" 2>"$run/export-hash-equality.stderr"
hash_status=$?
set -e
printf '%s\n' "$hash_status" >"$run/export-hash-equality.exit"
(( comparator_status == 0 )) || exit "$comparator_status"
exit "$hash_status"
