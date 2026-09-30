#!/usr/bin/env bash
set -euo pipefail

repository_root=/home/flengyel/src/FailureOfComposition-port
evidence_root="$repository_root/.codex-work/palomar/seven-godel-range/20260930T010330Z"
run=$(realpath -m "${1:?explicit Comparator run directory required}")
case "$run" in
  "$evidence_root"/runs/*) ;;
  *) echo "Comparator run is outside the Seven evidence root: $run" >&2; exit 2 ;;
esac
inputs="$evidence_root/inputs/comparator"
prefix=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2
gnu_time="$repository_root/.codex-work/tmp/gnu-time/usr/bin/time"
challenge="$evidence_root/exports/comparator-seven-challenge.ndjson"
solution="$evidence_root/exports/comparator-seven-solution.ndjson"

cp "$inputs/portable-comparator-seven.json" "$run/portable-comparator-seven.json"
cp "$inputs/protected-comparator-seven.json" "$run/protected-comparator-seven.json"
cp "$inputs/identity.json" "$run/identity.json"

python3 "$repository_root/Audit/palomar-seven-godel-range-20260930/record_input_hashes.py" \
  "$run/export-hashes-before.json" "$challenge" "$solution" \
  "$run/portable-comparator-seven.json" "$run/protected-comparator-seven.json"

set +e
"$gnu_time" -v -o "$run/time.log" \
  "$prefix/bin/lake" comparator \
  --config "$run/protected-comparator-seven.json" \
  --challenge-from-export "$challenge" \
  --solution-from-export "$solution" \
  >"$run/comparator.log" 2>&1
comparator_status=$?
set -e

python3 "$repository_root/Audit/palomar-seven-godel-range-20260930/record_input_hashes.py" \
  "$run/export-hashes-after.json" "$challenge" "$solution" \
  "$run/portable-comparator-seven.json" "$run/protected-comparator-seven.json"
set +e
python3 "$repository_root/Audit/palomar-seven-godel-range-20260930/compare_input_hashes.py" \
  "$run/export-hashes-before.json" "$run/export-hashes-after.json" \
  >"$run/export-hash-equality.stdout" 2>"$run/export-hash-equality.stderr"
hash_status=$?
set -e
printf '%s\n' "$hash_status" >"$run/export-hash-equality.exit"
(( comparator_status == 0 )) || exit "$comparator_status"
exit "$hash_status"
