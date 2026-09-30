#!/usr/bin/env bash
set -euo pipefail

repository_root=/home/flengyel/src/FailureOfComposition-port
evidence_root="$repository_root/.codex-work/palomar/nine-generated-quotient/20260930T051722Z"
run=$(realpath -m "${1:?explicit Comparator run directory required}")
case "$run" in
  "$evidence_root"/runs/*) ;;
  *) echo "Comparator run is outside the Nine evidence root: $run" >&2; exit 2 ;;
esac
inputs="$evidence_root/inputs/comparator"
prefix=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2
gnu_time="$repository_root/.codex-work/tmp/gnu-time/usr/bin/time"
challenge="$evidence_root/exports/comparator-nine-challenge.ndjson"
solution="$evidence_root/exports/comparator-nine-solution.ndjson"

cp "$inputs/portable-comparator-nine.json" "$run/portable-comparator-nine.json"
cp "$inputs/protected-comparator-nine.json" "$run/protected-comparator-nine.json"
cp "$inputs/identity.json" "$run/identity.json"

python3 "$repository_root/Audit/palomar-nine-generated-quotient-20260930/record_input_hashes.py" \
  "$run/export-hashes-before.json" "$challenge" "$solution" \
  "$run/portable-comparator-nine.json" "$run/protected-comparator-nine.json"

set +e
"$gnu_time" -v -o "$run/time.log" \
  "$prefix/bin/lake" comparator \
  --config "$run/protected-comparator-nine.json" \
  --challenge-from-export "$challenge" \
  --solution-from-export "$solution" \
  >"$run/comparator.log" 2>&1
comparator_status=$?
set -e

python3 "$repository_root/Audit/palomar-nine-generated-quotient-20260930/record_input_hashes.py" \
  "$run/export-hashes-after.json" "$challenge" "$solution" \
  "$run/portable-comparator-nine.json" "$run/protected-comparator-nine.json"
set +e
python3 "$repository_root/Audit/palomar-nine-generated-quotient-20260930/compare_input_hashes.py" \
  "$run/export-hashes-before.json" "$run/export-hashes-after.json" \
  >"$run/export-hash-equality.stdout" 2>"$run/export-hash-equality.stderr"
hash_status=$?
set -e
printf '%s\n' "$hash_status" >"$run/export-hash-equality.exit"
(( comparator_status == 0 )) || exit "$comparator_status"
exit "$hash_status"
