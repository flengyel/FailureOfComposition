#!/usr/bin/env bash
set -euo pipefail

repository_root=/home/flengyel/src/FailureOfComposition-port
evidence_root="$repository_root/.codex-work/palomar/godel-bottleneck/20260927T222925Z"
lean_root="$repository_root/Lean"
toolchain_bin=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin
gnu_time=/usr/bin/time
if [[ ! -x $gnu_time ]]; then
  gnu_time="$repository_root/.codex-work/tmp/gnu-time/usr/bin/time"
fi
label=${1:?export label required}
shift
[[ $# -gt 0 ]] || { printf 'at least one selected declaration is required\n' >&2; exit 2; }
output="$evidence_root/exports/$label.ndjson"

cd "$lean_root"
lean_path=$("$toolchain_bin/lake" env printenv LEAN_PATH)
export LEAN_PATH="$lean_path"
export LEAN_NUM_THREADS=1
export LEAN_ABORT_ON_PANIC=1

{
  printf 'module=FailureOfComposition.Palomar.SolutionThree\n'
  printf 'roots='
  printf '%s ' "$@"
  printf '\n'
  printf 'source_commit=%s\n' "$(git -C "$repository_root" rev-parse HEAD)"
  printf 'leanexport=%s\n' "$toolchain_bin/leanexport"
  printf 'leanexport_sha256=%s\n' "$(sha256sum "$toolchain_bin/leanexport" | cut -d' ' -f1)"
  printf 'lean_path=%s\n' "$lean_path"
} >"$evidence_root/exports/$label.command.txt"

"$gnu_time" -v -o "$evidence_root/exports/$label.time" \
  "$toolchain_bin/leanexport" \
  FailureOfComposition.Palomar.SolutionThree -- \
  Quot Quot.mk Quot.lift Quot.ind \
  "$@" \
  propext Quot.sound Classical.choice \
  Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble \
  Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight \
  String.ofList Char.ofNat List eagerReduce Nat String String.mk Char \
  optParam autoParam semiOutParam outParam \
  >"$output" 2>"$evidence_root/exports/$label.stderr"
