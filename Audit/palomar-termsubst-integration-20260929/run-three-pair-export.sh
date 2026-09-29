#!/usr/bin/env bash
set -euo pipefail

repository_root=/home/flengyel/src/FailureOfComposition-port
evidence_root="$repository_root/.codex-work/palomar/termsubst-integration/20260929T062653Z"
lean_root="$repository_root/Lean"
prefix=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2
leanexport="$prefix/bin/leanexport"
challenge="$evidence_root/exports/comparator-three-challenge.ndjson"
solution="$evidence_root/exports/comparator-three-solution.ndjson"
identity="$evidence_root/analysis/comparator-three-export-command.txt"

[[ ! -e $challenge && ! -e $solution ]] || {
  printf 'stable Comparator exports already exist\n' >&2
  exit 2
}

cd "$lean_root"
export LEAN_PATH
LEAN_PATH=$("$prefix/bin/lake" env printenv LEAN_PATH)
export LEAN_NUM_THREADS=1
export LEAN_ABORT_ON_PANIC=1

roots=(
  Quot Quot.mk Quot.lift Quot.ind
  FailureOfComposition.Palomar.obstruction_four_properties
  FailureOfComposition.Palomar.no_quotient_composition_productive
  FailureOfComposition.Palomar.no_quotient_composition_godel
  propext Quot.sound Classical.choice
  Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble
  Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList
  Char.ofNat List eagerReduce Nat String String.mk Char
  optParam autoParam semiOutParam outParam
)

{
  printf 'source_commit=%s\n' "$(git -C "$repository_root" rev-parse HEAD)"
  printf 'foundation_revision=%s\n' "$(git -C "$lean_root/.lake/packages/Foundation" rev-parse HEAD)"
  printf 'leanexport=%s\n' "$leanexport"
  printf 'leanexport_sha256=%s\n' "$(sha256sum "$leanexport" | cut -d' ' -f1)"
  printf 'lean_path=%s\n' "$LEAN_PATH"
  printf 'root_order=builtin_targets,theorem_names,permitted_axioms,primitive_targets,definition_names\n'
  printf 'challenge_command='
  printf '%q ' "$leanexport" FailureOfComposition.Palomar.ChallengeThree -- "${roots[@]}"
  printf '\nsolution_command='
  printf '%q ' "$leanexport" FailureOfComposition.Palomar.SolutionThree -- "${roots[@]}"
  printf '\n'
} >"$identity"

"$leanexport" FailureOfComposition.Palomar.ChallengeThree -- "${roots[@]}" >"$challenge"
"$leanexport" FailureOfComposition.Palomar.SolutionThree -- "${roots[@]}" >"$solution"

/usr/bin/python3 "$evidence_root/analysis/export_stats.py" "$challenge" \
  "$evidence_root/analysis/comparator-three-challenge-stats.json"
/usr/bin/python3 "$evidence_root/analysis/export_stats.py" "$solution" \
  "$evidence_root/analysis/comparator-three-solution-stats.json"
