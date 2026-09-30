#!/usr/bin/env bash
set -euo pipefail

repository_root=/home/flengyel/src/FailureOfComposition-port
evidence_root="$repository_root/.codex-work/palomar/seven-godel-range/20260930T010330Z"
lean_root="$repository_root/Lean"
prefix=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2
leanexport="$prefix/bin/leanexport"
challenge="$evidence_root/exports/comparator-seven-challenge.ndjson"
solution="$evidence_root/exports/comparator-seven-solution.ndjson"
identity="$evidence_root/logs/comparator-seven-export-command.txt"

mkdir -p "$evidence_root/exports"
[[ ! -e $challenge && ! -e $solution ]] || { echo "stable Seven exports already exist" >&2; exit 2; }

cd "$lean_root"
export LEAN_PATH
LEAN_PATH=$("$prefix/bin/lake" env printenv LEAN_PATH)
export LEAN_NUM_THREADS=1 LEAN_ABORT_ON_PANIC=1
roots=(
  Quot Quot.mk Quot.lift Quot.ind
  FailureOfComposition.Palomar.obstruction_four_properties
  FailureOfComposition.Palomar.no_quotient_composition_productive
  FailureOfComposition.Palomar.no_quotient_composition_godel
  FailureOfComposition.Palomar.pi_one_characterization
  FailureOfComposition.Palomar.generated_congruence_classification
  FailureOfComposition.Palomar.weak_totality_counterexample
  FailureOfComposition.Palomar.range_counterexample_godel
  propext Quot.sound Classical.choice
  Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble
  Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList
  Char.ofNat List eagerReduce Nat String String.mk Char
  optParam autoParam semiOutParam outParam
)

{
  printf 'source_commit=%s\nfoundation_revision=%s\n' \
    "$(git -C "$repository_root" rev-parse HEAD)" \
    "$(git -C "$lean_root/.lake/packages/Foundation" rev-parse HEAD)"
  printf 'leanexport=%s\nleanexport_sha256=%s\n' "$leanexport" \
    "$(sha256sum "$leanexport" | cut -d' ' -f1)"
  printf 'lean_path=%s\n' "$LEAN_PATH"
  printf 'root_order=builtin_targets,theorem_names,permitted_axioms,primitive_targets,definition_names\n'
  printf 'challenge_command='; printf '%q ' "$leanexport" FailureOfComposition.Palomar.ChallengeSeven -- "${roots[@]}"; printf '\n'
  printf 'solution_command='; printf '%q ' "$leanexport" FailureOfComposition.Palomar.SolutionSeven -- "${roots[@]}"; printf '\n'
} >"$identity"

"$leanexport" FailureOfComposition.Palomar.ChallengeSeven -- "${roots[@]}" >"$challenge"
"$leanexport" FailureOfComposition.Palomar.SolutionSeven -- "${roots[@]}" >"$solution"
/usr/bin/python3 "$repository_root/Audit/palomar-termsubst-integration-20260929/export_stats.py" \
  "$challenge" "$evidence_root/logs/comparator-seven-challenge-stats.json"
/usr/bin/python3 "$repository_root/Audit/palomar-termsubst-integration-20260929/export_stats.py" \
  "$solution" "$evidence_root/logs/comparator-seven-solution-stats.json"
