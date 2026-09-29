#!/usr/bin/env bash
set -euo pipefail

module=FailureOfComposition.Palomar.SolutionThree
root=FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_2
toolchain=${LEAN_TOOLCHAIN_PREFIX:?set LEAN_TOOLCHAIN_PREFIX to the pinned Lean prefix}
output=${1:?output NDJSON path required}

"$toolchain/bin/leanexport" "$module" -- \
  Quot Quot.mk Quot.lift Quot.ind \
  "$root" \
  propext Quot.sound Classical.choice \
  Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble \
  Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight \
  String.ofList Char.ofNat List eagerReduce Nat String String.mk Char \
  optParam autoParam semiOutParam outParam >"$output"

