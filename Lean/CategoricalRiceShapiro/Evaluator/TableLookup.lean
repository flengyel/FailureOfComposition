/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalRiceShapiro.ArithmeticCode.EncodedList
import CategoricalRiceShapiro.ArithmeticCode.Pairing

/-!
# The table-lookup code

`codeTableLookup dtable dk dq dn` reads entry `dn` of the row of the encoded
table `dtable` indexed by the Cantor pair of `dk` and `dq`.

A row is stored as an encoded `Option (List (Option ℕ))`, so the row read out
of the table is an encoded `Option (Option ℕ)`, and the two layers are
flattened by `codeOptionJoin`.  Subtracting `1` before the second lookup
replaces an absent row by the empty row.

The literal construction matters: later results reason about this code itself,
not only about the function it realizes over the natural numbers, so it must not
be replaced by an extensionally equivalent one.
-/

set_option autoImplicit false

open Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro.Evaluator

open CategoricalRiceShapiro.ArithmeticCode

/-- Flatten an encoded `Option (Option ℕ)` to an encoded `Option ℕ`. -/
private def codeOptionJoin {r : ℕ} (d : Code r) : Code r :=
  codeSub d (codeConst 1)

/-- Entry `dn` of the row of `dtable` indexed by the pair of `dk` and `dq`. -/
def codeTableLookup {r : ℕ}
    (dtable dk dq dn : Code r) : Code r :=
  codeOptionJoin
    (codeListGet?
      (codeSub
        (codeListGet? dtable (codePair dk dq))
        (codeConst 1))
      dn)

/-- The table-lookup code written out without the private flattening helper. -/
theorem codeTableLookup_eq {r : ℕ} (dtable dk dq dn : Code r) :
    codeTableLookup dtable dk dq dn =
      codeSub
        (codeListGet?
          (codeSub (codeListGet? dtable (codePair dk dq)) (codeConst 1))
          dn)
        (codeConst 1) := rfl

end CategoricalRiceShapiro.Evaluator
