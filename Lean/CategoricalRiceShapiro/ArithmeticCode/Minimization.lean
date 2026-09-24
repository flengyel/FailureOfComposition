/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalRiceShapiro.ArithmeticCode.Basic

/-!
# Unbounded minimization and substitution of a minimized value

Two constructors over the primitives of
`CategoricalRiceShapiro.ArithmeticCode.Basic`.

`codeRfindPos` is the least argument at which a code is positive, expressed
through `Nat.ArithPart₁.Code.rfind`, which searches for a zero.  `codeBind`
substitutes the value of one code for the head argument of another, and is the
idiom in which a minimized value is consumed.

Each construction is accompanied by the theorem that it realizes the intended
function over the natural numbers.  Those `Computes` theorems are the input of
the standard-model bridge, which turns a computation over `ℕ` into evaluation at
standard numerals in an arbitrary model.
-/

set_option autoImplicit false

open Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro.ArithmeticCode

/-- The least argument at which `d` takes a positive value.

`Code.rfind` searches for a zero, so the body is inverted twice: `codePos`
normalises a positive value to `1`, and `codeInv` exchanges `0` and `1`. -/
def codeRfindPos {n : ℕ} (d : Code (n + 1)) : Code n :=
  (codeInv (codePos d)).rfind

/-- Evaluate `dc` with the value of `dg` as its head argument and the ambient
arguments beneath it. -/
def codeBind {n : ℕ} (dg : Code n) (dc : Code (n + 1)) : Code n :=
  dc.comp (Fin.cases dg (fun i => Code.proj i))

/-! ### Standard computations over the natural numbers -/

theorem eval_codeRfindPos {n : ℕ} {d : Code (n + 1)} {f : List.Vector ℕ (n + 1) → ℕ}
    (hd : Computes d f) :
    Code.eval (codeRfindPos d)
      (fun v => Nat.rfind fun m => Part.some (0 < f (m ::ᵥ v))) := by
  have hinv : Computes (codeInv (codePos d)) (fun w => Nat.inv (Nat.pos (f w))) :=
    computes_codeInv (computes_codePos hd)
  have h := Code.eval.rfind (codeInv (codePos d)) (fun w => Nat.inv (Nat.pos (f w))) hinv
  refine eval_of_eq h ?_
  funext v
  congr 1
  funext m
  congr 1
  simp only [Nat.inv, Nat.pos, isEqNat, isLtNat]
  by_cases hz : f (m ::ᵥ v) = 0
  · simp [hz]
  · simp [Nat.pos_of_ne_zero hz]

set_option backward.isDefEq.respectTransparency.types false in
theorem eval_codeBind {n : ℕ} {dg : Code n} {dc : Code (n + 1)}
    {gp : List.Vector ℕ n →. ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hg : Code.eval dg gp) (hc : Computes dc f) :
    Code.eval (codeBind dg dc) (fun v => (gp v).bind (fun x => (f (x ::ᵥ v) : Part ℕ))) := by
  have h := Code.eval.comp dc (Fin.cases dg (fun i => Code.proj i))
    (fun w => (f w : Part ℕ))
    (Fin.cases gp (fun i v => ((v.get i : ℕ) : Part ℕ)))
    hc
    (by
      intro i
      refine Fin.cases ?_ ?_ i
      · exact hg
      · intro j; exact Code.eval.proj j)
  refine eval_of_eq h ?_
  funext v
  simp [List.Vector.mOfFn, Part.bind_assoc]

end CategoricalRiceShapiro.ArithmeticCode
