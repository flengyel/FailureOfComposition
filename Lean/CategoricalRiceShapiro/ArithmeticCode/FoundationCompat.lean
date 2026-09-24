/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Compatibility results for Foundation's arithmetic codes

Foundation defines `LO.FirstOrder.Arithmetic.code`, the arithmetic formula
associated with a partial-recursive code `Nat.ArithPart₁.Code k`, together with
its auxiliary formula `codeAux`.  Foundation's own uniqueness statements for
these formulas are dormant source at the recorded revision, so this module
supplies the corresponding active result.

`eval_unique` states that the evaluation relation of an arithmetic code is
functional in every model of `𝗣𝗔⁻`, under an arbitrary assignment.
-/

set_option autoImplicit false

namespace CategoricalRiceShapiro.ArithmeticCode

open Encodable LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic

-- The two proofs below are migrated verbatim from the verified checkpoint;
-- rewriting their `simp` calls as `simp only` is deferred.
set_option linter.flexible false in
private theorem evalAux_unique
    {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {k : ℕ} {c : Nat.ArithPart₁.Code k}
    {v : Fin k → M} {z z' : M}
    (hz :
      Semiformula.Evalf (M := M) (z :> v)
        (LO.FirstOrder.Arithmetic.codeAux c))
    (hz' :
      Semiformula.Evalf (M := M) (z' :> v)
        (LO.FirstOrder.Arithmetic.codeAux c)) :
    z = z' := by
  revert hz hz'
  induction c generalizing z z' <;>
    simp [LO.FirstOrder.Arithmetic.codeAux]
  case zero => rintro rfl rfl; rfl
  case one  => rintro rfl rfl; rfl
  case add  => rintro rfl rfl; rfl
  case mul  => rintro rfl rfl; rfl
  case proj => rintro rfl rfl; rfl
  case equal i j =>
    by_cases hv : v i = v j <;> simp [hv]
    · rintro rfl rfl; rfl
    · rintro rfl rfl; rfl
  case lt i j =>
    by_cases hv : v i < v j <;> simp [hv, -not_lt, ←not_lt]
    · rintro rfl rfl; rfl
    · rintro rfl rfl; rfl
  case comp m n c d ihc ihd =>
    simp [Semiformula.eval_rew, Function.comp_def,
      Matrix.empty_eq, Matrix.comp_vecCons']
    intro w₁ hc₁ hd₁ w₂ hc₂ hd₂
    have hw : w₁ = w₂ := funext fun i => ihd i (hd₁ i) (hd₂ i)
    rcases hw with rfl
    exact ihc hc₁ hc₂
  case rfind c ih =>
    simp [Semiformula.eval_rew, Function.comp_def,
      Matrix.empty_eq, Matrix.comp_vecCons']
    intro h₁ hm₁ h₂ hm₂
    by_contra hzz
    wlog h : z < z' with Hz
    case inr =>
      have hlt : z' < z := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hzz)
      exact Hz (k := k) c ih h₂ hm₂ h₁ hm₁ (Ne.symm hzz) hlt
    have hex : ∃ x, x ≠ 0 ∧
        Semiformula.Evalf (M := M)
          (x :> z :> fun i => v i)
          (LO.FirstOrder.Arithmetic.codeAux c) := hm₂ z h
    rcases hex with ⟨x, xz, hx⟩
    exact xz (ih hx h₁)

set_option linter.flexible false in
theorem eval_unique
    {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {k : ℕ} {c : Nat.ArithPart₁.Code k}
    {v : Fin k → M} {z z' : M}
    (hz :
      Semiformula.Evalb (M := M) (z :> v)
        (LO.FirstOrder.Arithmetic.code c))
    (hz' :
      Semiformula.Evalb (M := M) (z' :> v)
        (LO.FirstOrder.Arithmetic.code c)) :
    z = z' := by
  simp [LO.FirstOrder.Arithmetic.code, Semiformula.eval_rew,
    Matrix.empty_eq, Function.comp_def] at hz hz'
  exact evalAux_unique hz hz'

end CategoricalRiceShapiro.ArithmeticCode
