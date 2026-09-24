/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ProgramIndices

/-!
Representation transport under the manuscript's explicit realization laws.
The translations are selected by classical choice and no effective compiler
between arbitrary arithmetizations is asserted. They induce equivalences of
quotient sets, not functors between categories with an assumed composition.
-/

set_option autoImplicit false



open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace FailureOfComposition.ArithmetizationTransport
open ProofSearch ProgramIndices
noncomputable section

/-- Select a target index with a PA-provably equivalent source graph. -/
def translate (A B : Arithmetization) (e : ℕ) : ℕ :=
  Classical.choose (B.realization (A.graph e) (A.functional e))

theorem translate_uniform (A B : Arithmetization) (e : ℕ) :
    Uniform 𝗣𝗔 (B.graph (translate A B e)) (A.graph e) :=
  Classical.choose_spec (B.realization (A.graph e) (A.functional e))

theorem translate_pointwise_iff (A B : Arithmetization)
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (e f : ℕ) :
    PointwiseIndex B T (translate A B e) (translate A B f) ↔
      PointwiseIndex A T e f := by
  rw [pointwiseIndex_iff,pointwiseIndex_iff]
  have eqv := pointwise_equivalence T
  have he := uniform_to_pointwise T (translate_uniform A B e)
  have hf := uniform_to_pointwise T (translate_uniform A B f)
  exact ⟨fun h => eqv.trans (eqv.symm he) (eqv.trans h hf),
    fun h => eqv.trans he (eqv.trans h (eqv.symm hf))⟩

theorem translate_roundtrip (A B : Arithmetization)
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (e : ℕ) :
    PointwiseIndex A T (translate B A (translate A B e)) e := by
  apply (pointwiseIndex_iff A T _ _).mpr
  exact (pointwise_equivalence T).trans
    (uniform_to_pointwise T (translate_uniform B A (translate A B e)))
    (uniform_to_pointwise T (translate_uniform A B e))

/-- Preservation of composition is stated on representative classes, without
assuming composition is well-defined on either quotient. -/
theorem translate_composition (A B : Arithmetization)
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (e f : ℕ) :
    PointwiseIndex B T (translate A B (A.compIndex e f))
      (B.compIndex (translate A B e) (translate A B f)) := by
  apply (pointwiseIndex_iff B T _ _).mpr
  have eqv := pointwise_equivalence T
  have hl := eqv.trans
    (uniform_to_pointwise T (translate_uniform A B (A.compIndex e f)))
    (uniform_to_pointwise T (A.composition e f))
  have hr := eqv.trans
    (uniform_to_pointwise T (B.composition (translate A B e) (translate A B f)))
    (uniform_to_pointwise T (uniform_comp (translate_uniform A B e) (translate_uniform A B f)))
  exact eqv.trans hl (eqv.symm hr)

/-- The pointwise-provability quotient sets are equivalent. -/
def quotientEquiv (A B : Arithmetization) (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    Quotient (indexSetoid A T) ≃ Quotient (indexSetoid B T) where
  toFun := Quotient.map (translate A B)
    (fun {e f} h => (translate_pointwise_iff A B T e f).mpr h)
  invFun := Quotient.map (translate B A)
    (fun {e f} h => (translate_pointwise_iff B A T e f).mpr h)
  left_inv q := Quotient.inductionOn q fun e =>
    Quotient.sound (translate_roundtrip A B T e)
  right_inv q := Quotient.inductionOn q fun e =>
    Quotient.sound (translate_roundtrip B A T e)

@[simp] theorem quotientEquiv_mk (A B : Arithmetization)
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (e : ℕ) :
    quotientEquiv A B T (Quotient.mk (indexSetoid A T) e) =
      Quotient.mk (indexSetoid B T) (translate A B e) := rfl

theorem quotientEquiv_composition (A B : Arithmetization)
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (e f : ℕ) :
    quotientEquiv A B T (Quotient.mk (indexSetoid A T) (A.compIndex e f)) =
      Quotient.mk (indexSetoid B T)
        (B.compIndex (translate A B e) (translate A B f)) :=
  Quotient.sound (translate_composition A B T e f)

end
end FailureOfComposition.ArithmetizationTransport
