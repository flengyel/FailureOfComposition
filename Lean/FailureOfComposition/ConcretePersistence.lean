/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ConcreteWitnessGraphs
import FailureOfComposition.MinimizationPersistence
import CategoricalRiceShapiro.Evaluator.PairPersistence
import CategoricalRiceShapiro.Evaluator.CompositionPersistence
import CategoricalRiceShapiro.Evaluator.PrimitiveRecursionPersistence

/-!
Persistence of the repository's concrete evaluator at every standard program
index. The induction is external on the natural-number index. The stage, input,
and output range over an arbitrary model of PA, including its nonstandard
elements. The constructor lemmas discharge every induction case.
-/

set_option autoImplicit false



open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.ConcreteEvaluator

theorem partrecCodeTag_lt_eight (q : ℕ) : partrecCodeTag q < 8 := by
  have hb : ∀ n : ℕ, n.bodd.toNat = n % 2 := fun n => by
    rw [Nat.mod_two_of_bodd]
  simp only [partrecCodeTag, hb]
  split_ifs <;> omega

theorem lt_four_of_partrecCodeTag_lt_four (q : ℕ)
    (hq : partrecCodeTag q < 4) : q < 4 := by
  unfold partrecCodeTag at hq
  split_ifs at hq with h
  · exact h
  · dsimp at hq
    omega

/-- Unconditional persistence for every standard Mathlib program index in
every PA model. No persistence or arithmetization field is a hypothesis. -/
theorem evalnCertificateFormula_natCode_persist
    {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (q : ℕ) :
    ∀ s t u y : M, s ≤ t →
      Semiformula.Evalb ![s, ((q : ℕ) : M), u, y]
        (evalnCertificateFormula : ArithmeticSemisentence 4) →
      Semiformula.Evalb ![t, ((q : ℕ) : M), u, y]
        (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hsmall : partrecCodeTag q < 4
    · exact ConcreteWitnessGraphs.evalnCertificateFormula_natCode_persist_of_lt_four q
        (lt_four_of_partrecCodeTag_lt_four q hsmall)
    have hbound := partrecCodeTag_lt_eight q
    have hcases : partrecCodeTag q = 4 ∨ partrecCodeTag q = 5 ∨
        partrecCodeTag q = 6 ∨ partrecCodeTag q = 7 := by omega
    rcases hcases with h4 | h5 | h6 | h7
    · exact evalnCertificateFormula_natCode_persist_of_tag_four q h4 ih
    · exact evalnCertificateFormula_natCode_persist_of_tag_five q h5 ih
    · exact evalnCertificateFormula_natCode_persist_of_tag_six q h6 ih
    · exact evalnCertificateFormula_natCode_persist_of_tag_seven q h7 ih

end FailureOfComposition.ConcreteEvaluator
