/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.GraphQuotient
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-!
Graph witnesses for the second-incompleteness obstruction.
-/

set_option autoImplicit false

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment

namespace FailureOfComposition

theorem proofBot_consistency_bridge (T : ArithmeticTheory) [T.Δ₁] :
    𝗣𝗔 ⊢ “(∀ p, ¬!(ProofSearch.proofTarget T ⊥).sigma p) ↔ !T.consistent.val” := by
  apply complete.{0} 𝗣𝗔
  intro V _ _
  haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  simp [models_iff, Theory.consistent, Bootstrapping.Provable]

theorem numeral_nonproof_of_consistency (T : ArithmeticTheory) [T.Δ₁]
    [Consistent T] (n : ℕ) :
    𝗣𝗔 ⊢ (ProofSearch.notProofTarget T ⊥).val/[n] :=
  ProofSearch.numeral_negative T ⊥
    (consistent_iff_unprovable_bot.mp (inferInstance : Consistent T)) n

/-- The second-incompleteness route to noncongruence for functional graphs. -/
theorem graph_noncongruence_via_godel (T : ArithmeticTheory) [T.Δ₁]
    [Consistent T] [𝗣𝗔 ⪯ T] :
    ∃ F I G : ProofSearch.Graph,
      ProofSearch.Functional F ∧ ProofSearch.Functional I ∧ ProofSearch.Functional G ∧
      ProofSearch.Pointwise T F I ∧
      ¬ProofSearch.Pointwise T (ProofSearch.comp F G) (ProofSearch.comp I G) := by
  letI : 𝗜𝚺₁ ⪯ T := WeakerThan.trans (𝓣 := 𝗣𝗔) inferInstance inferInstance
  apply ProofSearch.functional_graph_noncongruence T ⊥ T
  · exact consistent_iff_unprovable_bot.mp (inferInstance : Consistent T)
  · simpa [Theory.consistent] using consistent_unprovable T

theorem pa_graph_noncongruence_via_godel :
    ∃ F I G : ProofSearch.Graph,
      ProofSearch.Functional F ∧ ProofSearch.Functional I ∧ ProofSearch.Functional G ∧
      ProofSearch.Pointwise 𝗣𝗔 F I ∧
      ¬ProofSearch.Pointwise 𝗣𝗔 (ProofSearch.comp F G) (ProofSearch.comp I G) :=
  graph_noncongruence_via_godel 𝗣𝗔

theorem no_graph_quotient_composition_via_godel (T : ArithmeticTheory) [T.Δ₁]
    [Consistent T] [𝗣𝗔 ⪯ T] : ProofSearch.NoQuotientComposition T :=
  ProofSearch.no_quotient_composition_of_graph_noncongruence T
    (graph_noncongruence_via_godel T)

end FailureOfComposition
