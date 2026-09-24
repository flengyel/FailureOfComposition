/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.GodelGraph
import FailureOfComposition.CraigPresentation
import FailureOfComposition.RangeWitness

/-!
The manuscript's range obstruction via Gödel's second incompleteness theorem.
A program that outputs zero on codes of proofs of contradiction agrees
pointwise with the empty program. Its range at zero encodes the existence
of a contradiction proof.
Craig's presentation removes the Delta-one axiom-presentation hypothesis.
-/

set_option autoImplicit false

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition.ConcreteIndices

open ConcreteEmptyGraph

/-- The positive proof-of-contradiction predicate of the chosen presentation. -/
noncomputable def proofBotPredicate (T : ArithmeticTheory) [T.Δ₁] : 𝚺₁.Semisentence 1 :=
  (ProofSearch.proofTarget T ⊥).sigma

/-- Consistency refutes each fixed proof code in PA, including the Sigma-one form. -/
theorem proofBotPredicate_numeral_refutation
    (T : ArithmeticTheory) [T.Δ₁] [Consistent T] (n : ℕ) :
    𝗣𝗔 ⊢ ∼(proofBotPredicate T).val/[n] := by
  have h : 𝗣𝗔 ⊢ (ProofSearch.notProofTarget T ⊥).val/[n] 🡒
      ∼(proofBotPredicate T).val/[n] := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
    simp [models_iff, Semiformula.eval_substs, proofBotPredicate]
  exact mdp! h (numeral_nonproof_of_consistency T n)

/-- Universal absence of contradiction proofs would establish the theory's
own consistency, which Gödel's second incompleteness theorem excludes. -/
theorem proofBotPredicate_absence_unprovable
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔 ⪯ T] [Consistent T] :
    T ⊬ absenceSentence (proofBotPredicate T) := by
  haveI : 𝗜𝚺₁ ⪯ T := WeakerThan.trans (𝓣 := 𝗣𝗔) inferInstance inferInstance
  have hb : 𝗣𝗔 ⊢ absenceSentence (proofBotPredicate T) 🡘 T.consistent.val := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    have hBridge := consequence_iff.mp (Theory.Proof.sound
      (proofBot_consistency_bridge T)) M inferInstance
    simpa [models_iff, absenceSentence, proofBotPredicate] using hBridge
  intro h
  apply consistent_unprovable T
  have hbT : T ⊢ absenceSentence (proofBotPredicate T) 🡘 T.consistent.val :=
    WeakerThan.pbl hb
  cl_prover [h, hbT]

/-- The manuscript's zero-output proof probe is pointwise empty, but its
range program is not pointwise equal to the empty program's range. -/
theorem range_counterexample_via_godel
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔 ⪯ T] [Consistent T] :
    PointwiseIndex T (probeIndex (proofBotPredicate T)) concreteEmptyIndex ∧
      ¬PointwiseIndex T (rangeIndex (probeIndex (proofBotPredicate T)))
        (rangeIndex concreteEmptyIndex) :=
  range_counterexample_of_instance_refutations T (proofBotPredicate T)
    (proofBotPredicate_numeral_refutation T) (proofBotPredicate_absence_unprovable T)

/-- A quotient range operation would contradict the concrete Gödel-II witnesses. -/
theorem no_index_quotient_range_via_godel
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔 ⪯ T] [Consistent T] :
    NoIndexQuotientRange T :=
  no_quotient_range_of_instance_refutations T (proofBotPredicate T)
    (proofBotPredicate_numeral_refutation T) (proofBotPredicate_absence_unprovable T)

/-- Deductive equivalence transports the same natural-number witnesses. The
chosen range indices depend on their programs, not on the theory presentation. -/
theorem range_counterexample_of_equivalent_presentation
    (S T : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ T] [Consistent T]
    (hST : S ⪯ T) (hTS : T ⪯ S) :
    ∃ u : ℕ, PointwiseIndex T u concreteEmptyIndex ∧
      ¬PointwiseIndex T (rangeIndex u) (rangeIndex concreteEmptyIndex) := by
  letI : S ⪯ T := hST
  letI : T ⪯ S := hTS
  haveI : 𝗣𝗔 ⪯ S := WeakerThan.trans (𝓣 := T) inferInstance hTS
  haveI : Consistent S := consistent_iff_unprovable_bot.mpr fun h =>
    consistent_iff_unprovable_bot.mp (inferInstance : Consistent T) (WeakerThan.pbl h)
  obtain ⟨hu, hrange⟩ := range_counterexample_via_godel S
  refine ⟨probeIndex (proofBotPredicate S), fun n => WeakerThan.pbl (hu n), ?_⟩
  intro h
  exact hrange (fun n => WeakerThan.pbl (h n))

/-- For every consistent recursively axiomatized extension of PA, range
assignment fails to preserve the external pointwise relation. -/
theorem range_counterexample_of_re_axioms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ∃ u : ℕ, PointwiseIndex T u concreteEmptyIndex ∧
      ¬PointwiseIndex T (rangeIndex u) (rangeIndex concreteEmptyIndex) := by
  obtain ⟨S, ⟨hS⟩, hST, hTS⟩ := CraigPresentation.exists_craig_presentation T hT
  letI : S.Δ₁ := hS
  exact range_counterexample_of_equivalent_presentation S T hST hTS

/-- The range assignment does not descend to the quotient in the manuscript's
full recursively enumerable axiom setting. -/
theorem no_index_quotient_range_of_re_axioms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) : NoIndexQuotientRange T := by
  obtain ⟨u, hu, hrange⟩ := range_counterexample_of_re_axioms T hT
  exact no_index_quotient_range_of_counterexample T u concreteEmptyIndex hu hrange

/-- The explicit axiom-program enumeration used in the manuscript suffices. -/
theorem range_counterexample_of_axiom_enumerator
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T] (a : ℕ)
    (ha : ∀ n : ℕ, AxiomCodes T n ↔ ∃ x : ℕ, n ∈ Kleene.eval a x) :
    ∃ u : ℕ, PointwiseIndex T u concreteEmptyIndex ∧
      ¬PointwiseIndex T (rangeIndex u) (rangeIndex concreteEmptyIndex) :=
  range_counterexample_of_re_axioms T (axiom_codes_re_of_program_enumerator T a ha)

/-- No quotient range operation exists for an explicitly enumerated axiom set. -/
theorem no_index_quotient_range_of_axiom_enumerator
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T] (a : ℕ)
    (ha : ∀ n : ℕ, AxiomCodes T n ↔ ∃ x : ℕ, n ∈ Kleene.eval a x) :
    NoIndexQuotientRange T :=
  no_index_quotient_range_of_re_axioms T (axiom_codes_re_of_program_enumerator T a ha)

/-- The proof-of-contradiction probe supplies the obstruction already over PA. -/
theorem pa_range_counterexample :
    ∃ u : ℕ, PointwiseIndex 𝗣𝗔 u concreteEmptyIndex ∧
      ¬PointwiseIndex 𝗣𝗔 (rangeIndex u) (rangeIndex concreteEmptyIndex) :=
  ⟨probeIndex (proofBotPredicate 𝗣𝗔), range_counterexample_via_godel 𝗣𝗔⟩

/-- The range assignment does not descend to the external pointwise quotient of PA. -/
theorem pa_no_index_quotient_range : NoIndexQuotientRange 𝗣𝗔 :=
  no_index_quotient_range_via_godel 𝗣𝗔

end FailureOfComposition.ConcreteIndices
