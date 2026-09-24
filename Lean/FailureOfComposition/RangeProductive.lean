/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.RangeWitness

/-!
An independent productive-set proof of the range-assignment obstruction.
The probe tests whether the concrete diagonal history has a positive result
at the supplied stage. Every standard stage is separately PA-refutable, while
the internally quantified absence sentence is unprovable in the ambient theory.
-/

set_option autoImplicit false

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

namespace FailureOfComposition.ConcreteIndices

open ProofSearch ConcreteEvaluator HistoryWitnesses ProgramIndices ConcreteEmptyGraph

private theorem eval_numeral_substitution {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (P : ArithmeticSemisentence 1) (n : ℕ) :
    (P/[n]).Evalb (M := M) ![] ↔ P.Evalb ![(n : M)] := by
  simp [Semiformula.eval_substs, numeral_eq_natCast]

/-- True diagonal divergence refutes the positive-history test at each standard stage. -/
theorem historyPositive_refutable_of_divergence (d : ℕ)
    (hdiv : ¬diagonalHistoryFormula.Evalb ![d]) (n : ℕ) :
    𝗣𝗔 ⊢ ∼(historyPositiveFormula d).val/[n] := by
  have hi : 𝗣𝗔 ⊢ eqAt (guardGraph d) identity n 🡒
      ∼(historyPositiveFormula d).val/[n] := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
    simp only [models_iff, LogicalConnective.HomClass.map_imply,
      LogicalConnective.HomClass.map_neg, eqAt_eval]
    intro he
    have hg := (he (n : M)).mpr ((identity_eval _).mpr rfl)
    have hzero := ((guardGraph_eval d _).mp hg).1
    have hn := (history_zero_iff_no_positive d (n : M)).mp hzero
    have hP : ¬(historyPositiveFormula d).val.Evalb ![(n : M)] := by
      simpa [historyPositiveFormula] using hn
    exact fun hp => hP ((eval_numeral_substitution (historyPositiveFormula d).val n).mp hp)
  exact mdp! hi (guard_pointwise_identity 𝗣𝗔 d hdiv n)

/-- Absence of all positive history stages is exactly diagonal divergence in PA. -/
theorem history_absence_iff_divergence (d : ℕ) :
    𝗣𝗔 ⊢ absenceSentence (historyPositiveFormula d) 🡘 ∼diagonalHistoryFormula/[d] := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  simp only [models_iff, LogicalConnective.HomClass.map_iff,
    LogicalConnective.HomClass.map_neg, absenceSentence_eval]
  rw [diagonalHistory_iff d]
  simp [historyPositiveFormula]

theorem history_absence_unprovable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (d : ℕ) (hnot : T ⊬ ∼diagonalHistoryFormula/[d]) :
    T ⊬ absenceSentence (historyPositiveFormula d) := by
  intro hp
  have hi : T ⊢ absenceSentence (historyPositiveFormula d) 🡘
      ∼diagonalHistoryFormula/[d] := WeakerThan.pbl (history_absence_iff_divergence d)
  apply hnot
  cl_prover [hi, hp]

/-- A concrete productive divergence witness gives the required range counterexample. -/
theorem range_counterexample_of_history_divergence
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (d : ℕ)
    (hdiv : ¬diagonalHistoryFormula.Evalb ![d])
    (hnot : T ⊬ ∼diagonalHistoryFormula/[d]) :
    PointwiseIndex T (probeIndex (historyPositiveFormula d)) concreteEmptyIndex ∧
      ¬PointwiseIndex T (rangeIndex (probeIndex (historyPositiveFormula d)))
        (rangeIndex concreteEmptyIndex) :=
  range_counterexample_of_instance_refutations T (historyPositiveFormula d)
    (historyPositive_refutable_of_divergence d hdiv) (history_absence_unprovable T d hnot)

/-- Productiveness supplies the witness for an enumerable theorem-code set. -/
theorem range_counterexample_via_productiveness
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (TheoremCodes T)) :
    ∃ u : ℕ, PointwiseIndex T u concreteEmptyIndex ∧
      ¬PointwiseIndex T (rangeIndex u) (rangeIndex concreteEmptyIndex) := by
  obtain ⟨d, hdiv, hnot⟩ := exists_true_unprovable_history_divergence_of_theorem_codes T hT
  exact ⟨probeIndex (historyPositiveFormula d),
    range_counterexample_of_history_divergence T d hdiv hnot⟩

/-- The productive proof requires only recursively enumerable axiom codes. -/
theorem range_counterexample_via_productiveness_of_re_axioms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ∃ u : ℕ, PointwiseIndex T u concreteEmptyIndex ∧
      ¬PointwiseIndex T (rangeIndex u) (rangeIndex concreteEmptyIndex) :=
  range_counterexample_via_productiveness T (theorem_codes_re_of_axiom_codes T hT)

/-- The explicit program-enumerator specialization of the productive route. -/
theorem range_counterexample_via_productiveness_of_axiom_enumerator
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T] (a : ℕ)
    (ha : ∀ n : ℕ, AxiomCodes T n ↔ ∃ x : ℕ, n ∈ Kleene.eval a x) :
    ∃ u : ℕ, PointwiseIndex T u concreteEmptyIndex ∧
      ¬PointwiseIndex T (rangeIndex u) (rangeIndex concreteEmptyIndex) :=
  range_counterexample_via_productiveness_of_re_axioms T
    (axiom_codes_re_of_program_enumerator T a ha)

/-- The same productive witness rules out an induced operation on the quotient. -/
theorem no_index_quotient_range_via_productiveness_of_re_axioms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) : NoIndexQuotientRange T := by
  obtain ⟨d, hdiv, hnot⟩ := exists_true_unprovable_history_divergence_of_theorem_codes T
    (theorem_codes_re_of_axiom_codes T hT)
  exact no_quotient_range_of_instance_refutations T (historyPositiveFormula d)
    (historyPositive_refutable_of_divergence d hdiv) (history_absence_unprovable T d hnot)

end FailureOfComposition.ConcreteIndices
