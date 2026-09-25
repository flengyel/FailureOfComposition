/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.HistoryWitnesses
import FailureOfComposition.ConcreteDiagonal

/-!
The composition obstruction from unprovable diagonal history divergence.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.HistoryWitnesses
open ProofSearch ConcreteEvaluator

def historyZeroFormula (d : ℕ) : 𝚺₁.Semisentence 1 :=
  .mkSigma “s. !(historyGraph d).val s 0”

def historyPositiveFormula (d : ℕ) : 𝚺₁.Semisentence 1 :=
  .mkSigma “s. ∃ z, 0 < z ∧ !(historyGraph d).val s z”

variable {M : Type*} [ORingStructure M]

theorem history_positive_iff [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
    (d : ℕ) (s : M) :
    (∃ z : M, 0 < z ∧ (historyGraph d).val.Evalb ![s, z]) ↔
      ∃ y : M, Semiformula.Evalb ![s, (d : M), (d : M), y]
        (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  constructor
  · rintro ⟨z, hz, h⟩
    refine ⟨z - 1, (evalnCertificateFormula_eval_history_iff _ _ _ _).mpr ?_⟩
    rw [Arithmetic.sub_add_self_of_le (Arithmetic.one_le_of_zero_lt z hz)]
    exact (historyGraph_eval d s z).mp h
  · rintro ⟨y, h⟩
    refine ⟨y + 1, lt_of_le_of_lt (Arithmetic.zero_le y) (lt_add_one y), ?_⟩
    exact (historyGraph_eval d s (y + 1)).mpr
      ((evalnCertificateFormula_eval_history_iff _ _ _ _).mp h)

theorem diagonalHistory_iff [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
    (d : ℕ) :
    (diagonalHistoryFormula/[d]).Evalb (M:=M) ![] ↔
      ∃ s z : M, 0 < z ∧ (historyGraph d).val.Evalb ![s, z] := by
  simp only [diagonalHistoryFormula, Semiformula.eval_substs]
  simpa [numeral_eq_natCast] using
    (exists_congr fun s : M => (history_positive_iff d s).symm)

theorem history_zero_iff_no_positive
    [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (d : ℕ) (s : M) :
    (historyGraph d).val.Evalb ![s, 0] ↔
      ¬∃ z : M, 0 < z ∧ (historyGraph d).val.Evalb ![s, z] := by
  constructor
  · rintro h0 ⟨z, hz, h⟩
    exact (ne_of_gt hz) (history_unique d s z 0 h h0)
  · intro hn
    obtain ⟨z, hz⟩ := history_total d s
    have hz0 : z = 0 := le_antisymm
      (not_lt.mp (fun hpos => hn ⟨z, hpos, hz⟩)) (Arithmetic.zero_le z)
    simpa only [hz0] using hz

theorem guard_pointwise_identity (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (d : ℕ) (hdiv : ¬diagonalHistoryFormula.Evalb ![d]) :
    Pointwise T (guardGraph d) identity := by
  intro n
  have hn : (historyZeroFormula d).val.Evalb ![n] := by
    have h0 : (historyGraph d).val.Evalb ![n, (0:ℕ)] := by
      apply (history_zero_iff_no_positive d n).mpr
      intro hpos
      apply hdiv
      have hh := (diagonalHistory_iff d).mpr ⟨n, hpos⟩
      simpa [Semiformula.eval_substs] using hh
    simpa [historyZeroFormula] using h0
  have hp : 𝗣𝗔 ⊢ (historyZeroFormula d).val/[n] := by
    apply sigma_one_completeness (by simp)
    simpa [models_iff, Semiformula.eval_substs] using hn
  have hi : 𝗣𝗔 ⊢ (historyZeroFormula d).val/[n] 🡒 eqAt (guardGraph d) identity n := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    simp [models_iff, historyZeroFormula, eqAt, guardGraph, identity,
      Semiformula.eval_substs]
  exact WeakerThan.pbl (Entailment.mdp hi hp)

theorem search_empty_implies_absence (d : ℕ) :
    𝗣𝗔 ⊢ eqAt (searchGraph d) empty 0 🡒 ∼diagonalHistoryFormula/[d] := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  simp only [models_iff, LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_neg]
  intro he hh
  obtain ⟨s, hs⟩ := (diagonalHistory_iff d).mp hh
  let P : M → Prop := fun s => ∃ z : M, 0 < z ∧ (historyGraph d).val.Evalb ![s, z]
  have hP : 𝚺₁-Predicate P := by
    refine ⟨(historyPositiveFormula d).rew Rew.emb, ?_⟩
    intro v
    simp [P, historyPositiveFormula]
  obtain ⟨t, ht, hmin⟩ := InductionOnHierarchy.least_number_sigma 𝚺 1 hP hs
  have hsearch : (searchGraph d).val.Evalb ![(0:M), t] := by
    apply (searchGraph_eval d _).mpr
    refine ⟨ht, fun r hr => ?_⟩
    exact (history_zero_iff_no_positive d r).mpr (hmin r hr)
  have hEq := (eqAt_eval (searchGraph d) empty 0).mp he t
  exact (empty_eval _).mp (hEq.mp hsearch)

theorem graph_noncongruence_of_history_divergence (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (d : ℕ) (hdiv : ¬diagonalHistoryFormula.Evalb ![d])
    (hnot : T ⊬ ∼diagonalHistoryFormula/[d]) :
    Pointwise T (guardGraph d) identity ∧
      ¬Pointwise T (comp (guardGraph d) (searchGraph d)) (comp identity (searchGraph d)) := by
  refine ⟨guard_pointwise_identity T d hdiv, ?_⟩
  intro he
  have hi : 𝗣𝗔 ⊢ eqAt (comp (guardGraph d) (searchGraph d))
      (comp identity (searchGraph d)) 0 🡒 eqAt (searchGraph d) empty 0 := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
    have hempty := consequence_iff.mp (Theory.Proof.sound (guard_search_empty d)) M inferInstance
    have hid := consequence_iff.mp
      (Theory.Proof.sound (identity_comp (searchGraph d))) M inferInstance
    simp only [models_iff, uniformSentence_eval] at hempty hid
    simp only [models_iff, LogicalConnective.HomClass.map_imply, eqAt_eval]
    intro h y
    exact (hid 0 y).symm.trans ((h y).symm.trans (hempty 0 y))
  exact hnot (Entailment.mdp (WeakerThan.pbl (search_empty_implies_absence d))
    (Entailment.mdp (WeakerThan.pbl hi) (he 0)))

end FailureOfComposition.HistoryWitnesses
