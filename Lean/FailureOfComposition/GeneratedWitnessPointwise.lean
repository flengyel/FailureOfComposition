/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.PiOneExtensionality
import FailureOfComposition.GeneratedWitnessGraphs

/-!
The stage-restricted witnesses are pointwise PA-equivalent whenever the
underlying graphs agree on the standard naturals. A true ground equation for
the total history evaluator fixes all possible internal outputs at that
standard stage and input. No uniform equivalence premise is assumed.
-/

set_option autoImplicit false

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.GeneratedWitnessGraphs
open ProofSearch ConcreteEvaluator PiOneCharacterization

private def historyGround (e s x z : ℕ) : 𝚺₁.Semisentence 0 :=
  .mkSigma “!(code codeHistoryEvaluator) !!(z) !!(s) !!(e) !!(x)”

private theorem historyGround_provable (e s x z : ℕ)
    (hz : Semiformula.Evalb ![z, s, e, x] (code codeHistoryEvaluator)) :
    𝗣𝗔 ⊢ (historyGround e s x z).val := by
  apply sigma_one_completeness (historyGround e s x z).sigma_prop
  simpa [models_iff, historyGround, numeral_eq_natCast, natCast_nat] using hz

private theorem history_output_at_numerals (e s x z : ℕ)
    (hz : Semiformula.Evalb ![z, s, e, x] (code codeHistoryEvaluator))
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] :
    Semiformula.Evalb ![(z : M), (s : M), (e : M), (x : M)] (code codeHistoryEvaluator) := by
  have hp := consequence_iff.mp (Theory.Proof.sound (historyGround_provable e s x z hz))
    M inferInstance
  simpa [models_iff, historyGround, numeral_eq_natCast] using hp

/-- A fixed standard stage can only return its genuine standard output in
any PA model. Standard agreement then supplies the second graph at that output. -/
private theorem standard_stage_implies_graph (e : ℕ) (G : Graph)
    (hExt : Extensional (eventualGraph e) G) (s x : ℕ)
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
    (y : M) (hy : Semiformula.Evalb ![(s : M), (e : M), (x : M), y]
      (evalnCertificateFormula : ArithmeticSemisentence 4)) :
    G.val.Evalb ![(x : M), y] := by
  haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  obtain ⟨z, hz⟩ := eval_codeHistoryEvaluator_exists (s : ℕ) e x
  have hzM := history_output_at_numerals e s x z hz (M := M)
  have hyz := eval_unique ((evalnCertificateFormula_eval_history_iff _ _ _ _).mp hy) hzM
  cases z with
  | zero =>
    have heq : y + 1 = 0 := by simpa only [Nat.cast_zero] using hyz
    exact False.elim ((ne_of_gt (lt_of_le_of_lt (Arithmetic.zero_le y) (lt_add_one y))) heq)
  | succ m =>
    have heq : y = (m : M) := by simpa using hyz
    have hm : Semiformula.Evalb ![s, e, x, m]
        (evalnCertificateFormula : ArithmeticSemisentence 4) :=
      (evalnCertificateFormula_eval_history_iff s e x m).mpr (by simpa using hz)
    have hE : (eventualGraph e).val.Evalb ![x, m] := by
      apply (eventualGraph_eval e _).mpr
      refine ⟨s, ?_⟩
      simpa only [numeral_eq_natCast_app, natCast_nat, Matrix.cons_val_zero,
        Matrix.cons_val_one] using hm
    have hG := true_graph_instance_provable G x m ((hExt x m).mp hE)
    have hv := consequence_iff.mp (Theory.Proof.sound hG) M inferInstance
    have hval : G.val.Evalb ![(x : M), (m : M)] := by
      simpa only [models_iff, graphInstance_eval] using hv
    simpa only [heq] using hval

/-- At each fixed standard stage/input pair, PA proves equality of the two
witness graphs over all internal outputs. -/
theorem AGraph_eqAt_B_pair (e : ℕ) (G : Graph)
    (hExt : Extensional (eventualGraph e) G) (s x : ℕ) :
    𝗣𝗔 ⊢ eqAt (AGraph e G) (BGraph e) (Nat.pair s x) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  rw [models_iff, eqAt_eval]
  intro y
  rw [coe_pair_eq_pair_coe, AGraph_pair_eval, BGraph_pair_eval]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, standard_stage_implies_graph e G hExt s x y
      ((stageGraph_eval e (s : M) (x : M) y).mp h)⟩

/-- Standard equality of the original graphs suffices for pointwise
PA-provable equality of the stage-restricted witnesses. No functionality
assumption on G and no uniform-equivalence premise is needed. -/
theorem AGraph_pointwise_B (e : ℕ) (G : Graph)
    (hExt : Extensional (eventualGraph e) G) :
    Pointwise 𝗣𝗔 (AGraph e G) (BGraph e) := by
  intro n
  simpa only [Nat.pair_unpair] using
    AGraph_eqAt_B_pair e G hExt (Nat.unpair n).1 (Nat.unpair n).2

end FailureOfComposition.GeneratedWitnessGraphs
