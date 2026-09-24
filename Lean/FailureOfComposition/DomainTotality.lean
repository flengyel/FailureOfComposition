/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ConcreteWeakTotality
import FailureOfComposition.SigmaOneRealization

/-!
The domain partial identity and the manuscript's index formulation of R totality.
The chosen domain program satisfies its graph equation in PA, so all following
pointwise statements quantify over the fixed evaluator's natural-number indices.
-/

set_option autoImplicit false

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

namespace FailureOfComposition.ConcreteIndices

open ProofSearch ConcreteEvaluator ProgramIndices

/-- The partial identity on the domain of the program with index `e`. -/
def domainGraph (e : ℕ) : Graph :=
  .mkSigma “x y. x = y ∧ ∃ v, !(eventualGraph e).val x v”

@[simp] theorem domainGraph_eval {M : Type*} [ORingStructure M]
    (e : ℕ) (v : Fin 2 → M) :
    (domainGraph e).val.Evalb v ↔
      v 0 = v 1 ∧ ∃ z : M, (eventualGraph e).val.Evalb ![v 0, z] := by
  simp [domainGraph]

/-- Domain partial identities are PA-provably functional, regardless of whether
the original program is total. -/
theorem domainGraph_functional (e : ℕ) : Functional (domainGraph e) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  exact ((domainGraph_eval e _).mp hy).1.symm.trans
    ((domainGraph_eval e _).mp hz).1

/-- A fixed program realizing the domain partial identity. The choice uses the
proved Sigma-one graph realization theorem. -/
noncomputable def domainIndex (e : ℕ) : ℕ :=
  Classical.choose (SigmaOneRealization.realize_graph (domainGraph e)
    (domainGraph_functional e))

theorem domainIndex_realizes (e : ℕ) :
    Uniform 𝗣𝗔 (eventualGraph (domainIndex e)) (domainGraph e) :=
  Classical.choose_spec (SigmaOneRealization.realize_graph (domainGraph e)
    (domainGraph_functional e))

/-- The chosen index has the required graph equation in every PA model. -/
theorem domainIndex_graph_equation {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : ℕ) (x y : M) :
    (eventualGraph (domainIndex e)).val.Evalb ![x, y] ↔
      x = y ∧ ∃ z : M, (eventualGraph e).val.Evalb ![x, z] := by
  have h := consequence_iff.mp (Theory.Proof.sound (domainIndex_realizes e))
    M inferInstance
  simp only [models_iff, uniformSentence_eval] at h
  exact (h x y).trans (domainGraph_eval e _)

/-- Montagna's R-totality condition, stated directly for program indices. -/
def RTotal (T : ArithmeticTheory) (e : ℕ) : Prop :=
  PointwiseIndex T (domainIndex e) Kleene.identityIndex

theorem domainGraph_pointwise_identity (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (e : ℕ) (he : PointwiseIndex T e Kleene.identityIndex) :
    Pointwise T (domainGraph e) identity := by
  have hpoint := (pointwise_equivalence T).trans
    ((pointwiseIndex_iff T e Kleene.identityIndex).mp he)
    (uniform_to_pointwise T eventualGraph_identity)
  intro n
  apply complete.{0} T
  intro M _ _
  haveI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  have h := consequence_iff.mp (Theory.Proof.sound (hpoint n)) M inferInstance
  simp only [models_iff, eqAt_eval] at h
  have hconv : ∃ z : M, (eventualGraph e).val.Evalb ![(n : M), z] :=
    ⟨n, (h n).mpr ((identity_eval _).mpr rfl)⟩
  rw [models_iff, eqAt_eval]
  intro y
  simp only [domainGraph_eval, identity_eval, Matrix.cons_val_zero, Matrix.cons_val_one,
    hconv, and_true]
  exact eq_comm

/-- Being pointwise provably equal to identity implies R totality. This uses
neither consistency nor an enumeration of the ambient theory. -/
theorem rTotal_of_pointwise_identity (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (e : ℕ) (he : PointwiseIndex T e Kleene.identityIndex) : RTotal T e := by
  apply (pointwiseIndex_iff T (domainIndex e) Kleene.identityIndex).mpr
  have eqv := pointwise_equivalence T
  exact eqv.trans (uniform_to_pointwise T (domainIndex_realizes e))
    (eqv.trans (domainGraph_pointwise_identity T e he)
      (eqv.symm (uniform_to_pointwise T eventualGraph_identity)))

/-- The guard is R total whenever its diagonal search diverges in the standard
model; unprovability of divergence is not needed for this half. -/
theorem guard_rTotal_of_history_divergence (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (d : ℕ) (hdiv : ¬diagonalHistoryFormula.Evalb ![d]) :
    RTotal T (guardIndex d) :=
  rTotal_of_pointwise_identity T (guardIndex d)
    (guardIndex_pointwise_identity T d hdiv)

/-- The concrete obstruction has R totality but fails the weak-totality
condition on indices. -/
theorem guard_rTotal_not_weaklyTotal_of_history_divergence
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (d : ℕ)
    (hdiv : ¬diagonalHistoryFormula.Evalb ![d])
    (hnot : T ⊬ ∼diagonalHistoryFormula/[d]) :
    RTotal T (guardIndex d) ∧ ¬WeaklyTotalIndex T (guardIndex d) :=
  ⟨guard_rTotal_of_history_divergence T d hdiv,
    not_weaklyTotalIndex_guard T d hnot⟩

/-- Every consistent PA extension with enumerable axioms has an R-total
program that is not weakly total in the index sense. -/
theorem exists_rTotal_not_weaklyTotal_of_re_axioms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (FailureOfComposition.AxiomCodes T)) :
    ∃ e : ℕ, RTotal T e ∧ ¬WeaklyTotalIndex T e := by
  obtain ⟨d, hdiv, hnot⟩ :=
    exists_true_unprovable_history_divergence_of_theorem_codes T
      (theorem_codes_re_of_axiom_codes T hT)
  exact ⟨guardIndex d,
    guard_rTotal_not_weaklyTotal_of_history_divergence T d hdiv hnot⟩

/-- In particular, R totality does not imply index weak totality over PA. -/
theorem pa_exists_rTotal_not_weaklyTotal :
    ∃ e : ℕ, RTotal 𝗣𝗔 e ∧ ¬WeaklyTotalIndex 𝗣𝗔 e := by
  obtain ⟨d, hdiv, hnot⟩ := exists_true_unprovable_history_divergence 𝗣𝗔
  exact ⟨guardIndex d,
    guard_rTotal_not_weaklyTotal_of_history_divergence 𝗣𝗔 d hdiv hnot⟩

end FailureOfComposition.ConcreteIndices
