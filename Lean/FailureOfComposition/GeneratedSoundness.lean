/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.PiOneExtensionality

/-!
Sigma-one soundness is enough to make pointwise provability sound for the
standard extensions of arbitrary Sigma-one graphs. This statement needs
neither graph functionality nor an enumerability assumption on the theory.
-/

set_option autoImplicit false



open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

namespace FailureOfComposition.GeneratedCongruence
open ProofSearch PiOneCharacterization

/-- Every Sigma-one sentence proved by the theory is true in the standard
natural numbers. -/
def SigmaOneSound (T : ArithmeticTheory) : Prop :=
  ∀ σ : ArithmeticSentence, Hierarchy 𝚺 1 σ → T ⊢ σ → ℕ↓[ℒₒᵣ] ⊧ σ

/-- Failure of Sigma-one soundness supplies a single false proved Sigma-one
sentence. No consistency hypothesis is required. -/
theorem not_sigmaOneSound_iff (T : ArithmeticTheory) :
    ¬SigmaOneSound T ↔
      ∃ σ : ArithmeticSentence, Hierarchy 𝚺 1 σ ∧ T ⊢ σ ∧ ¬ℕ↓[ℒₒᵣ] ⊧ σ := by
  classical
  simp only [SigmaOneSound, not_forall, exists_prop]

/-- The propositional formulation agrees with Foundation's soundness class. -/
theorem sigmaOneSound_iff_nonempty_soundOnHierarchy (T : ArithmeticTheory) :
    SigmaOneSound T ↔ Nonempty (T.SoundOnHierarchy 𝚺 1) := by
  constructor
  · intro h
    exact ⟨⟨fun hp hσ => h _ hσ hp⟩⟩
  · rintro ⟨h⟩ σ hσ hp
    exact h.sound hp hσ

private theorem ground_proof_of_pointwise (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (F G : Graph) (hFG : Pointwise T F G) (n m : ℕ)
    (hF : F.val.Evalb ![n, m]) : T ⊢ graphInstance G n m := by
  have hpF : T ⊢ graphInstance F n m :=
    WeakerThan.pbl (true_graph_instance_provable F n m hF)
  apply complete.{0} T
  intro M _ _
  haveI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  have hEq : M↓[ℒₒᵣ] ⊧ eqAt F G n :=
    consequence_iff.mp (Theory.Proof.sound (hFG n)) M inferInstance
  have hVal : M↓[ℒₒᵣ] ⊧ graphInstance F n m :=
    consequence_iff.mp (Theory.Proof.sound hpF) M inferInstance
  simp only [models_iff, eqAt_eval] at hEq
  simp only [models_iff, graphInstance_eval] at hVal ⊢
  exact (hEq (m : M)).mp hVal

/-- Sigma-one soundness turns each pointwise proof into equality of standard
graphs, without assuming that either graph is functional. -/
theorem pointwise_implies_extensional_of_sigmaOneSound (T : ArithmeticTheory)
    [𝗣𝗔 ⪯ T] (hT : SigmaOneSound T) (F G : Graph)
    (hFG : Pointwise T F G) : Extensional F G := by
  intro n m
  have forward {F G : Graph} (hFG : Pointwise T F G)
      (hF : F.val.Evalb ![n, m]) : G.val.Evalb ![n, m] := by
    have hp := ground_proof_of_pointwise T F G hFG n m hF
    have hs := hT _ (graphInstance_sigma_one G n m) hp
    simpa only [models_iff, graphInstance_eval, natCast_nat] using hs
  exact ⟨forward hFG, forward ((pointwise_equivalence T).symm hFG)⟩

end FailureOfComposition.GeneratedCongruence
