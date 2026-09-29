/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.Palomar.GeneratedCongruenceInterface
import FailureOfComposition.Palomar.PiOneBridge
import FailureOfComposition.ConcreteGeneratedCongruence

/-!
# Generated-congruence classification bridge

This module proves two independent correspondences. First, the explicit Σ₁
grammar and standard-soundness predicate agree with the maintained Foundation
notions. Second, the intersection defining the least composition congruence
agrees with the maintained concrete relation. The final theorem transports the
maintained classification without assuming consistency or enumerability.

The typed obligations proved below are: `SigmaOne p ↔ Hierarchy 𝚺 1
p.toFoundation` for every free-variable type and binder arity;
`SigmaOneSound T ↔ GeneratedCongruence.SigmaOneSound (toFoundation T)` for
every independent theory; and `GeneratedRel T e d ↔
ConcreteIndices.GeneratedRel (toFoundation T) e d` for every theory and pair
of natural-number indices. Generator containment, equivalence, two-argument
composition closure, and leastness are separately named before the final
classification transport.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition.Palomar.Arithmetic

namespace Hierarchy

variable {ξ : Type} {n : ℕ}

private theorem shiftedTermPositiveSigma (t : Term ξ n) :
    (Rew.bShift t.toFoundation).Positive := by
  exact Rew.positive_iff.mpr ⟨t.toFoundation, rfl⟩

@[simp] private theorem ofFoundation_ballLTSigma (t : ArithmeticSemiterm ξ n)
    (p : ArithmeticSemiformula ξ (n + 1)) :
    Formula.ofFoundation (Semiformula.ballLT t p) =
      Formula.ball (Term.ofFoundation t) (Formula.ofFoundation p) := by
  apply Formula.toFoundation_injective
  simp

@[simp] private theorem ofFoundation_bexsLTSigma (t : ArithmeticSemiterm ξ n)
    (p : ArithmeticSemiformula ξ (n + 1)) :
    Formula.ofFoundation (Semiformula.bexsLT t p) =
      Formula.bexs (Term.ofFoundation t) (Formula.ofFoundation p) := by
  apply Formula.toFoundation_injective
  simp

/-- Independent Σ₁ membership implies maintained Σ₁ membership. -/
theorem sigmaOne_toFoundation {p : Formula ξ n} (hp : SigmaOne p) :
    FFL.FirstOrder.Arithmetic.Hierarchy 𝚺 1 p.toFoundation := by
  induction hp with
  | delta h => exact deltaZero_toFoundation h 𝚺 |>.of_zero
  | and _ _ ihp ihq => exact .and ihp ihq
  | or _ _ ihp ihq => exact .or ihp ihq
  | ball t _ ih =>
      rw [Formula.toFoundation_ball]
      exact FFL.FirstOrder.Arithmetic.Hierarchy.ball
        (shiftedTermPositiveSigma t) ih
  | bexs t _ ih =>
      rw [Formula.toFoundation_bexs]
      exact FFL.FirstOrder.Arithmetic.Hierarchy.bexs
        (shiftedTermPositiveSigma t) ih
  | exs _ ih => exact .exs ih

private theorem deltaZero_ofFoundationSigmaAux
    {p : ArithmeticSemiformula ξ n} {Γ : Polarity} {s : ℕ}
    (hp : FFL.FirstOrder.Arithmetic.Hierarchy Γ s p) :
    s = 0 → DeltaZero (Formula.ofFoundation p) := by
  induction hp with
  | verum => intro _; exact .verum
  | falsum => intro _; exact .falsum
  | rel _ _ r v =>
      intro _
      cases r with
      | eq => exact .equal _ _
      | lt => exact .less _ _
  | nrel _ _ r v =>
      intro _
      cases r with
      | eq => exact .nequal _ _
      | lt => exact .nless _ _
  | and _ _ ihp ihq => intro hs; exact .and (ihp hs) (ihq hs)
  | or _ _ ihp ihq => intro hs; exact .or (ihp hs) (ihq hs)
  | ball ht _ ih =>
      intro hs
      rcases Rew.positive_iff.mp ht with ⟨t, rfl⟩
      change DeltaZero (Formula.ofFoundation (Semiformula.ballLT t _))
      rw [ofFoundation_ballLTSigma]
      exact DeltaZero.ball (Term.ofFoundation t) (ih hs)
  | bexs ht _ ih =>
      intro hs
      rcases Rew.positive_iff.mp ht with ⟨t, rfl⟩
      change DeltaZero (Formula.ofFoundation (Semiformula.bexsLT t _))
      rw [ofFoundation_bexsLTSigma]
      exact DeltaZero.bexs (Term.ofFoundation t) (ih hs)
  | exs _ _ => omega
  | all _ _ => omega
  | sigma _ _ => omega
  | pi _ _ => omega
  | dummy_sigma _ _ => omega
  | dummy_pi _ _ => omega

private theorem sigmaOne_ofFoundationAux
    {p : ArithmeticSemiformula ξ n} {Γ : Polarity} {s : ℕ}
    (hp : FFL.FirstOrder.Arithmetic.Hierarchy Γ s p) :
    Γ = 𝚺 → s = 1 → SigmaOne (Formula.ofFoundation p) := by
  induction hp with
  | verum => intro _ _; exact .delta .verum
  | falsum => intro _ _; exact .delta .falsum
  | rel _ _ r v =>
      intro _ _
      cases r with
      | eq => exact .delta (.equal _ _)
      | lt => exact .delta (.less _ _)
  | nrel _ _ r v =>
      intro _ _
      cases r with
      | eq => exact .delta (.nequal _ _)
      | lt => exact .delta (.nless _ _)
  | and _ _ ihp ihq => intro hΓ hs; exact .and (ihp hΓ hs) (ihq hΓ hs)
  | or _ _ ihp ihq => intro hΓ hs; exact .or (ihp hΓ hs) (ihq hΓ hs)
  | ball ht _ ih =>
      intro hΓ hs
      rcases Rew.positive_iff.mp ht with ⟨t, rfl⟩
      change SigmaOne (Formula.ofFoundation (Semiformula.ballLT t _))
      rw [ofFoundation_ballLTSigma]
      exact SigmaOne.ball (Term.ofFoundation t) (ih hΓ hs)
  | bexs ht _ ih =>
      intro hΓ hs
      rcases Rew.positive_iff.mp ht with ⟨t, rfl⟩
      change SigmaOne (Formula.ofFoundation (Semiformula.bexsLT t _))
      rw [ofFoundation_bexsLTSigma]
      exact SigmaOne.bexs (Term.ofFoundation t) (ih hΓ hs)
  | exs _ ih => intro _ hs; exact .exs (ih rfl hs)
  | sigma h _ =>
      intro _ hs
      exact .exs (.delta (deltaZero_ofFoundationSigmaAux h (by omega)))
  | all _ _ => simp
  | pi _ _ => simp
  | dummy_sigma _ _ => omega
  | dummy_pi _ _ => simp

/-- Every maintained Σ₁ formula has the independent Σ₁ grammar. -/
theorem sigmaOne_ofFoundation {p : ArithmeticSemiformula ξ n}
    (hp : FFL.FirstOrder.Arithmetic.Hierarchy 𝚺 1 p) :
    SigmaOne (Formula.ofFoundation p) :=
  sigmaOne_ofFoundationAux hp rfl rfl

/-- Exact two-way correspondence for Σ₁ membership. -/
theorem sigmaOne_toFoundation_iff (p : Formula ξ n) :
    SigmaOne p ↔ FFL.FirstOrder.Arithmetic.Hierarchy 𝚺 1 p.toFoundation := by
  constructor
  · exact sigmaOne_toFoundation
  · intro h
    simpa using sigmaOne_ofFoundation h

end Hierarchy

/-- Independent and maintained Σ₁ soundness agree for every theory. -/
theorem sigmaOneSound_toFoundation_iff (T : Theory) :
    SigmaOneSound T ↔
      FailureOfComposition.GeneratedCongruence.SigmaOneSound
        (TheoryCorrespondence.toFoundation T) := by
  constructor
  · intro h σ hσ hproof
    let p := Formula.ofFoundation σ
    have hp : Hierarchy.SigmaOne p := Hierarchy.sigmaOne_ofFoundation hσ
    have hproofNonempty : Nonempty (FFL.FirstOrder.Theory.Proof
        (TheoryCorrespondence.toFoundation T) σ) := by
      change Nonempty (FFL.FirstOrder.Theory.Proof
        (TheoryCorrespondence.toFoundation T) σ) at hproof
      exact hproof
    have hproof' : Provable T p :=
      (provable_toFoundation_iff T p).mpr (by simpa [p] using hproofNonempty)
    have htrue := h p hp hproof'
    have htrue' := (standardTrue_toFoundation_iff p).mp htrue
    simpa [p] using htrue'
  · intro h p hp hproof
    apply (standardTrue_toFoundation_iff p).mpr
    exact h p.toFoundation (Hierarchy.sigmaOne_toFoundation hp)
      ((provable_toFoundation_iff T p).mp hproof)

end FailureOfComposition.Palomar.Arithmetic

namespace FailureOfComposition.Palomar.Arithmetic.Evaluator

/-- Every pointwise generator belongs to the independent generated relation. -/
theorem generatedRel_base (T : Theory) {e d : ℕ}
    (h : PointwiseIndex T e d) : GeneratedRel T e d :=
  fun _R _ hbase => hbase e d h

/-- The independent generated relation is an equivalence relation. -/
theorem generatedRel_equivalence (T : Theory) : Equivalence (GeneratedRel T) :=
  ⟨fun e _R hR _ => hR.1.refl e,
    fun h R hR hbase => hR.1.symm (h R hR hbase),
    fun h h' R hR hbase => hR.1.trans (h R hR hbase) (h' R hR hbase)⟩

/-- The independent generated relation respects concrete composition in both
arguments. -/
theorem generatedRel_comp (T : Theory) {a a' b b' : ℕ}
    (ha : GeneratedRel T a a') (hb : GeneratedRel T b b') :
    GeneratedRel T (compIndex a b) (compIndex a' b') :=
  fun R hR hbase => hR.2 a a' b b' (ha R hR hbase) (hb R hR hbase)

/-- Leastness of the independent generated relation. -/
theorem generatedRel_least (T : Theory) {R : ℕ → ℕ → Prop}
    (hR : IsCompositionCongruence R)
    (hbase : ∀ x y : ℕ, PointwiseIndex T x y → R x y)
    {e d : ℕ} (h : GeneratedRel T e d) : R e d :=
  h R hR hbase

/-- The explicit independent intersection is exactly the maintained generated
composition congruence on concrete indices. -/
theorem generatedRel_toFoundation_iff (T : Theory) (e d : ℕ) :
    GeneratedRel T e d ↔
      FailureOfComposition.ConcreteIndices.GeneratedRel
        (TheoryCorrespondence.toFoundation T) e d := by
  unfold GeneratedRel IsCompositionCongruence
  unfold FailureOfComposition.ConcreteIndices.GeneratedRel
    FailureOfComposition.CompositionClosure.Generated
    FailureOfComposition.CompositionClosure.IsCongruence
  rw [show compIndex =
      CategoricalRiceShapiro.PartialRecursive.canonicalPartrecCompIndex from
    funext fun f => funext fun g => compIndex_toFoundation f g]
  simp_rw [pointwiseIndex_toFoundation_iff]

/-- The independent generated-congruence classification, transported from the
maintained concrete theorem for every deductive PA extension. -/
theorem generated_congruence_classification
    (T : Theory) (hPA : DeductivelyExtends Peano T) :
    (Arithmetic.SigmaOneSound T →
      ∀ e d : ℕ, GeneratedRel T e d ↔ actualEval e = actualEval d) ∧
    (¬Arithmetic.SigmaOneSound T → ∀ e d : ℕ, GeneratedRel T e d) := by
  let _ : FFL.Entailment.WeakerThan FFL.FirstOrder.Arithmetic.Peano
      (TheoryCorrespondence.toFoundation T) :=
    (deductivelyExtendsPeano_toFoundation_iff T).mp hPA
  have h := FailureOfComposition.ConcreteIndices.generated_congruence_classification
    (TheoryCorrespondence.toFoundation T)
  constructor
  · intro hsound e d
    have heval (q : ℕ) : actualEval q = FailureOfComposition.Kleene.eval q :=
      funext fun x => actualEval_toFoundation q x
    rw [generatedRel_toFoundation_iff, heval e, heval d]
    exact h.1 ((Arithmetic.sigmaOneSound_toFoundation_iff T).mp hsound) e d
  · intro hnotsound e d
    apply (generatedRel_toFoundation_iff T e d).mpr
    exact h.2 (fun hsound => hnotsound
      ((Arithmetic.sigmaOneSound_toFoundation_iff T).mpr hsound)) e d

end FailureOfComposition.Palomar.Arithmetic.Evaluator
