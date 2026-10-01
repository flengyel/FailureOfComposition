/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.Palomar.PiOneInterface
public import FailureOfComposition.Palomar.EvaluatorBridge
public import FailureOfComposition.ConcretePiOneCharacterization

/-!
# Π₁ characterization bridge

The bridge has four typed layers: standard evaluation of every independent
term and formula, two-way membership in the bounded/Π₁ grammars, completeness
for every true Π₁ sentence, and the three index-level relations.  The final
theorem transports the maintained concrete characterization without adding an
enumerability or soundness assumption.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition.Palomar.Arithmetic

namespace Term

variable {ξ : Type} {n : ℕ}

/-- Standard term evaluation is preserved by the syntax equivalence. -/
@[simp] theorem standardEval_toFoundation (t : Term ξ n)
    (b : Fin n → ℕ) (f : ξ → ℕ) :
    Semiterm.val b f t.toFoundation = t.standardEval b f := by
  induction t with
  | bvar i => rfl
  | fvar x => rfl
  | zero => rfl
  | one => rfl
  | add s t ihs iht =>
      change Semiterm.val b f s.toFoundation + Semiterm.val b f t.toFoundation = _
      simp [Term.standardEval, ihs, iht]
  | mul s t ihs iht =>
      change Semiterm.val b f s.toFoundation * Semiterm.val b f t.toFoundation = _
      simp [Term.standardEval, ihs, iht]

end Term

namespace Formula

variable {ξ : Type} {n : ℕ}

/-- Standard satisfaction, including every binder environment, is preserved. -/
@[simp] theorem standardEval_toFoundation (p : Formula ξ n)
    (b : Fin n → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval b f p.toFoundation ↔ p.standardEval b f := by
  induction p with
  | verum => rfl
  | falsum => rfl
  | equal s t =>
      change Semiterm.val b f s.toFoundation = Semiterm.val b f t.toFoundation ↔ _
      simp [Formula.standardEval]
  | nequal s t =>
      change Semiterm.val b f s.toFoundation ≠ Semiterm.val b f t.toFoundation ↔ _
      simp [Formula.standardEval]
  | less s t =>
      change Semiterm.val b f s.toFoundation < Semiterm.val b f t.toFoundation ↔ _
      simp [Formula.standardEval]
  | nless s t =>
      change ¬Semiterm.val b f s.toFoundation < Semiterm.val b f t.toFoundation ↔ _
      simp [Formula.standardEval]
  | and p q ihp ihq =>
      change (Semiformula.Eval b f p.toFoundation ∧
        Semiformula.Eval b f q.toFoundation) ↔ _
      simp [Formula.standardEval, ihp, ihq]
  | or p q ihp ihq =>
      change (Semiformula.Eval b f p.toFoundation ∨
        Semiformula.Eval b f q.toFoundation) ↔ _
      simp [Formula.standardEval, ihp, ihq]
  | all p ih =>
      change (∀ x : ℕ, Semiformula.Eval (Matrix.vecCons x b) f p.toFoundation) ↔ _
      simp [Formula.standardEval, ih]
  | exs p ih =>
      change (∃ x : ℕ, Semiformula.Eval (Matrix.vecCons x b) f p.toFoundation) ↔ _
      simp [Formula.standardEval, ih]

@[simp] theorem toFoundation_ball (t : Term ξ n) (p : Formula ξ (n + 1)) :
    toFoundation (ball t p) =
      Semiformula.ballLT t.toFoundation p.toFoundation := by
  calc
    toFoundation (ball t p) =
        .all (.or (.nrel Language.ORing.Rel.lt
          ![(#0 : ArithmeticSemiterm ξ (n + 1)), Rew.bShift t.toFoundation])
          p.toFoundation) := by
            simp [ball, Formula.toFoundation, Term.toFoundation_lift,
              Term.toFoundation_bvar, Matrix.fun_eq_vec_two]
    _ = Semiformula.ballLT t.toFoundation p.toFoundation := by rfl

@[simp] theorem toFoundation_bexs (t : Term ξ n) (p : Formula ξ (n + 1)) :
    toFoundation (bexs t p) =
      Semiformula.bexsLT t.toFoundation p.toFoundation := by
  calc
    toFoundation (bexs t p) =
        .exs (.and (.rel Language.ORing.Rel.lt
          ![(#0 : ArithmeticSemiterm ξ (n + 1)), Rew.bShift t.toFoundation])
          p.toFoundation) := by
            simp [bexs, Formula.toFoundation, Term.toFoundation_lift,
              Term.toFoundation_bvar, Matrix.fun_eq_vec_two]
    _ = Semiformula.bexsLT t.toFoundation p.toFoundation := by rfl

end Formula

/-- Closed standard truth is preserved and reflected. -/
theorem standardTrue_toFoundation_iff (p : Sentence) :
    StandardTrue p ↔ ℕ↓[ℒₒᵣ] ⊧ Formula.toFoundation p := by
  simp [StandardTrue, models_iff, Matrix.empty_eq]

namespace Hierarchy

variable {ξ : Type} {n : ℕ}

private theorem shiftedTermPositive (t : Term ξ n) :
    (Rew.bShift t.toFoundation).Positive := by
  exact Rew.positive_iff.mpr ⟨t.toFoundation, rfl⟩

@[simp] private theorem ofFoundation_ballLT (t : ArithmeticSemiterm ξ n)
    (p : ArithmeticSemiformula ξ (n + 1)) :
    Formula.ofFoundation (Semiformula.ballLT t p) =
      Formula.ball (Term.ofFoundation t) (Formula.ofFoundation p) := by
  apply Formula.toFoundation_injective
  simp

@[simp] private theorem ofFoundation_bexsLT (t : ArithmeticSemiterm ξ n)
    (p : ArithmeticSemiformula ξ (n + 1)) :
    Formula.ofFoundation (Semiformula.bexsLT t p) =
      Formula.bexs (Term.ofFoundation t) (Formula.ofFoundation p) := by
  apply Formula.toFoundation_injective
  simp

/-- Independent bounded formulas translate to level zero in either polarity. -/
theorem deltaZero_toFoundation {p : Formula ξ n} (hp : DeltaZero p) (Γ : Polarity) :
    FFL.FirstOrder.Arithmetic.Hierarchy Γ 0 p.toFoundation := by
  induction hp generalizing Γ with
  | verum => exact .verum _ _ _
  | falsum => exact .falsum _ _ _
  | equal s t => exact .rel _ _ _ _
  | nequal s t => exact .nrel _ _ _ _
  | less s t => exact .rel _ _ _ _
  | nless s t => exact .nrel _ _ _ _
  | and _ _ ihp ihq => exact .and (ihp Γ) (ihq Γ)
  | or _ _ ihp ihq => exact .or (ihp Γ) (ihq Γ)
  | ball t _ ih =>
      rw [Formula.toFoundation_ball]
      exact FFL.FirstOrder.Arithmetic.Hierarchy.ball (shiftedTermPositive t) (ih Γ)
  | bexs t _ ih =>
      rw [Formula.toFoundation_bexs]
      exact FFL.FirstOrder.Arithmetic.Hierarchy.bexs (shiftedTermPositive t) (ih Γ)

/-- Independent Π₁ membership implies maintained Π₁ membership. -/
theorem piOne_toFoundation {p : Formula ξ n} (hp : PiOne p) :
    FFL.FirstOrder.Arithmetic.Hierarchy 𝚷 1 p.toFoundation := by
  induction hp with
  | delta h => exact deltaZero_toFoundation h 𝚷 |>.of_zero
  | and _ _ ihp ihq => exact .and ihp ihq
  | or _ _ ihp ihq => exact .or ihp ihq
  | ball t _ ih =>
      rw [Formula.toFoundation_ball]
      exact FFL.FirstOrder.Arithmetic.Hierarchy.ball (shiftedTermPositive t) ih
  | bexs t _ ih =>
      rw [Formula.toFoundation_bexs]
      exact FFL.FirstOrder.Arithmetic.Hierarchy.bexs (shiftedTermPositive t) ih
  | all _ ih => exact .all ih

private theorem deltaZero_ofFoundationAux {p : ArithmeticSemiformula ξ n}
    {Γ : Polarity} {s : ℕ}
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
      rw [ofFoundation_ballLT]
      exact DeltaZero.ball (Term.ofFoundation t) (ih hs)
  | bexs ht _ ih =>
      intro hs
      rcases Rew.positive_iff.mp ht with ⟨t, rfl⟩
      change DeltaZero (Formula.ofFoundation (Semiformula.bexsLT t _))
      rw [ofFoundation_bexsLT]
      exact DeltaZero.bexs (Term.ofFoundation t) (ih hs)
  | exs _ _ => omega
  | all _ _ => omega
  | sigma _ _ => omega
  | pi _ _ => omega
  | dummy_sigma _ _ => omega
  | dummy_pi _ _ => omega

/-- Every maintained level-zero formula has the independent bounded grammar. -/
theorem deltaZero_ofFoundation {p : ArithmeticSemiformula ξ n} {Γ : Polarity}
    (hp : FFL.FirstOrder.Arithmetic.Hierarchy Γ 0 p) :
    DeltaZero (Formula.ofFoundation p) :=
  deltaZero_ofFoundationAux hp rfl

private theorem piOne_ofFoundationAux {p : ArithmeticSemiformula ξ n}
    {Γ : Polarity} {s : ℕ}
    (hp : FFL.FirstOrder.Arithmetic.Hierarchy Γ s p) :
    Γ = 𝚷 → s = 1 → PiOne (Formula.ofFoundation p) := by
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
      change PiOne (Formula.ofFoundation (Semiformula.ballLT t _))
      rw [ofFoundation_ballLT]
      exact PiOne.ball (Term.ofFoundation t) (ih hΓ hs)
  | bexs ht _ ih =>
      intro hΓ hs
      rcases Rew.positive_iff.mp ht with ⟨t, rfl⟩
      change PiOne (Formula.ofFoundation (Semiformula.bexsLT t _))
      rw [ofFoundation_bexsLT]
      exact PiOne.bexs (Term.ofFoundation t) (ih hΓ hs)
  | all _ ih => intro _ hs; exact .all (ih rfl hs)
  | pi h _ =>
      intro _ hs
      exact .all (.delta (deltaZero_ofFoundationAux h (by omega)))
  | exs _ _ => simp
  | sigma _ _ => simp
  | dummy_sigma _ _ => simp
  | dummy_pi _ _ => omega

/-- Every maintained Π₁ formula has the independent Π₁ grammar. -/
theorem piOne_ofFoundation {p : ArithmeticSemiformula ξ n}
    (hp : FFL.FirstOrder.Arithmetic.Hierarchy 𝚷 1 p) :
    PiOne (Formula.ofFoundation p) :=
  piOne_ofFoundationAux hp rfl rfl

/-- Exact two-way correspondence for bounded membership. -/
theorem deltaZero_toFoundation_iff (p : Formula ξ n) (Γ : Polarity) :
    DeltaZero p ↔ FFL.FirstOrder.Arithmetic.Hierarchy Γ 0 p.toFoundation := by
  constructor
  · intro h; exact deltaZero_toFoundation h Γ
  · intro h
    simpa using deltaZero_ofFoundation h

/-- Exact two-way correspondence for Π₁ membership. -/
theorem piOne_toFoundation_iff (p : Formula ξ n) :
    PiOne p ↔ FFL.FirstOrder.Arithmetic.Hierarchy 𝚷 1 p.toFoundation := by
  constructor
  · exact piOne_toFoundation
  · intro h
    simpa using piOne_ofFoundation h

end Hierarchy

/-- Independent and maintained true-Π₁ completeness agree for every theory. -/
theorem piOneComplete_toFoundation_iff (T : Theory) :
    PiOneComplete T ↔
      FailureOfComposition.PiOneCharacterization.PiOneComplete
        (TheoryCorrespondence.toFoundation T) := by
  constructor
  · intro h σ hσ htrue
    let p := Formula.ofFoundation σ
    have hp : Hierarchy.PiOne p := Hierarchy.piOne_ofFoundation hσ
    have hptrue : StandardTrue p :=
      (standardTrue_toFoundation_iff p).mpr (by simpa [p] using htrue)
    have hproof := h p hp hptrue
    have htranslated := (provable_toFoundation_iff T p).mp hproof
    change Nonempty (FFL.FirstOrder.Theory.Proof
      (TheoryCorrespondence.toFoundation T) σ)
    simpa [p] using htranslated
  · intro h p hp htrue
    apply (provable_toFoundation_iff T p).mpr
    exact h p.toFoundation (Hierarchy.piOne_toFoundation hp)
      ((standardTrue_toFoundation_iff p).mp htrue)

end FailureOfComposition.Palomar.Arithmetic

namespace FailureOfComposition.Palomar.Arithmetic.Evaluator

/-- The independent and maintained evaluators are definitionally the same. -/
@[simp] theorem actualEval_toFoundation (e x : ℕ) :
    actualEval e x = FailureOfComposition.Kleene.eval e x := rfl

/-- Right compatibility is preserved and reflected. -/
theorem rightCompatible_toFoundation_iff (T : Theory) :
    RightCompatible T ↔
      FailureOfComposition.ConcreteIndices.RightCompatible
        (TheoryCorrespondence.toFoundation T) := by
  constructor
  · intro h f i g hfi
    rw [← compIndex_toFoundation, ← compIndex_toFoundation]
    apply (pointwiseIndex_toFoundation_iff T _ _).mp
    exact h f i g ((pointwiseIndex_toFoundation_iff T f i).mpr hfi)
  · intro h f i g hfi
    apply (pointwiseIndex_toFoundation_iff T _ _).mpr
    rw [compIndex_toFoundation, compIndex_toFoundation]
    exact h f i g ((pointwiseIndex_toFoundation_iff T f i).mp hfi)

/-- Full composition congruence is preserved and reflected. -/
theorem compositionCongruence_toFoundation_iff (T : Theory) :
    CompositionCongruence T ↔
      FailureOfComposition.ConcreteIndices.CompositionCongruence
        (TheoryCorrespondence.toFoundation T) := by
  constructor
  · intro h f f' g g' hff hgg
    rw [← compIndex_toFoundation, ← compIndex_toFoundation]
    apply (pointwiseIndex_toFoundation_iff T _ _).mp
    exact h f f' g g' ((pointwiseIndex_toFoundation_iff T f f').mpr hff)
      ((pointwiseIndex_toFoundation_iff T g g').mpr hgg)
  · intro h f f' g g' hff hgg
    apply (pointwiseIndex_toFoundation_iff T _ _).mpr
    rw [compIndex_toFoundation, compIndex_toFoundation]
    exact h f f' g g' ((pointwiseIndex_toFoundation_iff T f f').mp hff)
      ((pointwiseIndex_toFoundation_iff T g g').mp hgg)

/-- Agreement with equality of actual partial functions is preserved and reflected. -/
theorem agreesWithExtensional_toFoundation_iff (T : Theory) :
    AgreesWithExtensional T ↔
      FailureOfComposition.ConcreteIndices.AgreesWithExtensional
        (TheoryCorrespondence.toFoundation T) := by
  constructor
  · intro h e d
    exact (pointwiseIndex_toFoundation_iff T e d).symm.trans (h e d)
  · intro h e d
    exact (pointwiseIndex_toFoundation_iff T e d).trans (h e d)

/-- The independent four-way Π₁ characterization, transported from the
maintained concrete theorem with no enumerability or soundness hypothesis. -/
theorem pi_one_characterization
    (T : Theory) (hPA : DeductivelyExtends Peano T) (hCons : Consistent T) :
    (RightCompatible T ↔ CompositionCongruence T) ∧
    (CompositionCongruence T ↔ Arithmetic.PiOneComplete T) ∧
    (Arithmetic.PiOneComplete T ↔ AgreesWithExtensional T) := by
  let _ : FFL.Entailment.WeakerThan FFL.FirstOrder.Arithmetic.Peano
      (TheoryCorrespondence.toFoundation T) :=
    (deductivelyExtendsPeano_toFoundation_iff T).mp hPA
  let _ : FFL.Entailment.Consistent (TheoryCorrespondence.toFoundation T) :=
    (consistent_toFoundation_iff T).mp hCons
  rw [rightCompatible_toFoundation_iff,
    compositionCongruence_toFoundation_iff,
    Arithmetic.piOneComplete_toFoundation_iff,
    agreesWithExtensional_toFoundation_iff]
  exact FailureOfComposition.ConcreteIndices.pi_one_characterization
    (TheoryCorrespondence.toFoundation T)

end FailureOfComposition.Palomar.Arithmetic.Evaluator
