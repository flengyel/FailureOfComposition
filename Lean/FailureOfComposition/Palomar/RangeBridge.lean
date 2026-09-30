/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.Palomar.RangeInterface
import FailureOfComposition.Palomar.EvaluatorBridge
import FailureOfComposition.RangeGodel

/-!
# Range-assignment correspondence

The independent and maintained selectors need not be the same natural number.
Their PA-uniform graph equations imply pointwise equivalence over every
deductive extension of PA.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition.Palomar.Arithmetic.Evaluator

@[simp] theorem toFoundation_rangeGraph (e : ℕ) :
    Formula.toFoundation (rangeGraph e) =
      (FailureOfComposition.ConcreteIndices.rangeGraph e).val := by
  simp [rangeGraph, rangeOfGraph,
    FailureOfComposition.ConcreteIndices.rangeGraph,
    FailureOfComposition.ConcreteIndices.rangeOfGraph,
    Formula.toFoundation_and, Formula.toFoundation_equal,
    Formula.toFoundation_exs, Formula.toFoundation_subst,
    Term.toFoundation_bvar, Matrix.fun_eq_vec_two]

@[simp] theorem toFoundation_rangeRealizesSentence (e r : ℕ) :
    Formula.toFoundation
        (uniformGraphSentence (eventualGraph r) (rangeGraph e)) =
      FailureOfComposition.ProofSearch.uniformSentence
        (FailureOfComposition.ConcreteEvaluator.eventualGraph r)
        (FailureOfComposition.ConcreteIndices.rangeGraph e) := by
  simp [uniformGraphSentence,
    FailureOfComposition.ProofSearch.uniformSentence,
    Formula.toFoundation_all, toFoundation_biimp,
    Formula.toFoundation_subst, Term.toFoundation_bvar,
    Matrix.fun_eq_vec_two]

/-- The independent realization predicate is exactly the maintained PA-uniform
graph equation. -/
theorem rangeRealizes_toFoundation_iff (e r : ℕ) :
    RangeRealizes e r ↔
      FailureOfComposition.ProofSearch.Uniform
        FFL.FirstOrder.Arithmetic.Peano
        (FailureOfComposition.ConcreteEvaluator.eventualGraph r)
        (FailureOfComposition.ConcreteIndices.rangeGraph e) := by
  unfold RangeRealizes FailureOfComposition.ProofSearch.Uniform
  rw [provable_toFoundation_iff, TheoryCorrespondence.peano_toFoundation,
    toFoundation_rangeRealizesSentence]
  rfl

/-- Every source index has an independent range realization. -/
theorem exists_rangeRealizes (e : ℕ) : ∃ r : ℕ, RangeRealizes e r := by
  refine ⟨FailureOfComposition.ConcreteIndices.rangeIndex e, ?_⟩
  exact (rangeRealizes_toFoundation_iff e _).mpr
    (FailureOfComposition.ConcreteIndices.rangeIndex_realizes e)

/-- The fixed epsilon selector satisfies its defining PA-uniform equation. -/
theorem rangeIndex_realizes (e : ℕ) : RangeRealizes e (rangeIndex e) := by
  exact Classical.epsilon_spec (exists_rangeRealizes e)

/-- The fixed independent choice and the maintained choice represent the same
pointwise class over every deductive extension of PA. -/
theorem rangeIndex_choice_toFoundation
    (T : Theory) (hPA : DeductivelyExtends Peano T) (e : ℕ) :
    FailureOfComposition.ConcreteIndices.PointwiseIndex
      (TheoryCorrespondence.toFoundation T) (rangeIndex e)
      (FailureOfComposition.ConcreteIndices.rangeIndex e) := by
  let _ : FFL.Entailment.WeakerThan FFL.FirstOrder.Arithmetic.Peano
      (TheoryCorrespondence.toFoundation T) :=
    (deductivelyExtendsPeano_toFoundation_iff T).mp hPA
  exact FailureOfComposition.ConcreteIndices.rangeIndex_choice_independent
    (TheoryCorrespondence.toFoundation T)
    ((rangeRealizes_toFoundation_iff e (rangeIndex e)).mp
      (rangeIndex_realizes e))

/-- Pointwise equality between two independent range choices is equivalent to
pointwise equality between the corresponding maintained choices.  Both
operands use choice independence. -/
theorem rangeIndices_toFoundation_iff
    (T : Theory) (hPA : DeductivelyExtends Peano T) (e d : ℕ) :
    PointwiseIndex T (rangeIndex e) (rangeIndex d) ↔
      FailureOfComposition.ConcreteIndices.PointwiseIndex
        (TheoryCorrespondence.toFoundation T)
        (FailureOfComposition.ConcreteIndices.rangeIndex e)
        (FailureOfComposition.ConcreteIndices.rangeIndex d) := by
  let _ : FFL.Entailment.WeakerThan FFL.FirstOrder.Arithmetic.Peano
      (TheoryCorrespondence.toFoundation T) :=
    (deductivelyExtendsPeano_toFoundation_iff T).mp hPA
  let eqv := (FailureOfComposition.ConcreteIndices.indexSetoid
    (TheoryCorrespondence.toFoundation T)).iseqv
  have he := rangeIndex_choice_toFoundation T hPA e
  have hd := rangeIndex_choice_toFoundation T hPA d
  constructor
  · intro h
    have h' := (pointwiseIndex_toFoundation_iff T _ _).mp h
    exact eqv.trans (eqv.symm he) (eqv.trans h' hd)
  · intro h
    apply (pointwiseIndex_toFoundation_iff T _ _).mpr
    exact eqv.trans he (eqv.trans h (eqv.symm hd))

/-- The seventh independent result, transported from the maintained Gödel-II
range obstruction without changing its witness or public assumptions. -/
theorem range_counterexample_godel
    (T : Theory) (hPA : DeductivelyExtends Peano T) (hCons : Consistent T)
    (hT : REPred (AxiomCodes T)) :
    ∃ u : ℕ, PointwiseIndex T u emptyIndex ∧
      ¬PointwiseIndex T (rangeIndex u) (rangeIndex emptyIndex) := by
  let Tf := TheoryCorrespondence.toFoundation T
  let _ : FFL.Entailment.WeakerThan FFL.FirstOrder.Arithmetic.Peano Tf :=
    (deductivelyExtendsPeano_toFoundation_iff T).mp hPA
  let _ : FFL.Entailment.Consistent Tf :=
    (consistent_toFoundation_iff T).mp hCons
  obtain ⟨u, hu, hn⟩ :=
    FailureOfComposition.ConcreteIndices.range_counterexample_of_re_axioms
      Tf ((reAxiomCodes_toFoundation_iff T).mp hT)
  refine ⟨u, ?_, ?_⟩
  · apply (pointwiseIndex_toFoundation_iff T _ _).mpr
    simpa using hu
  · intro h
    apply hn
    have h' := (rangeIndices_toFoundation_iff T hPA u emptyIndex).mp h
    simpa using h'

end FailureOfComposition.Palomar.Arithmetic.Evaluator
