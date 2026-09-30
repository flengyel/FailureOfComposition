/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.Palomar.RangeBridge
import FailureOfComposition.RangeProductive

/-!
# Productive range-obstruction correspondence

This module transports the maintained productive proof through the range
correspondence already established for the independent interface.  It keeps the
maintained witness and does not identify the two classically chosen range
indices as natural numbers.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition.Palomar.Arithmetic.Evaluator

/-- Proposition 6, productive route, with the exact independent range selector
and public hypotheses. -/
theorem range_counterexample_productive
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
    FailureOfComposition.ConcreteIndices.range_counterexample_via_productiveness_of_re_axioms
      Tf ((reAxiomCodes_toFoundation_iff T).mp hT)
  refine ⟨u, ?_, ?_⟩
  · apply (pointwiseIndex_toFoundation_iff T _ _).mpr
    simpa using hu
  · intro h
    apply hn
    have h' := (rangeIndices_toFoundation_iff T hPA u emptyIndex).mp h
    simpa using h'

end FailureOfComposition.Palomar.Arithmetic.Evaluator
