/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.Palomar.QuotientBridge

/-! Proved cumulative counterpart of the two-result Challenge checkpoint. -/

set_option autoImplicit false

namespace FailureOfComposition.Palomar

open Arithmetic Arithmetic.Evaluator

/-- Theorem 1: four properties of the productive indices with two internal uniform clauses. -/
theorem obstruction_four_properties
    (T : Arithmetic.Theory)
    (hPA : Arithmetic.DeductivelyExtends Arithmetic.Peano T)
    (hCons : Arithmetic.Consistent T)
    (hT : REPred (Arithmetic.AxiomCodes T)) :
    ∃ f g : ℕ,
      Arithmetic.Evaluator.PointwiseIndex T f Arithmetic.Evaluator.identityIndex ∧
      Arithmetic.Evaluator.UniformIndex T (Arithmetic.Evaluator.compIndex f g)
        Arithmetic.Evaluator.emptyIndex ∧
      Arithmetic.Evaluator.UniformIndex T
        (Arithmetic.Evaluator.compIndex Arithmetic.Evaluator.identityIndex g) g ∧
      ¬Arithmetic.Evaluator.PointwiseIndex T g Arithmetic.Evaluator.emptyIndex := by
  exact Arithmetic.Evaluator.obstruction_four_properties T hPA hCons hT

/-- Theorem 1 and Corollary 2: no operation on the pointwise-provability quotient can obey
the representative composition equation. -/
theorem no_quotient_composition_productive
    (T : Arithmetic.Theory)
    (hPA : Arithmetic.DeductivelyExtends Arithmetic.Peano T)
    (hCons : Arithmetic.Consistent T)
    (hT : REPred (Arithmetic.AxiomCodes T)) :
    ¬∃ C : Arithmetic.Evaluator.IndexQuotient T →
        Arithmetic.Evaluator.IndexQuotient T →
        Arithmetic.Evaluator.IndexQuotient T,
      ∀ e d : ℕ,
        C (Arithmetic.Evaluator.indexQuotientMk T e)
            (Arithmetic.Evaluator.indexQuotientMk T d) =
          Arithmetic.Evaluator.indexQuotientMk T
            (Arithmetic.Evaluator.compIndex e d) := by
  exact Arithmetic.Evaluator.no_quotient_composition_of_four_properties T hPA
    (obstruction_four_properties T hPA hCons hT)

end FailureOfComposition.Palomar
