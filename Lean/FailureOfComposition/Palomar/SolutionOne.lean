/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.Palomar.ObstructionBridge

/-! Proved counterpart of the temporary first-result Challenge checkpoint. -/

set_option autoImplicit false

namespace FailureOfComposition.Palomar

open Arithmetic Arithmetic.Evaluator

/-- Theorem 1: four witnesses for every consistent recursively enumerable
extension of PA; the middle clauses are single uniform proofs. -/
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

end FailureOfComposition.Palomar
