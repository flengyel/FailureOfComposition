module

public import FailureOfComposition.Palomar.RangeBridge

/-! Exact-type negative fixture using the wrong range-counterexample proof route. -/

@[expose] public section

set_option autoImplicit false

namespace FailureOfComposition.Palomar.NineWrongRoute

open Arithmetic Arithmetic.Evaluator

/-- Negative fixture: the nineh statement with the already accepted Gödel-II
proof route substituted for the required productive route. -/
theorem range_counterexample_productive
    (T : Arithmetic.Theory)
    (hPA : Arithmetic.DeductivelyExtends Arithmetic.Peano T)
    (hCons : Arithmetic.Consistent T)
    (hT : REPred (Arithmetic.AxiomCodes T)) :
    ∃ u : ℕ, Arithmetic.Evaluator.PointwiseIndex T u
        Arithmetic.Evaluator.emptyIndex ∧
      ¬Arithmetic.Evaluator.PointwiseIndex T
        (Arithmetic.Evaluator.rangeIndex u)
        (Arithmetic.Evaluator.rangeIndex Arithmetic.Evaluator.emptyIndex) := by
  exact Arithmetic.Evaluator.range_counterexample_godel T hPA hCons hT

end FailureOfComposition.Palomar.NineWrongRoute
