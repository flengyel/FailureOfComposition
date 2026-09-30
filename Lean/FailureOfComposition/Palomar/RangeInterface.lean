/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.Palomar.EvaluatorInterface

/-!
# Independent range-program interface

The selector is fixed by the existence-free `Classical.epsilon` definition.
Its PA-uniform correctness is proved on the Solution side.
-/

set_option autoImplicit false

namespace FailureOfComposition.Palomar.Arithmetic.Evaluator

/-- The partial identity on the image of a binary program graph. -/
def rangeOfGraph (F : Graph) : Graph :=
  .and (.equal (.bvar fin0) (.bvar fin1))
    (.exs (F.subst ![.bvar fin0, .bvar fin1]))

/-- The range partial identity of the fixed evaluator program `e`. -/
def rangeGraph (e : ℕ) : Graph :=
  rangeOfGraph (eventualGraph e)

/-- One PA-internal equation between two binary graphs. -/
def uniformGraphSentence (F G : Graph) : Sentence :=
  .all (.all (biimp
    (F.subst ![.bvar fin1, .bvar fin0])
    (G.subst ![.bvar fin1, .bvar fin0])))

/-- A concrete index realizes the independent range graph by one PA proof. -/
def RangeRealizes (e r : ℕ) : Prop :=
  Provable Peano (uniformGraphSentence (eventualGraph r) (rangeGraph e))

/-- A fixed independent range-index assignment.  Existence is not assumed by
the definition and is proved in the Solution correspondence. -/
noncomputable def rangeIndex (e : ℕ) : ℕ :=
  Classical.epsilon (RangeRealizes e)

end FailureOfComposition.Palomar.Arithmetic.Evaluator
