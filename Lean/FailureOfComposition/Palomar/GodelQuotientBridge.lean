/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.Palomar.QuotientBridge
public import FailureOfComposition.ConcreteGodelRE

/-!
# Gödel-II quotient obstruction for the independent Palomar interface

This file transports the maintained Gödel-II/Craig-presentation proof through
the already checked theory and quotient correspondences.  The productive and
Gödel-II routes remain separate proof roots.
-/

@[expose] public section

set_option autoImplicit false

namespace FailureOfComposition.Palomar.Arithmetic.Evaluator

/-- Failure of representative-respecting composition on the independent
pointwise quotient, using the maintained Gödel-II route.  Craig's Delta-one
presentation remains internal to the maintained theorem. -/
theorem no_quotient_composition_godel
    (T : Theory) (hPA : DeductivelyExtends Peano T) (hCons : Consistent T)
    (hT : REPred (AxiomCodes T)) :
    ¬∃ C : IndexQuotient T → IndexQuotient T → IndexQuotient T,
      ∀ e d : ℕ,
        C (indexQuotientMk T e) (indexQuotientMk T d) =
          indexQuotientMk T (compIndex e d) := by
  apply (noIndexQuotientComposition_iff_maintained T hPA).mpr
  let _ : FFL.Entailment.WeakerThan FFL.FirstOrder.Arithmetic.Peano
      (TheoryCorrespondence.toFoundation T) :=
    (deductivelyExtendsPeano_toFoundation_iff T).mp hPA
  let _ : FFL.Entailment.Consistent (TheoryCorrespondence.toFoundation T) :=
    (consistent_toFoundation_iff T).mp hCons
  exact
    FailureOfComposition.ConcreteIndices.no_index_quotient_via_godel_of_re_axioms
      (TheoryCorrespondence.toFoundation T)
      ((reAxiomCodes_toFoundation_iff T).mp hT)

end FailureOfComposition.Palomar.Arithmetic.Evaluator
