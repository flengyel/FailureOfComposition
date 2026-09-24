/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ConcreteGodel
import FailureOfComposition.CraigPresentation

/-!
The concrete second-incompleteness obstruction for every consistent extension
of PA with recursively enumerable axiom codes. Craig's padded presentation
discharges the Delta-one presentation requirement of the proof predicate.
-/

set_option autoImplicit false



open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition.ConcreteIndices

theorem index_noncongruence_via_godel_of_re_axioms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (FailureOfComposition.AxiomCodes T)) :
    ∃ f i g : ℕ, PointwiseIndex T f i ∧
      ¬PointwiseIndex T
        (canonicalPartrecCompIndex f g) (canonicalPartrecCompIndex i g) := by
  obtain ⟨S, ⟨hS⟩, hST, hTS⟩ := CraigPresentation.exists_craig_presentation T hT
  letI : S.Δ₁ := hS
  exact index_noncongruence_via_godel_of_equivalent_presentation S T hST hTS

/-- The Gödel-II route, with the same r.e.-axiom assumptions as the independent
productive-set route and no realization or presentation hypothesis. -/
theorem no_index_quotient_via_godel_of_re_axioms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (FailureOfComposition.AxiomCodes T)) : NoIndexQuotientComposition T := by
  obtain ⟨f, i, g, hfi, hcomp⟩ := index_noncongruence_via_godel_of_re_axioms T hT
  exact no_quotient_composition_of_noncongruence (indexSetoid T)
    canonicalPartrecCompIndex f i g hfi hcomp

theorem no_index_quotient_via_godel_of_axiom_enumerator
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T] (a : ℕ)
    (ha : ∀ n : ℕ, AxiomCodes T n ↔ ∃ x : ℕ, n ∈ Kleene.eval a x) :
    NoIndexQuotientComposition T :=
  no_index_quotient_via_godel_of_re_axioms T
    (axiom_codes_re_of_program_enumerator T a ha)

end FailureOfComposition.ConcreteIndices
