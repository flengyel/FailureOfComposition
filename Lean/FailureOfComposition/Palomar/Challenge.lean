/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ManuscriptObstruction
import FailureOfComposition.ConcretePiOneCharacterization
import FailureOfComposition.PartialRecursiveQuotient
import FailureOfComposition.RangeAssignment

/-!
# Draft statement interface for Palomar preparation

**DRAFT REVIEW INTERFACE: NOT ELIGIBLE UNDER THE CURRENT PALOMAR IMPORT POLICY.**
These imports reach Foundation and project-specific sources, including proved
results. Palomar currently forbids those dependencies in the Challenge import
closure. This file makes the intended statements reviewable; it does not solve
that eligibility problem or claim an independent, permitted statement kernel.
The nine deliberate theorem holes are confined to this draft. The separate
`Solution` module supplies declarations with the same names and types.

The statements cover the six numbered results of manuscript v36. The two
composition-obstruction routes and two range-obstruction routes remain separate
declarations; the final declaration records the generated quotient's concrete
partial-recursive monoid. The categorical corollary is represented by failure
of composition on the quotient of endomorphisms of omega, without claiming a
formal reconstruction of every historical multiobject syntactic category.

`PointwiseIndex T e d` means that, for every **external standard** input `n`,
`T` proves equality of the two partial computations at that numeral.
`UniformIndex` instead asserts one universally quantified graph equality in `T`.
The evaluator is the constructed PA arithmetization of Mathlib program indices;
`Kleene.eval` is their actual partial-function evaluation. All quantifiers over
indices below range over the natural numbers. No arithmetization, realization,
Delta-one presentation, or soundness assumption is hidden in the r.e. results.

`GeneratedRel` is the intersection of all equivalence relations compatible with
the displayed program composition and containing `PointwiseIndex`.
`WeaklyTotalIndex T e` says that every program whose composite with `e` is
pointwise provably empty is itself pointwise provably empty. `rangeIndex e`
realizes the partial identity on the range, with its graph equation proved
uniformly in PA; standard-model agreement alone is not the specification.
-/

set_option autoImplicit false

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition.Palomar

open ConcreteIndices ConcreteEmptyGraph

/-- Theorem 1: four witnesses for every consistent r.e. extension of PA.
The middle clauses retain uniform provability, rather than only its instances. -/
theorem obstruction_four_properties
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ∃ f g : ℕ, PointwiseIndex T f Kleene.identityIndex ∧
      UniformIndex T (canonicalPartrecCompIndex f g) concreteEmptyIndex ∧
      UniformIndex T (canonicalPartrecCompIndex Kleene.identityIndex g) g ∧
      ¬PointwiseIndex T g concreteEmptyIndex := by
  sorry

/-- Theorem 1 and Corollary 2, productive route: no binary operation on the
actual pointwise quotient satisfies the representative composition equation. -/
theorem no_quotient_composition_productive
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ¬∃ C : Quotient (indexSetoid T) → Quotient (indexSetoid T) →
        Quotient (indexSetoid T),
      ∀ e d : ℕ, C (Quotient.mk (indexSetoid T) e) (Quotient.mk (indexSetoid T) d) =
        Quotient.mk (indexSetoid T) (canonicalPartrecCompIndex e d) := by
  sorry

/-- The same obstruction, with the same assumptions, by the separate Gödel-II
route. The proof-dependency audits distinguish these routes. -/
theorem no_quotient_composition_godel
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ¬∃ C : Quotient (indexSetoid T) → Quotient (indexSetoid T) →
        Quotient (indexSetoid T),
      ∀ e d : ℕ, C (Quotient.mk (indexSetoid T) e) (Quotient.mk (indexSetoid T) d) =
        Quotient.mk (indexSetoid T) (canonicalPartrecCompIndex e d) := by
  sorry

/-- Theorem 3: for every consistent PA extension, right compatibility,
composition congruence, completeness for true Pi-one sentences, and agreement
with actual partial-function equality are equivalent. No r.e. assumption. -/
theorem pi_one_characterization (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T] :
    (RightCompatible T ↔ CompositionCongruence T) ∧
    (CompositionCongruence T ↔ PiOneCharacterization.PiOneComplete T) ∧
    (PiOneCharacterization.PiOneComplete T ↔ AgreesWithExtensional T) := by
  sorry

/-- Theorem 4: the least generated composition congruence is extensional in
the Sigma-one sound case and universal otherwise. Only PA extension is assumed. -/
theorem generated_congruence_classification (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    (GeneratedCongruence.SigmaOneSound T →
      ∀ e d : ℕ, GeneratedRel T e d ↔ Kleene.eval e = Kleene.eval d) ∧
    (¬GeneratedCongruence.SigmaOneSound T → ∀ e d : ℕ, GeneratedRel T e d) := by
  sorry

/-- Proposition 5: a concrete guard is pointwise provably equal to identity,
although identity is weakly total and the guard is not. -/
theorem weak_totality_counterexample
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ∃ d : ℕ, PointwiseIndex T (guardIndex d) Kleene.identityIndex ∧
      ¬WeaklyTotalIndex T (guardIndex d) ∧ WeaklyTotalIndex T Kleene.identityIndex := by
  sorry

/-- Proposition 6, Gödel-II route: an index pointwise provably equal to the
empty program has a range index inequivalent to the range index of that empty program. -/
theorem range_counterexample_godel
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ∃ u : ℕ, PointwiseIndex T u concreteEmptyIndex ∧
      ¬PointwiseIndex T (rangeIndex u) (rangeIndex concreteEmptyIndex) := by
  sorry

/-- Proposition 6 with the identical statement, proved by the productive route. -/
theorem range_counterexample_productive
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ∃ u : ℕ, PointwiseIndex T u concreteEmptyIndex ∧
      ¬PointwiseIndex T (rangeIndex u) (rangeIndex concreteEmptyIndex) := by
  sorry

/-- In the Sigma-one sound case, the generated quotient is isomorphic to the
monoid of actual unary partial recursive functions under partial composition.
The representative equation fixes the isomorphism to ordinary evaluation. -/
theorem generated_quotient_partial_recursive
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (hT : GeneratedCongruence.SigmaOneSound T) :
    ∃ E : GeneratedQuotient T ≃* UnaryPartrec,
      ∀ e : ℕ, E (generatedQuotientMk T e) = UnaryPartrec.ofIndex e := by
  sorry

end FailureOfComposition.Palomar
