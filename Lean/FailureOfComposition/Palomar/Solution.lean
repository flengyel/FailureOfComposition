/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ManuscriptObstruction
import FailureOfComposition.ConcreteGodelRE
import FailureOfComposition.ConcretePiOneCharacterization
import FailureOfComposition.PartialRecursiveQuotient
import FailureOfComposition.RangeGodel
import FailureOfComposition.RangeProductive

/-!
# Proved counterpart of the draft Palomar statement interface

This module supplies the nine draft declarations independently of `Challenge`.
It does not import that module or its deliberate theorem holes. The theorem
names and types agree with the draft, and the proofs use the maintained concrete
formalization without new axioms or supplied arithmetization assumptions.

**This paired preparation does not make the Challenge eligible under Palomar's
current import policy.** Its Foundation and project-specific import closure
still needs a legitimate statement-interface solution before submission.

The productive and Gödel-II declarations deliberately use separate proof roots.
Their dependency separation is an audited property of these proofs, not a claim
of logical independence between unspecified formal sentences. Mathematical and
historical scope is documented in the draft and the manuscript coverage map.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
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
  exact ConcreteIndices.obstruction_four_properties_of_re_axioms T hT

/-- Theorem 1 and Corollary 2, productive route: no binary operation on the
actual pointwise quotient satisfies the representative composition equation. -/
theorem no_quotient_composition_productive
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ¬∃ C : Quotient (indexSetoid T) → Quotient (indexSetoid T) →
        Quotient (indexSetoid T),
      ∀ e d : ℕ, C (Quotient.mk (indexSetoid T) e) (Quotient.mk (indexSetoid T) d) =
        Quotient.mk (indexSetoid T) (canonicalPartrecCompIndex e d) := by
  exact ConcreteIndices.no_index_quotient_of_re_axioms T hT

/-- The same obstruction, with the same assumptions, by the separate Gödel-II
route. The proof-dependency audits distinguish these routes. -/
theorem no_quotient_composition_godel
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ¬∃ C : Quotient (indexSetoid T) → Quotient (indexSetoid T) →
        Quotient (indexSetoid T),
      ∀ e d : ℕ, C (Quotient.mk (indexSetoid T) e) (Quotient.mk (indexSetoid T) d) =
        Quotient.mk (indexSetoid T) (canonicalPartrecCompIndex e d) := by
  exact ConcreteIndices.no_index_quotient_via_godel_of_re_axioms T hT

/-- Theorem 3: for every consistent PA extension, right compatibility,
composition congruence, completeness for true Pi-one sentences, and agreement
with actual partial-function equality are equivalent. No r.e. assumption. -/
theorem pi_one_characterization (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T] :
    (RightCompatible T ↔ CompositionCongruence T) ∧
    (CompositionCongruence T ↔ PiOneCharacterization.PiOneComplete T) ∧
    (PiOneCharacterization.PiOneComplete T ↔ AgreesWithExtensional T) := by
  exact ConcreteIndices.pi_one_characterization T

/-- Theorem 4: the least generated composition congruence is extensional in
the Sigma-one sound case and universal otherwise. Only PA extension is assumed. -/
theorem generated_congruence_classification (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    (GeneratedCongruence.SigmaOneSound T →
      ∀ e d : ℕ, GeneratedRel T e d ↔ Kleene.eval e = Kleene.eval d) ∧
    (¬GeneratedCongruence.SigmaOneSound T → ∀ e d : ℕ, GeneratedRel T e d) := by
  exact ConcreteIndices.generated_congruence_classification T

/-- Proposition 5: a concrete guard is pointwise provably equal to identity,
although identity is weakly total and the guard is not. -/
theorem weak_totality_counterexample
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ∃ d : ℕ, PointwiseIndex T (guardIndex d) Kleene.identityIndex ∧
      ¬WeaklyTotalIndex T (guardIndex d) ∧ WeaklyTotalIndex T Kleene.identityIndex := by
  exact ConcreteIndices.weak_totality_counterexample_of_re_axioms T hT

/-- Proposition 6, Gödel-II route: an index pointwise provably equal to the
empty program has a range index inequivalent to the range index of that empty program. -/
theorem range_counterexample_godel
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ∃ u : ℕ, PointwiseIndex T u concreteEmptyIndex ∧
      ¬PointwiseIndex T (rangeIndex u) (rangeIndex concreteEmptyIndex) := by
  exact ConcreteIndices.range_counterexample_of_re_axioms T hT

/-- Proposition 6 with the identical statement, proved by the productive route. -/
theorem range_counterexample_productive
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ∃ u : ℕ, PointwiseIndex T u concreteEmptyIndex ∧
      ¬PointwiseIndex T (rangeIndex u) (rangeIndex concreteEmptyIndex) := by
  exact ConcreteIndices.range_counterexample_via_productiveness_of_re_axioms T hT

/-- In the Sigma-one sound case, the generated quotient is isomorphic to the
monoid of actual unary partial recursive functions under partial composition.
The representative equation fixes the isomorphism to ordinary evaluation. -/
theorem generated_quotient_partial_recursive
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (hT : GeneratedCongruence.SigmaOneSound T) :
    ∃ E : GeneratedQuotient T ≃* UnaryPartrec,
      ∀ e : ℕ, E (generatedQuotientMk T e) = UnaryPartrec.ofIndex e := by
  refine ⟨ConcreteIndices.generatedQuotientPartialRecursiveEquiv T hT, ?_⟩
  intro e
  exact ConcreteIndices.generatedQuotientPartialRecursiveEquiv_mk T hT e

end FailureOfComposition.Palomar
