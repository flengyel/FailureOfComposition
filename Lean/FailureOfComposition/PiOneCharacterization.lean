/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.PiOneNecessity
import FailureOfComposition.PiOneExtensionality
import FailureOfComposition.PiOneCongruence
import FailureOfComposition.QuotientComposition

/-!
Characterization of congruence by Pi-one completeness.
-/

set_option autoImplicit false

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

namespace FailureOfComposition.PiOneCharacterization
open ProofSearch

/-- For a consistent extension of PA, right composition is compatible exactly
when every true Pi-one sentence is provable. No enumerability is assumed. -/
theorem rightCompatible_iff_piOneComplete (T : ArithmeticTheory)
    [𝗣𝗔 ⪯ T] [Consistent T] : RightCompatible T ↔ PiOneComplete T := by
  constructor
  · exact rightCompatible_implies_piOneComplete T
  · intro h
    exact rightCompatible_of_pointwise_iff_extensional T
      (fun F G hF hG => pointwise_iff_extensional T h F G hF hG)

theorem compositionCongruence_iff_piOneComplete (T : ArithmeticTheory)
    [𝗣𝗔 ⪯ T] [Consistent T] : CompositionCongruence T ↔ PiOneComplete T :=
  (congruence_iff_rightCompatible T).trans (rightCompatible_iff_piOneComplete T)

theorem agreesWithExtensional_iff_piOneComplete (T : ArithmeticTheory)
    [𝗣𝗔 ⪯ T] [Consistent T] : AgreesWithExtensional T ↔ PiOneComplete T := by
  constructor
  · intro h
    exact rightCompatible_implies_piOneComplete T
      (rightCompatible_of_pointwise_iff_extensional T h)
  · intro h F G hF hG
    exact pointwise_iff_extensional T h F G hF hG

/-- The four statements in the manuscript's characterization theorem. -/
theorem characterization (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T] :
    (RightCompatible T ↔ CompositionCongruence T) ∧
    (CompositionCongruence T ↔ PiOneComplete T) ∧
    (PiOneComplete T ↔ AgreesWithExtensional T) :=
  ⟨(congruence_iff_rightCompatible T).symm,
    compositionCongruence_iff_piOneComplete T,
    (agreesWithExtensional_iff_piOneComplete T).symm⟩

theorem quotient_composition_exists_iff_congruence (T : ArithmeticTheory)
    [𝗣𝗔 ⪯ T] :
    (∃ C : Quotient (pointwiseSetoid T) → Quotient (pointwiseSetoid T) →
      Quotient (pointwiseSetoid T),
      ∀ F G, C (Quotient.mk (pointwiseSetoid T) F)
        (Quotient.mk (pointwiseSetoid T) G) =
        Quotient.mk (pointwiseSetoid T) (functionalComp F G)) ↔
    CompositionCongruence T := by
  rw [FailureOfComposition.quotient_composition_exists_iff]
  constructor
  · intro h F F' G G' hF hF' hG hG' hFF' hGG'
    exact h ⟨F, hF⟩ ⟨F', hF'⟩ ⟨G, hG⟩ ⟨G', hG'⟩ hFF' hGG'
  · intro h F F' G G' hFF' hGG'
    exact h F.val F'.val G.val G'.val F.property F'.property G.property G'.property
      hFF' hGG'

theorem no_quotient_composition_iff_not_piOneComplete (T : ArithmeticTheory)
    [𝗣𝗔 ⪯ T] [Consistent T] : NoQuotientComposition T ↔ ¬PiOneComplete T := by
  unfold NoQuotientComposition
  exact not_congr ((quotient_composition_exists_iff_congruence T).trans
    (compositionCongruence_iff_piOneComplete T))

end FailureOfComposition.PiOneCharacterization
