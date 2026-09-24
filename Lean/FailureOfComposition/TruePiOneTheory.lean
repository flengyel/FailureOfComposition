/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ConcretePiOneCharacterization

/-!
The example after manuscript Theorem 3: adjoining every true Pi-one sentence
to PA gives a consistent Pi-one-complete theory. Its axiom and theorem codes
are not recursively enumerable. The nonenumerability proof uses the existing
productive obstruction and the characterization theorem.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition.PiOneCharacterization

/-- PA with all true Pi-one arithmetic sentences adjoined as axioms. -/
def truePiOneExtension : ArithmeticTheory :=
  𝗣𝗔 ∪ {σ : ArithmeticSentence | Hierarchy 𝚷 1 σ ∧ ℕ↓[ℒₒᵣ] ⊧ σ}

instance truePiOneExtension_extends_pa : 𝗣𝗔 ⪯ truePiOneExtension :=
  Axiomatized.le_of_subset fun _ h => Or.inl h

instance truePiOneExtension_standard_model : ℕ↓[ℒₒᵣ] ⊧* truePiOneExtension := by
  constructor
  intro σ hσ
  rcases hσ with hσ | hσ
  · exact (inferInstance : ℕ↓[ℒₒᵣ] ⊧* 𝗣𝗔).models_set hσ
  · exact hσ.2

instance truePiOneExtension_consistent : Consistent truePiOneExtension :=
  consistent_of_model truePiOneExtension ℕ

/-- Every true Pi-one sentence is already an axiom of this extension. -/
theorem truePiOneExtension_piOneComplete : PiOneComplete truePiOneExtension :=
  fun _ hσ htrue => by_axm (Or.inr ⟨hσ, htrue⟩)

/-- The example satisfies the manuscript's composition-congruence condition. -/
theorem truePiOneExtension_compositionCongruence :
    ConcreteIndices.CompositionCongruence truePiOneExtension :=
  (ConcreteIndices.compositionCongruence_iff_piOneComplete truePiOneExtension).mpr
    truePiOneExtension_piOneComplete

/-- Its pointwise quotient identifies exactly extensionally equal programs. -/
theorem truePiOneExtension_agreesWithExtensional :
    ConcreteIndices.AgreesWithExtensional truePiOneExtension :=
  (ConcreteIndices.agreesWithExtensional_iff_piOneComplete truePiOneExtension).mpr
    truePiOneExtension_piOneComplete

/-- The productive obstruction excludes an enumerable set of theorem codes. -/
theorem truePiOneExtension_theorem_codes_not_re :
    ¬REPred (TheoremCodes truePiOneExtension) := by
  intro hT
  exact (ConcreteIndices.no_index_quotient_iff_not_piOneComplete truePiOneExtension).mp
    (ConcreteIndices.no_index_quotient_via_productiveness truePiOneExtension hT)
    truePiOneExtension_piOneComplete

/-- In particular, this axiom presentation is not recursively enumerable. -/
theorem truePiOneExtension_axiom_codes_not_re :
    ¬REPred (AxiomCodes truePiOneExtension) :=
  fun hT => truePiOneExtension_theorem_codes_not_re
    (theorem_codes_re_of_axiom_codes truePiOneExtension hT)

end FailureOfComposition.PiOneCharacterization
