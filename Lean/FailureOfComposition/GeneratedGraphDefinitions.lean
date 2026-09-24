/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.CompositionClosure
import FailureOfComposition.ProgramIndices
import FailureOfComposition.PiOneDefinitions

/-!
Definitions and closure laws for the generated graph congruence.
-/

set_option autoImplicit false

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

namespace FailureOfComposition.GeneratedCongruence
open ProofSearch

/-- The least composition congruence on PA-functional Sigma-one graphs
containing external pointwise provability in T. -/
def Rel (T : ArithmeticTheory) (F G : FunctionalGraph) : Prop :=
  CompositionClosure.Generated functionalComp
    (fun H K : FunctionalGraph => Pointwise T H.val K.val) F G

theorem rel_base (T : ArithmeticTheory) {F G : FunctionalGraph}
    (h : Pointwise T F.val G.val) : Rel T F G := by
  intro R _ hR
  exact hR F G h

theorem rel_refl (T : ArithmeticTheory) (F : FunctionalGraph) : Rel T F F := by
  intro R hR _
  exact hR.1.refl F

theorem rel_symm (T : ArithmeticTheory) {F G : FunctionalGraph}
    (h : Rel T F G) : Rel T G F := by
  intro R hR hb
  exact hR.1.symm (h R hR hb)

theorem rel_trans (T : ArithmeticTheory) {F G H : FunctionalGraph}
    (hFG : Rel T F G) (hGH : Rel T G H) : Rel T F H := by
  intro R hR hb
  exact hR.1.trans (hFG R hR hb) (hGH R hR hb)

theorem rel_comp (T : ArithmeticTheory) {F F' G G' : FunctionalGraph}
    (hF : Rel T F F') (hG : Rel T G G') :
    Rel T (functionalComp F G) (functionalComp F' G') := by
  intro R hR hb
  exact hR.2 F F' G G' (hF R hR hb) (hG R hR hb)

theorem rel_of_uniform (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {F G : FunctionalGraph} (h : Uniform 𝗣𝗔 F.val G.val) : Rel T F G :=
  rel_base T (ProgramIndices.uniform_to_pointwise T h)

def graphSetoid (T : ArithmeticTheory) : Setoid FunctionalGraph where
  r := Rel T
  iseqv := ⟨rel_refl T, rel_symm T, rel_trans T⟩

end FailureOfComposition.GeneratedCongruence
