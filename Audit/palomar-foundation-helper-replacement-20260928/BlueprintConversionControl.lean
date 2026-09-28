module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Basic

/-!
# Narrow conversion control

This intentionally tiny proposition isolates the broad definitional reduction
of `blueprint.func.val`.  Its `rfl` proof is definitionally valid, but the
recorded bounded Lean elaboration did not finish before its 120-second deadline.
It is a reproducer, not a maintained proof dependency.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV

open FFL FirstOrder Arithmetic

def constructionFuncTermsProbe : Fin 2 → ArithmeticSemiterm Empty 5 :=
  ![FirstOrder.Semiterm.bvar 0, FirstOrder.Semiterm.bvar 4]

lemma constructionFuncBlueprintValProbe :
    blueprint.func.val =
      ((↑Arithmetic.listMaxDef : ArithmeticSemisentence 2) ⇜
        constructionFuncTermsProbe) := rfl

end FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV
