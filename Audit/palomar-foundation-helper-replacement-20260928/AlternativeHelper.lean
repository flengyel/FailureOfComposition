module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Basic
import Lean.Elab.Term

/-!
# Exact replacement candidate for the bounded-variable construction field

This theorem restates the generated `func_defined` obligation from
`IsUTerm.BV.construction`.  It is a local experiment and is not wired into the
pinned Foundation dependency.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV

open FFL FirstOrder Arithmetic
open Lean Elab Term Meta

/- `type_of%` preserves the two reducible `IsDefinedBy` wrappers.  The generated
Foundation field's helper is stated after those wrappers have been unfolded, so
this diagnostic elaborator exposes only the reducible head of the inferred type.
It affects elaboration of the local comparison theorem, not its exported term. -/
elab "unfolded_type_of% " value:term : term => do
  let valueExpr ← elabTerm value none
  withReducible <| whnf (← inferType valueExpr)

variable {V : Type*} [ORingStructure V]

def constructionFuncAssignment (v : Fin 5 → V) : Fin 2 → V :=
  ![v 0, v 4]

lemma constructionFuncTerms_val (v : Fin 5 → V) :
    FirstOrder.Semiterm.val v Empty.elim ∘
        ((![FirstOrder.Semiterm.bvar 0, FirstOrder.Semiterm.bvar 4]) :
          Fin 2 → ArithmeticSemiterm Empty 5) =
      constructionFuncAssignment v := by
  apply Fin.funext_two
  · rfl
  · rfl
  · intro i
    exact Fin.elim0 i

lemma constructionFuncSubstitution_eval (v : Fin 5 → V) :
    (FirstOrder.Semiformula.Evalb v)
        ((↑Arithmetic.listMaxDef : ArithmeticSemisentence 2) ⇜
          ((![FirstOrder.Semiterm.bvar 0, FirstOrder.Semiterm.bvar 4]) :
            Fin 2 → ArithmeticSemiterm Empty 5)) ↔
      (FirstOrder.Semiformula.Evalb (constructionFuncAssignment v))
        (↑Arithmetic.listMaxDef : ArithmeticSemisentence 2) :=
  Iff.trans
    (FirstOrder.Semiformula.eval_substs
      ((![FirstOrder.Semiterm.bvar 0, FirstOrder.Semiterm.bvar 4]) :
        Fin 2 → ArithmeticSemiterm Empty 5)
      (↑Arithmetic.listMaxDef : ArithmeticSemisentence 2))
    (Iff.of_eq (congrArg
      (fun e ↦ (FirstOrder.Semiformula.Evalb e)
        (↑Arithmetic.listMaxDef : ArithmeticSemisentence 2))
      (constructionFuncTerms_val v)))

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma constructionFuncResult (v : Fin 5 → V) :
    (FirstOrder.Semiformula.Evalb (constructionFuncAssignment v))
        (↑Arithmetic.listMaxDef : ArithmeticSemisentence 2) ↔
      v 0 = (fun v : Fin (0 + 1 + 1 + 1 + 1) → V ↦
        Arithmetic.listMax (v 3))
        (fun x : Fin (0 + 1 + 1 + 1 + 1) ↦ v x.succ) := by
  have hDefined :
      (FirstOrder.Semiformula.Evalb (constructionFuncAssignment v))
          (↑Arithmetic.listMaxDef : ArithmeticSemisentence 2) ↔
        constructionFuncAssignment v 0 =
          (fun u : Fin 1 → V ↦ Arithmetic.listMax (u 0))
            (fun x : Fin 1 ↦ constructionFuncAssignment v x.succ) :=
    Arithmetic.listMax_defined.iff
  have hResult :
      constructionFuncAssignment v 0 =
          (fun u : Fin 1 → V ↦ Arithmetic.listMax (u 0))
            (fun x : Fin 1 ↦ constructionFuncAssignment v x.succ) ↔
        v 0 = (fun u : Fin (0 + 1 + 1 + 1 + 1) → V ↦
          Arithmetic.listMax (u 3))
          (fun x : Fin (0 + 1 + 1 + 1 + 1) ↦ v x.succ) := by
    change (v 0 = Arithmetic.listMax (v 4)) ↔
      (v 0 = Arithmetic.listMax (v 4))
    exact Iff.rfl
  exact hDefined.trans hResult

theorem constructionFuncDefinedReplacement :
    𝚺₁.DefinedFunction
      (fun v : Fin (0 + 1 + 1 + 1 + 1) → V ↦ Arithmetic.listMax (v 3))
      blueprint.func :=
  .mk fun v ↦ by
    unfold blueprint
    dsimp only [Language.TermRec.Blueprint.func]
    rw [HierarchySymbol.Semiformula.val_mkSigma]
    exact (constructionFuncSubstitution_eval v).trans
      (constructionFuncResult v)

theorem construction_func_defined_replacement :
    unfolded_type_of% (constructionFuncDefinedReplacement (V := V)).defined :=
  (constructionFuncDefinedReplacement (V := V)).defined

end FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV
