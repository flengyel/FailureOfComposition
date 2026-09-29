module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions
import Lean.Elab.Term
import Lean.Util.CollectAxioms

/-!
# Standalone exact-type replacement for `TermSubst.construction._proof_2`

This diagnostic module is deliberately outside the maintained proof and the
submission path.  It factors the bound-variable proof without using the
existing `TermSubst.construction` or its generated proof helper.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubstDiagnostic

open Lean Elab Term Meta

elab "unfolded_type_of% " value:term : term => do
  let valueExpr ← elabTerm value none
  withReducible <| whnf (← inferType valueExpr)

variable {V : Type*} [ORingStructure V]

def constructionBvarAssignment (v : Fin 3 → V) : Fin 3 → V :=
  ![v 0, v 2, v 1]

lemma constructionBvarTerms_val (v : Fin 3 → V) :
    FirstOrder.Semiterm.val v Empty.elim ∘
        ((![FirstOrder.Semiterm.bvar 0, FirstOrder.Semiterm.bvar 2,
          FirstOrder.Semiterm.bvar 1]) :
          Fin 3 → ArithmeticSemiterm Empty 3) =
      constructionBvarAssignment v := by
  apply Fin.funext_two
  · rfl
  · rfl
  · intro i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i

lemma constructionBvarSubstitution_eval (v : Fin 3 → V) :
    (FirstOrder.Semiformula.Evalb v)
        ((↑Arithmetic.nthDef : ArithmeticSemisentence 3) ⇜
          ((![FirstOrder.Semiterm.bvar 0, FirstOrder.Semiterm.bvar 2,
            FirstOrder.Semiterm.bvar 1]) :
            Fin 3 → ArithmeticSemiterm Empty 3)) ↔
      (FirstOrder.Semiformula.Evalb (constructionBvarAssignment v))
        (↑Arithmetic.nthDef : ArithmeticSemisentence 3) :=
  Iff.trans
    (FirstOrder.Semiformula.eval_substs
      ((![FirstOrder.Semiterm.bvar 0, FirstOrder.Semiterm.bvar 2,
        FirstOrder.Semiterm.bvar 1]) :
        Fin 3 → ArithmeticSemiterm Empty 3)
      (↑Arithmetic.nthDef : ArithmeticSemisentence 3))
    (Iff.of_eq (congrArg
      (fun e ↦ (FirstOrder.Semiformula.Evalb e)
        (↑Arithmetic.nthDef : ArithmeticSemisentence 3))
      (constructionBvarTerms_val v)))

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma constructionBvarResult (v : Fin 3 → V) :
    (FirstOrder.Semiformula.Evalb (constructionBvarAssignment v))
        (↑Arithmetic.nthDef : ArithmeticSemisentence 3) ↔
      v 0 =
        (fun w : Fin (1 + 1) → V ↦
          Arithmetic.nth ((fun x : Fin 1 ↦ w x.succ) 1) (w 0))
          (fun x : Fin (1 + 1) ↦ v x.succ) := by
  have hDefined :
      (FirstOrder.Semiformula.Evalb (constructionBvarAssignment v))
          (↑Arithmetic.nthDef : ArithmeticSemisentence 3) ↔
        constructionBvarAssignment v 0 =
          (fun w : Fin (1 + 1) → V ↦ Arithmetic.nth (w 0) (w 1))
            (fun x : Fin (1 + 1) ↦
              (constructionBvarAssignment v) x.succ) :=
    Arithmetic.nth_defined.iff
  have hResult :
      constructionBvarAssignment v 0 =
          (fun w : Fin (1 + 1) → V ↦ Arithmetic.nth (w 0) (w 1))
            (fun x : Fin (1 + 1) ↦
              (constructionBvarAssignment v) x.succ) ↔
        v 0 =
          (fun w : Fin (1 + 1) → V ↦
            Arithmetic.nth ((fun x : Fin 1 ↦ w x.succ) 1) (w 0))
            (fun x : Fin (1 + 1) ↦ v x.succ) := by
    change (v 0 = Arithmetic.nth (v 2) (v 1)) ↔
      (v 0 = Arithmetic.nth (v 2) (v 1))
    exact Iff.rfl
  exact hDefined.trans hResult

lemma constructionBvarEvaluation (v : Fin 3 → V) :
    (FirstOrder.Semiformula.Evalb v) TermSubst.blueprint.bvar.val ↔
      v 0 =
        (fun w : Fin (1 + 1) → V ↦
          Arithmetic.nth ((fun x : Fin 1 ↦ w x.succ) 1) (w 0))
          (fun x : Fin (1 + 1) ↦ v x.succ) := by
  unfold TermSubst.blueprint
  dsimp only [Language.TermRec.Blueprint.bvar]
  rw [HierarchySymbol.Semiformula.val_mkSigma]
  exact (constructionBvarSubstitution_eval v).trans
    (constructionBvarResult v)

theorem constructionBvarFieldDefined :
    𝚺₁.DefinedFunction
      (fun w : Fin (1 + 1) → V ↦
        Arithmetic.nth ((fun x : Fin 1 ↦ w x.succ) 1) (w 0))
      TermSubst.blueprint.bvar :=
  .mk constructionBvarEvaluation

theorem constructionBvarDefinedExact :
    unfolded_type_of% (constructionBvarFieldDefined (V := V)).defined :=
  (constructionBvarFieldDefined (V := V)).defined

end FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubstDiagnostic

set_option autoImplicit false

open Lean Elab Command

namespace FailureOfComposition.Palomar.TermSubstStandaloneAudit

private def dependencies : ConstantInfo → Array Name
  | .axiomInfo value => value.type.getUsedConstants
  | .defnInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .thmInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .opaqueInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .ctorInfo value => value.type.getUsedConstants
  | .recInfo value => value.type.getUsedConstants
  | .inductInfo value => value.type.getUsedConstants ++ value.ctors.toArray
  | .quotInfo value => value.type.getUsedConstants

private partial def closure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : Except String NameSet := do
  match todo with
  | [] => return seen
  | name :: rest =>
    if seen.contains name then
      closure env rest seen
    else
      let some info := env.checked.get.find? name
        | throw s!"unresolved dependency: {name}"
      closure env ((dependencies info).toList ++ rest) (seen.insert name)

private def permittedAxiom (name : Name) : Bool :=
  name == `propext || name == `Classical.choice || name == `Quot.sound

run_cmd do
  let env ← getEnv
  let exactProof :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubstDiagnostic.constructionBvarDefinedExact
  let fieldProof :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubstDiagnostic.constructionBvarFieldDefined
  let forbidden := #[
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction,
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarDefined,
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarDefinedExact,
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_2
  ]
  let selected ← match closure env [exactProof, fieldProof] with
    | .ok result => pure result
    | .error message => throwError message
  let reachedForbidden := forbidden.filter selected.contains
  unless reachedForbidden.isEmpty do
    throwError m!"standalone replacement reaches integrated/original proof declarations: {reachedForbidden}"
  let exactAxioms ← Lean.collectAxioms exactProof
  let fieldAxioms ← Lean.collectAxioms fieldProof
  let axioms := (exactAxioms ++ fieldAxioms).foldl
    (fun names name => if names.contains name then names else names.push name) #[]
  let unexpected := axioms.filter fun name => !permittedAxiom name
  unless unexpected.isEmpty do
    throwError m!"unexpected axioms: {unexpected}"
  let sortedAxioms := axioms.qsort fun left right =>
    decide (left.toString < right.toString)
  logInfo "PASS standalone checker candidate excludes integrated/original construction proofs"
  logInfo m!"PASS standalone checker candidate axioms: {sortedAxioms}"
  logInfo m!"STANDALONE_CHECKER_CLOSURE count={selected.size}"

end FailureOfComposition.Palomar.TermSubstStandaloneAudit
