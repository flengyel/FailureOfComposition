module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions
import Lean
import Lean.Elab.Term
import Lean.Util.CollectAxioms

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst

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
          (fun w : Fin (1 + 1) → V ↦
            Arithmetic.nth (w 0) (w 1))
            (fun x : Fin (1 + 1) ↦
              (constructionBvarAssignment v) x.succ) :=
    Arithmetic.nth_defined.iff
  have hResult :
      constructionBvarAssignment v 0 =
          (fun w : Fin (1 + 1) → V ↦
            Arithmetic.nth (w 0) (w 1))
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

theorem constructionBvarEvaluation
    (v : Fin (1 + 1 + 1) → V) :
    (FirstOrder.Semiformula.Evalb v) blueprint.bvar.val ↔
      v 0 =
        (fun w : Fin (1 + 1) → V ↦
          Arithmetic.nth ((fun x : Fin 1 ↦ w x.succ) 1) (w 0))
          (fun x : Fin (1 + 1) ↦ v x.succ) := by
  unfold blueprint
  dsimp only [Language.TermRec.Blueprint.bvar]
  rw [HierarchySymbol.Semiformula.val_mkSigma]
  exact (constructionBvarSubstitution_eval v).trans
    (constructionBvarResult v)

theorem constructionBvarFieldDefined :
    𝚺₁.DefinedFunction
      (fun w : Fin (1 + 1) → V ↦
        Arithmetic.nth ((fun x : Fin 1 ↦ w x.succ) 1) (w 0))
      blueprint.bvar :=
  .mk constructionBvarEvaluation

theorem constructionBvarDefinedExact :
    unfolded_type_of% (constructionBvarFieldDefined (V := V)).defined :=
  (constructionBvarFieldDefined (V := V)).defined

end FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst

set_option autoImplicit false

open Lean Elab Command

namespace FailureOfComposition.Palomar.TermSubstReplacementAudit

private partial def canonicalBinders : Expr → Expr
  | .app f a => .app (canonicalBinders f) (canonicalBinders a)
  | .lam _ type body binderInfo =>
    .lam .anonymous (canonicalBinders type) (canonicalBinders body) binderInfo
  | .forallE _ type body binderInfo =>
    .forallE .anonymous (canonicalBinders type) (canonicalBinders body) binderInfo
  | .letE _ type value body nondep =>
    .letE .anonymous (canonicalBinders type) (canonicalBinders value)
      (canonicalBinders body) nondep
  | .mdata data body => .mdata data (canonicalBinders body)
  | .proj name index body => .proj name index (canonicalBinders body)
  | expr => expr

private def normalized (info : ConstantInfo) (expr : Expr) : Expr :=
  let levels := (List.range info.levelParams.length).map fun index =>
    Level.param (Name.num `_termsubst_repair_universe index)
  canonicalBinders (expr.instantiateLevelParams info.levelParams levels)

private def dependencies (info : ConstantInfo) : Array Name :=
  match info with
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

private partial def firstDifference (left right : Expr)
    (path : String := "root") (fuel : Nat := 32) :
    Option (String × Expr × Expr) :=
  if left.eqv right then none
  else if fuel == 0 then some (path, left, right)
  else
    match left, right with
    | .app leftFn leftArg, .app rightFn rightArg =>
      firstDifference leftFn rightFn (path ++ ".fn") (fuel - 1) <|>
        firstDifference leftArg rightArg (path ++ ".arg") (fuel - 1)
    | .lam _ leftType leftBody leftInfo, .lam _ rightType rightBody rightInfo
    | .forallE _ leftType leftBody leftInfo,
        .forallE _ rightType rightBody rightInfo =>
      if leftInfo != rightInfo then some (path ++ ".binderInfo", left, right)
      else
        firstDifference leftType rightType (path ++ ".type") (fuel - 1) <|>
          firstDifference leftBody rightBody (path ++ ".body") (fuel - 1)
    | .letE _ leftType leftValue leftBody leftNondep,
        .letE _ rightType rightValue rightBody rightNondep =>
      if leftNondep != rightNondep then some (path ++ ".letNondep", left, right)
      else
        firstDifference leftType rightType (path ++ ".type") (fuel - 1) <|>
          firstDifference leftValue rightValue (path ++ ".value") (fuel - 1) <|>
          firstDifference leftBody rightBody (path ++ ".body") (fuel - 1)
    | .mdata _ leftBody, .mdata _ rightBody =>
      firstDifference leftBody rightBody (path ++ ".mdata") (fuel - 1)
    | .proj leftName leftIndex leftBody, .proj rightName rightIndex rightBody =>
      if leftName == rightName && leftIndex == rightIndex then
        firstDifference leftBody rightBody (path ++ ".proj") (fuel - 1)
      else some (path, left, right)
    | _, _ => some (path, left, right)

run_cmd do
  let env ← getEnv
  let original :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_2
  let replacement :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarDefinedExact
  let fieldProof :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarFieldDefined
  let some originalInfo := env.checked.get.find? original
    | throwError "missing original helper"
  let some replacementInfo := env.checked.get.find? replacement
    | throwError "missing exact replacement"
  unless originalInfo.levelParams.length == replacementInfo.levelParams.length do
    throwError "universe-parameter-count mismatch"
  let originalType := normalized originalInfo originalInfo.type
  let replacementType := normalized replacementInfo replacementInfo.type
  unless originalType.eqv replacementType do
    logInfo m!"ORIGINAL_NORMALIZED_TYPE\t{originalType}"
    logInfo m!"REPLACEMENT_NORMALIZED_TYPE\t{replacementType}"
    match firstDifference originalType replacementType with
    | some (path, left, right) =>
      logInfo m!"FIRST_TYPE_DIFFERENCE\tpath={path}\toriginal={left}\treplacement={right}"
    | none => logInfo "FIRST_TYPE_DIFFERENCE unavailable"
    throwError "universe-renamed, alpha-normalized types differ"
  let selected ← match closure env [replacement, fieldProof] with
    | .ok result => pure result
    | .error message => throwError message
  if selected.contains original then
    throwError "replacement closure reaches the original generated helper"
  let replacementAxioms ← Lean.collectAxioms replacement
  let fieldAxioms ← Lean.collectAxioms fieldProof
  let axioms := (replacementAxioms ++ fieldAxioms).foldl
    (fun names name => if names.contains name then names else names.push name) #[]
  let unexpected := axioms.filter fun name => !permittedAxiom name
  unless unexpected.isEmpty do
    throwError m!"unexpected axioms: {unexpected}"
  let sortedAxioms := axioms.qsort fun left right =>
    decide (left.toString < right.toString)
  logInfo "PASS exact universe-renamed, alpha-normalized helper type equality"
  logInfo m!"PASS replacement closure excludes {original}"
  logInfo m!"PASS replacement recursive axiom closure: {sortedAxioms}"
  logInfo m!"REPLACEMENT_CLOSURE\tcount={selected.size}"
  logInfo m!"EXACT_REPLACEMENT_TYPE\t{replacementType}"

end FailureOfComposition.Palomar.TermSubstReplacementAudit
