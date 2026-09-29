import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions
import Lean
import Lean.Elab.Term

set_option autoImplicit false

open Lean Elab Command Term Meta

elab "unfolded_type_of% " value:term : term => do
  let valueExpr ← elabTerm value none
  withReducible <| whnf (← inferType valueExpr)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem constructionBvarIntegratedFieldObligationExact :
    unfolded_type_of% (constructionBvarDefined (V := V)).defined :=
  constructionBvarDefinedExact

end FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst

namespace FailureOfComposition.Palomar.TermSubstPatchedConstructionAudit

private partial def canonicalBinders : Expr → Expr
  | .app f a => .app (canonicalBinders f) (canonicalBinders a)
  | .lam _ type body binderInfo =>
    .lam .anonymous (canonicalBinders type) (canonicalBinders body) binderInfo
  | .forallE _ type body binderInfo =>
    .forallE .anonymous (canonicalBinders type) (canonicalBinders body) binderInfo
  | .letE _ type value body nondep =>
    .letE .anonymous (canonicalBinders type) (canonicalBinders value)
      (canonicalBinders body) nondep
  | .mdata _ body => canonicalBinders body
  | .proj name index body => .proj name index (canonicalBinders body)
  | expr => expr

private def normalized (info : ConstantInfo) (expr : Expr) : Expr :=
  let levels := (List.range info.levelParams.length).map fun index =>
    Level.param (Name.num `_termsubst_integrated_universe index)
  canonicalBinders (expr.instantiateLevelParams info.levelParams levels)

private partial def firstDifference (left right : Expr)
    (path : String := "root") (fuel : Nat := 64) :
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
  let construction :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction
  let exactProof :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarDefinedExact
  let fieldProof :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarDefined
  let fieldObligation :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarIntegratedFieldObligationExact
  let some constructionInfo := env.checked.get.find? construction
    | throwError "missing patched construction"
  let some constructionBody := constructionInfo.value? (allowOpaque := true)
    | throwError "patched construction has no body"
  let some exactInfo := env.checked.get.find? exactProof
    | throwError "missing named exact replacement"
  let some obligationInfo := env.checked.get.find? fieldObligation
    | throwError "missing integrated field-obligation witness"
  let exactType := normalized exactInfo exactInfo.type
  let obligationType := normalized obligationInfo obligationInfo.type
  unless exactInfo.levelParams.length == obligationInfo.levelParams.length &&
      exactType.eqv obligationType do
    match firstDifference exactType obligationType with
    | some (path, left, right) =>
      logInfo m!"FIRST_INTEGRATED_TYPE_DIFFERENCE path={path}"
      logInfo m!"EXPLICIT_TYPE_FRAGMENT {left}"
      logInfo m!"FIELD_OBLIGATION_FRAGMENT {right}"
    | none => logInfo "FIRST_INTEGRATED_TYPE_DIFFERENCE unavailable"
    throwError "named replacement type differs from the integrated bvar field obligation"
  let direct := constructionBody.getUsedConstants
  unless direct.contains fieldProof do
    throwError "construction body does not directly use the named bvar field proof"
  let selected ← match closure env [construction, exactProof, fieldProof] with
    | .ok result => pure result
    | .error message => throwError message
  unless selected.contains exactProof && selected.contains fieldProof do
    throwError "integrated construction closure does not reach both named proofs"
  let constructionAxioms ← Lean.collectAxioms construction
  let exactAxioms ← Lean.collectAxioms exactProof
  let fieldAxioms ← Lean.collectAxioms fieldProof
  let axioms := (constructionAxioms ++ exactAxioms ++ fieldAxioms).foldl
    (fun names name => if names.contains name then names else names.push name) #[]
  let unexpected := axioms.filter fun name => !permittedAxiom name
  unless unexpected.isEmpty do
    throwError m!"unexpected axioms: {unexpected}"
  let sortedAxioms := axioms.qsort fun left right =>
    decide (left.toString < right.toString)
  logInfo "PASS construction body directly uses constructionBvarDefined"
  logInfo "PASS named exact replacement type equals the integrated bvar field obligation"
  logInfo "PASS integrated construction closure reaches both named replacement proofs"
  logInfo m!"PASS integrated recursive axiom closure: {sortedAxioms}"
  logInfo m!"INTEGRATED_CLOSURE count={selected.size}"
  logInfo m!"DIRECT_CONSTRUCTION_DEPENDENCIES count={direct.size}"

end FailureOfComposition.Palomar.TermSubstPatchedConstructionAudit
