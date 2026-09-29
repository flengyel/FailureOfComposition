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
  let evaluationProof :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarEvaluation
  let fieldObligation :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarIntegratedFieldObligationExact
  let some constructionInfo := env.checked.get.find? construction
    | throwError "missing patched construction"
  let some constructionBody := constructionInfo.value? (allowOpaque := true)
    | throwError "patched construction has no body"
  let some exactInfo := env.checked.get.find? exactProof
    | throwError "missing named exact replacement"
  let some exactBody := exactInfo.value? (allowOpaque := true)
    | throwError "named exact replacement has no body"
  let some fieldInfo := env.checked.get.find? fieldProof
    | throwError "missing named bvar field proof"
  let some fieldBody := fieldInfo.value? (allowOpaque := true)
    | throwError "named bvar field proof has no body"
  let some obligationInfo := env.checked.get.find? fieldObligation
    | throwError "missing integrated field-obligation witness"
  let exactType := normalized exactInfo exactInfo.type
  let obligationType := normalized obligationInfo obligationInfo.type
  let rawTypeEqual := exactInfo.levelParams.length == obligationInfo.levelParams.length &&
    exactType.eqv obligationType
  if rawTypeEqual then
    logInfo "RAW_TYPE_EQUAL true"
  else
    match firstDifference exactType obligationType with
    | some (path, _, _) =>
      logInfo m!"FIRST_INTEGRATED_TYPE_DIFFERENCE path={path}"
    | none => logInfo "FIRST_INTEGRATED_TYPE_DIFFERENCE unavailable"
    logInfo "RAW_TYPE_EQUAL false"
  let direct := constructionBody.getUsedConstants
  unless direct.contains fieldProof do
    throwError "construction body does not directly use the named bvar field proof"
  let fieldDirect := fieldBody.getUsedConstants
  unless fieldDirect.contains evaluationProof do
    throwError "named bvar field proof does not directly use the factored evaluation proof"
  let exactDirect := exactBody.getUsedConstants
  unless exactDirect.contains fieldProof do
    throwError "named exact replacement is not projected from the named bvar field proof"
  let fieldSelected ← match closure env [fieldProof] with
    | .ok result => pure result
    | .error message => throwError message
  if fieldSelected.contains construction then
    throwError "named bvar field proof recursively depends on TermSubst.construction"
  unless fieldSelected.contains evaluationProof do
    throwError "named bvar field proof closure omits the factored evaluation proof"
  let exactSelected ← match closure env [exactProof] with
    | .ok result => pure result
    | .error message => throwError message
  if exactSelected.contains construction then
    throwError "named exact replacement recursively depends on TermSubst.construction"
  unless exactSelected.contains fieldProof do
    throwError "named exact replacement closure omits the named bvar field proof"
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
  if rawTypeEqual then
    logInfo "PASS named exact replacement type is raw-expression equal to the field obligation"
  else
    logInfo "PASS kernel conversion witness assigns the inferred replacement to the field obligation"
  logInfo "PASS named field proof directly uses constructionBvarEvaluation"
  logInfo "PASS exact proof is projected from the new field proof"
  logInfo "PASS new field and exact proof closures exclude TermSubst.construction"
  logInfo "PASS integrated construction closure reaches both named replacement proofs"
  logInfo m!"PASS integrated recursive axiom closure: {sortedAxioms}"
  logInfo m!"INTEGRATED_CLOSURE count={selected.size}"
  logInfo m!"DIRECT_CONSTRUCTION_DEPENDENCIES count={direct.size}"
  logInfo m!"FIELD_PROOF_CLOSURE count={fieldSelected.size}"
  logInfo m!"EXACT_PROOF_CLOSURE count={exactSelected.size}"

end FailureOfComposition.Palomar.TermSubstPatchedConstructionAudit
