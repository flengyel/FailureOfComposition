import AlternativeHelper
import Lean
import Lean.Meta.Sym.ExprPtr

set_option autoImplicit false

open Lean Elab Command

namespace FailureOfComposition.Palomar.FoundationHelperReplacementAudit

private abbrev PhysicalSet := Std.HashSet Lean.Meta.Sym.ExprPtr
private abbrev StructuralSet := Std.HashSet Expr

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
    if seen.contains name then closure env rest seen
    else
      let some info := env.checked.get.find? name
        | throw s!"unresolved dependency: {name}"
      closure env ((dependencies info).toList ++ rest) (seen.insert name)

private unsafe def visitDistinct (expr : Expr)
    (physical : PhysicalSet) (structural : StructuralSet) :
    PhysicalSet × StructuralSet :=
  let pointer : Lean.Meta.Sym.ExprPtr := ⟨expr⟩
  if physical.contains pointer then (physical, structural)
  else
    let physical := physical.insert pointer
    let structural := structural.insert expr
    match expr with
    | .app f a =>
      let (physical, structural) := visitDistinct f physical structural
      visitDistinct a physical structural
    | .lam _ type body _ | .forallE _ type body _ =>
      let (physical, structural) := visitDistinct type physical structural
      visitDistinct body physical structural
    | .letE _ type value body _ =>
      let (physical, structural) := visitDistinct type physical structural
      let (physical, structural) := visitDistinct value physical structural
      visitDistinct body physical structural
    | .mdata _ body | .proj _ _ body => visitDistinct body physical structural
    | _ => (physical, structural)

private unsafe def size (expr : Expr) : Nat × Nat :=
  let result := visitDistinct expr {} {}
  (result.1.size, result.2.size)

private def normalized (info : ConstantInfo) (expr : Expr) : Expr :=
  let levels := (List.range info.levelParams.length).map fun index =>
    Level.param (Name.num `_replacement_universe index)
  expr.instantiateLevelParams info.levelParams levels

private def permittedAxiom (name : Name) : Bool :=
  name == `propext || name == `Classical.choice || name == `Quot.sound

private partial def firstDifference (left right : Expr)
    (path : String := "root") (fuel : Nat := 14) :
    Option (String × Expr × Expr) :=
  if left.eqv right then none
  else if fuel == 0 then some (path, left, right)
  else
    match left, right with
    | .app leftFn leftArg, .app rightFn rightArg =>
      firstDifference leftFn rightFn (path ++ ".fn") (fuel - 1) <|>
        firstDifference leftArg rightArg (path ++ ".arg") (fuel - 1)
    | .lam _ leftType leftBody _, .lam _ rightType rightBody _
    | .forallE _ leftType leftBody _, .forallE _ rightType rightBody _ =>
      firstDifference leftType rightType (path ++ ".type") (fuel - 1) <|>
        firstDifference leftBody rightBody (path ++ ".body") (fuel - 1)
    | .letE _ leftType leftValue leftBody _,
        .letE _ rightType rightValue rightBody _ =>
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
    `FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.construction._proof_4
  let replacement :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.construction_func_defined_replacement
  let some originalInfo := env.checked.get.find? original
    | throwError "missing original helper"
  let some replacementInfo := env.checked.get.find? replacement
    | throwError "missing replacement helper"
  unless originalInfo.levelParams.length == replacementInfo.levelParams.length do
    throwError "universe-parameter-count mismatch"
  let originalType := normalized originalInfo originalInfo.type
  let replacementType := normalized replacementInfo replacementInfo.type
  unless originalType.eqv replacementType do
    match firstDifference originalType replacementType with
    | some (path, left, right) =>
      logInfo m!"FIRST_TYPE_DIFFERENCE\tpath={path}\toriginal={left}\treplacement={right}"
    | none => logInfo "FIRST_TYPE_DIFFERENCE unavailable"
    throwError "universe-renamed elaborated types differ"
  let selected ← match closure env [replacement] with
    | .ok result => pure result
    | .error message => throwError message
  if selected.contains original then
    throwError "replacement closure reaches the original generated helper"
  let axioms := selected.toArray.filter fun name =>
    match env.checked.get.find? name with
    | some (.axiomInfo _) => true
    | _ => false
  let unexpected := axioms.filter fun name => !permittedAxiom name
  unless unexpected.isEmpty do
    throwError m!"unexpected axioms: {unexpected}"
  let some originalBody := originalInfo.value? (allowOpaque := true)
    | throwError "original helper has no body"
  let some replacementBody := replacementInfo.value? (allowOpaque := true)
    | throwError "replacement helper has no body"
  let originalTypeSize := size originalInfo.type
  let originalBodySize := size originalBody
  let replacementTypeSize := size replacementInfo.type
  let replacementBodySize := size replacementBody
  logInfo m!"PASS exact universe-renamed type equality"
  logInfo m!"PASS replacement closure excludes {original}"
  logInfo m!"PASS replacement recursive axiom closure: {axioms}"
  logInfo m!"REPLACEMENT_CLOSURE\tcount={selected.size}"
  logInfo m!"ORIGINAL_SHAPE\ttypePhysical={originalTypeSize.1}\ttypeStructural={originalTypeSize.2}\tbodyPhysical={originalBodySize.1}\tbodyStructural={originalBodySize.2}"
  logInfo m!"REPLACEMENT_SHAPE\ttypePhysical={replacementTypeSize.1}\ttypeStructural={replacementTypeSize.2}\tbodyPhysical={replacementBodySize.1}\tbodyStructural={replacementBodySize.2}"
  for dependency in replacementBody.getUsedConstants.qsort
      (fun left right => decide (left.toString < right.toString)) do
    logInfo m!"REPLACEMENT_DIRECT_BODY_DEP\t{dependency}"

end FailureOfComposition.Palomar.FoundationHelperReplacementAudit
