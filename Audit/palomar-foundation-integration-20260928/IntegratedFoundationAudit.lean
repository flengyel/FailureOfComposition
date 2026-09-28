import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Basic
import Lean
import Lean.Meta.Sym.ExprPtr

set_option autoImplicit false

open Lean Elab Command

namespace FailureOfComposition.Palomar.IntegratedFoundationAudit

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

private def permittedAxiom (name : Name) : Bool :=
  name == `propext || name == `Classical.choice || name == `Quot.sound

private def requireInfo (env : Environment) (name : Name) :
    CommandElabM ConstantInfo := do
  let some info := env.checked.get.find? name
    | throwError m!"missing declaration: {name}"
  pure info

run_cmd do
  let env ← getEnv
  let blueprint :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.blueprint
  let construction :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.construction
  let assignment :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.constructionFuncAssignment
  let terms :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.constructionFuncTerms_val
  let substitution :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.constructionFuncSubstitution_eval
  let result :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.constructionFuncResult
  let replacement :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.constructionFuncDefined
  let oldGenerated :=
    `FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.construction._proof_4

  let blueprintInfo ← requireInfo env blueprint
  let constructionInfo ← requireInfo env construction
  let replacementInfo ← requireInfo env replacement
  let some constructionBody := constructionInfo.value? (allowOpaque := true)
    | throwError "integrated construction has no body"
  unless constructionBody.getUsedConstants.contains replacement do
    throwError "integrated construction body does not directly use the factored proof"

  let replacementClosure ← match closure env [replacement] with
    | .ok value => pure value
    | .error message => throwError message
  let constructionClosure ← match closure env [construction] with
    | .ok value => pure value
    | .error message => throwError message
  if replacementClosure.contains oldGenerated then
    throwError "factored proof closure reaches the former generated helper name"

  let axioms := constructionClosure.toArray.filter fun name =>
    match env.checked.get.find? name with
    | some (.axiomInfo _) => true
    | _ => false
  let unexpected := axioms.filter fun name => !permittedAxiom name
  unless unexpected.isEmpty do
    throwError m!"unexpected axioms in integrated construction: {unexpected}"

  let some replacementBody := replacementInfo.value? (allowOpaque := true)
    | throwError "factored proof has no body"
  let replacementTypeSize := size replacementInfo.type
  let replacementBodySize := size replacementBody

  logInfo "PASS rebuilt integrated Foundation declarations are present"
  logInfo m!"PASS construction body directly uses {replacement}"
  logInfo m!"PASS factored proof closure excludes former generated helper {oldGenerated}"
  logInfo m!"PASS construction recursive axiom closure: {axioms.qsort (fun a b => decide (a.toString < b.toString))}"
  logInfo m!"BLUEPRINT_TYPE\t{blueprintInfo.type}"
  logInfo m!"CONSTRUCTION_TYPE\t{constructionInfo.type}"
  logInfo m!"ASSIGNMENT_TYPE\t{(← requireInfo env assignment).type}"
  logInfo m!"TERMS_TYPE\t{(← requireInfo env terms).type}"
  logInfo m!"SUBSTITUTION_TYPE\t{(← requireInfo env substitution).type}"
  logInfo m!"RESULT_TYPE\t{(← requireInfo env result).type}"
  logInfo m!"FACTORED_PROOF_TYPE\t{replacementInfo.type}"
  logInfo m!"FACTORED_PROOF_CLOSURE\tcount={replacementClosure.size}"
  logInfo m!"CONSTRUCTION_CLOSURE\tcount={constructionClosure.size}"
  logInfo m!"FACTORED_PROOF_SHAPE\ttypePhysical={replacementTypeSize.1}\ttypeStructural={replacementTypeSize.2}\tbodyPhysical={replacementBodySize.1}\tbodyStructural={replacementBodySize.2}"
  match env.checked.get.find? oldGenerated with
  | none => logInfo m!"GENERATED_NAME\t{oldGenerated}\tabsent"
  | some info =>
    logInfo m!"GENERATED_NAME\t{oldGenerated}\tpresent\ttype={info.type}\tdirectDeps={dependencies info}"
  for dependency in constructionBody.getUsedConstants.qsort
      (fun left right => decide (left.toString < right.toString)) do
    logInfo m!"CONSTRUCTION_DIRECT_BODY_DEP\t{dependency}"
  for dependency in replacementBody.getUsedConstants.qsort
      (fun left right => decide (left.toString < right.toString)) do
    logInfo m!"FACTORED_PROOF_DIRECT_BODY_DEP\t{dependency}"

end FailureOfComposition.Palomar.IntegratedFoundationAudit
