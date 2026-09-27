/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Lean

/-!
# Exact local check of the cumulative two-result Palomar interface

This executable deliberately imports neither side at elaboration time.  It loads
`ChallengeTwo` and `SolutionTwo` into separate environments, checks the selected
theorem's ownership and type, and then compares the complete declaration graph
reachable from the theorem type.  Declaration types and shared definition
bodies are compared after consistently renaming each declaration's universe
parameters.

This is a local interface and axiom check.  It is not Palomar Comparator or an
external-kernel replay.  The separate source-policy command checks the Challenge
import closure.
-/

set_option autoImplicit false

open Lean

namespace FailureOfComposition.Palomar.TwoInterfaceCheck

private def challengeModule : Name := `FailureOfComposition.Palomar.ChallengeTwo
private def solutionModule : Name := `FailureOfComposition.Palomar.SolutionTwo
private def selected : Array Name := #[
  `FailureOfComposition.Palomar.obstruction_four_properties,
  `FailureOfComposition.Palomar.no_quotient_composition_productive
]

private def permittedAxiom (name : Name) : Bool :=
  name == `propext || name == `Quot.sound || name == `Classical.choice

private def normalized (info : ConstantInfo) (expr : Expr) : Expr :=
  let levels := (List.range info.levelParams.length).map fun index =>
    Level.param (Name.num `_interface_universe index)
  expr.instantiateLevelParams info.levelParams levels

private def kindName (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque definition"
  | .quotInfo _ => "quotient primitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def sameKind (left right : ConstantInfo) : Bool :=
  match left, right with
  | .axiomInfo _, .axiomInfo _
  | .defnInfo _, .defnInfo _
  | .thmInfo _, .thmInfo _
  | .opaqueInfo _, .opaqueInfo _
  | .quotInfo _, .quotInfo _
  | .inductInfo _, .inductInfo _
  | .ctorInfo _, .ctorInfo _
  | .recInfo _, .recInfo _ => true
  | _, _ => false

private def sameRecursorRules (leftInfo rightInfo : ConstantInfo) :
    List RecursorRule → List RecursorRule → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      left.ctor == right.ctor && left.nfields == right.nfields &&
        (normalized leftInfo left.rhs).eqv (normalized rightInfo right.rhs) &&
        sameRecursorRules leftInfo rightInfo leftRest rightRest
  | _, _ => false

/-- Compare the non-expression declaration data that the kernel/exporter keeps. -/
private def sameMetadata (left right : ConstantInfo) : Bool :=
  match left, right with
  | .axiomInfo a, .axiomInfo b => a.isUnsafe == b.isUnsafe
  | .defnInfo a, .defnInfo b =>
      a.hints == b.hints && a.safety == b.safety && a.all == b.all
  | .thmInfo a, .thmInfo b => a.all == b.all
  | .opaqueInfo a, .opaqueInfo b => a.isUnsafe == b.isUnsafe && a.all == b.all
  | .quotInfo a, .quotInfo b => a.kind == b.kind
  | .inductInfo a, .inductInfo b =>
      a.numParams == b.numParams && a.numIndices == b.numIndices &&
        a.all == b.all && a.ctors == b.ctors && a.numNested == b.numNested &&
        a.isRec == b.isRec && a.isUnsafe == b.isUnsafe &&
        a.isReflexive == b.isReflexive
  | .ctorInfo a, .ctorInfo b =>
      a.induct == b.induct && a.cidx == b.cidx &&
        a.numParams == b.numParams && a.numFields == b.numFields &&
        a.isUnsafe == b.isUnsafe
  | .recInfo a, .recInfo b =>
      a.all == b.all && a.numParams == b.numParams &&
        a.numIndices == b.numIndices && a.numMotives == b.numMotives &&
        a.numMinors == b.numMinors && a.k == b.k &&
        a.isUnsafe == b.isUnsafe && sameRecursorRules left right a.rules b.rules
  | _, _ => false

private def sharedBody? (name : Name) (info : ConstantInfo) : Option Expr :=
  if selected.contains name then none else info.value? (allowOpaque := true)

/--
Dependencies relevant to the statement interface under the earlier exact-check
convention: every declaration type and every available shared body, including
supporting theorem proofs.  Only the two selected theorem proofs are omitted, since
ChallengeTwo deliberately replaces those proofs with its two holes.  This
stronger traversal explains why its count is much larger than a definitions-only
statement graph.
-/
private def statementDependencies (name : Name) (info : ConstantInfo) : Array Name :=
  match info with
  | .axiomInfo value => value.type.getUsedConstants
  | .defnInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .thmInfo value =>
      if selected.contains name then value.type.getUsedConstants
      else value.type.getUsedConstants ++ value.value.getUsedConstants
  | .opaqueInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .ctorInfo value => value.type.getUsedConstants
  | .recInfo value => value.type.getUsedConstants
  | .inductInfo value => value.type.getUsedConstants ++ value.ctors.toArray
  | .quotInfo value => value.type.getUsedConstants

private def allDependencies (info : ConstantInfo) : Array Name :=
  match info with
  | .axiomInfo value => value.type.getUsedConstants
  | .defnInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .thmInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .opaqueInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .ctorInfo value => value.type.getUsedConstants
  | .recInfo value => value.type.getUsedConstants
  | .inductInfo value => value.type.getUsedConstants ++ value.ctors.toArray
  | .quotInfo value => value.type.getUsedConstants

private partial def statementClosure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : Except String NameSet := do
  match todo with
  | [] => return seen
  | name :: rest =>
    if seen.contains name then
      statementClosure env rest seen
    else
      let some info := env.checked.get.find? name
        | throw s!"Unresolved statement dependency: {name}"
      statementClosure env
        ((statementDependencies name info).toList ++ rest) (seen.insert name)

/-- Full recursive type/proof/definition closure, used only for axiom auditing. -/
private partial def proofClosure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : Except String NameSet := do
  match todo with
  | [] => return seen
  | name :: rest =>
    if seen.contains name then
      proofClosure env rest seen
    else
      let some info := env.checked.get.find? name
        | throw s!"Unresolved proof dependency: {name}"
      let more := allDependencies info
      proofClosure env (more.toList ++ rest) (seen.insert name)

private def ownedTheorem (env : Environment) (moduleName name : Name) : IO TheoremVal := do
  let some index := env.getModuleIdxFor? name
    | throw <| IO.userError s!"No defining module for {name}"
  unless env.header.moduleNames[index.toNat]! == moduleName do
    throw <| IO.userError s!"{name} is not defined in {moduleName}"
  let some (.thmInfo value) := env.checked.get.find? name
    | throw <| IO.userError s!"Missing theorem declaration: {name}"
  return value

private def normalizedTheoremType (value : TheoremVal) : Expr :=
  let levels := (List.range value.levelParams.length).map fun index =>
    Level.param (Name.num `_interface_universe index)
  value.type.instantiateLevelParams value.levelParams levels

private def compareDeclaration (challenge solution : Environment) (name : Name) : IO Unit := do
  let some left := challenge.checked.get.find? name
    | throw <| IO.userError s!"Challenge statement dependency is unresolved: {name}"
  let some right := solution.checked.get.find? name
    | throw <| IO.userError s!"Solution is missing statement dependency: {name}"
  unless sameKind left right do
    throw <| IO.userError <| s!"Declaration-kind mismatch for {name}: " ++
      s!"Challenge {kindName left}, Solution {kindName right}"
  unless sameMetadata left right do
    throw <| IO.userError s!"Declaration metadata mismatch: {name}"
  unless left.levelParams.length == right.levelParams.length do
    throw <| IO.userError s!"Universe-parameter-count mismatch: {name}"
  unless (normalized left left.type).eqv (normalized right right.type) do
    throw <| IO.userError s!"Declaration type mismatch: {name}"
  match sharedBody? name left, sharedBody? name right with
  | some leftValue, some rightValue =>
      unless (normalized left leftValue).eqv (normalized right rightValue) do
        throw <| IO.userError s!"Shared definition body mismatch: {name}"
  | none, none => pure ()
  | _, _ => throw <| IO.userError s!"Definition-body availability mismatch: {name}"

private def auditAxioms (env : Environment) (name : Name) (challenge : Bool) : IO NameSet := do
  let visited ← match proofClosure env [name] with
    | .ok result => pure result
    | .error message => throw <| IO.userError message
  let axioms := visited.toArray.filter fun dependency =>
    match env.checked.get.find? dependency with
    | some (.axiomInfo _) => true
    | _ => false
  let unexpected := axioms.filter fun axiomName =>
    !permittedAxiom axiomName && !(challenge && axiomName == `sorryAx)
  unless unexpected.isEmpty do
    throw <| IO.userError s!"Unexpected axioms of {name}: {unexpected}"
  if challenge then
    unless axioms.contains `sorryAx do
      throw <| IO.userError s!"Selected Challenge theorem does not contain its deliberate hole: {name}"
  else
    if visited.contains `sorryAx then
      throw <| IO.userError s!"Solution depends on sorryAx: {name}"
  let side := if challenge then "ChallengeTwo" else "SolutionTwo"
  IO.println s!"PASS {side} recursive axiom closure: {axioms}; {visited.size} declarations"
  return visited

private def auditOwnedHoles (env : Environment) : IO Unit := do
  let mut holes : Array Name := #[]
  let mut definitionHoles : Array Name := #[]
  for (name, info) in env.constants do
    let owned := match env.getModuleIdxFor? name with
      | some index => env.header.moduleNames[index.toNat]! == challengeModule
      | none => false
    if owned then
      if let some body := info.value? (allowOpaque := true) then
        if body.getUsedConstants.contains `sorryAx then
          holes := holes.push name
          match info with
          | .defnInfo _ | .opaqueInfo _ => definitionHoles := definitionHoles.push name
          | _ => pure ()
  unless holes.size == selected.size && selected.all fun name => holes.contains name do
    throw <| IO.userError s!"ChallengeTwo direct holes are not exactly the selected theorems: {holes}"
  unless definitionHoles.isEmpty do
    throw <| IO.userError s!"ChallengeTwo contains selected definition holes: {definitionHoles}"

private def requireExactSelection (names : Array Name) : IO Unit := do
  unless names == selected do
    throw <| IO.userError s!"Two-result selection must be exactly {selected}; got {names}"

private def checkExactPair : IO Unit := do
  initSearchPath (← findSysroot)
  requireExactSelection selected
  IO.println s!"Challenge module: {challengeModule}"
  IO.println s!"Solution module: {solutionModule}"
  IO.println s!"Selected declarations: {selected}"
  let challenge ← importModules #[{ module := challengeModule }] {}
  let solution ← importModules #[{ module := solutionModule }] {}
  if challenge.header.moduleNames.contains solutionModule then
    throw <| IO.userError "ChallengeTwo imports SolutionTwo"
  if solution.header.moduleNames.contains challengeModule then
    throw <| IO.userError "SolutionTwo imports ChallengeTwo"
  for name in selected do
    let statement ← ownedTheorem challenge challengeModule name
    let proof ← ownedTheorem solution solutionModule name
    unless statement.levelParams.length == proof.levelParams.length &&
        (normalizedTheoremType statement).eqv (normalizedTheoremType proof) do
      throw <| IO.userError s!"Selected theorem type mismatch: {name}"
  IO.println "PASS both selected theorem ownership and universe-renamed type comparisons"
  let closure ← match statementClosure challenge selected.toList with
    | .ok result => pure result
    | .error message => throw <| IO.userError message
  for name in closure.toArray do
    compareDeclaration challenge solution name
  IO.println s!"PASS exact cumulative statement declaration and definition-body comparison: {closure.size} constants"
  for name in selected do
    let _ ← auditAxioms challenge name true
    let _ ← auditAxioms solution name false
  auditOwnedHoles challenge
  IO.println "PASS SolutionTwo does not import ChallengeTwo"
  IO.println s!"PASS selected theorem holes: exactly {selected}; definition holes: []"
  IO.println "PASS exact cumulative two-result local interface check"
  IO.println "This check is not Palomar Comparator or an external-kernel replay."

private def checkExpectedSelectionRejection : IO Unit := do
  let mut rejected := false
  try
    requireExactSelection #[selected[0]!]
  catch error =>
    if error.toString.contains "selection must be exactly" then
      rejected := true
    else
      throw error
  unless rejected do
    throw <| IO.userError "One-only theorem selection was unexpectedly accepted"
  IO.println "PASS negative regression: a one-result selection is rejected by the two-result checker"

/-- Generic comparison entry used only by the isolated negative regression. -/
private def checkExpectedDefinitionRejection
    (leftModule rightModule declaration expectedDefinition : Name) : IO Unit := do
  initSearchPath (← findSysroot)
  let left ← importModules #[{ module := leftModule }] {}
  let right ← importModules #[{ module := rightModule }] {}
  let some leftInfo := left.checked.get.find? declaration
    | throw <| IO.userError s!"Negative-test declaration missing on left: {declaration}"
  let closure ← match statementClosure left [declaration] with
    | .ok result => pure result
    | .error message => throw <| IO.userError message
  let some _ := right.checked.get.find? declaration
    | throw <| IO.userError s!"Negative-test declaration missing on right: {declaration}"
  unless (normalized leftInfo leftInfo.type).eqv
      (normalized (right.checked.get.find? declaration).get! (right.checked.get.find? declaration).get!.type) do
    throw <| IO.userError "Negative-test outer theorem types unexpectedly differ"
  let mut rejected := false
  for name in closure.toArray do
    try
      compareDeclaration left right name
    catch error =>
      if name == expectedDefinition && error.toString.contains "Shared definition body mismatch" then
        rejected := true
      else
        throw error
  unless rejected do
    throw <| IO.userError s!"Changed shared definition was not rejected: {expectedDefinition}"
  IO.println "PASS negative regression: matching outer theorem type did not mask a changed shared definition"

def main (args : List String) : IO Unit :=
  match args with
  | [] => checkExactPair
  | ["--negative-shared-definition", left, right, declaration, expected] =>
      checkExpectedDefinitionRejection left.toName right.toName declaration.toName expected.toName
  | ["--negative-selection-count"] => checkExpectedSelectionRejection
  | _ => throw <| IO.userError
      "This two-result checker accepts no module overrides; legacy and One-only selection are rejected"

end FailureOfComposition.Palomar.TwoInterfaceCheck

def main (args : List String) : IO Unit :=
  FailureOfComposition.Palomar.TwoInterfaceCheck.main args
