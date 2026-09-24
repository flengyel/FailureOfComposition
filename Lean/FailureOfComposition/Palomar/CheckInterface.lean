/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Lean

/-!
# Local check of the draft Palomar interface

After compiling `Challenge` and `Solution`, run this file with `lean --run` in
the configured Lake environment. The two modules are loaded into independent
environments; their nine declaration types and recursive axiom dependencies
are checked without importing either module into this checker's environment.

This is a local draft check, not Palomar Comparator, a kernel replay, or an
eligibility check. In particular, it does not establish Palomar's restrictions
on the Challenge import closure or compare the meanings of all imported names.
-/

set_option autoImplicit false

open Lean

namespace FailureOfComposition.Palomar.InterfaceCheck

private def challengeModule : Name := `FailureOfComposition.Palomar.Challenge
private def solutionModule : Name := `FailureOfComposition.Palomar.Solution

private def declarations : Array Name := #[
  `FailureOfComposition.Palomar.obstruction_four_properties,
  `FailureOfComposition.Palomar.no_quotient_composition_productive,
  `FailureOfComposition.Palomar.no_quotient_composition_godel,
  `FailureOfComposition.Palomar.pi_one_characterization,
  `FailureOfComposition.Palomar.generated_congruence_classification,
  `FailureOfComposition.Palomar.weak_totality_counterexample,
  `FailureOfComposition.Palomar.range_counterexample_godel,
  `FailureOfComposition.Palomar.range_counterexample_productive,
  `FailureOfComposition.Palomar.generated_quotient_partial_recursive]

private def permittedAxiom (name : Name) : Bool :=
  name == `propext || name == `Quot.sound || name == `Classical.choice

/-- Traverse types and proof/definition bodies, failing on unresolved constants. -/
private partial def dependencies (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : Except String NameSet := do
  match todo with
  | [] => return seen
  | name :: rest =>
    if seen.contains name then
      dependencies env rest seen
    else
      let some info := env.checked.get.find? name
        | throw s!"Unresolved dependency: {name}"
      let more := match info with
        | .axiomInfo value => value.type.getUsedConstants
        | .defnInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
        | .thmInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
        | .opaqueInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
        | .ctorInfo value => value.type.getUsedConstants
        | .recInfo value => value.type.getUsedConstants
        | .inductInfo value => value.type.getUsedConstants ++ value.ctors.toArray
        | .quotInfo value => value.type.getUsedConstants
      dependencies env (more.toList ++ rest) (seen.insert name)

private def ownedTheorem (env : Environment) (moduleName name : Name) : IO TheoremVal := do
  let some index := env.getModuleIdxFor? name
    | throw <| IO.userError s!"No defining module for {name}"
  unless env.header.moduleNames[index.toNat]! == moduleName do
    throw <| IO.userError s!"{name} is not defined in {moduleName}"
  let some (.thmInfo value) := env.checked.get.find? name
    | throw <| IO.userError s!"Missing theorem declaration: {name}"
  return value

private def normalizedType (value : TheoremVal) : Expr :=
  let levels := (List.range value.levelParams.length).map fun index =>
    Level.param (Name.num `_interface_universe index)
  value.type.instantiateLevelParams value.levelParams levels

private def auditAxioms (env : Environment) (name : Name) (challenge : Bool) : IO Unit := do
  let visited ← match dependencies env [name] with
    | .ok result => pure result
    | .error message => throw <| IO.userError message
  let axioms := visited.toArray.filter fun dependency =>
    match env.checked.get.find? dependency with
    | some (.axiomInfo _) => true
    | _ => false
  let unexpected := axioms.filter fun ax =>
    !permittedAxiom ax && !(challenge && ax == `sorryAx)
  unless unexpected.isEmpty do
    throw <| IO.userError s!"Unexpected axioms of {name}: {unexpected}"
  if challenge then
    unless axioms.contains `sorryAx do
      throw <| IO.userError s!"Expected the deliberate Challenge hole in {name}"
  else
    if visited.contains `sorryAx then
      throw <| IO.userError s!"Solution depends on sorryAx: {name}"
  let side := if challenge then "Challenge" else "Solution"
  IO.println s!"PASS {side} axioms {name}: {axioms}; {visited.size} declarations traversed"

def check : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← importModules #[{ module := challengeModule }] {}
  let solution ← importModules #[{ module := solutionModule }] {}
  if challenge.header.moduleNames.contains solutionModule then
    throw <| IO.userError "Challenge imports Solution"
  if solution.header.moduleNames.contains challengeModule then
    throw <| IO.userError "Solution imports Challenge"
  for name in declarations do
    let statement ← ownedTheorem challenge challengeModule name
    let proof ← ownedTheorem solution solutionModule name
    unless statement.levelParams.length == proof.levelParams.length &&
        (normalizedType statement).eqv (normalizedType proof) do
      throw <| IO.userError s!"Declaration type mismatch: {name}"
    IO.println s!"PASS independent-environment type comparison: {name}"
    auditAxioms challenge name true
    auditAxioms solution name false
  IO.println s!"PASS local draft interface: {declarations.size} type matches and axiom audits"
  IO.println "This check is not Palomar Comparator and does not establish submission eligibility."

end FailureOfComposition.Palomar.InterfaceCheck

def main : IO Unit := FailureOfComposition.Palomar.InterfaceCheck.check
