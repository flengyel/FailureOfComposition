import Lean

/-! Exact regression check that Nine preserves the first eight public contracts. -/

set_option autoImplicit false

open Lean

namespace FailureOfComposition.Palomar.NinePreservesEight

private def selected : Array Name := #[
  `FailureOfComposition.Palomar.obstruction_four_properties,
  `FailureOfComposition.Palomar.no_quotient_composition_productive,
  `FailureOfComposition.Palomar.no_quotient_composition_godel,
  `FailureOfComposition.Palomar.pi_one_characterization,
  `FailureOfComposition.Palomar.generated_congruence_classification,
  `FailureOfComposition.Palomar.weak_totality_counterexample,
  `FailureOfComposition.Palomar.range_counterexample_godel,
  `FailureOfComposition.Palomar.range_counterexample_productive
]

private def theoremType (env : Environment) (moduleName name : Name) : IO Expr := do
  let some index := env.getModuleIdxFor? name
    | throw <| IO.userError s!"No defining module for {name}"
  unless env.header.moduleNames[index.toNat]! == moduleName do
    throw <| IO.userError s!"{name} is not owned by {moduleName}"
  let some (.thmInfo value) := env.checked.get.find? name
    | throw <| IO.userError s!"Missing theorem {name}"
  let levels := (List.range value.levelParams.length).map fun index =>
    Level.param (Name.num `_preserved_universe index)
  return value.type.instantiateLevelParams value.levelParams levels

private def compareModules (earlier later : Name) : IO Unit := do
  let earlierEnv ← importModules #[{ module := earlier }] {}
  let laterEnv ← importModules #[{ module := later }] {}
  for name in selected do
    let earlierType ← theoremType earlierEnv earlier name
    let laterType ← theoremType laterEnv later name
    unless earlierType.eqv laterType do
      throw <| IO.userError s!"Nine changed an accepted Eight theorem type: {name}"

def main : IO Unit := do
  initSearchPath (← findSysroot)
  compareModules `FailureOfComposition.Palomar.ChallengeEight
    `FailureOfComposition.Palomar.ChallengeNine
  compareModules `FailureOfComposition.Palomar.SolutionEight
    `FailureOfComposition.Palomar.SolutionNine
  IO.println "PASS Nine preserves all first-eight Challenge and Solution theorem types"

end FailureOfComposition.Palomar.NinePreservesEight

def main : IO Unit := FailureOfComposition.Palomar.NinePreservesEight.main
