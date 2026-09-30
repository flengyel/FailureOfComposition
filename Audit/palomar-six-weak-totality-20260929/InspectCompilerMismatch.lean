import Lean

open Lean

private def target : Name :=
  `FailureOfComposition.Palomar.Arithmetic.Evaluator.IndexCompiler.compile._f

private def normalized (info : ConstantInfo) (expr : Expr) : Expr :=
  let levels := (List.range info.levelParams.length).map fun index =>
    Level.param (Name.num `_interface_universe index)
  expr.instantiateLevelParams info.levelParams levels

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← importModules
    #[{ module := `FailureOfComposition.Palomar.ChallengeSix }] {}
  let solution ← importModules
    #[{ module := `FailureOfComposition.Palomar.SolutionSix }] {}
  for (label, env) in [("challenge", challenge), ("solution", solution)] do
    let some info := env.checked.get.find? target
      | throw <| IO.userError s!"missing {target} in {label}"
    let some value := info.value? (allowOpaque := true)
      | throw <| IO.userError s!"missing body for {target} in {label}"
    IO.println s!"===== {label} type =====\n{repr (normalized info info.type)}"
    IO.println s!"===== {label} body =====\n{repr (normalized info value)}"
