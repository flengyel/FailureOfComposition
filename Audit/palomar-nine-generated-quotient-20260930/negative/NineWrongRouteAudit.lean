import NineWrongRouteSolution
import FailureOfComposition.Palomar.RangeProductiveBridge
import Lean

set_option autoImplicit false

open Lean Elab Command

namespace FailureOfComposition.Palomar.NineWrongRouteAudit

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
        | throw s!"Unresolved dependency: {name}"
      closure env ((dependencies info).toList ++ rest) (seen.insert name)

private def normalizedType (info : ConstantInfo) : Expr :=
  let levels := (List.range info.levelParams.length).map fun index =>
    Level.param (Name.num `_route_universe index)
  info.type.instantiateLevelParams info.levelParams levels

run_cmd do
  let env ← getEnv
  let fixture := ``FailureOfComposition.Palomar.NineWrongRoute.range_counterexample_productive
  let intended := ``FailureOfComposition.Palomar.Arithmetic.Evaluator.range_counterexample_productive
  let some fixtureInfo := env.checked.get.find? fixture
    | throwError "wrong-route fixture is missing"
  let some intendedInfo := env.checked.get.find? intended
    | throwError "intended productive bridge is missing"
  unless fixtureInfo.levelParams.length == intendedInfo.levelParams.length &&
      (normalizedType fixtureInfo).eqv (normalizedType intendedInfo) do
    throwError "wrong-route fixture does not have the exact productive theorem type"
  let fixtureClosure ← match closure env [fixture] with
    | .ok result => pure result
    | .error message => throwError message
  let required := ``FailureOfComposition.ConcreteIndices.range_counterexample_via_productiveness_of_re_axioms
  let forbidden := ``FailureOfComposition.ConcreteIndices.range_counterexample_of_re_axioms
  if fixtureClosure.contains required then
    throwError "wrong-route fixture unexpectedly reaches the productive maintained root"
  unless fixtureClosure.contains forbidden do
    throwError "wrong-route fixture does not expose its substituted Gödel-II route"
  logInfo "PASS exact-type wrong-route fixture is rejected: productive root absent and Gödel-II root reached"

end FailureOfComposition.Palomar.NineWrongRouteAudit
