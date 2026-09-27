import FailureOfComposition.Palomar.SolutionThree
import Lean

set_option autoImplicit false

open Lean Elab Command

namespace FailureOfComposition.Palomar.GodelBoundaryOverlap

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
      let some info := env.checked.get.find? name | throw s!"unresolved dependency: {name}"
      closure env ((dependencies info).toList ++ rest) (seen.insert name)

private def getClosure (env : Environment) (roots : List Name) : CommandElabM NameSet :=
  match closure env roots with
  | .ok result => pure result
  | .error message => throwError message

private def intersectionSize (left right : NameSet) : Nat :=
  left.toArray.foldl (init := 0) fun count name =>
    if right.contains name then count + 1 else count

private def differenceSize (left right : NameSet) : Nat :=
  left.size - intersectionSize left right

private def union (left right : NameSet) : NameSet :=
  right.toArray.foldl (init := left) fun result name => result.insert name

private def uniqueAgainst (source left right : NameSet) : Nat :=
  source.toArray.foldl (init := 0) fun count name =>
    if left.contains name || right.contains name then count else count + 1

run_cmd do
  let env ← getEnv
  let first := ``FailureOfComposition.Palomar.obstruction_four_properties
  let productive := ``FailureOfComposition.Palomar.no_quotient_composition_productive
  let godel := ``FailureOfComposition.Palomar.no_quotient_composition_godel
  let reBridge := ``FailureOfComposition.Palomar.Arithmetic.reAxiomCodes_toFoundation_iff
  let craig := ``FailureOfComposition.CraigPresentation.exists_craig_presentation
  let indexGodel := ``FailureOfComposition.ConcreteIndices.index_noncongruence_via_godel
  let graphGodel := ``FailureOfComposition.graph_noncongruence_via_godel
  let arithmetization := ``FailureOfComposition.ConcreteEvaluator.arithmetization
  let realization := ``FailureOfComposition.SigmaOneRealization.realize_graph
  let two ← getClosure env [first, productive]
  let godelClosure ← getClosure env [godel]
  let reClosure ← getClosure env [reBridge]
  let craigClosure ← getClosure env [craig]
  let indexClosure ← getClosure env [indexGodel]
  let graphClosure ← getClosure env [graphGodel]
  let arithClosure ← getClosure env [arithmetization]
  let realizationClosure ← getClosure env [realization]
  let reCraig := union reClosure craigClosure
  let reCraigIndex := union reCraig indexClosure

  logInfo m!"BASELINE_MARGINAL\tgodel_minus_two={differenceSize godelClosure two}"
  logInfo m!"BOUNDARY_VS_TWO\tre_minus_two={differenceSize reClosure two}\tcraig_minus_two={differenceSize craigClosure two}\tindex_minus_two={differenceSize indexClosure two}\tgraph_minus_two={differenceSize graphClosure two}\tarithmetization_minus_two={differenceSize arithClosure two}\trealization_minus_two={differenceSize realizationClosure two}"
  logInfo m!"PAIRWISE\tre_craig_overlap={intersectionSize reClosure craigClosure}\tre_index_overlap={intersectionSize reClosure indexClosure}\tcraig_index_overlap={intersectionSize craigClosure indexClosure}\tgraph_arithmetization_overlap={intersectionSize graphClosure arithClosure}\tarithmetization_realization_overlap={intersectionSize arithClosure realizationClosure}"
  logInfo m!"PAIRWISE_DIFFERENCE\tre_not_craig={differenceSize reClosure craigClosure}\tcraig_not_re={differenceSize craigClosure reClosure}\tre_not_index={differenceSize reClosure indexClosure}\tindex_not_re={differenceSize indexClosure reClosure}\tgraph_not_arithmetization={differenceSize graphClosure arithClosure}\tarithmetization_not_graph={differenceSize arithClosure graphClosure}"
  logInfo m!"THREE_BRANCH_UNIQUE\tre_unique_vs_craig_index={uniqueAgainst reClosure craigClosure indexClosure}\tcraig_unique_vs_re_index={uniqueAgainst craigClosure reClosure indexClosure}\tindex_unique_vs_re_craig={uniqueAgainst indexClosure reClosure craigClosure}\tre_craig_index_union={reCraigIndex.size}\tgodel_outside_three_boundaries={differenceSize godelClosure reCraigIndex}"

end FailureOfComposition.Palomar.GodelBoundaryOverlap
