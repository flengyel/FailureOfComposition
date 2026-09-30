import FailureOfComposition.Palomar.SolutionSeven
import Lean

set_option autoImplicit false

open Lean Elab Command

namespace FailureOfComposition.Palomar.SevenDependencyAudit

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
        | throw s!"Unresolved proof dependency: {name}"
      closure env ((dependencies info).toList ++ rest) (seen.insert name)

private def getClosure (env : Environment) (roots : List Name) : CommandElabM NameSet :=
  match closure env roots with
  | .ok result => pure result
  | .error message => throwError message

private def axiomNames (env : Environment) (names : NameSet) : Array Name :=
  names.toArray.filter fun name =>
    match env.checked.get.find? name with
    | some (.axiomInfo _) => true
    | _ => false

private def sortedNames (names : NameSet) : Array Name :=
  names.toArray.qsort fun left right => decide (left.toString < right.toString)

private def printSet (label : String) (names : NameSet) : CommandElabM Unit := do
  for name in sortedNames names do
    logInfo m!"{label}\t{name}"

private def permittedAxiom (name : Name) : Bool :=
  name == `propext || name == `Classical.choice || name == `Quot.sound

run_cmd do
  let env ← getEnv
  let first := ``FailureOfComposition.Palomar.obstruction_four_properties
  let productive := ``FailureOfComposition.Palomar.no_quotient_composition_productive
  let godel := ``FailureOfComposition.Palomar.no_quotient_composition_godel
  let piOne := ``FailureOfComposition.Palomar.pi_one_characterization
  let generated := ``FailureOfComposition.Palomar.generated_congruence_classification
  let weak := ``FailureOfComposition.Palomar.weak_totality_counterexample
  let range := ``FailureOfComposition.Palomar.range_counterexample_godel
  let firstClosure ← getClosure env [first]
  let productiveClosure ← getClosure env [productive]
  let godelClosure ← getClosure env [godel]
  let piOneClosure ← getClosure env [piOne]
  let generatedClosure ← getClosure env [generated]
  let weakClosure ← getClosure env [weak]
  let rangeClosure ← getClosure env [range]
  let generatedSupport := [
    ``FailureOfComposition.Palomar.Arithmetic.Hierarchy.sigmaOne_toFoundation_iff,
    ``FailureOfComposition.Palomar.Arithmetic.sigmaOneSound_toFoundation_iff,
    ``FailureOfComposition.Palomar.Arithmetic.Evaluator.generatedRel_base,
    ``FailureOfComposition.Palomar.Arithmetic.Evaluator.generatedRel_equivalence,
    ``FailureOfComposition.Palomar.Arithmetic.Evaluator.generatedRel_comp,
    ``FailureOfComposition.Palomar.Arithmetic.Evaluator.generatedRel_least,
    ``FailureOfComposition.Palomar.Arithmetic.Evaluator.generatedRel_toFoundation_iff
  ]
  let generatedSupportClosure ← getClosure env generatedSupport
  let generatedRelationBridgeClosure ← getClosure env
    [``FailureOfComposition.Palomar.Arithmetic.Evaluator.generatedRel_toFoundation_iff]
  let weakSupport := [
    ``FailureOfComposition.Palomar.Arithmetic.Evaluator.IndexCompiler.compile_toFoundation,
    ``FailureOfComposition.Palomar.Arithmetic.Evaluator.guardCode_toFoundation,
    ``FailureOfComposition.Palomar.Arithmetic.Evaluator.guardIndex_toFoundation,
    ``FailureOfComposition.Palomar.Arithmetic.Evaluator.weaklyTotalIndex_toFoundation_iff
  ]
  let weakSupportClosure ← getClosure env weakSupport
  let weakPredicateBridgeClosure ← getClosure env
    [``FailureOfComposition.Palomar.Arithmetic.Evaluator.weaklyTotalIndex_toFoundation_iff]
  let rangeSupport := [
    ``FailureOfComposition.Palomar.Arithmetic.Evaluator.toFoundation_rangeGraph,
    ``FailureOfComposition.Palomar.Arithmetic.Evaluator.rangeRealizes_toFoundation_iff,
    ``FailureOfComposition.Palomar.Arithmetic.Evaluator.exists_rangeRealizes,
    ``FailureOfComposition.Palomar.Arithmetic.Evaluator.rangeIndex_realizes,
    ``FailureOfComposition.Palomar.Arithmetic.Evaluator.rangeIndex_choice_toFoundation,
    ``FailureOfComposition.Palomar.Arithmetic.Evaluator.rangeIndices_toFoundation_iff
  ]
  let rangeSupportClosure ← getClosure env rangeSupport
  let rangeChoiceBridgeClosure ← getClosure env
    [``FailureOfComposition.Palomar.Arithmetic.Evaluator.rangeIndices_toFoundation_iff]
  let threeUnion ← getClosure env [first, productive, godel]
  let fourUnion ← getClosure env [first, productive, godel, piOne]
  let fiveUnion ← getClosure env [first, productive, godel, piOne, generated]
  let sixUnion ← getClosure env [first, productive, godel, piOne, generated, weak]
  let sevenUnion ← getClosure env [first, productive, godel, piOne, generated, weak, range]
  let marginal := rangeClosure.toArray.filter fun name => !sixUnion.contains name
  let removed := sixUnion.toArray.filter fun name => !sevenUnion.contains name

  logInfo m!"SUMMARY\tfirst={firstClosure.size}\tproductive={productiveClosure.size}\tgodel={godelClosure.size}\tpi_one={piOneClosure.size}\tgenerated={generatedClosure.size}\tweak_totality={weakClosure.size}\trange={rangeClosure.size}\tthree_union={threeUnion.size}\tfour_union={fourUnion.size}\tfive_union={fiveUnion.size}\tsix_union={sixUnion.size}\tseven_union={sevenUnion.size}\tmarginal_over_six={marginal.size}\tremoved={removed.size}"
  logInfo m!"AXIOMS_FIRST\t{axiomNames env firstClosure}"
  logInfo m!"AXIOMS_PRODUCTIVE\t{axiomNames env productiveClosure}"
  logInfo m!"AXIOMS_GODEL\t{axiomNames env godelClosure}"
  logInfo m!"AXIOMS_PI_ONE\t{axiomNames env piOneClosure}"
  logInfo m!"AXIOMS_GENERATED\t{axiomNames env generatedClosure}"
  logInfo m!"AXIOMS_GENERATED_SUPPORT\t{axiomNames env generatedSupportClosure}"
  logInfo m!"AXIOMS_WEAK_TOTALITY\t{axiomNames env weakClosure}"
  logInfo m!"AXIOMS_WEAK_SUPPORT\t{axiomNames env weakSupportClosure}"
  logInfo m!"AXIOMS_RANGE\t{axiomNames env rangeClosure}"
  logInfo m!"AXIOMS_RANGE_SUPPORT\t{axiomNames env rangeSupportClosure}"
  logInfo m!"AXIOMS_UNION\t{axiomNames env sevenUnion}"
  logInfo m!"PRODUCTIVE_USES_FIRST_RESULT\t{productiveClosure.contains first}"

  let godelRequired := #[
    "FailureOfComposition.ConcreteIndices.no_index_quotient_via_godel_of_re_axioms".toName,
    "FailureOfComposition.ConcreteIndices.index_noncongruence_via_godel_of_re_axioms".toName,
    "FailureOfComposition.CraigPresentation.exists_craig_presentation".toName,
    "FailureOfComposition.ConcreteIndices.index_noncongruence_via_godel_of_equivalent_presentation".toName,
    "FailureOfComposition.ConcreteIndices.index_noncongruence_via_godel".toName,
    "FailureOfComposition.graph_noncongruence_via_godel".toName
  ]
  let godelMissing := godelRequired.filter fun name => !godelClosure.contains name
  let productiveReached := godelRequired.filter fun name => productiveClosure.contains name
  for name in godelRequired do
    logInfo m!"GODEL_ROUTE\t{name}\t{godelClosure.contains name}"
    logInfo m!"PRODUCTIVE_GODEL_ROUTE\t{name}\t{productiveClosure.contains name}"

  let godelForbidden := #[
    "FailureOfComposition.productive_escape_re".toName,
    first,
    productive,
    "FailureOfComposition.Palomar.Arithmetic.Evaluator.obstruction_four_properties".toName,
    "FailureOfComposition.Palomar.Arithmetic.Evaluator.no_quotient_composition_of_four_properties".toName,
    "FailureOfComposition.ConcreteIndices.obstruction_four_properties_of_re_axioms".toName,
    "FailureOfComposition.ConcreteIndices.no_index_quotient_of_re_axioms".toName,
    "FailureOfComposition.ConcreteIndices.no_index_quotient_via_productiveness".toName
  ]
  let godelForbiddenReached := godelForbidden.filter fun name => godelClosure.contains name
  for name in godelForbidden do
    logInfo m!"GODEL_PRODUCTIVE_ROUTE\t{name}\t{godelClosure.contains name}"

  let piOneRequired := #[
    "FailureOfComposition.ConcreteIndices.pi_one_characterization".toName,
    "FailureOfComposition.Palomar.Arithmetic.standardTrue_toFoundation_iff".toName,
    "FailureOfComposition.Palomar.Arithmetic.Hierarchy.piOne_toFoundation".toName,
    "FailureOfComposition.Palomar.Arithmetic.Hierarchy.piOne_ofFoundation".toName,
    "FailureOfComposition.Palomar.Arithmetic.piOneComplete_toFoundation_iff".toName,
    "FailureOfComposition.Palomar.Arithmetic.Evaluator.rightCompatible_toFoundation_iff".toName,
    "FailureOfComposition.Palomar.Arithmetic.Evaluator.compositionCongruence_toFoundation_iff".toName,
    "FailureOfComposition.Palomar.Arithmetic.Evaluator.agreesWithExtensional_toFoundation_iff".toName
  ]
  let piOneMissing := piOneRequired.filter fun name => !piOneClosure.contains name
  for name in piOneRequired do
    logInfo m!"PI_ONE_ROUTE\t{name}\t{piOneClosure.contains name}"

  let generatedRequired := #[
    "FailureOfComposition.ConcreteIndices.generated_congruence_classification".toName,
    "FailureOfComposition.Palomar.Arithmetic.Hierarchy.sigmaOne_toFoundation".toName,
    "FailureOfComposition.Palomar.Arithmetic.Hierarchy.sigmaOne_ofFoundation".toName,
    "FailureOfComposition.Palomar.Arithmetic.sigmaOneSound_toFoundation_iff".toName,
    "FailureOfComposition.Palomar.Arithmetic.Evaluator.generatedRel_toFoundation_iff".toName,
    "FailureOfComposition.Palomar.Arithmetic.Evaluator.generated_congruence_classification".toName
  ]
  let generatedMissing := generatedRequired.filter fun name => !generatedClosure.contains name
  for name in generatedRequired do
    logInfo m!"GENERATED_ROUTE\t{name}\t{generatedClosure.contains name}"

  let weakRequired := #[
    "FailureOfComposition.ConcreteIndices.weak_totality_counterexample_of_re_axioms".toName,
    "FailureOfComposition.ConcreteIndices.weak_totality_counterexample_via_productiveness".toName,
    "FailureOfComposition.ConcreteEvaluator.exists_true_unprovable_history_divergence_of_theorem_codes".toName,
    "FailureOfComposition.Palomar.Arithmetic.Evaluator.IndexCompiler.compile_toFoundation".toName,
    "FailureOfComposition.Palomar.Arithmetic.Evaluator.guardIndex_toFoundation".toName,
    "FailureOfComposition.Palomar.Arithmetic.Evaluator.weaklyTotalIndex_toFoundation_iff".toName,
    "FailureOfComposition.Palomar.Arithmetic.Evaluator.weak_totality_counterexample".toName
  ]
  let weakMissing := weakRequired.filter fun name => !weakClosure.contains name
  let weakGodelReached := godelRequired.filter fun name => weakClosure.contains name
  for name in weakRequired do
    logInfo m!"WEAK_TOTALITY_ROUTE\t{name}\t{weakClosure.contains name}"
  for name in godelRequired do
    logInfo m!"WEAK_TOTALITY_GODEL_ROUTE\t{name}\t{weakClosure.contains name}"

  let rangeRequired := #[
    "FailureOfComposition.ConcreteIndices.range_counterexample_of_re_axioms".toName,
    "FailureOfComposition.ConcreteIndices.range_counterexample_of_equivalent_presentation".toName,
    "FailureOfComposition.ConcreteIndices.range_counterexample_via_godel".toName,
    "FailureOfComposition.CraigPresentation.exists_craig_presentation".toName,
    "FailureOfComposition.Palomar.Arithmetic.Evaluator.rangeRealizes_toFoundation_iff".toName,
    "FailureOfComposition.Palomar.Arithmetic.Evaluator.rangeIndex_choice_toFoundation".toName,
    "FailureOfComposition.Palomar.Arithmetic.Evaluator.rangeIndices_toFoundation_iff".toName,
    "FailureOfComposition.Palomar.Arithmetic.Evaluator.range_counterexample_godel".toName
  ]
  let rangeMissing := rangeRequired.filter fun name => !rangeClosure.contains name
  let rangeProductiveForbidden := #[
    "FailureOfComposition.ConcreteIndices.range_counterexample_via_productiveness".toName,
    "FailureOfComposition.ConcreteIndices.range_counterexample_via_productiveness_of_re_axioms".toName,
    "FailureOfComposition.ConcreteEvaluator.exists_true_unprovable_history_divergence_of_theorem_codes".toName
  ]
  let rangeProductiveReached := rangeProductiveForbidden.filter fun name => rangeClosure.contains name
  for name in rangeRequired do
    logInfo m!"RANGE_GODEL_ROUTE\t{name}\t{rangeClosure.contains name}"
  for name in rangeProductiveForbidden do
    logInfo m!"RANGE_PRODUCTIVE_ROUTE\t{name}\t{rangeClosure.contains name}"

  printSet "FIRST_DEP" firstClosure
  printSet "PRODUCTIVE_DEP" productiveClosure
  printSet "GODEL_DEP" godelClosure
  printSet "PI_ONE_DEP" piOneClosure
  printSet "GENERATED_DEP" generatedClosure
  printSet "WEAK_TOTALITY_DEP" weakClosure
  printSet "RANGE_DEP" rangeClosure
  printSet "SEVEN_UNION_DEP" sevenUnion
  for name in marginal.qsort (fun left right => decide (left.toString < right.toString)) do
    logInfo m!"MARGINAL_DEP\t{name}"

  unless productiveClosure.contains first do
    throwError "The productive quotient theorem does not retain its owned first-result dependency"
  unless removed.isEmpty do
    throwError "The cumulative seven-root union unexpectedly removed a Six dependency"
  unless godelMissing.isEmpty do
    throwError m!"The Gödel theorem misses maintained route declarations: {godelMissing}"
  unless productiveReached.isEmpty do
    throwError m!"The productive theorem reaches Gödel-II/Craig declarations: {productiveReached}"
  unless godelForbiddenReached.isEmpty do
    throwError m!"The Gödel theorem reaches productive/first-result proof roots: {godelForbiddenReached}"
  unless piOneMissing.isEmpty do
    throwError m!"The Π₁ theorem misses correspondence/maintained roots: {piOneMissing}"
  unless generatedMissing.isEmpty do
    throwError m!"The generated theorem misses correspondence/maintained roots: {generatedMissing}"
  unless weakMissing.isEmpty do
    throwError m!"The weak-totality theorem misses correspondence/maintained roots: {weakMissing}"
  unless weakGodelReached.isEmpty do
    throwError m!"The weak-totality theorem reaches Gödel-II/Craig declarations: {weakGodelReached}"
  if generatedRelationBridgeClosure.contains
      ``FailureOfComposition.ConcreteIndices.generated_congruence_classification then
    throwError "The generated-relation correspondence is circular through the classification theorem"
  unless axiomNames env generatedSupportClosure |>.all permittedAxiom do
    throwError "The generated correspondence support contains an unpermitted axiom"
  if weakPredicateBridgeClosure.contains
      ``FailureOfComposition.ConcreteIndices.weak_totality_counterexample_of_re_axioms then
    throwError "The weak-totality predicate correspondence is circular through the counterexample"
  unless axiomNames env weakSupportClosure |>.all permittedAxiom do
    throwError "The weak-totality correspondence support contains an unpermitted axiom"
  unless rangeMissing.isEmpty do
    throwError m!"The range theorem misses correspondence/maintained roots: {rangeMissing}"
  unless rangeProductiveReached.isEmpty do
    throwError m!"The Gödel range theorem reaches the productive range route: {rangeProductiveReached}"
  if rangeChoiceBridgeClosure.contains
      ``FailureOfComposition.ConcreteIndices.range_counterexample_of_re_axioms then
    throwError "The range choice correspondence is circular through the counterexample"
  unless axiomNames env rangeSupportClosure |>.all permittedAxiom do
    throwError "The range correspondence support contains an unpermitted axiom"
  unless axiomNames env sevenUnion |>.all permittedAxiom do
    throwError "The cumulative proof closure contains an unpermitted axiom"

end FailureOfComposition.Palomar.SevenDependencyAudit
