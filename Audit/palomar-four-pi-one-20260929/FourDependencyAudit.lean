import FailureOfComposition.Palomar.SolutionFour
import Lean

set_option autoImplicit false

open Lean Elab Command

namespace FailureOfComposition.Palomar.FourDependencyAudit

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
  let firstClosure ← getClosure env [first]
  let productiveClosure ← getClosure env [productive]
  let godelClosure ← getClosure env [godel]
  let piOneClosure ← getClosure env [piOne]
  let threeUnion ← getClosure env [first, productive, godel]
  let fourUnion ← getClosure env [first, productive, godel, piOne]
  let marginal := piOneClosure.toArray.filter fun name => !threeUnion.contains name
  let removed := threeUnion.toArray.filter fun name => !fourUnion.contains name

  logInfo m!"SUMMARY\tfirst={firstClosure.size}\tproductive={productiveClosure.size}\tgodel={godelClosure.size}\tpi_one={piOneClosure.size}\tthree_union={threeUnion.size}\tfour_union={fourUnion.size}\tmarginal={marginal.size}\tremoved={removed.size}"
  logInfo m!"AXIOMS_FIRST\t{axiomNames env firstClosure}"
  logInfo m!"AXIOMS_PRODUCTIVE\t{axiomNames env productiveClosure}"
  logInfo m!"AXIOMS_GODEL\t{axiomNames env godelClosure}"
  logInfo m!"AXIOMS_PI_ONE\t{axiomNames env piOneClosure}"
  logInfo m!"AXIOMS_UNION\t{axiomNames env fourUnion}"
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

  printSet "FIRST_DEP" firstClosure
  printSet "PRODUCTIVE_DEP" productiveClosure
  printSet "GODEL_DEP" godelClosure
  printSet "PI_ONE_DEP" piOneClosure
  printSet "FOUR_UNION_DEP" fourUnion
  for name in marginal.qsort (fun left right => decide (left.toString < right.toString)) do
    logInfo m!"MARGINAL_DEP\t{name}"

  unless productiveClosure.contains first do
    throwError "The productive quotient theorem does not retain its owned first-result dependency"
  unless removed.isEmpty do
    throwError "The cumulative four-root union unexpectedly removed a Three dependency"
  unless godelMissing.isEmpty do
    throwError m!"The Gödel theorem misses maintained route declarations: {godelMissing}"
  unless productiveReached.isEmpty do
    throwError m!"The productive theorem reaches Gödel-II/Craig declarations: {productiveReached}"
  unless godelForbiddenReached.isEmpty do
    throwError m!"The Gödel theorem reaches productive/first-result proof roots: {godelForbiddenReached}"
  unless piOneMissing.isEmpty do
    throwError m!"The Π₁ theorem misses correspondence/maintained roots: {piOneMissing}"
  unless axiomNames env fourUnion |>.all permittedAxiom do
    throwError "The cumulative proof closure contains an unpermitted axiom"

end FailureOfComposition.Palomar.FourDependencyAudit
