/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition
import Lean

/-!
Audit proof dependencies and the separation of the obstruction proof routes.
-/

open Lean Elab Command

/- An audit helper, not part of any mathematical proof. -/
private partial def collectDependencies (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: ns =>
    if seen.contains n then collectDependencies env ns seen
    else
      let seen := seen.insert n
      let more := match env.checked.get.find? n with
        | some (.axiomInfo v) => v.type.getUsedConstants
        | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
        | some (.thmInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
        | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
        | some (.ctorInfo v) => v.type.getUsedConstants
        | some (.recInfo v) => v.type.getUsedConstants
        | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
        | _ => #[]
      collectDependencies env (more.toList ++ ns) seen

run_cmd do
  let root := ``FailureOfComposition.ProgramIndices.no_index_quotient_via_productiveness
  let deps := collectDependencies (← getEnv) [root]
  let forbidden := deps.toArray.filter fun n =>
    n.toString.endsWith "consistent_unprovable" || n.toString.endsWith "con_unprovable" ||
    n.toString == "sorryAx"
  unless forbidden.isEmpty do
    throwError "Forbidden dependencies: {forbidden}"
  logInfo m!"Productiveness proof: traversed {deps.size} declarations; no consistent_unprovable, con_unprovable, or sorryAx dependency."

run_cmd do
  let env ← getEnv
  let roots := [``FailureOfComposition.ConcreteEvaluator.evalnCertificateFormula_natCode_persist,
    ``FailureOfComposition.ConcreteEvaluator.eventualGraph_functional,
    ``FailureOfComposition.ConcreteEvaluator.eventualGraph_composition,
    ``FailureOfComposition.ConcreteEvaluator.eventualGraph_identity,
    ``FailureOfComposition.ConcreteEvaluator.eventualGraph_empty,
    ``FailureOfComposition.ConcreteEvaluator.stageComputation_iff_evaln,
    ``FailureOfComposition.ConcreteEvaluator.eventualGraph_adequate,
    ``FailureOfComposition.ConcreteEvaluator.eventualGraph_rfind_code_eval,
    ``FailureOfComposition.ArithmeticCodeCompiler.computes_compile,
    ``FailureOfComposition.ArithmeticCodeCompiler.unaryCompile_realizes,
    ``FailureOfComposition.ConcreteIndices.guardIndex_realizes,
    ``FailureOfComposition.ConcreteIndices.searchIndex_realizes,
    ``FailureOfComposition.ConcreteIndices.no_index_quotient_via_productiveness,
    ``FailureOfComposition.ConcreteIndices.no_index_quotient_of_delta_one,
    ``FailureOfComposition.ConcreteIndices.no_index_quotient_of_re_axioms,
    ``FailureOfComposition.ConcreteIndices.no_index_quotient_of_axiom_enumerator,
    ``FailureOfComposition.ConcreteNormalForm.normalFormGraph_realizes,
    ``FailureOfComposition.ConcreteNormalForm.computationPredicate_nat,
    ``FailureOfComposition.SigmaOneRealization.semidecision_exists,
    ``FailureOfComposition.SigmaOneRealization.realize_graph,
    ``FailureOfComposition.CraigPresentation.exists_craig_presentation,
    ``FailureOfComposition.theorem_codes_re_of_axiom_codes]
  for root in roots do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString.contains "Arithmetization" || n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" || n.toString.endsWith "con_unprovable"
    unless forbidden.isEmpty do
      throwError "Forbidden concrete-evaluator dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected concrete-evaluator axioms: {unexpected}"
    logInfo m!"Concrete result {root}: {deps.size} declarations; no Arithmetization, Godel-II, or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  let roots := [``FailureOfComposition.ConcreteIndices.no_index_quotient_via_godel,
    ``FailureOfComposition.ConcreteIndices.no_index_quotient_via_godel_of_re_axioms,
    ``FailureOfComposition.ConcreteIndices.no_index_quotient_via_godel_of_axiom_enumerator]
  for root in roots do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString.toLower.contains "productive" || n.toString == "sorryAx"
    unless forbidden.isEmpty do
      throwError "Forbidden Godel-II dependencies: {forbidden}"
    unless deps.toArray.any (fun n => n.toString.endsWith "consistent_unprovable") do
      throwError "Godel-II proof does not use the audited second-incompleteness theorem"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected Godel-II axioms: {unexpected}"
    logInfo m!"Godel-II result {root}: {deps.size} declarations; uses consistent_unprovable; no productiveness or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.ConcreteEvaluator.arithmetization,
      ``FailureOfComposition.ConcreteTransport.toConcrete_uniform,
      ``FailureOfComposition.ConcreteTransport.quotientEquiv,
      ``FailureOfComposition.ConcreteTransport.toConcrete_composition] do
    let deps := collectDependencies env [root]
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected representation-transport axioms: {unexpected}"
    logInfo m!"Representation result {root}: {deps.size} declarations; standard axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.PiOneCharacterization.rightCompatible_implies_piOneComplete,
      ``FailureOfComposition.PiOneCharacterization.pointwise_iff_extensional,
      ``FailureOfComposition.PiOneCharacterization.characterization,
      ``FailureOfComposition.ProgramIndices.characterization,
      ``FailureOfComposition.ConcreteIndices.pi_one_characterization,
      ``FailureOfComposition.ConcreteIndices.no_index_quotient_iff_not_piOneComplete] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" || n.toString.toLower.contains "productive" ||
      n.toString.endsWith "consistent_unprovable" || n.toString.endsWith "con_unprovable"
    unless forbidden.isEmpty do
      throwError "Forbidden characterization dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected characterization axioms: {unexpected}"
    logInfo m!"Characterization result {root}: {deps.size} declarations; no productiveness, Godel-II, or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.GeneratedWitnessGraphs.AGraph_pointwise_B,
      ``FailureOfComposition.GeneratedCongruence.extensional_implies_generated,
      ``FailureOfComposition.GeneratedCongruence.classification,
      ``FailureOfComposition.ProgramIndices.generatedRel_iff_graph,
      ``FailureOfComposition.ProgramIndices.generated_congruence_classification,
      ``FailureOfComposition.ProgramIndices.generatedQuotientMulEquiv,
      ``FailureOfComposition.ConcreteIndices.generated_congruence_classification,
      ``FailureOfComposition.ConcreteIndices.pa_generated_iff_extensional,
      ``FailureOfComposition.ConcreteIndices.generated_quotient_subsingleton_iff_not_sound] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" || n.toString.toLower.contains "productive" ||
      n.toString.endsWith "consistent_unprovable" || n.toString.endsWith "con_unprovable" ||
      n.toString.endsWith ".PiOneComplete"
    unless forbidden.isEmpty do
      throwError "Forbidden generated-congruence dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected generated-congruence axioms: {unexpected}"
    logInfo m!"Generated congruence result {root}: {deps.size} declarations; no productiveness, Godel-II, PiOneComplete, or sorryAx dependency; axioms {axioms}."

-- Concrete weak totality, domain totality, and the conservativity consequence.
run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.ConcreteIndices.weaklyTotalIndex_identity,
      ``FailureOfComposition.ConcreteIndices.index_four_witnesses_of_history_divergence,
      ``FailureOfComposition.ConcreteIndices.weak_totality_counterexample_of_re_axioms,
      ``FailureOfComposition.ConcreteIndices.weak_totality_counterexample_of_axiom_enumerator,
      ``FailureOfComposition.ConcreteIndices.no_quotient_weak_totality_of_re_axioms,
      ``FailureOfComposition.ConcreteIndices.domainIndex_realizes,
      ``FailureOfComposition.ConcreteIndices.rTotal_of_pointwise_identity,
      ``FailureOfComposition.ConcreteIndices.exists_rTotal_not_weaklyTotal_of_re_axioms,
      ``FailureOfComposition.ConcreteIndices.pa_exists_rTotal_not_weaklyTotal,
      ``FailureOfComposition.ConcreteIndices.insert_provable_iff_of_provable,
      ``FailureOfComposition.ConcreteIndices.guard_convergenceAt_provable,
      ``FailureOfComposition.ConcreteIndices.montagna_condition_two_not_one,
      ``FailureOfComposition.ConcreteIndices.not_montagna_condition_two_implies_one] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" || n.toString.contains "Arithmetization" ||
      n.toString.endsWith "consistent_unprovable" || n.toString.endsWith "con_unprovable"
    unless forbidden.isEmpty do
      throwError "Forbidden weak-totality dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected weak-totality axioms: {unexpected}"
    logInfo m!"Weak-totality result {root}: {deps.size} declarations; no Arithmetization, Godel-II, or sorryAx dependency; axioms {axioms}."

-- Concrete range assignment, witnesses, and the two proof routes.

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.ConcreteIndices.rangeOfGraph_functional,
      ``FailureOfComposition.ConcreteIndices.uniform_rangeOfGraph,
      ``FailureOfComposition.ConcreteIndices.rangeIndex_realizes,
      ``FailureOfComposition.ConcreteIndices.rangeIndex_graph_equation,
      ``FailureOfComposition.ConcreteIndices.rangeIndex_eval,
      ``FailureOfComposition.ConcreteIndices.rangeIndex_empty,
      ``FailureOfComposition.ConcreteIndices.rangeIndex_choice_independent,
      ``FailureOfComposition.ConcreteIndices.probeIndex_realizes,
      ``FailureOfComposition.ConcreteIndices.probeIndex_pointwise_empty,
      ``FailureOfComposition.ConcreteIndices.range_probe_at_zero,
      ``FailureOfComposition.ConcreteIndices.range_probe_empty_implies_absence,
      ``FailureOfComposition.ConcreteIndices.range_counterexample_of_instance_refutations,
      ``FailureOfComposition.ConcreteIndices.no_quotient_range_of_instance_refutations,
      ``FailureOfComposition.ConcreteIndices.no_quotient_range_of_correct_assignment] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.contains "Arithmetization" ||
      n.toString.toLower.contains "productive" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable"
    unless forbidden.isEmpty do
      throwError "Forbidden Range foundation dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected Range foundation axioms: {unexpected}"
    logInfo m!"Range foundation result {root}: {deps.size} declarations; no productiveness, Godel-II, Arithmetization, or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.ConcreteIndices.proofBotPredicate_absence_unprovable,
      ``FailureOfComposition.ConcreteIndices.range_counterexample_via_godel,
      ``FailureOfComposition.ConcreteIndices.no_index_quotient_range_via_godel,
      ``FailureOfComposition.ConcreteIndices.range_counterexample_of_re_axioms,
      ``FailureOfComposition.ConcreteIndices.no_index_quotient_range_of_re_axioms,
      ``FailureOfComposition.ConcreteIndices.range_counterexample_of_axiom_enumerator,
      ``FailureOfComposition.ConcreteIndices.no_index_quotient_range_of_axiom_enumerator,
      ``FailureOfComposition.ConcreteIndices.pa_range_counterexample,
      ``FailureOfComposition.ConcreteIndices.pa_no_index_quotient_range] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.contains "Arithmetization" ||
      n.toString.toLower.contains "productive"
    unless forbidden.isEmpty do
      throwError "Forbidden Range Godel-II dependencies: {forbidden}"
    unless deps.toArray.any (fun n => n.toString.endsWith "consistent_unprovable") do
      throwError "Range Godel-II proof does not use the audited second-incompleteness theorem"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected Range Godel-II axioms: {unexpected}"
    logInfo m!"Range Godel-II result {root}: {deps.size} declarations; uses consistent_unprovable; no productiveness, Arithmetization, or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.ConcreteIndices.range_counterexample_via_productiveness,
      ``FailureOfComposition.ConcreteIndices.range_counterexample_via_productiveness_of_re_axioms,
      ``FailureOfComposition.ConcreteIndices.range_counterexample_via_productiveness_of_axiom_enumerator,
      ``FailureOfComposition.ConcreteIndices.no_index_quotient_range_via_productiveness_of_re_axioms] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.contains "Arithmetization" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable"
    unless forbidden.isEmpty do
      throwError "Forbidden Range productive dependencies: {forbidden}"
    unless deps.contains ``FailureOfComposition.productive_escape_re &&
        deps.contains ``FailureOfComposition.diagonal_escape do
      throwError "Range productive proof does not use the productive diagonal escape theorem"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected Range productive axioms: {unexpected}"
    logInfo m!"Range productive result {root}: {deps.size} declarations; uses diagonal-complement productiveness; no Godel-II, Arithmetization, or sorryAx dependency; axioms {axioms}."

-- Final manuscript coverage: uniform witnesses, true-Pi-one theory, and the extensional monoid.

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.ConcreteIndices.uniformKleeneSentence_iff_uniformSentence,
      ``FailureOfComposition.ConcreteIndices.uniformIndex_iff_kleene,
      ``FailureOfComposition.ConcreteIndices.identity_comp_uniformIndex,
      ``FailureOfComposition.ConcreteIndices.guard_search_uniformIndex_empty,
      ``FailureOfComposition.ConcreteIndices.obstruction_four_properties_of_re_axioms,
      ``FailureOfComposition.ConcreteIndices.obstruction_four_properties_of_axiom_enumerator] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" || n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable"
    unless forbidden.isEmpty do
      throwError "Forbidden Manuscript obstruction dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected Manuscript obstruction axioms: {unexpected}"
    logInfo m!"Manuscript obstruction result {root}: {deps.size} declarations; no Godel-II or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.PiOneCharacterization.truePiOneExtension_standard_model,
      ``FailureOfComposition.PiOneCharacterization.truePiOneExtension_consistent,
      ``FailureOfComposition.PiOneCharacterization.truePiOneExtension_piOneComplete,
      ``FailureOfComposition.PiOneCharacterization.truePiOneExtension_compositionCongruence,
      ``FailureOfComposition.PiOneCharacterization.truePiOneExtension_agreesWithExtensional,
      ``FailureOfComposition.PiOneCharacterization.truePiOneExtension_theorem_codes_not_re,
      ``FailureOfComposition.PiOneCharacterization.truePiOneExtension_axiom_codes_not_re] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" || n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable"
    unless forbidden.isEmpty do
      throwError "Forbidden True-Pi-one theory dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected True-Pi-one theory axioms: {unexpected}"
    logInfo m!"True-Pi-one theory result {root}: {deps.size} declarations; no Godel-II or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.UnaryPartrec.ofIndex_surjective,
      ``FailureOfComposition.ConcreteIndices.generatedQuotientDenotation_bijective,
      ``FailureOfComposition.ConcreteIndices.generatedQuotientPartialRecursiveEquiv,
      ``FailureOfComposition.ConcreteIndices.generatedQuotientPartialRecursiveEquiv_mk] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" || n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n.toString.toLower.contains "productive" || n.toString.endsWith ".PiOneComplete"
    unless forbidden.isEmpty do
      throwError "Forbidden Partial-recursive quotient dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected Partial-recursive quotient axioms: {unexpected}"
    logInfo m!"Partial-recursive quotient result {root}: {deps.size} declarations; no productiveness, Godel-II, PiOneComplete, or sorryAx dependency; axioms {axioms}."
