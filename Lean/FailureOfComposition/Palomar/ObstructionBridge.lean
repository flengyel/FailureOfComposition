/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.Palomar.EvaluatorBridge
import FailureOfComposition.ManuscriptObstruction

/-!
# Obstruction transport for the independent Palomar interface

This top bridge is intentionally separate from the evaluator/compiler
correspondence.  It is the only layer that imports the maintained manuscript
obstruction and its uniform-index formulation.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment

namespace FailureOfComposition.Palomar.Arithmetic.Evaluator

/-- The independent internally universal Kleene-equality sentence is literally
the maintained manuscript sentence after translation. -/
@[simp] theorem toFoundation_uniformKleeneSentence (e d : ℕ) :
    Formula.toFoundation
        (uniformKleeneSentence (eventualGraph e) (eventualGraph d)) =
      FailureOfComposition.ConcreteIndices.uniformKleeneSentence
        (FailureOfComposition.ConcreteEvaluator.eventualGraph e)
        (FailureOfComposition.ConcreteEvaluator.eventualGraph d) := by
  simp [uniformKleeneSentence, kleeneEqTerm, definedAt, commonValueAt,
    biimp, FailureOfComposition.ConcreteIndices.uniformKleeneSentence,
    LogicalConnective.iff, Matrix.fun_eq_vec_two,
    Formula.toFoundation_and, Formula.toFoundation_imply,
    Formula.toFoundation_all, Formula.toFoundation_exs,
    Formula.toFoundation_subst, Term.toFoundation_lift,
    Term.toFoundation_bvar]

/-- Uniform provability is preserved and reflected.  The maintained side uses
its output-graph formulation, whose equivalence with the manuscript's
definedness/common-value sentence is itself proved over PA. -/
theorem uniformIndex_toFoundation_iff (T : Theory)
    [FFL.Entailment.WeakerThan FFL.FirstOrder.Arithmetic.Peano
      (TheoryCorrespondence.toFoundation T)] (e d : ℕ) :
    UniformIndex T e d ↔
      FailureOfComposition.ConcreteIndices.UniformIndex
        (TheoryCorrespondence.toFoundation T) e d := by
  unfold UniformIndex
  constructor
  · intro h
    apply (FailureOfComposition.ConcreteIndices.uniformIndex_iff_kleene
      (TheoryCorrespondence.toFoundation T) e d).mpr
    change Nonempty (FFL.FirstOrder.Theory.Proof
      (TheoryCorrespondence.toFoundation T)
      (FailureOfComposition.ConcreteIndices.uniformKleeneSentence
        (FailureOfComposition.ConcreteEvaluator.eventualGraph e)
        (FailureOfComposition.ConcreteEvaluator.eventualGraph d)))
    simpa using (provable_toFoundation_iff T _).mp h
  · intro h
    apply (provable_toFoundation_iff T _).mpr
    have hk := (FailureOfComposition.ConcreteIndices.uniformIndex_iff_kleene
      (TheoryCorrespondence.toFoundation T) e d).mp h
    change Nonempty (FFL.FirstOrder.Theory.Proof
      (TheoryCorrespondence.toFoundation T)
      (FailureOfComposition.ConcreteIndices.uniformKleeneSentence
        (FailureOfComposition.ConcreteEvaluator.eventualGraph e)
        (FailureOfComposition.ConcreteEvaluator.eventualGraph d))) at hk
    simpa using hk

/-- The first Palomar target, transported without changing any hypothesis or
any of its four pointwise/uniform clauses. -/
theorem obstruction_four_properties
    (T : Theory) (hPA : DeductivelyExtends Peano T) (hCons : Consistent T)
    (hT : REPred (AxiomCodes T)) :
    ∃ f g : ℕ, PointwiseIndex T f identityIndex ∧
      UniformIndex T (compIndex f g) emptyIndex ∧
      UniformIndex T (compIndex identityIndex g) g ∧
      ¬PointwiseIndex T g emptyIndex := by
  let Tf := TheoryCorrespondence.toFoundation T
  have hpa : FFL.Entailment.WeakerThan FFL.FirstOrder.Arithmetic.Peano Tf :=
    (deductivelyExtendsPeano_toFoundation_iff T).mp hPA
  have hcon : FFL.Entailment.Consistent Tf :=
    (consistent_toFoundation_iff T).mp hCons
  let _ : FFL.Entailment.WeakerThan FFL.FirstOrder.Arithmetic.Peano Tf := hpa
  let _ : FFL.Entailment.Consistent Tf := hcon
  have hre : REPred (FailureOfComposition.AxiomCodes Tf) :=
    (reAxiomCodes_toFoundation_iff T).mp hT
  obtain ⟨f, g, hfi, hfg, hig, hgz⟩ :=
    FailureOfComposition.ConcreteIndices.obstruction_four_properties_of_re_axioms
      Tf hre
  refine ⟨f, g, ?_, ?_, ?_, ?_⟩
  · apply (pointwiseIndex_toFoundation_iff T f identityIndex).mpr
    simpa using hfi
  · apply (uniformIndex_toFoundation_iff T (compIndex f g) emptyIndex).mpr
    simpa using hfg
  · apply (uniformIndex_toFoundation_iff T (compIndex identityIndex g) g).mpr
    simpa using hig
  · intro hg
    apply hgz
    have hg' := (pointwiseIndex_toFoundation_iff T g emptyIndex).mp hg
    simpa using hg'

end FailureOfComposition.Palomar.Arithmetic.Evaluator
