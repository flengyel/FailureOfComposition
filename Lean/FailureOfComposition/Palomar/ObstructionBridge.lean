/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.Palomar.EvaluatorBridge
import FailureOfComposition.Palomar.DirectDivergenceBridge
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

open FailureOfComposition.Palomar.DirectDerivationEnumeration
open FailureOfComposition.ConcreteEvaluator

local instance obstructionFormulaPrimcodable
    {ξ : Type} [Primcodable ξ] {n : ℕ} :
    Primcodable (FailureOfComposition.Palomar.Arithmetic.Formula ξ n) :=
  Primcodable.ofEquiv (ArithmeticSemiformula ξ n)
    FailureOfComposition.Palomar.Arithmetic.Formula.equivalence

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

/-- The one-way uniform transport needed by the obstruction theorem.  Unlike
`uniformIndex_toFoundation_iff`, this direction is pure syntactic LK and does
not use functionality, PA, or semantic completeness. -/
theorem uniformIndex_of_toFoundation (T : Theory) (e d : ℕ)
    (h : FailureOfComposition.ConcreteIndices.UniformIndex
      (TheoryCorrespondence.toFoundation T) e d) :
    UniformIndex T e d := by
  unfold UniformIndex
  apply (provable_toFoundation_iff T _).mpr
  have hk :=
    FailureOfComposition.ConcreteIndices.uniformKleeneSentence_of_uniformSentence
      (TheoryCorrespondence.toFoundation T)
      (FailureOfComposition.ConcreteEvaluator.eventualGraph e)
      (FailureOfComposition.ConcreteEvaluator.eventualGraph d) h
  rw [toFoundation_uniformKleeneSentence]
  exact hk

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
  have hre : REPred (Provable T) :=
    DirectDerivationEnumeration.provable_re_of_axiom_codes T hT
  have hreDivergence : REPred (fun n ↦
      Provable T (directHistoryDivergenceSentence n)) :=
    hre.comp directHistoryDivergenceSentence_primrec.to_comp
  have hsound (n : ℕ) :
      Provable T (directHistoryDivergenceSentence n) →
        ¬FailureOfComposition.diagonalHalts n := by
    intro hp
    apply FailureOfComposition.ConcreteEvaluator.provableHistoryDivergence_sound
      Tf n
    have hp' :=
      (provable_toFoundation_iff T (directHistoryDivergenceSentence n)).mp hp
    change Nonempty (FFL.FirstOrder.Theory.Proof Tf
      (Formula.toFoundation (directHistoryDivergenceSentence n))) at hp'
    rw [toFoundation_directHistoryDivergenceSentence] at hp'
    change Nonempty (FFL.FirstOrder.Theory.Proof Tf
      (foundationHistoryDivergenceSentence n))
    exact hp'
  obtain ⟨d, hdivNat, hnotDirect⟩ :=
    FailureOfComposition.productive_escape_re hreDivergence hsound
  have hdiv :
      ¬FailureOfComposition.ConcreteEvaluator.diagonalHistoryFormula.Evalb
        ![d] := by
    intro hd
    apply hdivNat
    exact (diagonalHistoryFormula_nat d).mp hd
  have hnot : Tf ⊬
      ∼FailureOfComposition.ConcreteEvaluator.diagonalHistoryFormula/[d] := by
    intro hp
    apply hnotDirect
    apply (provable_toFoundation_iff T
      (directHistoryDivergenceSentence d)).mpr
    change Nonempty (FFL.FirstOrder.Theory.Proof Tf
      (Formula.toFoundation (directHistoryDivergenceSentence d)))
    rw [toFoundation_directHistoryDivergenceSentence]
    change Nonempty (FFL.FirstOrder.Theory.Proof Tf
      (foundationHistoryDivergenceSentence d)) at hp
    exact hp
  obtain ⟨hfi, hfg, hig, hgz⟩ :=
    FailureOfComposition.ConcreteIndices.index_four_witnesses_uniform_of_history_divergence
      Tf d hdiv hnot
  let f := FailureOfComposition.ConcreteIndices.guardIndex d
  let g := FailureOfComposition.ConcreteIndices.searchIndex d
  refine ⟨f, g, ?_, ?_, ?_, ?_⟩
  · apply (pointwiseIndex_toFoundation_iff T f identityIndex).mpr
    simpa [f] using hfi
  · apply uniformIndex_of_toFoundation T (compIndex f g) emptyIndex
    have hfg' : FailureOfComposition.ConcreteIndices.UniformIndex Tf
        (CategoricalRiceShapiro.PartialRecursive.canonicalPartrecCompIndex f g)
        FailureOfComposition.ConcreteEmptyGraph.concreteEmptyIndex :=
      WeakerThan.pbl hfg
    simpa [f, g] using hfg'
  · apply uniformIndex_of_toFoundation T (compIndex identityIndex g) g
    have hig' : FailureOfComposition.ConcreteIndices.UniformIndex Tf
        (CategoricalRiceShapiro.PartialRecursive.canonicalPartrecCompIndex
          FailureOfComposition.Kleene.identityIndex g) g :=
      WeakerThan.pbl hig
    simpa [g] using hig'
  · intro hg
    apply hgz
    have hg' := (pointwiseIndex_toFoundation_iff T g emptyIndex).mp hg
    simpa [g] using hg'

end FailureOfComposition.Palomar.Arithmetic.Evaluator
