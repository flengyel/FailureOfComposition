/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ConcreteWeakTotality

/-!
The four conclusions of manuscript Theorem 1, retaining uniform provable
equality in its two middle clauses. The concrete productive witnesses have
these uniform graph equations already in PA, before passing to the theory T.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition.ConcreteIndices

open ProofSearch ConcreteEvaluator HistoryWitnesses ProgramIndices ConcreteEmptyGraph

/-- Uniform equality of the concrete arithmetic program graphs. -/
def UniformIndex (T : ArithmeticTheory) (e f : ℕ) : Prop :=
  Uniform T (eventualGraph e) (eventualGraph f)

/-- The manuscript's Kleene equality formula, universally quantified over inputs. -/
def uniformKleeneSentence (F G : Graph) : ArithmeticSentence :=
  “∀ x, ((∃ y, !F.val x y) ↔ (∃ y, !G.val x y)) ∧
    ((∃ y, !F.val x y) → ∃ y, !F.val x y ∧ !G.val x y)”

@[simp] theorem uniformKleeneSentence_eval {M : Type*} [ORingStructure M] (F G : Graph) :
    (uniformKleeneSentence F G).Evalb (M := M) ![] ↔
      ∀ x : M, ((∃ y, F.val.Evalb ![x, y]) ↔ ∃ y, G.val.Evalb ![x, y]) ∧
        ((∃ y, F.val.Evalb ![x, y]) → ∃ y, F.val.Evalb ![x, y] ∧ G.val.Evalb ![x, y]) := by
  simp [uniformKleeneSentence]

/-- PA functionality equates the two uniform encodings, at all internal inputs. -/
theorem uniformKleeneSentence_iff_uniformSentence (F G : Graph)
    (hF : Functional F) (hG : Functional G) :
    𝗣𝗔 ⊢ uniformKleeneSentence F G 🡘 uniformSentence F G := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hf := consequence_iff.mp (Theory.Proof.sound hF) M inferInstance
  have hg := consequence_iff.mp (Theory.Proof.sound hG) M inferInstance
  simp only [models_iff, functionalSentence_eval] at hf hg
  simp only [models_iff, LogicalConnective.HomClass.map_iff,
    uniformKleeneSentence_eval, uniformSentence_eval, LogicalConnective.Prop.iff_eq]
  apply forall_congr'
  intro x
  constructor
  · rintro ⟨hdom, hcommon⟩ y
    constructor
    · intro hy
      obtain ⟨z, hzF, hzG⟩ := hcommon ⟨y, hy⟩
      exact (hf x y z hy hzF).symm ▸ hzG
    · intro hy
      obtain ⟨z, hzF, hzG⟩ := hcommon (hdom.mpr ⟨y, hy⟩)
      exact (hg x y z hy hzG).symm ▸ hzF
  · intro h
    exact ⟨exists_congr h, fun ⟨y, hy⟩ => ⟨y, hy, (h y).mp hy⟩⟩

/-- UniformIndex is precisely provability of the manuscript's uniform formula. -/
theorem uniformIndex_iff_kleene (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (e f : ℕ) :
    UniformIndex T e f ↔
      T ⊢ uniformKleeneSentence (eventualGraph e) (eventualGraph f) := by
  have h : T ⊢ uniformKleeneSentence (eventualGraph e) (eventualGraph f) 🡘
      uniformSentence (eventualGraph e) (eventualGraph f) :=
    WeakerThan.pbl (uniformKleeneSentence_iff_uniformSentence _ _
      (eventualGraph_functional e) (eventualGraph_functional f))
  constructor
  · intro he
    have he' : T ⊢ uniformSentence (eventualGraph e) (eventualGraph f) := he
    cl_prover [h, he']
  · intro he
    change T ⊢ uniformSentence (eventualGraph e) (eventualGraph f)
    cl_prover [h, he]

private theorem uniform_trans {F G H : Graph}
    (hFG : Uniform 𝗣𝗔 F G) (hGH : Uniform 𝗣𝗔 G H) : Uniform 𝗣𝗔 F H := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hFG' := consequence_iff.mp (Theory.Proof.sound hFG) M inferInstance
  have hGH' := consequence_iff.mp (Theory.Proof.sound hGH) M inferInstance
  simp only [models_iff, uniformSentence_eval] at hFG' hGH' ⊢
  exact fun x y => (hFG' x y).trans (hGH' x y)

private theorem uniform_symm {F G : Graph} (hFG : Uniform 𝗣𝗔 F G) :
    Uniform 𝗣𝗔 G F := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hFG' := consequence_iff.mp (Theory.Proof.sound hFG) M inferInstance
  simp only [models_iff, uniformSentence_eval] at hFG' ⊢
  exact fun x y => (hFG' x y).symm

/-- The concrete identity law is uniformly provable already in PA. -/
theorem identity_comp_uniformIndex (e : ℕ) :
    UniformIndex 𝗣𝗔 (canonicalPartrecCompIndex Kleene.identityIndex e) e := by
  have hRefl : Uniform 𝗣𝗔 (eventualGraph e) (eventualGraph e) := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    simp [models_iff, uniformSentence_eval]
  exact uniform_trans (eventualGraph_composition _ _)
    (uniform_trans (uniform_comp eventualGraph_identity hRefl)
      (identity_comp (eventualGraph e)))

/-- The guard-search composite has uniformly empty graph already in PA. -/
theorem guard_search_uniformIndex_empty (d : ℕ) :
    UniformIndex 𝗣𝗔 (canonicalPartrecCompIndex (guardIndex d) (searchIndex d))
      concreteEmptyIndex :=
  uniform_trans (eventualGraph_composition _ _)
    (uniform_trans (uniform_comp (guardIndex_realizes d) (searchIndex_realizes d))
      (uniform_trans (HistoryWitnesses.guard_search_empty d)
        (uniform_symm eventualGraph_empty)))

/-- The four manuscript properties, with the stronger PA-uniform middle clauses. -/
theorem index_four_witnesses_uniform_of_history_divergence
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (d : ℕ)
    (hdiv : ¬diagonalHistoryFormula.Evalb ![d])
    (hnot : T ⊬ ∼diagonalHistoryFormula/[d]) :
    PointwiseIndex T (guardIndex d) Kleene.identityIndex ∧
      UniformIndex 𝗣𝗔 (canonicalPartrecCompIndex (guardIndex d) (searchIndex d))
        concreteEmptyIndex ∧
      UniformIndex 𝗣𝗔 (canonicalPartrecCompIndex Kleene.identityIndex (searchIndex d))
        (searchIndex d) ∧
      ¬PointwiseIndex T (searchIndex d) concreteEmptyIndex :=
  ⟨guardIndex_pointwise_identity T d hdiv, guard_search_uniformIndex_empty d,
    identity_comp_uniformIndex (searchIndex d), searchIndex_not_pointwise_empty T d hnot⟩

/-- Theorem 1's four properties for every consistent recursively axiomatized
extension of PA. Uniform provability is retained, not replaced by its instances. -/
theorem obstruction_four_properties_of_re_axioms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ∃ f g : ℕ, PointwiseIndex T f Kleene.identityIndex ∧
      UniformIndex T (canonicalPartrecCompIndex f g) concreteEmptyIndex ∧
      UniformIndex T (canonicalPartrecCompIndex Kleene.identityIndex g) g ∧
      ¬PointwiseIndex T g concreteEmptyIndex := by
  obtain ⟨d, hdiv, hnot⟩ := exists_true_unprovable_history_divergence_of_theorem_codes T
    (theorem_codes_re_of_axiom_codes T hT)
  obtain ⟨hfi, hfg, hig, hgz⟩ :=
    index_four_witnesses_uniform_of_history_divergence T d hdiv hnot
  exact ⟨guardIndex d, searchIndex d, hfi, WeakerThan.pbl hfg,
    WeakerThan.pbl hig, hgz⟩

/-- The explicit partial-recursive axiom-enumerator presentation of Theorem 1. -/
theorem obstruction_four_properties_of_axiom_enumerator
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T] (a : ℕ)
    (ha : ∀ n : ℕ, AxiomCodes T n ↔ ∃ x : ℕ, n ∈ Kleene.eval a x) :
    ∃ f g : ℕ, PointwiseIndex T f Kleene.identityIndex ∧
      UniformIndex T (canonicalPartrecCompIndex f g) concreteEmptyIndex ∧
      UniformIndex T (canonicalPartrecCompIndex Kleene.identityIndex g) g ∧
      ¬PointwiseIndex T g concreteEmptyIndex :=
  obstruction_four_properties_of_re_axioms T (axiom_codes_re_of_program_enumerator T a ha)

end FailureOfComposition.ConcreteIndices
