/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.Palomar.ObstructionBridge
import FailureOfComposition.QuotientObstruction

/-!
# Productive quotient obstruction for the independent Palomar interface

This file relates the compact core quotient used by the eligible statement to
the maintained pointwise-index quotient, proves the representative equality
criterion, and derives the quotient obstruction from the four checked
productive witnesses.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment

namespace FailureOfComposition.Palomar.Arithmetic.Evaluator

private theorem graph_input_subst
    (F : FailureOfComposition.ProofSearch.Graph) (n : ℕ) :
    (Rew.subst ![(n : ArithmeticTerm Empty)]).q ▹
        Rewriting.subst F.val
          ![(#1 : ArithmeticSemiterm Empty 2),
            (#0 : ArithmeticSemiterm Empty 2)] =
      Rewriting.subst F.val
        ![(n : ArithmeticSemiterm Empty 1),
          (#0 : ArithmeticSemiterm Empty 1)] := by
  rw [← TransitiveRewriting.comp_app, Rew.q_subst,
    Rew.subst_comp_subst]
  apply Rewriting.smul_ext'
  apply Rew.ext
  · intro i
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun z ↦ Fin.elim0 z) j) i
    · simp
    · simp
  · intro x
    exact Empty.elim x

/-- Internal universal Kleene equality yields each external numeral instance.
This is pure syntactic LK and requires no arithmetic, consistency,
functionality, soundness, or completeness hypothesis. -/
theorem uniformIndex_imp_pointwiseIndex (T : Theory) (e d : ℕ) :
    UniformIndex T e d → PointwiseIndex T e d := by
  intro h n
  have hu := (provable_toFoundation_iff T _).mp h
  let F := FailureOfComposition.ConcreteEvaluator.eventualGraph e
  let G := FailureOfComposition.ConcreteEvaluator.eventualGraph d
  have hu' : TheoryCorrespondence.toFoundation T ⊢
      FailureOfComposition.ConcreteIndices.uniformKleeneSentence F G := by
    change Nonempty (FFL.FirstOrder.Theory.Proof
      (TheoryCorrespondence.toFoundation T)
      (FailureOfComposition.ConcreteIndices.uniformKleeneSentence F G))
    simpa [F, G] using hu
  let body : ArithmeticSemisentence 1 :=
    “x. ((∃ y, !F.val x y) ↔ (∃ y, !G.val x y)) ∧
      ((∃ y, !F.val x y) → ∃ y, !F.val x y ∧ !G.val x y)”
  have hi := FFL.FirstOrder.Theory.Proof.specialize
    (T := TheoryCorrespondence.toFoundation T) body
    (n : ArithmeticTerm Empty)
  have hs := Entailment.mdp hi hu'
  apply (provable_toFoundation_iff T _).mpr
  rw [toFoundation_kleeneEqAt]
  have hs' : Nonempty (FFL.FirstOrder.Theory.Proof
      (TheoryCorrespondence.toFoundation T)
      (FailureOfComposition.ProgramIndices.kleeneEqAt F G n)) := by
    rcases hs with ⟨b⟩
    change FFL.FirstOrder.Theory.Proof
      (TheoryCorrespondence.toFoundation T) _ at b
    refine ⟨?_⟩
    simpa [F, G, graph_input_subst,
      FailureOfComposition.ProgramIndices.kleeneEqAt, body,
      FailureOfComposition.ConcreteIndices.uniformKleeneSentence] using b
  simpa [F, G] using hs'

private theorem foundationWeakerThan (T : Theory)
    (hPA : DeductivelyExtends Peano T) :
    FFL.Entailment.WeakerThan FFL.FirstOrder.Arithmetic.Peano
      (TheoryCorrespondence.toFoundation T) :=
  (deductivelyExtendsPeano_toFoundation_iff T).mp hPA

/-- Under the stated PA-extension hypothesis, the independent pointwise
relation is an equivalence relation. -/
theorem pointwiseIndex_equivalence (T : Theory)
    (hPA : DeductivelyExtends Peano T) : Equivalence (PointwiseIndex T) := by
  let _ : FFL.Entailment.WeakerThan FFL.FirstOrder.Arithmetic.Peano
      (TheoryCorrespondence.toFoundation T) :=
    foundationWeakerThan T hPA
  constructor
  · intro e
    apply (pointwiseIndex_toFoundation_iff T e e).mpr
    exact (FailureOfComposition.ConcreteIndices.indexSetoid
      (TheoryCorrespondence.toFoundation T)).refl e
  · intro e d h
    apply (pointwiseIndex_toFoundation_iff T d e).mpr
    exact (FailureOfComposition.ConcreteIndices.indexSetoid
      (TheoryCorrespondence.toFoundation T)).symm
        ((pointwiseIndex_toFoundation_iff T e d).mp h)
  · intro e d k hed hdk
    apply (pointwiseIndex_toFoundation_iff T e k).mpr
    exact (FailureOfComposition.ConcreteIndices.indexSetoid
      (TheoryCorrespondence.toFoundation T)).trans
        ((pointwiseIndex_toFoundation_iff T e d).mp hed)
        ((pointwiseIndex_toFoundation_iff T d k).mp hdk)

/-- Identity on natural-number representatives induces the correspondence
between the independent core quotient and the maintained setoid quotient. -/
def indexQuotientEquiv (T : Theory) (hPA : DeductivelyExtends Peano T) :
    IndexQuotient T ≃
      Quotient (@FailureOfComposition.ConcreteIndices.indexSetoid
        (TheoryCorrespondence.toFoundation T) (foundationWeakerThan T hPA)) where
  toFun := Quot.lift
    (fun e ↦ Quotient.mk
      (@FailureOfComposition.ConcreteIndices.indexSetoid
        (TheoryCorrespondence.toFoundation T) (foundationWeakerThan T hPA)) e)
    (by
      intro e d h
      exact Quotient.sound ((pointwiseIndex_toFoundation_iff T e d).mp h))
  invFun := Quotient.lift
    (fun e ↦ indexQuotientMk T e)
    (by
      intro e d h
      exact Quot.sound ((pointwiseIndex_toFoundation_iff T e d).mpr h))
  left_inv := by
    intro q
    induction q using Quot.ind with
    | _ e => rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ e => rfl

/-- The quotient equivalence is induced by identity on representatives. -/
@[simp] theorem indexQuotientEquiv_mk (T : Theory)
    (hPA : DeductivelyExtends Peano T) (e : ℕ) :
    indexQuotientEquiv T hPA (indexQuotientMk T e) =
      Quotient.mk
        (@FailureOfComposition.ConcreteIndices.indexSetoid
          (TheoryCorrespondence.toFoundation T) (foundationWeakerThan T hPA)) e := by
  rfl

/-- Equality in the core quotient is exactly pointwise provable equality once
the latter is known to be an equivalence relation. -/
theorem indexQuotientMk_eq_iff (T : Theory)
    (hPA : DeductivelyExtends Peano T) (e d : ℕ) :
    indexQuotientMk T e = indexQuotientMk T d ↔
      PointwiseIndex T e d := by
  constructor
  · intro h
    apply (pointwiseIndex_toFoundation_iff T e d).mpr
    exact Quotient.exact (s :=
      @FailureOfComposition.ConcreteIndices.indexSetoid
        (TheoryCorrespondence.toFoundation T) (foundationWeakerThan T hPA))
      (by simpa using congrArg (indexQuotientEquiv T hPA) h)
  · exact Quot.sound

/-- The independent and maintained no-composition assertions are equivalent,
including their equations on concrete representatives. -/
theorem noIndexQuotientComposition_iff_maintained (T : Theory)
    (hPA : DeductivelyExtends Peano T) :
    (¬∃ C : IndexQuotient T → IndexQuotient T → IndexQuotient T,
        ∀ e d : ℕ,
          C (indexQuotientMk T e) (indexQuotientMk T d) =
            indexQuotientMk T (compIndex e d)) ↔
      @FailureOfComposition.ConcreteIndices.NoIndexQuotientComposition
        (TheoryCorrespondence.toFoundation T) (foundationWeakerThan T hPA) := by
  let E := indexQuotientEquiv T hPA
  constructor
  · intro h ⟨C, hC⟩
    apply h
    refine ⟨fun a b ↦ E.symm (C (E a) (E b)), ?_⟩
    intro e d
    apply E.injective
    simp [E, hC, compIndex_toFoundation]
  · intro h ⟨C, hC⟩
    apply h
    refine ⟨fun a b ↦ E (C (E.symm a) (E.symm b)), ?_⟩
    intro e d
    have hinv (k : ℕ) :
        E.symm
            (Quotient.mk
              (@FailureOfComposition.ConcreteIndices.indexSetoid
                (TheoryCorrespondence.toFoundation T)
                (foundationWeakerThan T hPA)) k) =
          indexQuotientMk T k := by
      apply E.injective
      simp [E]
    simp [hinv, hC, E, compIndex_toFoundation]

/-- The quotient contradiction extracted from any witnesses having exactly the
four properties of the first selected result. -/
theorem no_quotient_composition_of_four_properties
    (T : Theory) (hPA : DeductivelyExtends Peano T)
    (h : ∃ f g : ℕ, PointwiseIndex T f identityIndex ∧
      UniformIndex T (compIndex f g) emptyIndex ∧
      UniformIndex T (compIndex identityIndex g) g ∧
      ¬PointwiseIndex T g emptyIndex) :
    ¬∃ C : IndexQuotient T → IndexQuotient T → IndexQuotient T,
      ∀ e d : ℕ,
        C (indexQuotientMk T e) (indexQuotientMk T d) =
          indexQuotientMk T (compIndex e d) := by
  obtain ⟨f, g, hfi, hfg, hig, hgz⟩ := h
  have hfg' : PointwiseIndex T (compIndex f g) emptyIndex :=
    uniformIndex_imp_pointwiseIndex T _ _ hfg
  have hig' : PointwiseIndex T (compIndex identityIndex g) g :=
    uniformIndex_imp_pointwiseIndex T _ _ hig
  rintro ⟨C, hC⟩
  apply hgz
  apply (indexQuotientMk_eq_iff T hPA g emptyIndex).mp
  calc
    indexQuotientMk T g =
        indexQuotientMk T (compIndex identityIndex g) :=
      (Quot.sound hig').symm
    _ = C (indexQuotientMk T identityIndex) (indexQuotientMk T g) :=
      (hC identityIndex g).symm
    _ = C (indexQuotientMk T f) (indexQuotientMk T g) := by
      have hfieq : indexQuotientMk T f =
          indexQuotientMk T identityIndex := Quot.sound hfi
      rw [hfieq]
    _ = indexQuotientMk T (compIndex f g) := hC f g
    _ = indexQuotientMk T emptyIndex := Quot.sound hfg'

/-- Productive failure of representative-respecting composition on the actual
pointwise-provability quotient, derived from the checked four witness properties. -/
theorem no_quotient_composition_productive
    (T : Theory) (hPA : DeductivelyExtends Peano T) (hCons : Consistent T)
    (hT : REPred (AxiomCodes T)) :
    ¬∃ C : IndexQuotient T → IndexQuotient T → IndexQuotient T,
      ∀ e d : ℕ,
        C (indexQuotientMk T e) (indexQuotientMk T d) =
          indexQuotientMk T (compIndex e d) := by
  exact no_quotient_composition_of_four_properties T hPA
    (obstruction_four_properties T hPA hCons hT)

end FailureOfComposition.Palomar.Arithmetic.Evaluator
