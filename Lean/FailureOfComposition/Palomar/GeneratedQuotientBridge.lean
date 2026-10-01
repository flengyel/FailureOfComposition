/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.Palomar.GeneratedQuotientInterface
public import FailureOfComposition.Palomar.GeneratedCongruenceBridge
public import FailureOfComposition.PartialRecursiveQuotient

/-!
# Generated-quotient partial-recursive correspondence

Evaluation descends through the independent generated relation under Σ₁
soundness.  The resulting bijection preserves concrete program composition.
Identity-on-representatives quotient and target equivalences then compare the
construction with the maintained quotient, multiplication, and unit.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.Palomar.Arithmetic.Evaluator

@[simp] theorem generatedQuotient_mul_mk (T : Theory) (e d : ℕ) :
    generatedQuotientMk T e * generatedQuotientMk T d =
      generatedQuotientMk T (compIndex e d) := rfl

@[simp] theorem generatedQuotient_one_mk (T : Theory) :
    (1 : GeneratedQuotient T) = generatedQuotientMk T identityIndex := rfl

namespace UnaryPartrec

@[simp] theorem mul_apply (f g : UnaryPartrec) (x : ℕ) :
    (f * g).val x = (g.val x).bind f.val := rfl

@[simp] theorem one_apply (x : ℕ) :
    (1 : UnaryPartrec).val x = Part.some x := rfl

@[simp] theorem ofIndex_val (e : ℕ) :
    (ofIndex e).val = actualEval e := rfl

theorem ofIndex_surjective : Function.Surjective ofIndex := by
  rintro ⟨f, hf⟩
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  refine ⟨Encodable.encode c, Subtype.ext ?_⟩
  change Nat.Partrec.Code.eval
    (Denumerable.ofNat Nat.Partrec.Code (Encodable.encode c)) = f
  simpa only [Denumerable.ofNat_encode] using hc

end UnaryPartrec

/-- Evaluation is well-defined on the generated quotient under Σ₁ soundness. -/
noncomputable def generatedQuotientDenotation
    (T : Theory) (hPA : DeductivelyExtends Peano T)
    (hT : Arithmetic.SigmaOneSound T) : GeneratedQuotient T → UnaryPartrec :=
  Quot.lift UnaryPartrec.ofIndex (by
    intro e d h
    apply Subtype.ext
    exact ((generated_congruence_classification T hPA).1 hT e d).mp h)

@[simp] theorem generatedQuotientDenotation_mk
    (T : Theory) (hPA : DeductivelyExtends Peano T)
    (hT : Arithmetic.SigmaOneSound T) (e : ℕ) :
    generatedQuotientDenotation T hPA hT (generatedQuotientMk T e) =
      UnaryPartrec.ofIndex e := rfl

theorem generatedQuotientDenotation_bijective
    (T : Theory) (hPA : DeductivelyExtends Peano T)
    (hT : Arithmetic.SigmaOneSound T) :
    Function.Bijective (generatedQuotientDenotation T hPA hT) := by
  constructor
  · intro a b hab
    induction a using Quot.ind with
    | _ e =>
      induction b using Quot.ind with
      | _ d =>
        apply Quot.sound
        apply ((generated_congruence_classification T hPA).1 hT e d).mpr
        exact congrArg Subtype.val hab
  · intro f
    obtain ⟨e, he⟩ := UnaryPartrec.ofIndex_surjective f
    exact ⟨generatedQuotientMk T e, he⟩

/-- The generated quotient is multiplicatively equivalent to the actual unary
partial recursive functions, with evaluation on every representative. -/
noncomputable def generatedQuotientPartialRecursiveEquiv
    (T : Theory) (hPA : DeductivelyExtends Peano T)
    (hT : Arithmetic.SigmaOneSound T) : GeneratedQuotient T ≃* UnaryPartrec :=
  { Equiv.ofBijective (generatedQuotientDenotation T hPA hT)
      (generatedQuotientDenotation_bijective T hPA hT) with
    map_mul' := by
      intro a b
      induction a using Quot.ind with
      | _ e =>
        induction b using Quot.ind with
        | _ d =>
          apply Subtype.ext
          funext x
          change actualEval (compIndex e d) x =
            (actualEval d x).bind (actualEval e)
          rw [compIndex_toFoundation]
          exact FailureOfComposition.Kleene.eval_compIndex e d x }

@[simp] theorem generatedQuotientPartialRecursiveEquiv_mk
    (T : Theory) (hPA : DeductivelyExtends Peano T)
    (hT : Arithmetic.SigmaOneSound T) (e : ℕ) :
    generatedQuotientPartialRecursiveEquiv T hPA hT
        (generatedQuotientMk T e) = UnaryPartrec.ofIndex e := rfl

/-- The equivalence also sends the fixed identity-index class to the total
partial identity, so its multiplication has the intended unit. -/
@[simp] theorem generatedQuotientPartialRecursiveEquiv_one
    (T : Theory) (hPA : DeductivelyExtends Peano T)
    (hT : Arithmetic.SigmaOneSound T) :
    generatedQuotientPartialRecursiveEquiv T hPA hT
        (1 : GeneratedQuotient T) = (1 : UnaryPartrec) := by
  apply Subtype.ext
  funext x
  change actualEval identityIndex x = Part.some x
  rw [actualEval_toFoundation, identityIndex_toFoundation]
  exact FailureOfComposition.Kleene.identityIndex_spec x

/-! ## Correspondence with the maintained quotient and target -/

/-- Identity on program representatives identifies the independent generated
quotient with the maintained generated-index quotient. -/
noncomputable def generatedQuotientToFoundation (T : Theory) :
    GeneratedQuotient T ≃
      FailureOfComposition.ConcreteIndices.GeneratedQuotient
        (TheoryCorrespondence.toFoundation T) where
  toFun := Quot.lift
    (FailureOfComposition.ConcreteIndices.generatedQuotientMk
      (TheoryCorrespondence.toFoundation T)) (by
        intro e d h
        exact Quotient.sound ((generatedRel_toFoundation_iff T e d).mp h))
  invFun := Quotient.lift
    (generatedQuotientMk T) (by
      intro e d h
      exact Quot.sound ((generatedRel_toFoundation_iff T e d).mpr h))
  left_inv := by
    intro q
    induction q using Quot.ind with
    | _ e => rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ e => rfl

@[simp] theorem generatedQuotientToFoundation_mk (T : Theory) (e : ℕ) :
    generatedQuotientToFoundation T (generatedQuotientMk T e) =
      FailureOfComposition.ConcreteIndices.generatedQuotientMk
        (TheoryCorrespondence.toFoundation T) e := rfl

/-- The representative-preserving quotient equivalence also preserves the
fixed concrete composition operation. -/
theorem generatedQuotientToFoundation_mul (T : Theory)
    (a b : GeneratedQuotient T) :
    generatedQuotientToFoundation T (a * b) =
      generatedQuotientToFoundation T a * generatedQuotientToFoundation T b := by
  induction a using Quot.ind with
  | _ e =>
    induction b using Quot.ind with
    | _ d =>
      change FailureOfComposition.ConcreteIndices.generatedQuotientMk
          (TheoryCorrespondence.toFoundation T) (compIndex e d) =
        FailureOfComposition.ConcreteIndices.generatedQuotientMk
          (TheoryCorrespondence.toFoundation T)
          (CategoricalRiceShapiro.PartialRecursive.canonicalPartrecCompIndex e d)
      rw [compIndex_toFoundation]

/-- Quotient correspondence as a multiplicative equivalence. -/
noncomputable def generatedQuotientMulEquivToFoundation (T : Theory) :
    GeneratedQuotient T ≃*
      FailureOfComposition.ConcreteIndices.GeneratedQuotient
        (TheoryCorrespondence.toFoundation T) :=
  { generatedQuotientToFoundation T with
    map_mul' := generatedQuotientToFoundation_mul T }

/-- The independent and maintained actual-function targets are the same
partial maps, and their multiplication has the same orientation. -/
def unaryPartrecMulEquivToFoundation :
    UnaryPartrec ≃* FailureOfComposition.UnaryPartrec where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv _f := rfl
  right_inv _f := rfl
  map_mul' _ _ := rfl

@[simp] theorem unaryPartrecMulEquivToFoundation_ofIndex (e : ℕ) :
    unaryPartrecMulEquivToFoundation (UnaryPartrec.ofIndex e) =
      FailureOfComposition.UnaryPartrec.ofIndex e := rfl

@[simp] theorem unaryPartrecMulEquivToFoundation_one :
    unaryPartrecMulEquivToFoundation (1 : UnaryPartrec) =
      (1 : FailureOfComposition.UnaryPartrec) := rfl

theorem generatedFoundationWeakerThan (T : Theory)
    (hPA : DeductivelyExtends Peano T) :
    FFL.Entailment.WeakerThan FFL.FirstOrder.Arithmetic.Peano
      (TheoryCorrespondence.toFoundation T) :=
  (deductivelyExtendsPeano_toFoundation_iff T).mp hPA

/-- Although the maintained quotient unit uses a chosen PA realization of the
identity graph, its class equals the fixed independent identity-index class. -/
theorem generatedQuotientToFoundation_one (T : Theory)
    (hPA : DeductivelyExtends Peano T) :
    generatedQuotientToFoundation T (1 : GeneratedQuotient T) =
      (1 : FailureOfComposition.ConcreteIndices.GeneratedQuotient
        (TheoryCorrespondence.toFoundation T)) := by
  let _ : FFL.Entailment.WeakerThan FFL.FirstOrder.Arithmetic.Peano
      (TheoryCorrespondence.toFoundation T) := generatedFoundationWeakerThan T hPA
  let A := FailureOfComposition.ConcreteEvaluator.arithmetization
  let E := FailureOfComposition.ProgramIndices.generatedQuotientEquiv A
    (TheoryCorrespondence.toFoundation T)
  apply E.injective
  rw [FailureOfComposition.ProgramIndices.generatedQuotientEquiv_one]
  change FailureOfComposition.GeneratedCongruence.quotientMk
      (TheoryCorrespondence.toFoundation T)
      ⟨A.graph FailureOfComposition.Kleene.identityIndex,
        A.functional FailureOfComposition.Kleene.identityIndex⟩ = 1
  rw [FailureOfComposition.GeneratedCongruence.one_mk]
  apply Quotient.sound
  exact FailureOfComposition.GeneratedCongruence.rel_of_uniform
    (TheoryCorrespondence.toFoundation T)
    FailureOfComposition.ConcreteEvaluator.eventualGraph_identity

/-- The direct independent equivalence commutes with the maintained one on all
quotient representatives; hence it transports the same mathematical contract. -/
theorem generatedQuotientPartialRecursiveEquiv_toFoundation
    (T : Theory) (hPA : DeductivelyExtends Peano T)
    (hT : Arithmetic.SigmaOneSound T) (q : GeneratedQuotient T) :
    unaryPartrecMulEquivToFoundation
        (generatedQuotientPartialRecursiveEquiv T hPA hT q) =
      @FailureOfComposition.ConcreteIndices.generatedQuotientPartialRecursiveEquiv
        (TheoryCorrespondence.toFoundation T)
        (generatedFoundationWeakerThan T hPA)
        ((Arithmetic.sigmaOneSound_toFoundation_iff T).mp hT)
        (generatedQuotientToFoundation T q) := by
  let _ : FFL.Entailment.WeakerThan FFL.FirstOrder.Arithmetic.Peano
      (TheoryCorrespondence.toFoundation T) := generatedFoundationWeakerThan T hPA
  induction q using Quot.ind with
  | _ e => rfl

/-- Ninth eligible result: the generated quotient under Σ₁ soundness is
the multiplicative type of actual unary partial recursive functions. -/
theorem generated_quotient_partial_recursive
    (T : Theory) (hPA : DeductivelyExtends Peano T)
    (hT : Arithmetic.SigmaOneSound T) :
    ∃ E : GeneratedQuotient T ≃* UnaryPartrec,
      ∀ e : ℕ, E (generatedQuotientMk T e) = UnaryPartrec.ofIndex e := by
  exact ⟨generatedQuotientPartialRecursiveEquiv T hPA hT,
    generatedQuotientPartialRecursiveEquiv_mk T hPA hT⟩

end FailureOfComposition.Palomar.Arithmetic.Evaluator
