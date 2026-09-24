/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ConcreteAdequacy

/-!
An explicit internal Kleene normal form for the accepted Mathlib numbering.
The computation witness pairs a history-evaluator stage with its output.
PA proves equivalence to the existential-stage graph, and over natural numbers
the predicate and output graph equal the existing primitive-recursive T₁ and U.
No translation to a different historical numerical coding is asserted.
-/

set_option autoImplicit false

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder.Arithmetic
open Encodable Denumerable
open Nat.ArithPart₁
open CategoricalRiceShapiro.Evaluator CategoricalRiceShapiro.ArithmeticCode

namespace FailureOfComposition.ConcreteNormalForm
open ProofSearch ConcreteEvaluator

private def witnessPairCode : Code 2 := codePair (Code.proj 0) (Code.proj 1)
private def outputCode : Code 1 := codeUnpair₂ (Code.proj 0)

/-- The Sigma-one arithmetic formula for an encoded successful computation. -/
def computationPredicate : 𝚺₁.Semisentence 3 := .mkSigma
  “e x w. ∃ s y, !(code witnessPairCode) w s y ∧ !evalnCertificateFormula.val s e x y”

/-- The arithmetic graph of the primitive-recursive output decoder. -/
def outputGraph : Graph := .mkSigma “w y. !(code outputCode) y w”

/-- Normal form at a fixed standard program index. -/
def normalFormGraph (q : ℕ) : Graph := .mkSigma
  “x y. ∃ w, !computationPredicate.val !!(q) x w ∧ !outputGraph.val w y”

variable {M : Type*} [ORingStructure M]

private theorem witnessPairCode_eval [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (w s y : M) :
    Semiformula.Evalb ![w,s,y] (code witnessPairCode) ↔ w = pair s y := by
  have h : Semiformula.Evalb ![pair s y,s,y] (code witnessPairCode) :=
    eval_codePair (Code.proj 0) (Code.proj 1) s y ![s,y]
      ((eval_proj_iff _ _ _).mpr rfl) ((eval_proj_iff _ _ _).mpr rfl)
  constructor
  · intro hw
    exact eval_unique hw h
  · rintro rfl
    exact h

@[simp] theorem computationPredicate_eval [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (e x w : M) :
    computationPredicate.val.Evalb ![e,x,w] ↔
      ∃ s y : M, w = pair s y ∧ Semiformula.Evalb ![s,e,x,y]
        (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  simp [computationPredicate, witnessPairCode_eval]

@[simp] theorem outputGraph_eval [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (w y : M) :
    outputGraph.val.Evalb ![w,y] ↔ y = pi₂ w := by
  have h : Semiformula.Evalb ![pi₂ w,w] (code outputCode) :=
    eval_codeUnpair₂ (Code.proj 0) w ![w] ((eval_proj_iff _ _ _).mpr rfl)
  have he : outputGraph.val.Evalb ![w,y] ↔ Semiformula.Evalb ![y,w] (code outputCode) := by
    simp [outputGraph]
  rw [he]
  constructor
  · intro hy
    exact eval_unique hy h
  · rintro rfl
    exact h

/-- Every internal computation witness carries exactly its decoded output. -/
theorem normalFormGraph_eval_iff [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
    (q : ℕ) (x y : M) :
    (normalFormGraph q).val.Evalb ![x,y] ↔ (eventualGraph q).val.Evalb ![x,y] := by
  have hn : (normalFormGraph q).val.Evalb ![x,y] ↔
      ∃ w : M, computationPredicate.val.Evalb ![(q : M),x,w] ∧ outputGraph.val.Evalb ![w,y] := by
    simp [normalFormGraph, numeral_eq_natCast]
  rw [hn, eventualGraph_eval]
  simp only [computationPredicate_eval, outputGraph_eval, numeral_eq_natCast_app,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨w, ⟨s,z,rfl,hc⟩, hy⟩
    rw [pi₂_pair] at hy
    subst y
    exact ⟨s,hc⟩
  · rintro ⟨s,hc⟩
    exact ⟨pair s y, ⟨s,y,rfl,hc⟩, (pi₂_pair s y).symm⟩

/-- PA proves the normal-form equation for the chosen arithmetization. -/
theorem normalFormGraph_realizes (q : ℕ) :
    Uniform 𝗣𝗔 (eventualGraph q) (normalFormGraph q) := by
  apply complete.{0} 𝗣𝗔
  intro V _ _
  haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  exact (normalFormGraph_eval_iff q x y).symm

/-- The arithmetic computation formula represents exactly the concrete
primitive-recursive Kleene predicate already defined in `KleeneNormalForm`. -/
theorem computationPredicate_nat (e x w : ℕ) :
    computationPredicate.val.Evalb ![e,x,w] ↔ Kleene.T₁ e x w := by
  rw [computationPredicate_eval]
  simp only [nat_pair_eq]
  have hcomp (s y : ℕ) : Semiformula.Evalb ![s,e,x,y]
        (evalnCertificateFormula : ArithmeticSemisentence 4) ↔
      Nat.Partrec.Code.evaln s (ofNat Nat.Partrec.Code e) x = some y := by
    have h := stageComputation_iff_evaln s (ofNat Nat.Partrec.Code e) x y
    simpa only [stageComputation, Denumerable.encode_ofNat, Option.mem_def] using h
  simp only [hcomp]
  constructor
  · rintro ⟨s,y,rfl,h⟩
    simpa only [Kleene.T₁, Nat.unpair_pair] using h
  · intro h
    exact ⟨w.unpair.1,w.unpair.2,(Nat.pair_unpair w).symm,h⟩

/-- The arithmetic output graph represents exactly the concrete decoder U. -/
theorem outputGraph_nat (w y : ℕ) : outputGraph.val.Evalb ![w,y] ↔ Kleene.U w = y := by
  rw [outputGraph_eval]
  have h : (pair w.unpair.1 w.unpair.2 : ℕ) = w := by
    rw [nat_pair_eq, Nat.pair_unpair]
  have hp : pi₂ w = w.unpair.2 := by
    conv_lhs => rw [← h]
    exact pi₂_pair _ _
  rw [hp, Kleene.U]
  exact eq_comm

/-- The output graph is PA-provably functional. -/
theorem outputGraph_functional : Functional outputGraph := by
  apply complete.{0} 𝗣𝗔
  intro V _ _
  haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  rw [models_iff, functionalSentence_eval]
  intro w y z hy hz
  exact ((outputGraph_eval w y).mp hy).trans ((outputGraph_eval w z).mp hz).symm


/-- The represented computation predicate itself is primitive recursive on
standard natural numbers. -/
theorem computationPredicate_primrec : PrimrecPred
    (fun p : (ℕ × ℕ) × ℕ => computationPredicate.val.Evalb ![p.1.1,p.1.2,p.2]) :=
  Kleene.T₁_primrec.of_eq fun p => (computationPredicate_nat p.1.1 p.1.2 p.2).symm

/-- PA also proves functionality of the normal-form program graph. -/
theorem normalFormGraph_functional (q : ℕ) : Functional (normalFormGraph q) := by
  apply complete.{0} 𝗣𝗔
  intro V _ _
  haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  exact eventualGraph_output_unique q x y z
    ((normalFormGraph_eval_iff q x y).mp hy) ((normalFormGraph_eval_iff q x z).mp hz)

end FailureOfComposition.ConcreteNormalForm
