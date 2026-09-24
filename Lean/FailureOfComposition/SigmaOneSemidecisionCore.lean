/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ProgramGraph
import FailureOfComposition.ArithmeticCodeCompiler
import FailureOfComposition.ConcreteEmptyGraph

/-!
Concrete zero-valued semidecision programs. The defining equivalences hold
for every input vector in every model of PA.
-/

set_option autoImplicit false



open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace FailureOfComposition.SigmaOneRealization
open ProgramGraph ArithmeticCodeCompiler

/-- A program accepts exactly the satisfying input vectors and returns zero. -/
def Semidecides {n : ℕ} (φ : ArithmeticSemisentence n) (c : Nat.Partrec.Code) : Prop :=
  ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
    (v : Fin n → M) (z : M),
    Computes c (encodeVector v) z ↔ z = 0 ∧ Semiformula.Evalb v φ

/-- The zero program accepts every vector. -/
theorem verum_semidecides (n : ℕ) :
    Semidecides (⊤ : ArithmeticSemisentence n) .zero := by
  intro M _ _ _ v z
  simpa using computes_zero (encodeVector v) z

/-- Searching for a zero of successor accepts no vector. -/
theorem falsum_semidecides (n : ℕ) :
    Semidecides (⊥ : ArithmeticSemisentence n) (.rfind' .succ) := by
  intro M _ _ _ v z
  change Computes (.rfind' .succ) (encodeVector v) z ↔ z = 0 ∧ False
  rw [and_false]
  unfold Computes
  rw [ConcreteEvaluator.eventualGraph_eval]
  simpa only [ConcreteEmptyGraph.concreteEmptyIndex, numeral_eq_natCast_app,
    Matrix.cons_val_zero, Matrix.cons_val_one] using
    ConcreteEmptyGraph.concreteEmpty_unbounded_computation_iff (encodeVector v) z

/-- Evaluate both children and discard their outputs. -/
def andProgram (c d : Nat.Partrec.Code) : Nat.Partrec.Code :=
  .comp .zero (.pair c d)

/-- Pairing the two computations gives conjunction semidecision. -/
theorem and_semidecides {n : ℕ} {φ ψ : ArithmeticSemisentence n}
    {c d : Nat.Partrec.Code} (hφ : Semidecides φ c) (hψ : Semidecides ψ d) :
    Semidecides (φ ⋏ ψ) (andProgram c d) := by
  intro M _ _ _ v z
  change Computes (andProgram c d) (encodeVector v) z ↔
    z = 0 ∧ (Semiformula.Evalb v φ ∧ Semiformula.Evalb v ψ)
  rw [andProgram, computes_comp]
  simp only [computes_pair, computes_zero, hφ M v, hψ M v]
  constructor
  · rintro ⟨_, ⟨_, _, ⟨_, hp⟩, ⟨_, hq⟩, _⟩, hz⟩
    exact ⟨hz, hp, hq⟩
  · rintro ⟨hz, hp, hq⟩
    exact ⟨pair (0 : M) 0, ⟨0, 0, ⟨rfl, hp⟩, ⟨rfl, hq⟩, rfl⟩, hz⟩

end FailureOfComposition.SigmaOneRealization
