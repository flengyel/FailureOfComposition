/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.SigmaOneSemidecisionCore
import FailureOfComposition.SigmaOneSearch

/-!
Extracting an output from a semidecision program for a functional arithmetic
graph. The search ranges over candidate outputs together with computation
stages, so divergent rejected candidates do not block later outputs.
-/

set_option autoImplicit false



open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.SigmaOneRealization
open ProgramGraph ArithmeticCodeCompiler

/-- Convert a candidate/input pair into the graph's input/output vector. -/
def reorderProgram (c : PCode) : PCode :=
  .comp c (.pair .right (.pair .left .zero))

/-- Search the graph semidecision program and return its successful output. -/
def graphProgram (c : PCode) : PCode :=
  SigmaOneSearch.candidateSearch (reorderProgram c)

variable {M : Type*} [ORingStructure M]
  [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

theorem computes_reorder (c : PCode) (x y z : M) :
    Computes (reorderProgram c) (pair y x) z ↔
      Computes c (encodeVector ![x, y]) z := by
  rw [reorderProgram, computes_comp]
  simp only [computes_pair, computes_left, computes_right, computes_zero,
    pi₁_pair, pi₂_pair]
  constructor
  · rintro ⟨w, ⟨a, b, rfl, ⟨d, e, rfl, rfl, rfl⟩, rfl⟩, h⟩
    simpa only [encodeVector, Matrix.cons_val_zero, Matrix.cons_val_succ] using h
  · intro h
    refine ⟨pair x (pair y 0), ⟨x, pair y 0, rfl, ⟨y, 0, rfl, rfl, rfl⟩, rfl⟩, ?_⟩
    simpa only [encodeVector, Matrix.cons_val_zero, Matrix.cons_val_succ] using h

/-- A semidecision program for a PA-functional graph yields an actual program
whose graph PA proves uniformly equivalent to the original graph. -/
theorem realize_of_semidecides (F : ProofSearch.Graph) (hF : ProofSearch.Functional F)
    (c : PCode) (hc : Semidecides F.val c) :
    ProofSearch.Uniform 𝗣𝗔 (ConcreteEvaluator.eventualGraph (encode (graphProgram c))) F := by
  apply complete.{0} 𝗣𝗔
  intro V _ _
  haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  have hf : V↓[ℒₒᵣ] ⊧ ProofSearch.functionalSentence F :=
    consequence_iff.mp (Theory.Proof.sound hF) V inferInstance
  rw [models_iff, ProofSearch.functionalSentence_eval] at hf
  rw [models_iff, ProofSearch.uniformSentence_eval]
  intro x y
  change Computes (SigmaOneSearch.candidateSearch (reorderProgram c)) x y ↔
    Semiformula.Evalb ![x, y] F.val
  have hrel (a : V) : Computes (reorderProgram c) (pair a x) 0 ↔
      Semiformula.Evalb ![x, a] F.val := by
    rw [computes_reorder, hc V ![x, a] 0]
    simp
  have hu : ∀ a b : V, Computes (reorderProgram c) (pair a x) 0 →
      Computes (reorderProgram c) (pair b x) 0 → a = b := by
    intro a b ha hb
    exact hf x a b ((hrel a).mp ha) ((hrel b).mp hb)
  exact (SigmaOneSearch.candidateSearch_of_functional (reorderProgram c) x y hu).trans (hrel y)

end FailureOfComposition.SigmaOneRealization
