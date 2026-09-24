/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ConcreteWeakTotality

/-!
The program-index reading of Montagna's Theorem 2.3 fails: every standard-input
convergence sentence of the guard is already provable in PA, hence adjoining it
is Pi-one conservative, although the guard is not weakly total.

Conservativity below refers to provability in the actual theory obtained by
inserting the convergence sentence into PA.
-/

set_option autoImplicit false

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

namespace FailureOfComposition.ConcreteIndices

open ProofSearch ConcreteEvaluator HistoryWitnesses ProgramIndices

/-- Adjoining `σ` produces no new Pi-one theorems over `T`. -/
def PiOneConservativeSentence (T : ArithmeticTheory) (σ : ArithmeticSentence) : Prop :=
  ∀ τ : ArithmeticSentence, Hierarchy 𝚷 1 τ → insert σ T ⊢ τ → T ⊢ τ

/-- An already provable additional axiom leaves every consequence unchanged. -/
theorem insert_provable_iff_of_provable (T : ArithmeticTheory)
    {σ τ : ArithmeticSentence} (hσ : T ⊢ σ) :
    insert σ T ⊢ τ ↔ T ⊢ τ := by
  constructor
  · intro hτ
    exact mdp! (deduction! hτ) hσ
  · intro hτ
    exact wk! (Set.subset_insert σ T) hτ

/-- Full deductive equivalence in particular gives Pi-one conservativity. -/
theorem piOneConservativeSentence_of_provable (T : ArithmeticTheory)
    {σ : ArithmeticSentence} (hσ : T ⊢ σ) : PiOneConservativeSentence T σ := by
  intro τ _ hτ
  exact (insert_provable_iff_of_provable T hσ).mp hτ

/-- Convergence of the actual evaluator on the standard input `n`. -/
def convergenceAt (e n : ℕ) : ArithmeticSentence :=
  “∃ y, !(eventualGraph e).val !!(n) y”

@[simp] theorem convergenceAt_eval {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (e n : ℕ) :
    (convergenceAt e n).Evalb (M := M) ![] ↔
      ∃ y : M, (eventualGraph e).val.Evalb ![(n : M), y] := by
  simp [convergenceAt, numeral_eq_natCast]

/-- Montagna's condition (2), with its external quantifier over standard inputs. -/
def PointwiseConvergenceConservative (e : ℕ) : Prop :=
  ∀ n : ℕ, PiOneConservativeSentence 𝗣𝗔 (convergenceAt e n)

/-- Pointwise PA equality with identity proves each convergence sentence in PA. -/
theorem convergenceAt_provable_of_pointwise_identity (e : ℕ)
    (he : PointwiseIndex 𝗣𝗔 e Kleene.identityIndex)
    (n : ℕ) : 𝗣𝗔 ⊢ convergenceAt e n := by
  have hgraph : Pointwise 𝗣𝗔 (eventualGraph e) identity :=
    (pointwise_equivalence 𝗣𝗔).trans ((pointwiseIndex_iff 𝗣𝗔 _ _).mp he)
      (uniform_to_pointwise 𝗣𝗔 eventualGraph_identity)
  have himp : 𝗣𝗔 ⊢ eqAt (eventualGraph e) identity n 🡒 convergenceAt e n := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
    simp only [models_iff, LogicalConnective.HomClass.map_imply,
      eqAt_eval, convergenceAt_eval]
    intro h
    exact ⟨(n : M), (h (n : M)).mpr ((identity_eval _).mpr rfl)⟩
  exact mdp! himp (hgraph n)

/-- Each standard-input convergence sentence of the guard is PA-provable. -/
theorem guard_convergenceAt_provable (d : ℕ)
    (hdiv : ¬diagonalHistoryFormula.Evalb ![d]) (n : ℕ) :
    𝗣𝗔 ⊢ convergenceAt (guardIndex d) n :=
  convergenceAt_provable_of_pointwise_identity (guardIndex d)
    (guardIndex_pointwise_identity 𝗣𝗔 d hdiv) n

/-- The guard satisfies condition (2), because each added axiom is redundant. -/
theorem guard_pointwiseConvergenceConservative (d : ℕ)
    (hdiv : ¬diagonalHistoryFormula.Evalb ![d]) :
    PointwiseConvergenceConservative (guardIndex d) := by
  intro n
  exact piOneConservativeSentence_of_provable 𝗣𝗔 (guard_convergenceAt_provable d hdiv n)

/-- The same concrete guard satisfies condition (2) and fails the index version
of weak totality over `T`. -/
theorem guard_conservative_not_weaklyTotal (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (d : ℕ) (hdiv : ¬diagonalHistoryFormula.Evalb ![d])
    (hnot : T ⊬ ∼diagonalHistoryFormula/[d]) :
    PointwiseConvergenceConservative (guardIndex d) ∧
      ¬WeaklyTotalIndex T (guardIndex d) :=
  ⟨guard_pointwiseConvergenceConservative d hdiv, not_weaklyTotalIndex_guard T d hnot⟩

/-- A counterexample over PA to (2) implies (1) in the program-index reading of
Montagna's Theorem 2.3. The existential witness comes from productiveness. -/
theorem montagna_condition_two_not_one :
    ∃ e : ℕ, PointwiseConvergenceConservative e ∧ ¬WeaklyTotalIndex 𝗣𝗔 e := by
  obtain ⟨d, hdiv, hnot⟩ := exists_true_unprovable_history_divergence 𝗣𝗔
  exact ⟨guardIndex d, guard_conservative_not_weaklyTotal 𝗣𝗔 d hdiv hnot⟩

/-- Thus the implication fails without changing the meanings of either
conservativity or the index predicate for weak totality. -/
theorem not_montagna_condition_two_implies_one :
    ¬∀ e : ℕ, PointwiseConvergenceConservative e → WeaklyTotalIndex 𝗣𝗔 e := by
  intro h
  obtain ⟨e, hconservative, hnot⟩ := montagna_condition_two_not_one
  exact hnot (h e hconservative)

end FailureOfComposition.ConcreteIndices
