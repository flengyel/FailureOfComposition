/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.Palomar.DirectDerivationEnumeration
public import FailureOfComposition.ConcreteDiagonal

/-!
# Direct theorem enumeration at the history-divergence boundary

This small bridge constructs the concrete divergence sentence with independent
syntax and proves its effective dependence on the numerical input.  It avoids
routing the first obstruction proof through maintained quoted theorem codes.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open Encodable

namespace FailureOfComposition.Palomar.Arithmetic.Evaluator

open FailureOfComposition.Palomar.DirectDerivationEnumeration

local instance termPrimcodable {ξ : Type} [Primcodable ξ] {n : ℕ} :
    Primcodable (FailureOfComposition.Palomar.Arithmetic.Term ξ n) :=
  Primcodable.ofEquiv (ArithmeticSemiterm ξ n)
    FailureOfComposition.Palomar.Arithmetic.Term.equivalence

local instance formulaPrimcodable {ξ : Type} [Primcodable ξ] {n : ℕ} :
    Primcodable (FailureOfComposition.Palomar.Arithmetic.Formula ξ n) :=
  Primcodable.ofEquiv (ArithmeticSemiformula ξ n)
    FailureOfComposition.Palomar.Arithmetic.Formula.equivalence

def directDiagonalHistoryFormula : Semiproposition 1 :=
  Formula.ofFoundation
    (Rewriting.emb FailureOfComposition.ConcreteEvaluator.diagonalHistoryFormula)

def directHistoryDivergenceProposition (n : ℕ) : Proposition :=
  Formula.neg (Formula.substOne directDiagonalHistoryFormula
    (FailureOfComposition.Palomar.Arithmetic.Term.numeral n))

/-- The maintained closed sentence, with its free-variable type fixed
explicitly so that the substitution notation cannot infer a semisentence. -/
def foundationHistoryDivergenceSentence (n : ℕ) : ArithmeticSentence :=
  ∼FailureOfComposition.ConcreteEvaluator.diagonalHistoryFormula/[n]

/-- The actual closed independent sentence corresponding to represented
history divergence at `n`. -/
def directHistoryDivergenceSentence (n : ℕ) : Sentence :=
  Formula.ofFoundation (foundationHistoryDivergenceSentence n)

@[simp] theorem toFoundation_directHistoryDivergenceProposition (n : ℕ) :
    Formula.toFoundation (directHistoryDivergenceProposition n) =
      foundationHistoryDivergenceSentence n := by
  simp [directHistoryDivergenceProposition, directDiagonalHistoryFormula,
    foundationHistoryDivergenceSentence,
    Rewriting.emb_subst_eq_subst_coe₁]
  rfl

@[simp] theorem toFoundation_directHistoryDivergenceSentence (n : ℕ) :
    Formula.toFoundation (directHistoryDivergenceSentence n) =
      foundationHistoryDivergenceSentence n := by
  simp [directHistoryDivergenceSentence]

theorem encode_directHistoryDivergenceSentence (n : ℕ) :
    Encodable.encode (directHistoryDivergenceSentence n) =
      Encodable.encode (directHistoryDivergenceProposition n) := by
  change Encodable.encode
      (Formula.toFoundation (directHistoryDivergenceSentence n)) =
    Encodable.encode
      (Formula.toFoundation (directHistoryDivergenceProposition n))
  rw [toFoundation_directHistoryDivergenceSentence,
    toFoundation_directHistoryDivergenceProposition]
  exact (Semiformula.encode_emb
    (foundationHistoryDivergenceSentence n)).symm

theorem directHistoryDivergenceSentence_primrec :
    Primrec directHistoryDivergenceSentence := by
  have hsubst : Primrec (fun n : ℕ ↦
      Formula.substOne directDiagonalHistoryFormula
        (FailureOfComposition.Palomar.Arithmetic.Term.numeral n)) :=
    DirectFormula.actual_substOne_primrec.comp
      (Primrec.const directDiagonalHistoryFormula) termNumeral_primrec
  have hproposition : Primrec directHistoryDivergenceProposition :=
    DirectFormula.actual_neg_primrec.comp hsubst
  apply Primrec.encode_iff.mp
  exact (Primrec.encode.comp hproposition).of_eq fun n ↦
    (encode_directHistoryDivergenceSentence n).symm

end FailureOfComposition.Palomar.Arithmetic.Evaluator
