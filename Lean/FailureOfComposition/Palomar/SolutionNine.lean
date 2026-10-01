/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.Palomar.GodelQuotientBridge
public import FailureOfComposition.Palomar.PiOneBridge
public import FailureOfComposition.Palomar.GeneratedCongruenceBridge
public import FailureOfComposition.Palomar.WeakTotalityBridge
public import FailureOfComposition.Palomar.RangeBridge
public import FailureOfComposition.Palomar.RangeProductiveBridge
public import FailureOfComposition.Palomar.GeneratedQuotientBridge

/-! Proved cumulative counterpart of the nine-result Challenge checkpoint. -/

@[expose] public section

set_option autoImplicit false

namespace FailureOfComposition.Palomar

open Arithmetic Arithmetic.Evaluator

theorem obstruction_four_properties
    (T : Arithmetic.Theory)
    (hPA : Arithmetic.DeductivelyExtends Arithmetic.Peano T)
    (hCons : Arithmetic.Consistent T)
    (hT : REPred (Arithmetic.AxiomCodes T)) :
    ∃ f g : ℕ,
      Arithmetic.Evaluator.PointwiseIndex T f Arithmetic.Evaluator.identityIndex ∧
      Arithmetic.Evaluator.UniformIndex T (Arithmetic.Evaluator.compIndex f g)
        Arithmetic.Evaluator.emptyIndex ∧
      Arithmetic.Evaluator.UniformIndex T
        (Arithmetic.Evaluator.compIndex Arithmetic.Evaluator.identityIndex g) g ∧
      ¬Arithmetic.Evaluator.PointwiseIndex T g Arithmetic.Evaluator.emptyIndex := by
  exact Arithmetic.Evaluator.obstruction_four_properties T hPA hCons hT

theorem no_quotient_composition_productive
    (T : Arithmetic.Theory)
    (hPA : Arithmetic.DeductivelyExtends Arithmetic.Peano T)
    (hCons : Arithmetic.Consistent T)
    (hT : REPred (Arithmetic.AxiomCodes T)) :
    ¬∃ C : Arithmetic.Evaluator.IndexQuotient T →
        Arithmetic.Evaluator.IndexQuotient T →
        Arithmetic.Evaluator.IndexQuotient T,
      ∀ e d : ℕ,
        C (Arithmetic.Evaluator.indexQuotientMk T e)
            (Arithmetic.Evaluator.indexQuotientMk T d) =
          Arithmetic.Evaluator.indexQuotientMk T
            (Arithmetic.Evaluator.compIndex e d) := by
  exact Arithmetic.Evaluator.no_quotient_composition_of_four_properties T hPA
    (obstruction_four_properties T hPA hCons hT)

theorem no_quotient_composition_godel
    (T : Arithmetic.Theory)
    (hPA : Arithmetic.DeductivelyExtends Arithmetic.Peano T)
    (hCons : Arithmetic.Consistent T)
    (hT : REPred (Arithmetic.AxiomCodes T)) :
    ¬∃ C : Arithmetic.Evaluator.IndexQuotient T →
        Arithmetic.Evaluator.IndexQuotient T →
        Arithmetic.Evaluator.IndexQuotient T,
      ∀ e d : ℕ,
        C (Arithmetic.Evaluator.indexQuotientMk T e)
            (Arithmetic.Evaluator.indexQuotientMk T d) =
          Arithmetic.Evaluator.indexQuotientMk T
            (Arithmetic.Evaluator.compIndex e d) := by
  exact Arithmetic.Evaluator.no_quotient_composition_godel T hPA hCons hT

theorem pi_one_characterization
    (T : Arithmetic.Theory)
    (hPA : Arithmetic.DeductivelyExtends Arithmetic.Peano T)
    (hCons : Arithmetic.Consistent T) :
    (Arithmetic.Evaluator.RightCompatible T ↔
      Arithmetic.Evaluator.CompositionCongruence T) ∧
    (Arithmetic.Evaluator.CompositionCongruence T ↔
      Arithmetic.PiOneComplete T) ∧
    (Arithmetic.PiOneComplete T ↔
      Arithmetic.Evaluator.AgreesWithExtensional T) := by
  exact Arithmetic.Evaluator.pi_one_characterization T hPA hCons

theorem generated_congruence_classification
    (T : Arithmetic.Theory)
    (hPA : Arithmetic.DeductivelyExtends Arithmetic.Peano T) :
    (Arithmetic.SigmaOneSound T →
      ∀ e d : ℕ, Arithmetic.Evaluator.GeneratedRel T e d ↔
        Arithmetic.Evaluator.actualEval e = Arithmetic.Evaluator.actualEval d) ∧
    (¬Arithmetic.SigmaOneSound T →
      ∀ e d : ℕ, Arithmetic.Evaluator.GeneratedRel T e d) := by
  exact Arithmetic.Evaluator.generated_congruence_classification T hPA

theorem weak_totality_counterexample
    (T : Arithmetic.Theory)
    (hPA : Arithmetic.DeductivelyExtends Arithmetic.Peano T)
    (hCons : Arithmetic.Consistent T)
    (hT : REPred (Arithmetic.AxiomCodes T)) :
    ∃ d : ℕ, Arithmetic.Evaluator.PointwiseIndex T
        (Arithmetic.Evaluator.guardIndex d) Arithmetic.Evaluator.identityIndex ∧
      ¬Arithmetic.Evaluator.WeaklyTotalIndex T (Arithmetic.Evaluator.guardIndex d) ∧
      Arithmetic.Evaluator.WeaklyTotalIndex T Arithmetic.Evaluator.identityIndex := by
  exact Arithmetic.Evaluator.weak_totality_counterexample T hPA hCons hT

/-- Proposition 6, Gödel-II route: pointwise equality with empty is not preserved by the fixed
PA-uniform range assignment. -/
theorem range_counterexample_godel
    (T : Arithmetic.Theory)
    (hPA : Arithmetic.DeductivelyExtends Arithmetic.Peano T)
    (hCons : Arithmetic.Consistent T)
    (hT : REPred (Arithmetic.AxiomCodes T)) :
    ∃ u : ℕ, Arithmetic.Evaluator.PointwiseIndex T u
        Arithmetic.Evaluator.emptyIndex ∧
      ¬Arithmetic.Evaluator.PointwiseIndex T
        (Arithmetic.Evaluator.rangeIndex u)
        (Arithmetic.Evaluator.rangeIndex Arithmetic.Evaluator.emptyIndex) := by
  exact Arithmetic.Evaluator.range_counterexample_godel T hPA hCons hT

/-- Proposition 6, productive route: the same pointwise range obstruction, proved through
productive nonenumerability rather than Gödel II. -/
theorem range_counterexample_productive
    (T : Arithmetic.Theory)
    (hPA : Arithmetic.DeductivelyExtends Arithmetic.Peano T)
    (hCons : Arithmetic.Consistent T)
    (hT : REPred (Arithmetic.AxiomCodes T)) :
    ∃ u : ℕ, Arithmetic.Evaluator.PointwiseIndex T u
        Arithmetic.Evaluator.emptyIndex ∧
      ¬Arithmetic.Evaluator.PointwiseIndex T
        (Arithmetic.Evaluator.rangeIndex u)
        (Arithmetic.Evaluator.rangeIndex Arithmetic.Evaluator.emptyIndex) := by
  exact Arithmetic.Evaluator.range_counterexample_productive T hPA hCons hT

/-- The generated composition quotient is multiplicatively equivalent to the
actual unary partial recursive functions, preserving every representative. -/
theorem generated_quotient_partial_recursive
    (T : Arithmetic.Theory)
    (hPA : Arithmetic.DeductivelyExtends Arithmetic.Peano T)
    (hT : Arithmetic.SigmaOneSound T) :
    ∃ E : Arithmetic.Evaluator.GeneratedQuotient T ≃*
        Arithmetic.Evaluator.UnaryPartrec,
      ∀ e : ℕ, E (Arithmetic.Evaluator.generatedQuotientMk T e) =
        Arithmetic.Evaluator.UnaryPartrec.ofIndex e := by
  exact Arithmetic.Evaluator.generated_quotient_partial_recursive T hPA hT

end FailureOfComposition.Palomar
