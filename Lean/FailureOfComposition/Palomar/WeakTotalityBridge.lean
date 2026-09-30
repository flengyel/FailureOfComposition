/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.Palomar.EvaluatorBridge
import FailureOfComposition.ConcreteWeakTotality

/-!
# Exact guard-index and weak-totality correspondence

The compiler equalities below preserve the concrete program syntax, so the
same natural-number witness is transported to the maintained theorem.  The
weak-totality bridge is proved independently of the counterexample theorem.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition.Palomar.Arithmetic.Evaluator

namespace IndexCompiler

private theorem addProgram_eq :
    addProgram = FailureOfComposition.ConcreteEvaluator.addProgram := rfl

private theorem mulProgram_eq :
    mulProgram = FailureOfComposition.ConcreteEvaluator.mulProgram := by
  simp [mulProgram, FailureOfComposition.ConcreteEvaluator.mulProgram,
    addProgram_eq]

private theorem eqProgram_eq :
    eqProgram = FailureOfComposition.ConcreteEvaluator.eqProgram := by
  simp [eqProgram, FailureOfComposition.ConcreteEvaluator.eqProgram,
    isZeroProgram, FailureOfComposition.ConcreteEvaluator.isZeroProgram,
    subProgram, FailureOfComposition.ConcreteEvaluator.subProgram,
    predProgram, FailureOfComposition.ConcreteEvaluator.predProgram,
    addProgram_eq]

private theorem ltProgram_eq :
    ltProgram = FailureOfComposition.ConcreteEvaluator.ltProgram := by
  simp [ltProgram, FailureOfComposition.ConcreteEvaluator.ltProgram,
    isZeroProgram, FailureOfComposition.ConcreteEvaluator.isZeroProgram,
    subProgram, FailureOfComposition.ConcreteEvaluator.subProgram,
    predProgram, FailureOfComposition.ConcreteEvaluator.predProgram]

private theorem projectionCode_eq : {n : ℕ} → (i : Fin n) →
    projectionCode n i =
      FailureOfComposition.ArithmeticCodeCompiler.projectionCode n i
  | 0, i => Fin.elim0 i
  | n + 1, i => by
      refine Fin.cases rfl (fun j => ?_) i
      simp [projectionCode,
        FailureOfComposition.ArithmeticCodeCompiler.projectionCode,
        projectionCode_eq j]

private theorem tupleCode_eq : (n : ℕ) → (d : Fin n → PCode) →
    tupleCode n d = FailureOfComposition.ArithmeticCodeCompiler.tupleCode n d
  | 0, _ => rfl
  | n + 1, d => by
      simp [tupleCode, FailureOfComposition.ArithmeticCodeCompiler.tupleCode,
        tupleCode_eq n]

private theorem searchZeroCode_eq (c : PCode) :
    searchZeroCode c =
      FailureOfComposition.ArithmeticCodeCompiler.searchZeroCode c := rfl

/-- Structural compilation agrees exactly with the maintained compiler. -/
theorem compile_toFoundation {n : ℕ} (c : Code n) :
    compile c = FailureOfComposition.ArithmeticCodeCompiler.compile c.toFoundation := by
  induction c with
  | zero => rfl
  | one => rfl
  | add i j =>
      change _ = FailureOfComposition.ArithmeticCodeCompiler.compile (.add i j)
      rw [compile, FailureOfComposition.ArithmeticCodeCompiler.compile,
        addProgram_eq, projectionCode_eq, projectionCode_eq]
  | mul i j =>
      change _ = FailureOfComposition.ArithmeticCodeCompiler.compile (.mul i j)
      rw [compile, FailureOfComposition.ArithmeticCodeCompiler.compile,
        mulProgram_eq, projectionCode_eq, projectionCode_eq]
  | proj i => exact projectionCode_eq i
  | equal i j =>
      change _ = FailureOfComposition.ArithmeticCodeCompiler.compile (.equal i j)
      rw [compile, FailureOfComposition.ArithmeticCodeCompiler.compile,
        eqProgram_eq, projectionCode_eq, projectionCode_eq]
  | lt i j =>
      change _ = FailureOfComposition.ArithmeticCodeCompiler.compile (.lt i j)
      rw [compile, FailureOfComposition.ArithmeticCodeCompiler.compile,
        ltProgram_eq, projectionCode_eq, projectionCode_eq]
  | comp c d ihc ihd =>
      change _ = FailureOfComposition.ArithmeticCodeCompiler.compile
        (.comp c.toFoundation fun i => (d i).toFoundation)
      rw [compile, FailureOfComposition.ArithmeticCodeCompiler.compile, ihc,
        tupleCode_eq]
      congr 2
      funext i
      exact ihd i
  | rfind c ih =>
      change _ = FailureOfComposition.ArithmeticCodeCompiler.compile
        (.rfind c.toFoundation)
      rw [compile, FailureOfComposition.ArithmeticCodeCompiler.compile, ih,
        searchZeroCode_eq]

/-- Unary compilation agrees exactly with the maintained compiler. -/
theorem unaryCompile_toFoundation (c : Code 1) :
    unaryCompile c =
      FailureOfComposition.ArithmeticCodeCompiler.unaryCompile c.toFoundation := by
  simp [unaryCompile, FailureOfComposition.ArithmeticCodeCompiler.unaryCompile,
    compile_toFoundation]

end IndexCompiler

open Construction

@[simp] theorem historyCode_toFoundation (d : ℕ) :
    (historyCode d).toFoundation =
      FailureOfComposition.HistoryWitnesses.historyCode d := by
  simp [historyCode, FailureOfComposition.HistoryWitnesses.historyCode,
    Code.toFoundation, Matrix.fun_eq_vec_three]

@[simp] theorem guardCode_toFoundation (d : ℕ) :
    (guardCode d).toFoundation =
      FailureOfComposition.HistoryWitnesses.guardCode d := by
  simp [guardCode, FailureOfComposition.HistoryWitnesses.guardCode,
    Code.toFoundation]

/-- The independent guard is the same encoded program, not just an
extensionally equivalent index. -/
@[simp] theorem guardIndex_toFoundation (d : ℕ) :
    guardIndex d = FailureOfComposition.ConcreteIndices.guardIndex d := by
  simp [guardIndex, FailureOfComposition.ConcreteIndices.guardIndex,
    IndexCompiler.unaryCompile_toFoundation]

/-- The independent and maintained cancellation predicates agree at every
index, without assumptions on the theory. -/
theorem weaklyTotalIndex_toFoundation_iff (T : Theory) (e : ℕ) :
    WeaklyTotalIndex T e ↔
      FailureOfComposition.ConcreteIndices.WeaklyTotalIndex
        (TheoryCorrespondence.toFoundation T) e := by
  unfold WeaklyTotalIndex FailureOfComposition.ConcreteIndices.WeaklyTotalIndex
  simp_rw [compIndex_toFoundation, emptyIndex_toFoundation,
    pointwiseIndex_toFoundation_iff]

/-- The exact independent weak-totality counterexample, transported from the
maintained productive construction. -/
theorem weak_totality_counterexample
    (T : Theory) (hPA : DeductivelyExtends Peano T) (hCons : Consistent T)
    (hT : REPred (AxiomCodes T)) :
    ∃ d : ℕ, PointwiseIndex T (guardIndex d) identityIndex ∧
      ¬WeaklyTotalIndex T (guardIndex d) ∧ WeaklyTotalIndex T identityIndex := by
  let Tf := TheoryCorrespondence.toFoundation T
  let _ : FFL.Entailment.WeakerThan FFL.FirstOrder.Arithmetic.Peano Tf :=
    (deductivelyExtendsPeano_toFoundation_iff T).mp hPA
  let _ : FFL.Entailment.Consistent Tf :=
    (consistent_toFoundation_iff T).mp hCons
  obtain ⟨d, hguard, hnot, hid⟩ :=
    FailureOfComposition.ConcreteIndices.weak_totality_counterexample_of_re_axioms
      Tf ((reAxiomCodes_toFoundation_iff T).mp hT)
  refine ⟨d, ?_, ?_, ?_⟩
  · apply (pointwiseIndex_toFoundation_iff T _ _).mpr
    simpa using hguard
  · intro h
    apply hnot
    have h' := (weaklyTotalIndex_toFoundation_iff T (guardIndex d)).mp h
    simpa using h'
  · apply (weaklyTotalIndex_toFoundation_iff T identityIndex).mpr
    simpa using hid

end FailureOfComposition.Palomar.Arithmetic.Evaluator
