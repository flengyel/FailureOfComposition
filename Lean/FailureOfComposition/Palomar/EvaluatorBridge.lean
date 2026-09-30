/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.Palomar.ArithmeticBridge
public import FailureOfComposition.Palomar.EvaluatorInterface
public import FailureOfComposition.ConcreteEvaluatorGraph
public import FailureOfComposition.ConcreteIndexObstruction
public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Correspondence for the independent evaluator statement interface

The independent code language and formula compiler are mapped to the pinned
Foundation definitions used by the maintained concrete evaluator.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment

namespace FailureOfComposition.Palomar.Arithmetic.Evaluator

namespace Code

def toFoundation : {n : ℕ} → Code n → Nat.ArithPart₁.Code n
  | _, .zero n => .zero n
  | _, .one n => .one n
  | _, .add i j => .add i j
  | _, .mul i j => .mul i j
  | _, .proj i => .proj i
  | _, .equal i j => .equal i j
  | _, .lt i j => .lt i j
  | _, .comp c d => .comp (toFoundation c) (fun i ↦ toFoundation (d i))
  | _, .rfind c => .rfind (toFoundation c)

end Code

namespace Compiler

private theorem Formula.toFoundation_nequal {xi : Type} {n : ℕ}
    (s t : Term xi n) :
    Formula.toFoundation (.nequal s t) =
      ∼Formula.toFoundation (.equal s t) := rfl

private theorem Formula.toFoundation_nless {xi : Type} {n : ℕ}
    (s t : Term xi n) :
    Formula.toFoundation (.nless s t) =
      ∼Formula.toFoundation (.less s t) := rfl

@[simp] theorem toFoundation_finConj {xi : Type} {n k : ℕ}
    (v : Fin k → Formula xi n) :
    Formula.toFoundation (finConj v) =
      Matrix.conj (fun i ↦ Formula.toFoundation (v i)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change Formula.toFoundation
          (.and (v fin0) (finConj fun i ↦ v i.succ)) = _
      rw [Formula.toFoundation_and, Matrix.conj, ih]
      simp only [fin0_eq_zero, Matrix.vecTail]
      congr 1

@[simp] theorem toFoundation_exsClosure {xi : Type} {n : ℕ}
    (p : Formula xi n) :
    Formula.toFoundation (exsClosure p) =
      FFL.FirstOrder.exsClosure (Formula.toFoundation p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Formula.toFoundation (exsClosure (.exs p)) = _
      rw [ih, Formula.toFoundation_exs]
      rfl

@[simp] theorem toFoundation_codeAux {k : ℕ} (c : Code k) :
    Formula.toFoundation (codeAux c) =
      FFL.FirstOrder.Arithmetic.codeAux c.toFoundation := by
  induction c with
  | zero n =>
      simp only [codeAux, Code.toFoundation,
        FFL.FirstOrder.Arithmetic.codeAux, Formula.toFoundation_equal,
        Term.toFoundation_fvar, Term.toFoundation_zero, fin0_eq_zero]
  | one n =>
      simp only [codeAux, Code.toFoundation,
        FFL.FirstOrder.Arithmetic.codeAux, Formula.toFoundation_equal,
        Term.toFoundation_fvar, Term.toFoundation_one, fin0_eq_zero]
  | add i j => rfl
  | mul i j => rfl
  | proj i => rfl
  | equal i j =>
      simp only [codeAux, Code.toFoundation,
        FFL.FirstOrder.Arithmetic.codeAux, Formula.toFoundation_or,
        Formula.toFoundation_and, Formula.toFoundation_equal,
        Formula.toFoundation_nequal, Term.toFoundation_fvar,
        Term.toFoundation_zero, Term.toFoundation_one, fin0_eq_zero]
  | lt i j =>
      simp only [codeAux, Code.toFoundation,
        FFL.FirstOrder.Arithmetic.codeAux, Formula.toFoundation_or,
        Formula.toFoundation_and, Formula.toFoundation_equal,
        Formula.toFoundation_less, Formula.toFoundation_nless,
        Term.toFoundation_fvar,
        Term.toFoundation_zero, Term.toFoundation_one, fin0_eq_zero]
  | comp c d ihc ihd =>
      simp only [codeAux, Code.toFoundation,
        FFL.FirstOrder.Arithmetic.codeAux, toFoundation_exsClosure,
        Formula.toFoundation_and, Formula.toFoundation_rewrite,
        toFoundation_finConj, ihc, ihd]
      apply congrArg FFL.FirstOrder.exsClosure
      apply congrArg₂ Semiformula.and
      · apply congrArg (fun w ↦ Semiformula.rewAux w
          (FFL.FirstOrder.Arithmetic.codeAux c.toFoundation))
        apply Rew.ext
        · intro i
          exact Fin.elim0 i
        · intro i
          refine Fin.cases rfl (fun _ ↦ rfl) i
      · apply congrArg Matrix.conj
        funext i
        apply congrArg (fun w ↦ Semiformula.rewAux w
          (FFL.FirstOrder.Arithmetic.codeAux (d i).toFoundation))
        apply Rew.ext
        · intro j
          exact Fin.elim0 j
        · intro j
          refine Fin.cases rfl (fun _ ↦ rfl) j
  | rfind c ih =>
      simp only [codeAux, Code.toFoundation,
        FFL.FirstOrder.Arithmetic.codeAux, Formula.toFoundation_and,
        Formula.toFoundation_all, Formula.toFoundation_or,
        Formula.toFoundation_exs, Formula.toFoundation_rewrite,
        Formula.toFoundation_nless, Formula.toFoundation_less,
        Formula.toFoundation_nequal, Formula.toFoundation_equal,
        Term.toFoundation_zero, FFL.FirstOrder.ball,
        Semiformula.imp_eq, ih]
      apply congrArg₂ Semiformula.and
      · apply congrArg (fun w ↦ Semiformula.rewAux w
          (FFL.FirstOrder.Arithmetic.codeAux c.toFoundation))
        apply Rew.ext
        · intro i
          exact Fin.elim0 i
        · intro i
          refine Fin.cases ?_ (fun j ↦ Fin.cases rfl (fun _ ↦ rfl) j) i
          exact Term.toFoundation_zero
      · apply congrArg Semiformula.all
        apply congrArg₂ Semiformula.or
        · rfl
        · apply congrArg Semiformula.exs
          apply congrArg₂ Semiformula.and
          · rfl
          · apply congrArg (fun w ↦ Semiformula.rewAux w
              (FFL.FirstOrder.Arithmetic.codeAux c.toFoundation))
            apply Rew.ext
            · intro i
              exact Fin.elim0 i
            · intro i
              refine Fin.cases rfl (fun j ↦ Fin.cases rfl (fun _ ↦ rfl) j) i

@[simp] theorem toFoundation_code {k : ℕ} (c : Code k) :
    Formula.toFoundation (code c) =
      FFL.FirstOrder.Arithmetic.code c.toFoundation := by
  simp only [code, FFL.FirstOrder.Arithmetic.code,
    Formula.toFoundation_rewrite, toFoundation_codeAux]
  apply congrArg (fun w ↦ Semiformula.rewAux w
    (FFL.FirstOrder.Arithmetic.codeAux c.toFoundation))
  apply Rew.ext
  · intro i
    exact Fin.elim0 i
  · intro i
    refine Fin.cases rfl (fun _ ↦ rfl) i

end Compiler

namespace Construction

open CategoricalRiceShapiro.ArithmeticCode

@[simp] theorem toFoundation_codeSucc {n : ℕ} (d : Code n) :
    (codeSucc d).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeSucc d.toFoundation := by
  simp [codeSucc, CategoricalRiceShapiro.ArithmeticCode.codeSucc,
    Code.toFoundation, Matrix.fun_eq_vec_two]

@[simp] theorem toFoundation_codeConst {n : ℕ} (m : ℕ) :
    (codeConst (n := n) m).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeConst (n := n) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change (codeSucc (codeConst (n := n) m)).toFoundation = _
      rw [CategoricalRiceShapiro.ArithmeticCode.codeConst,
        toFoundation_codeSucc, ih]

@[simp] theorem toFoundation_codeInv {n : ℕ} (d : Code n) :
    (codeInv d).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeInv d.toFoundation := by
  simp [codeInv, CategoricalRiceShapiro.ArithmeticCode.codeInv,
    Code.toFoundation, Matrix.fun_eq_vec_two]

@[simp] theorem toFoundation_codePos {n : ℕ} (d : Code n) :
    (codePos d).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codePos d.toFoundation := by
  simp [codePos, CategoricalRiceShapiro.ArithmeticCode.codePos,
    Code.toFoundation, Matrix.fun_eq_vec_two]

@[simp] theorem toFoundation_codeAnd {n : ℕ} (d₀ d₁ : Code n) :
    (codeAnd d₀ d₁).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeAnd
        d₀.toFoundation d₁.toFoundation := by
  simp [codeAnd, CategoricalRiceShapiro.ArithmeticCode.codeAnd,
    Code.toFoundation, Matrix.fun_eq_vec_two]

@[simp] theorem toFoundation_codeOr {n : ℕ} (d₀ d₁ : Code n) :
    (codeOr d₀ d₁).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeOr
        d₀.toFoundation d₁.toFoundation := by
  simp [codeOr, CategoricalRiceShapiro.ArithmeticCode.codeOr,
    Code.toFoundation, Matrix.fun_eq_vec_two]

@[simp] theorem toFoundation_codeEq {n : ℕ} (d₀ d₁ : Code n) :
    (codeEq d₀ d₁).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeEq
        d₀.toFoundation d₁.toFoundation := by
  simp [codeEq, CategoricalRiceShapiro.ArithmeticCode.codeEq,
    Code.toFoundation, Matrix.fun_eq_vec_two]

@[simp] theorem toFoundation_codeLt {n : ℕ} (d₀ d₁ : Code n) :
    (codeLt d₀ d₁).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeLt
        d₀.toFoundation d₁.toFoundation := by
  simp [codeLt, CategoricalRiceShapiro.ArithmeticCode.codeLt,
    Code.toFoundation, Matrix.fun_eq_vec_two]

@[simp] theorem toFoundation_codeAdd {n : ℕ} (d₀ d₁ : Code n) :
    (codeAdd d₀ d₁).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeAdd
        d₀.toFoundation d₁.toFoundation := by
  simp [codeAdd, CategoricalRiceShapiro.ArithmeticCode.codeAdd,
    Code.toFoundation, Matrix.fun_eq_vec_two]

@[simp] theorem toFoundation_codeMul {n : ℕ} (d₀ d₁ : Code n) :
    (codeMul d₀ d₁).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeMul
        d₀.toFoundation d₁.toFoundation := by
  simp [codeMul, CategoricalRiceShapiro.ArithmeticCode.codeMul,
    Code.toFoundation, Matrix.fun_eq_vec_two]

@[simp] theorem toFoundation_codeLift {n : ℕ} (d : Code n) :
    (codeLift d).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeLift d.toFoundation := by
  simp [codeLift, CategoricalRiceShapiro.ArithmeticCode.codeLift,
    Code.toFoundation]

@[simp] theorem toFoundation_codeHead {n : ℕ} :
    (codeHead (n := n)).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeHead (n := n) := rfl

@[simp] theorem toFoundation_codeIfPos {n : ℕ} (df dg dh : Code n) :
    (codeIfPos df dg dh).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeIfPos
        df.toFoundation dg.toFoundation dh.toFoundation := by
  simp [codeIfPos, CategoricalRiceShapiro.ArithmeticCode.codeIfPos]

@[simp] theorem toFoundation_codeLe {n : ℕ} (d₀ d₁ : Code n) :
    (codeLe d₀ d₁).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeLe
        d₀.toFoundation d₁.toFoundation := by
  simp [codeLe, CategoricalRiceShapiro.ArithmeticCode.codeLe]

@[simp] theorem toFoundation_codeRfindPos {n : ℕ} (d : Code (n + 1)) :
    (codeRfindPos d).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeRfindPos d.toFoundation := by
  simp [codeRfindPos, CategoricalRiceShapiro.ArithmeticCode.codeRfindPos,
    Code.toFoundation]

@[simp] theorem toFoundation_codeBind {n : ℕ}
    (dg : Code n) (dc : Code (n + 1)) :
    (codeBind dg dc).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeBind
        dg.toFoundation dc.toFoundation := by
  simp only [codeBind, Code.toFoundation,
    CategoricalRiceShapiro.ArithmeticCode.codeBind,
    Nat.ArithPart₁.Code.comp.injEq, heq_eq_eq, true_and]
  funext i
  refine Fin.cases rfl (fun _ ↦ rfl) i

@[simp] theorem toFoundation_codeSub {n : ℕ} (d₀ d₁ : Code n) :
    (codeSub d₀ d₁).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeSub
        d₀.toFoundation d₁.toFoundation := by
  simp [codeSub, CategoricalRiceShapiro.ArithmeticCode.codeSub,
    Code.toFoundation]

@[simp] theorem toFoundation_codeSqrt {n : ℕ} (d : Code n) :
    (codeSqrt d).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeSqrt d.toFoundation := by
  simp [codeSqrt, CategoricalRiceShapiro.ArithmeticCode.codeSqrt]

@[simp] theorem toFoundation_codeUnpair₁ {n : ℕ} (d : Code n) :
    (codeUnpair₁ d).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeUnpair₁ d.toFoundation := by
  simp [codeUnpair₁, CategoricalRiceShapiro.ArithmeticCode.codeUnpair₁]

@[simp] theorem toFoundation_codeUnpair₂ {n : ℕ} (d : Code n) :
    (codeUnpair₂ d).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeUnpair₂ d.toFoundation := by
  simp [codeUnpair₂, CategoricalRiceShapiro.ArithmeticCode.codeUnpair₂]

@[simp] theorem toFoundation_codeDvd {n : ℕ} (d₀ d₁ : Code n) :
    (codeDvd d₀ d₁).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeDvd
        d₀.toFoundation d₁.toFoundation := by
  simp [codeDvd, CategoricalRiceShapiro.ArithmeticCode.codeDvd]

@[simp] theorem toFoundation_codeRem {n : ℕ} (d₀ d₁ : Code n) :
    (codeRem d₀ d₁).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeRem
        d₀.toFoundation d₁.toFoundation := by
  simp [codeRem, CategoricalRiceShapiro.ArithmeticCode.codeRem]

@[simp] theorem toFoundation_codeBeta {n : ℕ} (dn di : Code n) :
    (codeBeta dn di).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeBeta
        dn.toFoundation di.toFoundation := by
  simp [codeBeta, CategoricalRiceShapiro.ArithmeticCode.codeBeta]

@[simp] theorem toFoundation_codePair {n : ℕ} (d₀ d₁ : Code n) :
    (codePair d₀ d₁).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codePair
        d₀.toFoundation d₁.toFoundation := by
  simp [codePair, CategoricalRiceShapiro.ArithmeticCode.codePair]

@[simp] theorem toFoundation_codeBall {n : ℕ}
    (dphi : Code (n + 1)) (i : Fin n) :
    (codeBall dphi i).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeBall dphi.toFoundation i := by
  simp [codeBall, CategoricalRiceShapiro.ArithmeticCode.codeBall,
    Code.toFoundation]

@[simp] theorem toFoundation_codePrecStep {n : ℕ} (dg : Code (n + 2)) :
    (codePrecStep dg).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codePrecStep dg.toFoundation := by
  simp only [codePrecStep, fin1_eq_one, fin0_eq_zero,
    toFoundation_codeEq, toFoundation_codeBeta, Code.toFoundation,
    toFoundation_codeSucc, precStepArgs,
    CategoricalRiceShapiro.ArithmeticCode.codePrecStep]
  congr 2
  funext i
  refine Fin.cases rfl (fun j ↦ Fin.cases ?_ (fun _ ↦ rfl) j) i
  exact toFoundation_codeBeta (.proj 1) (.proj 0)

@[simp] theorem toFoundation_codePrecPredicate {n : ℕ}
    (df : Code n) (dg : Code (n + 2)) :
    (codePrecPredicate df dg).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codePrecPredicate
        df.toFoundation dg.toFoundation := by
  simp [codePrecPredicate,
    CategoricalRiceShapiro.ArithmeticCode.codePrecPredicate,
    codeTailTail, Code.toFoundation]
  rfl

@[simp] theorem toFoundation_codePrec {n : ℕ}
    (df : Code n) (dg : Code (n + 2)) :
    (codePrec df dg).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codePrec
        df.toFoundation dg.toFoundation := by
  simp [codePrec, CategoricalRiceShapiro.ArithmeticCode.codePrec]

@[simp] theorem toFoundation_codeListHead? {n : ℕ} (d : Code n) :
    (codeListHead? d).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeListHead? d.toFoundation := by
  simp [codeListHead?, CategoricalRiceShapiro.ArithmeticCode.codeListHead?,
    Code.toFoundation]

@[simp] theorem toFoundation_codeListTail {n : ℕ} (d : Code n) :
    (codeListTail d).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeListTail d.toFoundation := by
  simp [codeListTail, CategoricalRiceShapiro.ArithmeticCode.codeListTail]

@[simp] theorem toFoundation_codeListDrop {n : ℕ}
    (dlist didx : Code n) :
    (codeListDrop dlist didx).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeListDrop
        dlist.toFoundation didx.toFoundation := by
  rw [codeListDrop,
    CategoricalRiceShapiro.ArithmeticCode.codeListDrop_eq_comp]
  simp [Code.toFoundation, Matrix.fun_eq_vec_two]
  rfl

@[simp] theorem toFoundation_codeListGet? {n : ℕ}
    (dlist didx : Code n) :
    (codeListGet? dlist didx).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeListGet?
        dlist.toFoundation didx.toFoundation := by
  simp [codeListGet?, CategoricalRiceShapiro.ArithmeticCode.codeListGet?]

@[simp] theorem toFoundation_codeListLength {n : ℕ} (dlist : Code n) :
    (codeListLength dlist).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeListLength dlist.toFoundation := by
  simp [codeListLength,
    CategoricalRiceShapiro.ArithmeticCode.codeListLength]

@[simp] theorem toFoundation_codeOptionBind {n : ℕ}
    (dopt : Code n) (dk : Code (n + 1)) :
    (codeOptionBind dopt dk).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeOptionBind
        dopt.toFoundation dk.toFoundation := by
  simp [codeOptionBind,
    CategoricalRiceShapiro.ArithmeticCode.codeOptionBind,
    Code.toFoundation]

@[simp] theorem toFoundation_codeListNil {n : ℕ} :
    (codeListNil (n := n)).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeListNil (n := n) := rfl

@[simp] theorem toFoundation_codeListCons {n : ℕ} (dx dt : Code n) :
    (codeListCons dx dt).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeListCons
        dx.toFoundation dt.toFoundation := by
  simp [codeListCons, CategoricalRiceShapiro.ArithmeticCode.codeListCons]

@[simp] theorem toFoundation_codeListSnoc {r : ℕ}
    (dlist dx : Code r) :
    (codeListSnoc dlist dx).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeListSnoc
        dlist.toFoundation dx.toFoundation := by
  rw [codeListSnoc,
    CategoricalRiceShapiro.ArithmeticCode.codeListSnoc_eq_bind]
  simp [Code.toFoundation]

@[simp] theorem toFoundation_codeBodd {n : ℕ} (d : Code n) :
    (codeBodd d).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeBodd d.toFoundation := by
  simp [codeBodd, CategoricalRiceShapiro.ArithmeticCode.codeBodd]

@[simp] theorem toFoundation_codeDiv2Unary :
    codeDiv2Unary.toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeDiv2Unary := by
  simp [codeDiv2Unary,
    CategoricalRiceShapiro.ArithmeticCode.codeDiv2Unary,
    Code.toFoundation]

@[simp] theorem toFoundation_codeDiv2 {n : ℕ} (d : Code n) :
    (codeDiv2 d).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codeDiv2 d.toFoundation := by
  simp [codeDiv2, CategoricalRiceShapiro.ArithmeticCode.codeDiv2,
    Code.toFoundation, Matrix.fun_eq_vec_one]

@[simp] theorem toFoundation_codePartrecTag {n : ℕ} (d : Code n) :
    (codePartrecTag d).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codePartrecTag d.toFoundation := by
  simp [codePartrecTag,
    CategoricalRiceShapiro.ArithmeticCode.codePartrecTag]

@[simp] theorem toFoundation_codePartrecPayload {n : ℕ} (d : Code n) :
    (codePartrecPayload d).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codePartrecPayload d.toFoundation := by
  simp [codePartrecPayload,
    CategoricalRiceShapiro.ArithmeticCode.codePartrecPayload]

@[simp] theorem toFoundation_codePartrecPayload₁ {n : ℕ} (d : Code n) :
    (codePartrecPayload₁ d).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codePartrecPayload₁ d.toFoundation := by
  simp [codePartrecPayload₁,
    CategoricalRiceShapiro.ArithmeticCode.codePartrecPayload₁]

@[simp] theorem toFoundation_codePartrecPayload₂ {n : ℕ} (d : Code n) :
    (codePartrecPayload₂ d).toFoundation =
      CategoricalRiceShapiro.ArithmeticCode.codePartrecPayload₂ d.toFoundation := by
  simp [codePartrecPayload₂,
    CategoricalRiceShapiro.ArithmeticCode.codePartrecPayload₂]

@[simp] theorem toFoundation_codeTableLookup {r : ℕ}
    (dtable dk dq dn : Code r) :
    (codeTableLookup dtable dk dq dn).toFoundation =
      CategoricalRiceShapiro.Evaluator.codeTableLookup
        dtable.toFoundation dk.toFoundation dq.toFoundation dn.toFoundation := by
  rw [codeTableLookup,
    CategoricalRiceShapiro.Evaluator.codeTableLookup_eq]
  simp

@[simp] theorem toFoundation_codeBaseEvaluatorCell {r : ℕ}
    (dtable dn : Code r) :
    (codeBaseEvaluatorCell dtable dn).toFoundation =
      CategoricalRiceShapiro.Evaluator.codeBaseEvaluatorCell
        dtable.toFoundation dn.toFoundation := by
  simp [codeBaseEvaluatorCell,
    CategoricalRiceShapiro.Evaluator.codeBaseEvaluatorCell]

@[simp] theorem toFoundation_codePairEvaluatorCell {r : ℕ}
    (dtable dk dcf dcg dn : Code r) :
    (codePairEvaluatorCell dtable dk dcf dcg dn).toFoundation =
      CategoricalRiceShapiro.Evaluator.codePairEvaluatorCell
        dtable.toFoundation dk.toFoundation dcf.toFoundation
        dcg.toFoundation dn.toFoundation := by
  simp [codePairEvaluatorCell,
    CategoricalRiceShapiro.Evaluator.codePairEvaluatorCell,
    Code.toFoundation]

@[simp] theorem toFoundation_codeCompEvaluatorCell {r : ℕ}
    (dtable dk dcf dcg dn : Code r) :
    (codeCompEvaluatorCell dtable dk dcf dcg dn).toFoundation =
      CategoricalRiceShapiro.Evaluator.codeCompEvaluatorCell
        dtable.toFoundation dk.toFoundation dcf.toFoundation
        dcg.toFoundation dn.toFoundation := by
  simp [codeCompEvaluatorCell,
    CategoricalRiceShapiro.Evaluator.codeCompEvaluatorCell]

@[simp] theorem toFoundation_codePrecEvaluatorCell {r : ℕ}
    (dtable dk' dq dcf dcg dn : Code r) :
    (codePrecEvaluatorCell dtable dk' dq dcf dcg dn).toFoundation =
      CategoricalRiceShapiro.Evaluator.codePrecEvaluatorCell
        dtable.toFoundation dk'.toFoundation dq.toFoundation
        dcf.toFoundation dcg.toFoundation dn.toFoundation := by
  simp [codePrecEvaluatorCell,
    CategoricalRiceShapiro.Evaluator.codePrecEvaluatorCell]

@[simp] theorem toFoundation_codeRfindEvaluatorCell {r : ℕ}
    (dtable dk' dq dcf dn : Code r) :
    (codeRfindEvaluatorCell dtable dk' dq dcf dn).toFoundation =
      CategoricalRiceShapiro.Evaluator.codeRfindEvaluatorCell
        dtable.toFoundation dk'.toFoundation dq.toFoundation
        dcf.toFoundation dn.toFoundation := by
  simp [codeRfindEvaluatorCell,
    CategoricalRiceShapiro.Evaluator.codeRfindEvaluatorCell]

@[simp] theorem toFoundation_codeEvaluatorCell {r : ℕ}
    (dtable dn : Code r) :
    (codeEvaluatorCell dtable dn).toFoundation =
      CategoricalRiceShapiro.Evaluator.codeEvaluatorCell
        dtable.toFoundation dn.toFoundation := by
  simp [codeEvaluatorCell,
    CategoricalRiceShapiro.Evaluator.codeEvaluatorCell]

@[simp] theorem toFoundation_codeEvaluatorRow {r : ℕ}
    (dtable : Code r) :
    (codeEvaluatorRow dtable).toFoundation =
      CategoricalRiceShapiro.Evaluator.codeEvaluatorRow dtable.toFoundation := by
  rw [codeEvaluatorRow,
    CategoricalRiceShapiro.Evaluator.codeEvaluatorRow_eq_bind]
  simp [Code.toFoundation]

@[simp] theorem toFoundation_codeEvaluatorTableStep {r : ℕ}
    (dtable : Code r) :
    (codeEvaluatorTableStep dtable).toFoundation =
      CategoricalRiceShapiro.Evaluator.codeEvaluatorTableStep
        dtable.toFoundation := by
  simp [codeEvaluatorTableStep,
    CategoricalRiceShapiro.Evaluator.codeEvaluatorTableStep]

@[simp] theorem toFoundation_codeEvaluatorHistory :
    codeEvaluatorHistory.toFoundation =
      CategoricalRiceShapiro.Evaluator.codeEvaluatorHistory := by
  simp [codeEvaluatorHistory,
    CategoricalRiceShapiro.Evaluator.codeEvaluatorHistory,
    Code.toFoundation]

@[simp] theorem toFoundation_codeHistoryEvaluator :
    codeHistoryEvaluator.toFoundation =
      CategoricalRiceShapiro.Evaluator.codeHistoryEvaluator := by
  simp [codeHistoryEvaluator,
    CategoricalRiceShapiro.Evaluator.codeHistoryEvaluator,
    Code.toFoundation, Matrix.fun_eq_vec_one]

end Construction

open CategoricalRiceShapiro.Evaluator

@[simp] theorem toFoundation_certificateFormula :
    Formula.toFoundation certificateFormula =
      (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  simp only [certificateFormula, Nat.reduceAdd, fin3_eq_three,
    Fin.isValue, fin0_eq_zero, fin1_eq_one, fin2_eq_two,
    Formula.toFoundation_subst, Compiler.toFoundation_code,
    Construction.toFoundation_codeHistoryEvaluator,
    Matrix.fun_eq_vec_four', Nat.succ_eq_add_one,
    Matrix.cons_val_zero, Term.toFoundation_add, Term.toFoundation_one,
    Matrix.cons_val_one, Matrix.cons_app_two, Matrix.cons_app_three,
    Fin.Fin1.eq_one, Matrix.cons_val_fin_one, evalnCertificateFormula,
    evalnGraphFormula, HierarchySymbol.Semiformula.val_rew,
    HierarchySymbol.Semiformula.val_mkSigma]
  apply congrArg (fun w ↦ w ▹
    FFL.FirstOrder.Arithmetic.code
      CategoricalRiceShapiro.Evaluator.codeHistoryEvaluator)
  apply Rew.ext
  · intro i
    refine Fin.cases ?_ (fun j ↦
      Fin.cases rfl (fun k ↦
        Fin.cases rfl (fun l ↦
          Fin.cases rfl (fun z ↦ Fin.elim0 z) l) k) j) i
    simp only [Term.toFoundation_bvar]
  · intro x
    exact Empty.elim x

@[simp] theorem toFoundation_eventualGraph (q : ℕ) :
    Formula.toFoundation (eventualGraph q) =
      (FailureOfComposition.ConcreteEvaluator.eventualGraph q).val := by
  unfold eventualGraph
  rw [Formula.toFoundation_exs, Formula.toFoundation_subst,
    toFoundation_certificateFormula]
  unfold FailureOfComposition.ConcreteEvaluator.eventualGraph
  simp only [HierarchySymbol.Semiformula.val_mkSigma]
  apply congrArg Semiformula.exs
  apply congrArg (fun w ↦ w ▹
    (evalnCertificateFormula : ArithmeticSemisentence 4))
  apply Rew.ext
  · intro i
    refine Fin.cases rfl (fun j ↦
      Fin.cases ?_ (fun k ↦
        Fin.cases rfl (fun l ↦
          Fin.cases rfl (fun z ↦ Fin.elim0 z) l) k) j) i
    exact Term.toFoundation_numeral q
  · intro x
    exact Empty.elim x

@[simp] theorem toFoundation_definedAtArgs {n : ℕ} (x : Term Empty n)
    (i : Fin 2) :
    Term.toFoundation
        (Fin.cases x.lift
          (Fin.cases (.bvar ⟨0, Nat.zero_lt_succ n⟩) Fin.elim0) i) =
      ![Rew.bShift (Term.toFoundation x),
        (#0 : ArithmeticSemiterm Empty (n + 1))] i := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [Fin.cases_zero,
      Matrix.cons_val_zero, Term.toFoundation_lift]
  · refine Fin.cases ?_ (fun z ↦ Fin.elim0 z) j
    rfl

@[simp] theorem toFoundation_definedAtArgs_one {n : ℕ}
    (x : Term Empty n) :
    Term.toFoundation
        (Fin.cases x.lift
          (fun _ : Fin 1 ↦ (.bvar ⟨0, Nat.zero_lt_succ n⟩))
          (1 : Fin 2)) =
      (#0 : ArithmeticSemiterm Empty (n + 1)) := by
  rfl

@[simp] theorem toFoundation_finCases_one {xi : Type} {n : ℕ}
    (a : Term xi n) (b : Fin 1 → Term xi n) :
    Term.toFoundation (Fin.cases a b (1 : Fin 2)) =
      Term.toFoundation (b 0) := by
  rfl

@[simp] theorem toFoundation_biimp {xi : Type} {n : ℕ}
    (p q : Formula xi n) :
    Formula.toFoundation (biimp p q) =
      LogicalConnective.iff (Formula.toFoundation p) (Formula.toFoundation q) := by
  unfold biimp
  rw [Formula.toFoundation_and, Formula.toFoundation_imply,
    Formula.toFoundation_imply]
  rfl

/-- The independent fixed-input Kleene-equality sentence is literally the
maintained manuscript sentence after translation. -/
@[simp] theorem toFoundation_kleeneEqAt (e d n : ℕ) :
    Formula.toFoundation
        (kleeneEqAt (eventualGraph e) (eventualGraph d) n) =
      FailureOfComposition.ProgramIndices.kleeneEqAt
        (FailureOfComposition.ConcreteEvaluator.eventualGraph e)
        (FailureOfComposition.ConcreteEvaluator.eventualGraph d) n := by
  simp [kleeneEqAt, kleeneEqTerm, definedAt, commonValueAt, biimp,
    FailureOfComposition.ProgramIndices.kleeneEqAt,
    LogicalConnective.iff, Matrix.fun_eq_vec_two,
    Formula.toFoundation_and, Formula.toFoundation_imply,
    Formula.toFoundation_exs, Formula.toFoundation_subst,
    Term.toFoundation_lift, Term.toFoundation_numeral,
    Term.toFoundation_bvar]

/-- The independent fixed-index evaluator formula, packaged at the Foundation
hierarchy boundary used by the maintained development. -/
def foundationEventualGraph (q : ℕ) :
    FailureOfComposition.ProofSearch.Graph :=
  .mkSigma (Formula.toFoundation (eventualGraph q)) (by
    rw [toFoundation_eventualGraph]
    exact HierarchySymbol.Semiformula.sigma_prop
      (FailureOfComposition.ConcreteEvaluator.eventualGraph q))

/-- Formula correspondence determines the packaged Sigma-one graph as well. -/
@[simp] theorem foundationEventualGraph_eq (q : ℕ) :
    foundationEventualGraph q =
      FailureOfComposition.ConcreteEvaluator.eventualGraph q := by
  have h := toFoundation_eventualGraph q
  unfold foundationEventualGraph
  cases hG : FailureOfComposition.ConcreteEvaluator.eventualGraph q with
  | mkSigma φ hφ =>
      rw [hG] at h
      simp only [HierarchySymbol.Semiformula.val_mkSigma] at h
      cases h
      rfl

/-- PA proves the universally quantified equivalence between the independent
fixed-index graph and the maintained concrete evaluator graph. -/
theorem eventualGraph_uniform_equivalence (q : ℕ) :
    FailureOfComposition.ProofSearch.Uniform 𝗣𝗔
      (foundationEventualGraph q)
      (FailureOfComposition.ConcreteEvaluator.eventualGraph q) := by
  rw [foundationEventualGraph_eq]
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff, FailureOfComposition.ProofSearch.uniformSentence]

@[simp] theorem identityIndex_toFoundation :
    identityIndex = FailureOfComposition.Kleene.identityIndex := by
  rw [FailureOfComposition.ConcreteWitnessGraphs.identityIndex_eq]
  rfl

@[simp] theorem emptyIndex_toFoundation :
    emptyIndex = FailureOfComposition.ConcreteEmptyGraph.concreteEmptyIndex := by
  rw [FailureOfComposition.ConcreteEmptyGraph.concreteEmptyIndex_eq]
  rfl

@[simp] theorem compIndex_toFoundation (f g : ℕ) :
    compIndex f g =
      CategoricalRiceShapiro.PartialRecursive.canonicalPartrecCompIndex f g := by
  rw [CategoricalRiceShapiro.PartialRecursive.canonicalPartrecCompIndex_eq]
  rfl

/-- Pointwise provability is preserved and reflected for every local theory;
the standard-input quantifier remains outside the proof predicate. -/
theorem pointwiseIndex_toFoundation_iff (T : Theory) (e d : ℕ) :
    PointwiseIndex T e d ↔
      FailureOfComposition.ConcreteIndices.PointwiseIndex
        (TheoryCorrespondence.toFoundation T) e d := by
  unfold PointwiseIndex FailureOfComposition.ConcreteIndices.PointwiseIndex
  constructor
  · intro h n
    rw [← toFoundation_kleeneEqAt]
    exact (provable_toFoundation_iff T _).mp (h n)
  · intro h n
    apply (provable_toFoundation_iff T _).mpr
    rw [toFoundation_kleeneEqAt]
    exact h n

end FailureOfComposition.Palomar.Arithmetic.Evaluator
