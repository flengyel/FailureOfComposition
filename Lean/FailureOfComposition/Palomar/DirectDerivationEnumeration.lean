/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.TheoryEnumerability
import FailureOfComposition.Palomar.ArithmeticBridge
import Foundation.FirstOrder.LK.Simplified

/-!
# Direct enumeration of independent arithmetic derivations

This module gives an external, effective certificate checker for the actual
independent LK calculus.  Its theorem-code enumeration uses finite evidence
from an r.e. axiom predicate; it does not decide theory membership or pass
through internal arithmetized provability.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open Encodable

namespace FailureOfComposition.Palomar.DirectDerivationEnumeration

open FailureOfComposition.Palomar.Arithmetic

theorem computable₂_of_eq {α β γ : Type*}
    [Primcodable α] [Primcodable β] [Primcodable γ]
    {f g : α → β → γ} (hf : Computable₂ f)
    (h : ∀ a b, f a b = g a b) : Computable₂ g :=
  hf.of_eq fun p ↦ h p.1 p.2

local instance termPrimcodable {ξ : Type} [Primcodable ξ] {n : ℕ} :
    Primcodable (FailureOfComposition.Palomar.Arithmetic.Term ξ n) :=
  Primcodable.ofEquiv (ArithmeticSemiterm ξ n)
    FailureOfComposition.Palomar.Arithmetic.Term.equivalence

local instance formulaPrimcodable {ξ : Type} [Primcodable ξ] {n : ℕ} :
    Primcodable (FailureOfComposition.Palomar.Arithmetic.Formula ξ n) :=
  Primcodable.ofEquiv (ArithmeticSemiformula ξ n)
    FailureOfComposition.Palomar.Arithmetic.Formula.equivalence

example : Primcodable (SyntacticTerm 0) := inferInstance
example : Primcodable Proposition := inferInstance
example : Primcodable (Semiproposition 1) := inferInstance
example : Primcodable Sentence := inferInstance

example {ξ : Type} [Primcodable ξ] {n : ℕ}
    (t : FailureOfComposition.Palomar.Arithmetic.Term ξ n) :
    Encodable.encode t = Encodable.encode t.toFoundation := rfl

example {ξ : Type} [Primcodable ξ] {n : ℕ}
    (p : FailureOfComposition.Palomar.Arithmetic.Formula ξ n) :
    Encodable.encode p = Encodable.encode p.toFoundation := rfl

def courseTable {α : Type*} (step : α → List ℕ → ℕ → ℕ)
    (a : α) : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
      let T := courseTable step a n
      T ++ [step a T n]

def courseEval {α : Type*} (step : α → List ℕ → ℕ → ℕ)
    (a : α) (n : ℕ) : ℕ :=
  (courseTable step a (n + 1)).getD n 0

@[simp] theorem courseTable_zero {α : Type*}
    (step : α → List ℕ → ℕ → ℕ) (a : α) :
    courseTable step a 0 = [] := rfl

theorem courseTable_succ {α : Type*}
    (step : α → List ℕ → ℕ → ℕ) (a : α) (n : ℕ) :
    courseTable step a (n + 1) =
      courseTable step a n ++ [step a (courseTable step a n) n] := rfl

@[simp] theorem courseTable_length {α : Type*}
    (step : α → List ℕ → ℕ → ℕ) (a : α) (n : ℕ) :
    (courseTable step a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [courseTable, ih]

theorem courseTable_getD {α : Type*}
    (step : α → List ℕ → ℕ → ℕ) (a : α) {j n : ℕ} (h : j < n) :
    (courseTable step a n).getD j 0 = courseEval step a j := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hj : j < n
      · rw [courseTable_succ, List.getD_append _ _ _ _ (by
          simpa [courseTable_length] using hj)]
        exact ih hj
      · have hje : j = n := by omega
        subst j
        simp [courseEval, courseTable, courseTable_length]

theorem courseEval_eq_step {α : Type*}
    (step : α → List ℕ → ℕ → ℕ) (a : α) (n : ℕ) :
    courseEval step a n = step a (courseTable step a n) n := by
  simp [courseEval, courseTable, courseTable_length]

theorem courseTable_computable {α : Type*} [Primcodable α]
    (step : α → List ℕ → ℕ → ℕ)
    (hstep : Computable (fun p : (α × List ℕ) × ℕ =>
      step p.1.1 p.1.2 p.2)) :
    Computable (fun p : α × ℕ => courseTable step p.1 p.2) := by
  have hnext : Computable₂ (fun p : α × ℕ => fun s : ℕ × List ℕ =>
      s.2 ++ [step p.1 s.2 s.1]) := by
    apply (Computable.list_append.comp
      (Computable.snd.comp Computable.snd)
      (Computable.list_cons.comp
        (hstep.comp (Computable.pair
          (Computable.pair (Computable.fst.comp Computable.fst)
            (Computable.snd.comp Computable.snd))
          (Computable.fst.comp Computable.snd)))
        (Computable.const []))).to₂
  exact (Computable.nat_rec Computable.snd (Computable.const []) hnext).of_eq (by
    intro p
    induction p.2 with
    | zero => rfl
    | succ n ih => simp [courseTable, ih])

theorem courseEval_computable {α : Type*} [Primcodable α]
    (step : α → List ℕ → ℕ → ℕ)
    (hstep : Computable (fun p : (α × List ℕ) × ℕ =>
      step p.1.1 p.1.2 p.2)) :
    Computable₂ (courseEval step) := by
  apply (Primrec.list_getD 0).to_comp.comp
    ((courseTable_computable step hstep).comp
      (Computable.pair Computable.fst
        (Computable.succ.comp Computable.snd)))
    Computable.snd

theorem courseTable_primrec {α : Type*} [Primcodable α]
    (step : α → List ℕ → ℕ → ℕ)
    (hstep : Primrec (fun p : (α × List ℕ) × ℕ =>
      step p.1.1 p.1.2 p.2)) :
    Primrec (fun p : α × ℕ => courseTable step p.1 p.2) := by
  have hnext : Primrec₂ (fun a : α => fun s : ℕ × List ℕ =>
      s.2 ++ [step a s.2 s.1]) := by
    apply (Primrec.list_append.comp
      (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp
        (hstep.comp (Primrec.pair
          (Primrec.pair Primrec.fst
            (Primrec.snd.comp Primrec.snd))
          (Primrec.fst.comp Primrec.snd)))
        (Primrec.const []))).to₂
  exact ((Primrec.nat_rec (Primrec.const []) hnext).comp
    Primrec.fst Primrec.snd).of_eq (by
    intro p
    induction p.2 with
    | zero => rfl
    | succ n ih =>
        rw [courseTable_succ]
        simp [ih])

theorem courseEval_primrec {α : Type*} [Primcodable α]
    (step : α → List ℕ → ℕ → ℕ)
    (hstep : Primrec (fun p : (α × List ℕ) × ℕ =>
      step p.1.1 p.1.2 p.2)) :
    Primrec₂ (courseEval step) := by
  apply (Primrec.list_getD 0).comp
    ((courseTable_primrec step hstep).comp
      (Primrec.pair Primrec.fst (Primrec.succ.comp Primrec.snd)))
    Primrec.snd

def listCode : List ℕ → ℕ :=
  List.foldr (fun x r ↦ Nat.pair x r + 1) 0

@[simp] theorem listCode_nil : listCode [] = 0 := rfl

@[simp] theorem listCode_cons (x : ℕ) (l : List ℕ) :
    listCode (x :: l) = Nat.pair x (listCode l) + 1 := rfl

theorem listCode_ofFn {k : ℕ} (v : Fin k → ℕ) :
    listCode (List.ofFn v) = Matrix.vecToNat v := by
  induction k with
  | zero => simp [listCode, Matrix.vecToNat]
  | succ k ih =>
      rw [List.ofFn_succ, listCode_cons, ih]
      simpa using (Matrix.encode_succ (v 0) (fun i ↦ v i.succ)).symm

theorem listCode_primrec : Primrec listCode := by
  have hp : Primrec fun l : List ℕ ↦
      l.foldr (fun x r ↦ Nat.pair x r + 1) 0 := by
    refine Primrec.list_foldr (β := ℕ) (σ := ℕ)
      (f := fun l : List ℕ ↦ l) (g := fun _ ↦ (0 : ℕ))
      (h := fun _ x ↦ Nat.pair x.1 x.2 + 1)
      Primrec.id (Primrec.const 0) ?_
    exact (Primrec.nat_add.comp
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))
      (Primrec.const 1)).to₂
  exact hp

def transformVec (T : List ℕ) (e : ℕ) : ℕ :=
  listCode ((Nat.natToList e).map fun j ↦ T.getD j 0)

@[simp] theorem transformVec_zero (T : List ℕ) : transformVec T 0 = 0 := by
  simp [transformVec, listCode, Nat.natToList]

theorem transformVec_primrec : Primrec₂ transformVec := by
  apply (listCode_primrec.comp (Primrec.list_map
    (Primrec.nat_natToList.comp Primrec.snd)
    ((Primrec.list_getD 0).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)).to₂

def pairSucc (x y : ℕ) : ℕ := Nat.pair x y + 1

theorem pairSucc_primrec : Primrec₂ pairSucc :=
  (Primrec.nat_add.comp (Primrec₂.natPair.comp Primrec.fst Primrec.snd)
    (Primrec.const 1)).to₂

abbrev TermAction := (ℕ × ℕ) × ℕ

def termTransformBody (a : TermAction) (depth : ℕ) (T : List ℕ) (d : ℕ) : ℕ :=
  if d.unpair.1 = 0 then
    let z := d.unpair.2
    if a.1.1 = 1 then
      if z < depth then pairSucc 0 z
      else if z = depth then a.1.2
      else pairSucc 0 (z - 1)
    else pairSucc 0 z
  else if d.unpair.1 = 1 then
    let x := d.unpair.2
    pairSucc 1 (if a.2 = 1 then x + 1 else x)
  else if d.unpair.1 = 2 then
    pairSucc 2 (Nat.pair d.unpair.2.unpair.1
      (Nat.pair d.unpair.2.unpair.2.unpair.1
        (transformVec T d.unpair.2.unpair.2.unpair.2)))
  else 0

def termTransformStep (a : TermAction × ℕ) (T : List ℕ) (e : ℕ) : ℕ :=
  match e with
  | 0 => 0
  | d + 1 => termTransformBody a.1 a.2 T d

theorem termTransformBody_primrec :
    Primrec (fun q : (((TermAction × ℕ) × List ℕ) × ℕ) ↦
      termTransformBody q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  let Q := (((TermAction × ℕ) × List ℕ) × ℕ)
  have hd : Primrec (fun q : Q ↦ q.2) := Primrec.snd
  have htag : Primrec (fun q : Q ↦ q.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hd)
  have hpayload : Primrec (fun q : Q ↦ q.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hd)
  have hdepth : Primrec (fun q : Q ↦ q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hsubst : Primrec (fun q : Q ↦ q.1.1.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hrepl : Primrec (fun q : Q ↦ q.1.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hshift : Primrec (fun q : Q ↦ q.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have htable : Primrec (fun q : Q ↦ q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hsame : Primrec (fun q : Q ↦ pairSucc 0 q.2.unpair.2) :=
    pairSucc_primrec.comp (Primrec.const 0) hpayload
  have hpred : Primrec (fun q : Q ↦ pairSucc 0 (q.2.unpair.2 - 1)) :=
    pairSucc_primrec.comp (Primrec.const 0)
      (Primrec.nat_sub.comp hpayload (Primrec.const 1))
  have hbvarSub : Primrec (fun q : Q ↦
      if q.2.unpair.2 < q.1.1.2 then pairSucc 0 q.2.unpair.2
      else if q.2.unpair.2 = q.1.1.2 then q.1.1.1.1.2
      else pairSucc 0 (q.2.unpair.2 - 1)) :=
    Primrec.ite (Primrec.nat_lt.comp hpayload hdepth) hsame
      (Primrec.ite (Primrec.eq.comp hpayload hdepth) hrepl hpred)
  have hbvar : Primrec (fun q : Q ↦
      if q.1.1.1.1.1 = 1 then
        (if q.2.unpair.2 < q.1.1.2 then pairSucc 0 q.2.unpair.2
        else if q.2.unpair.2 = q.1.1.2 then q.1.1.1.1.2
        else pairSucc 0 (q.2.unpair.2 - 1))
      else pairSucc 0 q.2.unpair.2) :=
    Primrec.ite (Primrec.eq.comp hsubst (Primrec.const 1)) hbvarSub hsame
  have hfvarPayload : Primrec (fun q : Q ↦
      if q.1.1.1.2 = 1 then q.2.unpair.2 + 1 else q.2.unpair.2) :=
    Primrec.ite (Primrec.eq.comp hshift (Primrec.const 1))
      (Primrec.nat_add.comp hpayload (Primrec.const 1)) hpayload
  have hfvar : Primrec (fun q : Q ↦ pairSucc 1
      (if q.1.1.1.2 = 1 then q.2.unpair.2 + 1 else q.2.unpair.2)) :=
    pairSucc_primrec.comp (Primrec.const 1) hfvarPayload
  have harity : Primrec (fun q : Q ↦ q.2.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hpayload)
  have hrest : Primrec (fun q : Q ↦ q.2.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hpayload)
  have hsymbol : Primrec (fun q : Q ↦ q.2.unpair.2.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hrest)
  have hvec : Primrec (fun q : Q ↦ q.2.unpair.2.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hrest)
  have htvec : Primrec (fun q : Q ↦
      transformVec q.1.2 q.2.unpair.2.unpair.2.unpair.2) :=
    transformVec_primrec.comp htable hvec
  have hfunc : Primrec (fun q : Q ↦ pairSucc 2
      (Nat.pair q.2.unpair.2.unpair.1
        (Nat.pair q.2.unpair.2.unpair.2.unpair.1
          (transformVec q.1.2 q.2.unpair.2.unpair.2.unpair.2)))) :=
    pairSucc_primrec.comp (Primrec.const 2)
      (Primrec₂.natPair.comp harity
        (Primrec₂.natPair.comp hsymbol htvec))
  exact (Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) hbvar
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) hfvar
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) hfunc
        (Primrec.const 0)))).of_eq (fun q ↦ by rfl)

theorem termTransformStep_primrec :
    Primrec (fun p : ((TermAction × ℕ) × List ℕ) × ℕ ↦
      termTransformStep p.1.1 p.1.2 p.2) := by
  let R := ((TermAction × ℕ) × List ℕ) × ℕ
  have hh : Primrec₂ (fun r : R ↦ fun d : ℕ ↦
      termTransformBody r.1.1.1 r.1.1.2 r.1.2 d) := by
    exact (termTransformBody_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
  have h : Primrec (fun r : R ↦ termTransformStep r.1.1 r.1.2 r.2) := by
    exact (Primrec.nat_casesOn (f := fun r : R ↦ r.2)
      (g := fun _ ↦ (0 : ℕ))
      (h := fun r d ↦ termTransformBody r.1.1.1 r.1.1.2 r.1.2 d)
      Primrec.snd (Primrec.const 0) hh).of_eq (fun r ↦ by
        cases r.2 <;> rfl)
  exact h

theorem termTransformStep_computable :
    Computable (fun p : ((TermAction × ℕ) × List ℕ) × ℕ ↦
      termTransformStep p.1.1 p.1.2 p.2) :=
  termTransformStep_primrec.to_comp

def termTransformCode (a : TermAction) (depth e : ℕ) : ℕ :=
  courseEval termTransformStep (a, depth) e

theorem termTransformCode_computable :
    Computable (fun p : (TermAction × ℕ) × ℕ ↦
      termTransformCode p.1.1 p.1.2 p.2) := by
  exact (courseEval_computable termTransformStep
    termTransformStep_computable).comp Computable.fst Computable.snd

theorem termTransformCode_primrec :
    Primrec (fun p : (TermAction × ℕ) × ℕ ↦
      termTransformCode p.1.1 p.1.2 p.2) := by
  exact (courseEval_primrec termTransformStep
    termTransformStep_primrec).comp Primrec.fst Primrec.snd

namespace DirectTerm

@[simp] theorem encode_bvar {n : ℕ} (i : Fin n) :
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Term.bvar i :
        FailureOfComposition.Palomar.Arithmetic.Term ℕ n) =
      pairSucc 0 i := rfl

@[simp] theorem encode_fvar {n : ℕ} (x : ℕ) :
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Term.fvar x :
        FailureOfComposition.Palomar.Arithmetic.Term ℕ n) =
      pairSucc 1 x := rfl

@[simp] theorem encode_zero {n : ℕ} :
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Term.zero :
        FailureOfComposition.Palomar.Arithmetic.Term ℕ n) =
      pairSucc 2 (Nat.pair 0 (Nat.pair 0 0)) := rfl

@[simp] theorem encode_one {n : ℕ} :
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Term.one :
        FailureOfComposition.Palomar.Arithmetic.Term ℕ n) =
      pairSucc 2 (Nat.pair 0 (Nat.pair 1 0)) := rfl

@[simp] theorem encode_add {n : ℕ}
    (s t : FailureOfComposition.Palomar.Arithmetic.Term ℕ n) :
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Term.add s t) =
      pairSucc 2 (Nat.pair 2 (Nat.pair 0
        (listCode [Encodable.encode s, Encodable.encode t]))) := by
  change Encodable.encode
    (FailureOfComposition.Palomar.Arithmetic.Term.toFoundation
      (FailureOfComposition.Palomar.Arithmetic.Term.add s t)) = _
  rfl

@[simp] theorem encode_mul {n : ℕ}
    (s t : FailureOfComposition.Palomar.Arithmetic.Term ℕ n) :
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Term.mul s t) =
      pairSucc 2 (Nat.pair 2 (Nat.pair 1
        (listCode [Encodable.encode s, Encodable.encode t]))) := by
  change Encodable.encode
    (FailureOfComposition.Palomar.Arithmetic.Term.toFoundation
      (FailureOfComposition.Palomar.Arithmetic.Term.mul s t)) = _
  rfl

theorem transformVec_two (T : List ℕ) {a b a' b' : ℕ}
    (ha : T.getD a 0 = a') (hb : T.getD b 0 = b') :
    transformVec T (listCode [a, b]) = listCode [a', b'] := by
  have ha' : T[a]?.getD 0 = a' := by
    simpa only [List.getD_eq_getElem?_getD] using ha
  have hb' : T[b]?.getD 0 = b' := by
    simpa only [List.getD_eq_getElem?_getD] using hb
  simp [transformVec, listCode, Nat.natToList, ha', hb']

theorem left_lt_binaryTermCode (a b symbol : ℕ) :
    a < pairSucc 2 (Nat.pair 2 (Nat.pair symbol (listCode [a, b]))) := by
  let tail := Nat.pair b 0 + 1
  let vec := Nat.pair a tail + 1
  have hav : a ≤ vec := le_trans (Nat.left_le_pair a tail) (Nat.le_add_right _ 1)
  have hv₁ : vec ≤ Nat.pair symbol vec := Nat.right_le_pair _ _
  have hv₂ : Nat.pair symbol vec ≤ Nat.pair 2 (Nat.pair symbol vec) :=
    Nat.right_le_pair _ _
  have hv₃ : Nat.pair 2 (Nat.pair symbol vec) ≤
      Nat.pair 2 (Nat.pair 2 (Nat.pair symbol vec)) := Nat.right_le_pair _ _
  apply Nat.lt_succ_of_le
  simpa [tail, vec, pairSucc, listCode] using hav.trans (hv₁.trans (hv₂.trans hv₃))

theorem right_lt_binaryTermCode (a b symbol : ℕ) :
    b < pairSucc 2 (Nat.pair 2 (Nat.pair symbol (listCode [a, b]))) := by
  let tail := Nat.pair b 0 + 1
  let vec := Nat.pair a tail + 1
  have hbt : b ≤ tail := le_trans (Nat.left_le_pair b 0) (Nat.le_add_right _ 1)
  have htv : tail ≤ vec := le_trans (Nat.right_le_pair a tail) (Nat.le_add_right _ 1)
  have hv₁ : vec ≤ Nat.pair symbol vec := Nat.right_le_pair _ _
  have hv₂ : Nat.pair symbol vec ≤ Nat.pair 2 (Nat.pair symbol vec) :=
    Nat.right_le_pair _ _
  have hv₃ : Nat.pair 2 (Nat.pair symbol vec) ≤
      Nat.pair 2 (Nat.pair 2 (Nat.pair symbol vec)) := Nat.right_le_pair _ _
  apply Nat.lt_succ_of_le
  simpa [tail, vec, pairSucc, listCode] using
    hbt.trans (htv.trans (hv₁.trans (hv₂.trans hv₃)))

theorem encode_lt_add_left {n : ℕ}
    (s t : FailureOfComposition.Palomar.Arithmetic.Term ℕ n) :
    Encodable.encode s < Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Term.add s t) := by
  rw [encode_add]
  exact left_lt_binaryTermCode _ _ 0

theorem encode_lt_add_right {n : ℕ}
    (s t : FailureOfComposition.Palomar.Arithmetic.Term ℕ n) :
    Encodable.encode t < Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Term.add s t) := by
  rw [encode_add]
  exact right_lt_binaryTermCode _ _ 0

theorem encode_lt_mul_left {n : ℕ}
    (s t : FailureOfComposition.Palomar.Arithmetic.Term ℕ n) :
    Encodable.encode s < Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Term.mul s t) := by
  rw [encode_mul]
  exact left_lt_binaryTermCode _ _ 1

theorem encode_lt_mul_right {n : ℕ}
    (s t : FailureOfComposition.Palomar.Arithmetic.Term ℕ n) :
    Encodable.encode t < Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Term.mul s t) := by
  rw [encode_mul]
  exact right_lt_binaryTermCode _ _ 1

def liftClosed {d : ℕ} :
    FailureOfComposition.Palomar.Arithmetic.Term ℕ 0 →
      FailureOfComposition.Palomar.Arithmetic.Term ℕ d
  | .bvar i => Fin.elim0 i
  | .fvar x => .fvar x
  | .zero => .zero
  | .one => .one
  | .add s t => .add (liftClosed s) (liftClosed t)
  | .mul s t => .mul (liftClosed s) (liftClosed t)

@[simp] theorem encode_liftClosed {d : ℕ}
    (t : FailureOfComposition.Palomar.Arithmetic.Term ℕ 0) :
    Encodable.encode (liftClosed (d := d) t) = Encodable.encode t := by
  induction t with
  | bvar i => exact Fin.elim0 i
  | fvar x => rfl
  | zero => rfl
  | one => rfl
  | add s t ihs iht => simp [liftClosed, ihs, iht]
  | mul s t ihs iht => simp [liftClosed, ihs, iht]

def shiftFree {d : ℕ} :
    FailureOfComposition.Palomar.Arithmetic.Term ℕ d →
      FailureOfComposition.Palomar.Arithmetic.Term ℕ d
  | .bvar i => .bvar i
  | .fvar x => .fvar (x + 1)
  | .zero => .zero
  | .one => .one
  | .add s t => .add (shiftFree s) (shiftFree t)
  | .mul s t => .mul (shiftFree s) (shiftFree t)

theorem encode_shiftFree (depth : ℕ) {d : ℕ}
    (t : FailureOfComposition.Palomar.Arithmetic.Term ℕ d) :
    termTransformCode ((0, 0), 1) depth (Encodable.encode t) =
      Encodable.encode (shiftFree t) := by
  induction t with
  | bvar i =>
      simp [termTransformCode, courseEval_eq_step, termTransformStep,
        termTransformBody, pairSucc, shiftFree]
  | fvar x =>
      simp [termTransformCode, courseEval_eq_step, termTransformStep,
        termTransformBody, pairSucc, shiftFree]
  | zero =>
      simp [termTransformCode, courseEval_eq_step, termTransformStep,
        termTransformBody, pairSucc, shiftFree]
  | one =>
      simp [termTransformCode, courseEval_eq_step, termTransformStep,
        termTransformBody, pairSucc, shiftFree]
  | add s t ihs iht =>
      let T := courseTable termTransformStep (((0, 0), 1), depth)
        (Encodable.encode (FailureOfComposition.Palomar.Arithmetic.Term.add s t))
      have hs : T.getD (Encodable.encode s) 0 =
          Encodable.encode (shiftFree s) := by
        rw [show T.getD (Encodable.encode s) 0 =
          termTransformCode ((0, 0), 1) depth (Encodable.encode s) by
            exact courseTable_getD termTransformStep (((0, 0), 1), depth)
              (encode_lt_add_left s t)]
        exact ihs
      have ht : T.getD (Encodable.encode t) 0 =
          Encodable.encode (shiftFree t) := by
        rw [show T.getD (Encodable.encode t) 0 =
          termTransformCode ((0, 0), 1) depth (Encodable.encode t) by
            exact courseTable_getD termTransformStep (((0, 0), 1), depth)
              (encode_lt_add_right s t)]
        exact iht
      have hv : transformVec T (listCode [Encodable.encode s, Encodable.encode t]) =
          listCode [Encodable.encode (shiftFree s),
            Encodable.encode (shiftFree t)] := transformVec_two T hs ht
      rw [termTransformCode, courseEval_eq_step]
      change termTransformBody ((0, 0), 1) depth T
        (Nat.pair 2 (Nat.pair 2 (Nat.pair 0
          (listCode [Encodable.encode s, Encodable.encode t])))) = _
      simp [termTransformBody, shiftFree]
      simpa [listCode] using congrArg
        (fun x ↦ pairSucc 2 (Nat.pair 2 (Nat.pair 0 x))) hv
  | mul s t ihs iht =>
      let T := courseTable termTransformStep (((0, 0), 1), depth)
        (Encodable.encode (FailureOfComposition.Palomar.Arithmetic.Term.mul s t))
      have hs : T.getD (Encodable.encode s) 0 =
          Encodable.encode (shiftFree s) := by
        rw [show T.getD (Encodable.encode s) 0 =
          termTransformCode ((0, 0), 1) depth (Encodable.encode s) by
            exact courseTable_getD termTransformStep (((0, 0), 1), depth)
              (encode_lt_mul_left s t)]
        exact ihs
      have ht : T.getD (Encodable.encode t) 0 =
          Encodable.encode (shiftFree t) := by
        rw [show T.getD (Encodable.encode t) 0 =
          termTransformCode ((0, 0), 1) depth (Encodable.encode t) by
            exact courseTable_getD termTransformStep (((0, 0), 1), depth)
              (encode_lt_mul_right s t)]
        exact iht
      have hv : transformVec T (listCode [Encodable.encode s, Encodable.encode t]) =
          listCode [Encodable.encode (shiftFree s),
            Encodable.encode (shiftFree t)] := transformVec_two T hs ht
      rw [termTransformCode, courseEval_eq_step]
      change termTransformBody ((0, 0), 1) depth T
        (Nat.pair 2 (Nat.pair 2 (Nat.pair 1
          (listCode [Encodable.encode s, Encodable.encode t])))) = _
      simp [termTransformBody, shiftFree]
      simpa [listCode] using congrArg
        (fun x ↦ pairSucc 2 (Nat.pair 2 (Nat.pair 1 x))) hv

def dropBound (replacement : FailureOfComposition.Palomar.Arithmetic.Term ℕ 0)
    (shift : Bool) (d : ℕ) :
    FailureOfComposition.Palomar.Arithmetic.Term ℕ (d + 1) →
      FailureOfComposition.Palomar.Arithmetic.Term ℕ d
  | .bvar i =>
      if h : (i : ℕ) < d then .bvar ⟨i, h⟩ else liftClosed replacement
  | .fvar x => .fvar (if shift then x + 1 else x)
  | .zero => .zero
  | .one => .one
  | .add s t => .add (dropBound replacement shift d s)
      (dropBound replacement shift d t)
  | .mul s t => .mul (dropBound replacement shift d s)
      (dropBound replacement shift d t)

theorem encode_dropBound
    (replacement : FailureOfComposition.Palomar.Arithmetic.Term ℕ 0)
    (shift : Bool) (d : ℕ)
    (t : FailureOfComposition.Palomar.Arithmetic.Term ℕ (d + 1)) :
    termTransformCode
        ((1, Encodable.encode replacement), if shift then 1 else 0)
        d (Encodable.encode t) =
      Encodable.encode (dropBound replacement shift d t) := by
  induction t with
  | bvar i =>
      by_cases h : (i : ℕ) < d
      · simp [termTransformCode, courseEval_eq_step, termTransformStep,
          termTransformBody, pairSucc, dropBound, h]
      · have hi : (i : ℕ) = d := by omega
        simp [termTransformCode, courseEval_eq_step, termTransformStep,
          termTransformBody, pairSucc, dropBound, hi]
  | fvar x =>
      cases shift <;>
        simp [termTransformCode, courseEval_eq_step, termTransformStep,
          termTransformBody, pairSucc, dropBound]
  | zero =>
      simp [termTransformCode, courseEval_eq_step, termTransformStep,
        termTransformBody, pairSucc, dropBound]
  | one =>
      simp [termTransformCode, courseEval_eq_step, termTransformStep,
        termTransformBody, pairSucc, dropBound]
  | add s t ihs iht =>
      let a : TermAction :=
        ((1, Encodable.encode replacement), if shift then 1 else 0)
      let T := courseTable termTransformStep (a, d)
        (Encodable.encode (FailureOfComposition.Palomar.Arithmetic.Term.add s t))
      have hs : T.getD (Encodable.encode s) 0 =
          Encodable.encode (dropBound replacement shift d s) := by
        rw [show T.getD (Encodable.encode s) 0 =
          termTransformCode a d (Encodable.encode s) by
            exact courseTable_getD termTransformStep (a, d)
              (encode_lt_add_left s t)]
        exact ihs
      have ht : T.getD (Encodable.encode t) 0 =
          Encodable.encode (dropBound replacement shift d t) := by
        rw [show T.getD (Encodable.encode t) 0 =
          termTransformCode a d (Encodable.encode t) by
            exact courseTable_getD termTransformStep (a, d)
              (encode_lt_add_right s t)]
        exact iht
      have hv : transformVec T (listCode [Encodable.encode s, Encodable.encode t]) =
          listCode [Encodable.encode (dropBound replacement shift d s),
            Encodable.encode (dropBound replacement shift d t)] :=
        transformVec_two T hs ht
      rw [termTransformCode, courseEval_eq_step]
      change termTransformBody a d T
        (Nat.pair 2 (Nat.pair 2 (Nat.pair 0
          (listCode [Encodable.encode s, Encodable.encode t])))) = _
      simp [termTransformBody, dropBound]
      simpa [listCode] using congrArg
        (fun x ↦ pairSucc 2 (Nat.pair 2 (Nat.pair 0 x))) hv
  | mul s t ihs iht =>
      let a : TermAction :=
        ((1, Encodable.encode replacement), if shift then 1 else 0)
      let T := courseTable termTransformStep (a, d)
        (Encodable.encode (FailureOfComposition.Palomar.Arithmetic.Term.mul s t))
      have hs : T.getD (Encodable.encode s) 0 =
          Encodable.encode (dropBound replacement shift d s) := by
        rw [show T.getD (Encodable.encode s) 0 =
          termTransformCode a d (Encodable.encode s) by
            exact courseTable_getD termTransformStep (a, d)
              (encode_lt_mul_left s t)]
        exact ihs
      have ht : T.getD (Encodable.encode t) 0 =
          Encodable.encode (dropBound replacement shift d t) := by
        rw [show T.getD (Encodable.encode t) 0 =
          termTransformCode a d (Encodable.encode t) by
            exact courseTable_getD termTransformStep (a, d)
              (encode_lt_mul_right s t)]
        exact iht
      have hv : transformVec T (listCode [Encodable.encode s, Encodable.encode t]) =
          listCode [Encodable.encode (dropBound replacement shift d s),
            Encodable.encode (dropBound replacement shift d t)] :=
        transformVec_two T hs ht
      rw [termTransformCode, courseEval_eq_step]
      change termTransformBody a d T
        (Nat.pair 2 (Nat.pair 2 (Nat.pair 1
          (listCode [Encodable.encode s, Encodable.encode t])))) = _
      simp [termTransformBody, dropBound]
      simpa [listCode] using congrArg
        (fun x ↦ pairSucc 2 (Nat.pair 2 (Nat.pair 1 x))) hv

theorem encode_identity (depth : ℕ) {d : ℕ}
    (t : FailureOfComposition.Palomar.Arithmetic.Term ℕ d) :
    termTransformCode ((2, 0), 0) depth (Encodable.encode t) =
      Encodable.encode t := by
  induction t with
  | bvar i =>
      simp [termTransformCode, courseEval_eq_step, termTransformStep,
        termTransformBody, pairSucc]
  | fvar x =>
      simp [termTransformCode, courseEval_eq_step, termTransformStep,
        termTransformBody, pairSucc]
  | zero =>
      simp [termTransformCode, courseEval_eq_step, termTransformStep,
        termTransformBody, pairSucc]
  | one =>
      simp [termTransformCode, courseEval_eq_step, termTransformStep,
        termTransformBody, pairSucc]
  | add s t ihs iht =>
      let T := courseTable termTransformStep (((2, 0), 0), depth)
        (Encodable.encode (FailureOfComposition.Palomar.Arithmetic.Term.add s t))
      have hs : T.getD (Encodable.encode s) 0 = Encodable.encode s := by
        rw [show T.getD (Encodable.encode s) 0 =
          termTransformCode ((2, 0), 0) depth (Encodable.encode s) by
            exact courseTable_getD termTransformStep (((2, 0), 0), depth)
              (encode_lt_add_left s t)]
        exact ihs
      have ht : T.getD (Encodable.encode t) 0 = Encodable.encode t := by
        rw [show T.getD (Encodable.encode t) 0 =
          termTransformCode ((2, 0), 0) depth (Encodable.encode t) by
            exact courseTable_getD termTransformStep (((2, 0), 0), depth)
              (encode_lt_add_right s t)]
        exact iht
      have hv : transformVec T (listCode [Encodable.encode s, Encodable.encode t]) =
          listCode [Encodable.encode s, Encodable.encode t] :=
        transformVec_two T hs ht
      rw [termTransformCode, courseEval_eq_step]
      change termTransformBody ((2, 0), 0) depth T
        (Nat.pair 2 (Nat.pair 2 (Nat.pair 0
          (listCode [Encodable.encode s, Encodable.encode t])))) = _
      simp [termTransformBody]
      simpa [listCode] using congrArg
        (fun x ↦ pairSucc 2 (Nat.pair 2 (Nat.pair 0 x))) hv
  | mul s t ihs iht =>
      let T := courseTable termTransformStep (((2, 0), 0), depth)
        (Encodable.encode (FailureOfComposition.Palomar.Arithmetic.Term.mul s t))
      have hs : T.getD (Encodable.encode s) 0 = Encodable.encode s := by
        rw [show T.getD (Encodable.encode s) 0 =
          termTransformCode ((2, 0), 0) depth (Encodable.encode s) by
            exact courseTable_getD termTransformStep (((2, 0), 0), depth)
              (encode_lt_mul_left s t)]
        exact ihs
      have ht : T.getD (Encodable.encode t) 0 = Encodable.encode t := by
        rw [show T.getD (Encodable.encode t) 0 =
          termTransformCode ((2, 0), 0) depth (Encodable.encode t) by
            exact courseTable_getD termTransformStep (((2, 0), 0), depth)
              (encode_lt_mul_right s t)]
        exact iht
      have hv : transformVec T (listCode [Encodable.encode s, Encodable.encode t]) =
          listCode [Encodable.encode s, Encodable.encode t] :=
        transformVec_two T hs ht
      rw [termTransformCode, courseEval_eq_step]
      change termTransformBody ((2, 0), 0) depth T
        (Nat.pair 2 (Nat.pair 2 (Nat.pair 1
          (listCode [Encodable.encode s, Encodable.encode t])))) = _
      simp [termTransformBody]
      simpa [listCode] using congrArg
        (fun x ↦ pairSucc 2 (Nat.pair 2 (Nat.pair 1 x))) hv

end DirectTerm

def transformTermVec (a : TermAction) (depth : ℕ) (e : ℕ) : ℕ :=
  listCode ((Nat.natToList e).map fun j ↦ termTransformCode a depth j)

@[simp] theorem transformTermVec_zero (a : TermAction) (depth : ℕ) :
    transformTermVec a depth 0 = 0 := by
  simp [transformTermVec, listCode, Nat.natToList]

theorem transformTermVec_primrec :
    Primrec (fun q : (TermAction × ℕ) × ℕ ↦
      transformTermVec q.1.1 q.1.2 q.2) := by
  apply listCode_primrec.comp
  exact Primrec.list_map
    (Primrec.nat_natToList.comp Primrec.snd)
    (termTransformCode_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))

theorem transformTermVec_two (a : TermAction) (depth : ℕ)
    {s t s' t' : ℕ}
    (hs : termTransformCode a depth s = s')
    (ht : termTransformCode a depth t = t') :
    transformTermVec a depth (listCode [s, t]) = listCode [s', t'] := by
  simp [transformTermVec, listCode, Nat.natToList, hs, ht]

abbrev FormulaState := ℕ

def packFormulaState (a : TermAction) (depth code : ℕ) : FormulaState :=
  Nat.pair a.1.1 (Nat.pair a.1.2 (Nat.pair a.2 (Nat.pair depth code)))

def formulaStateSubst (b : FormulaState) : ℕ := b.unpair.1
def formulaStateReplacement (b : FormulaState) : ℕ := b.unpair.2.unpair.1
def formulaStateShift (b : FormulaState) : ℕ := b.unpair.2.unpair.2.unpair.1
def formulaStateDepth (b : FormulaState) : ℕ :=
  b.unpair.2.unpair.2.unpair.2.unpair.1
def formulaStateCode (b : FormulaState) : ℕ :=
  b.unpair.2.unpair.2.unpair.2.unpair.2

def formulaStateAction (b : FormulaState) : TermAction :=
  ((formulaStateSubst b, formulaStateReplacement b), formulaStateShift b)

@[simp] theorem formulaStateAction_pack (a : TermAction) (depth code : ℕ) :
    formulaStateAction (packFormulaState a depth code) = a := by
  simp [formulaStateAction, formulaStateSubst, formulaStateReplacement,
    formulaStateShift, packFormulaState]

@[simp] theorem formulaStateDepth_pack (a : TermAction) (depth code : ℕ) :
    formulaStateDepth (packFormulaState a depth code) = depth := by
  simp [formulaStateDepth, packFormulaState]

@[simp] theorem formulaStateCode_pack (a : TermAction) (depth code : ℕ) :
    formulaStateCode (packFormulaState a depth code) = code := by
  simp [formulaStateCode, packFormulaState]

def formulaSubArgs (b : FormulaState) : List FormulaState :=
  (FFL.FirstOrder.Semiformula.subArgs
    (formulaStateDepth b, formulaStateCode b)).map
    fun c ↦ packFormulaState (formulaStateAction b) c.1 c.2

def formulaAtomPayload (a : TermAction) (depth : ℕ) (e : ℕ) : ℕ :=
  let c := e.unpair.2
  Nat.pair c.unpair.1
    (Nat.pair c.unpair.2.unpair.1
      (transformTermVec a depth c.unpair.2.unpair.2))

def negateFormulaTag (tag : ℕ) : ℕ :=
  if tag = 0 then 1
  else if tag = 1 then 0
  else if tag = 2 then 3
  else if tag = 3 then 2
  else if tag = 4 then 5
  else if tag = 5 then 4
  else if tag = 6 then 7
  else if tag = 7 then 6
  else tag

def formulaOutputTag (a : TermAction) (tag : ℕ) : ℕ :=
  if a.1.1 = 2 then negateFormulaTag tag else tag

@[simp] theorem formulaOutputTag_subst_zero (replacement shift tag : ℕ) :
    formulaOutputTag ((0, replacement), shift) tag = tag := by
  simp [formulaOutputTag]

@[simp] theorem formulaOutputTag_subst_one (replacement shift tag : ℕ) :
    formulaOutputTag ((1, replacement), shift) tag = tag := by
  simp [formulaOutputTag]

def formulaQuantArm (tag v0 : ℕ) : ℕ :=
  if tag < 8 then pairSucc tag v0 else 0

def formulaBinaryOrQuantArm (tag v0 v1 : ℕ) : ℕ :=
  if tag < 6 then pairSucc tag (Nat.pair v0 v1)
  else formulaQuantArm tag v0

def formulaConstOrRestArm (tag v0 v1 : ℕ) : ℕ :=
  if tag < 4 then pairSucc tag 0
  else formulaBinaryOrQuantArm tag v0 v1

def formulaAtomicOrRestArm (tag atomPayload v0 v1 : ℕ) : ℕ :=
  if tag < 2 then pairSucc tag atomPayload
  else formulaConstOrRestArm tag v0 v1

def formulaTransformBody (a : TermAction) (depth : ℕ)
    (vs : List ℕ) (e : ℕ) : ℕ :=
  formulaAtomicOrRestArm (formulaOutputTag a e.unpair.1)
    (formulaAtomPayload a depth e)
    (vs.getD 0 0) (vs.getD 1 0)

theorem formulaTransformBody_eq (a : TermAction) (depth : ℕ)
    (vs : List ℕ) (e : ℕ) :
    formulaTransformBody a depth vs e =
      formulaAtomicOrRestArm (formulaOutputTag a e.unpair.1)
        (formulaAtomPayload a depth e)
        (vs.getD 0 0) (vs.getD 1 0) := rfl

@[irreducible] def formulaTransformSuccessor
    (b : FormulaState) (vs : List ℕ) (e : ℕ) : ℕ :=
  formulaAtomicOrRestArm
    (formulaOutputTag (formulaStateAction b) e.unpair.1)
    (formulaAtomPayload (formulaStateAction b) (formulaStateDepth b) e)
    (vs.getD 0 0) (vs.getD 1 0)

theorem formulaTransformSuccessor_eq
    (b : FormulaState) (vs : List ℕ) (e : ℕ) :
    formulaTransformSuccessor b vs e =
      formulaAtomicOrRestArm
        (formulaOutputTag (formulaStateAction b) e.unpair.1)
        (formulaAtomPayload (formulaStateAction b) (formulaStateDepth b) e)
        (vs.getD 0 0) (vs.getD 1 0) := by
  rw [formulaTransformSuccessor]

@[irreducible] def formulaTransformRaw
    (b : FormulaState) (vs : List ℕ) : ℕ :=
  Nat.casesOn (formulaStateCode b) 0 (formulaTransformSuccessor b vs)

theorem formulaTransformRaw_eq (b : FormulaState) (vs : List ℕ) :
    formulaTransformRaw b vs =
      Nat.casesOn (formulaStateCode b) 0 (formulaTransformSuccessor b vs) := by
  rw [formulaTransformRaw]

@[irreducible] def formulaTransformStep
    (b : FormulaState) (vs : List ℕ) : ℕ :=
  formulaTransformRaw b vs

theorem formulaTransformStep_eq (b : FormulaState) (vs : List ℕ) :
    formulaTransformStep b vs = formulaTransformRaw b vs := by
  rw [formulaTransformStep]

theorem formula_left_lt (e : ℕ) : e.unpair.2.unpair.1 < e + 1 :=
  Nat.lt_succ_of_le ((Nat.unpair_left_le _).trans (Nat.unpair_right_le _))

theorem formula_right_lt (e : ℕ) : e.unpair.2.unpair.2 < e + 1 :=
  Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _))

theorem formula_quant_lt (e : ℕ) : e.unpair.2 < e + 1 :=
  Nat.lt_succ_of_le (Nat.unpair_right_le _)

theorem formula_left_le (e : ℕ) : e.unpair.2.unpair.1 ≤ e :=
  (Nat.unpair_left_le _).trans (Nat.unpair_right_le _)

theorem formula_right_le (e : ℕ) : e.unpair.2.unpair.2 ≤ e :=
  (Nat.unpair_right_le _).trans (Nat.unpair_right_le _)

theorem formula_quant_le (e : ℕ) : e.unpair.2 ≤ e :=
  Nat.unpair_right_le _

def formulaTransformCode (a : TermAction) (depth : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 =>
      let tag := e.unpair.1
      let c := e.unpair.2
      let vs :=
        if tag = 4 ∨ tag = 5 then
          [formulaTransformCode a depth c.unpair.1,
            formulaTransformCode a depth c.unpair.2]
        else if tag = 6 ∨ tag = 7 then
          [formulaTransformCode a (depth + 1) c]
        else []
      formulaTransformBody a depth vs e
termination_by e => e
decreasing_by
  all_goals simp_wf
  all_goals first | exact formula_left_le _ | exact formula_right_le _ |
    exact formula_quant_le _

def formulaTransform (b : FormulaState) : ℕ :=
  formulaTransformCode (formulaStateAction b) (formulaStateDepth b)
    (formulaStateCode b)

theorem formulaStateAction_primrec : Primrec formulaStateAction := by
  have hsubst : Primrec formulaStateSubst :=
    Primrec.fst.comp Primrec.unpair
  have hrest₁ : Primrec (fun b : ℕ ↦ b.unpair.2) :=
    Primrec.snd.comp Primrec.unpair
  have hrepl : Primrec formulaStateReplacement :=
    Primrec.fst.comp (Primrec.unpair.comp hrest₁)
  have hrest₂ : Primrec (fun b : ℕ ↦ b.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hrest₁)
  have hshift : Primrec formulaStateShift :=
    Primrec.fst.comp (Primrec.unpair.comp hrest₂)
  exact (Primrec.pair (Primrec.pair hsubst hrepl) hshift).of_eq
    (fun _ ↦ by rfl)

theorem formulaStateDepth_primrec : Primrec formulaStateDepth := by
  exact (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp Primrec.unpair))))))).of_eq (fun _ ↦ by rfl)

theorem formulaStateCode_primrec : Primrec formulaStateCode := by
  exact (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp Primrec.unpair))))))).of_eq (fun _ ↦ by rfl)

theorem formulaSubArgs_primrec : Primrec formulaSubArgs := by
  have hbase : Primrec (fun b : FormulaState ↦
      FFL.FirstOrder.Semiformula.subArgs
        (formulaStateDepth b, formulaStateCode b)) :=
    FFL.FirstOrder.Semiformula.primrec_subArgs.comp
      (Primrec.pair formulaStateDepth_primrec formulaStateCode_primrec)
  have hmapper : Primrec (fun q : FormulaState × (ℕ × ℕ) ↦
      packFormulaState (formulaStateAction q.1) q.2.1 q.2.2) := by
    have hsubst : Primrec (fun q : FormulaState × (ℕ × ℕ) ↦
        formulaStateSubst q.1) :=
      (Primrec.fst.comp Primrec.unpair).comp Primrec.fst
    have hrepl : Primrec (fun q : FormulaState × (ℕ × ℕ) ↦
        formulaStateReplacement q.1) := by
      exact (Primrec.fst.comp (Primrec.unpair.comp
        (Primrec.snd.comp Primrec.unpair))).comp Primrec.fst
    have hshift : Primrec (fun q : FormulaState × (ℕ × ℕ) ↦
        formulaStateShift q.1) := by
      exact (Primrec.fst.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp
          (Primrec.snd.comp Primrec.unpair))))).comp Primrec.fst
    exact (Primrec₂.natPair.comp hsubst
      (Primrec₂.natPair.comp hrepl
        (Primrec₂.natPair.comp hshift
          (Primrec₂.natPair.comp
            (Primrec.fst.comp Primrec.snd)
            (Primrec.snd.comp Primrec.snd))))).of_eq (fun _ ↦ by rfl)
  exact (Primrec.list_map hbase hmapper.to₂).of_eq (fun _ ↦ by rfl)

theorem formulaSubArgs_ord (b : FormulaState) :
    ∀ b' ∈ formulaSubArgs b,
      formulaStateCode b' < formulaStateCode b := by
  intro b' hb'
  rw [formulaSubArgs] at hb'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb'
  simpa using FFL.FirstOrder.Semiformula.subArgs_ord
    (formulaStateDepth b, formulaStateCode b) c hc

theorem formulaAtomPayload_primrec :
    Primrec (fun q : (TermAction × ℕ) × ℕ ↦
      formulaAtomPayload q.1.1 q.1.2 q.2) := by
  have hc : Primrec (fun q : (TermAction × ℕ) × ℕ ↦ q.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have harity : Primrec (fun q : (TermAction × ℕ) × ℕ ↦
      q.2.unpair.2.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp hc)
  have hrest : Primrec (fun q : (TermAction × ℕ) × ℕ ↦
      q.2.unpair.2.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp hc)
  have hsymbol : Primrec (fun q : (TermAction × ℕ) × ℕ ↦
      q.2.unpair.2.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hrest)
  have hvec : Primrec (fun q : (TermAction × ℕ) × ℕ ↦
      q.2.unpair.2.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hrest)
  have htvec : Primrec (fun q : (TermAction × ℕ) × ℕ ↦
      transformTermVec q.1.1 q.1.2
        q.2.unpair.2.unpair.2.unpair.2) :=
    transformTermVec_primrec.comp
      (Primrec.pair Primrec.fst hvec)
  exact (Primrec₂.natPair.comp harity
    (Primrec₂.natPair.comp hsymbol htvec)).of_eq (fun _ ↦ by rfl)

theorem negateFormulaTag_primrec : Primrec negateFormulaTag := by
  unfold negateFormulaTag
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const 1)
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1))
      (Primrec.const 0)
      (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 2))
        (Primrec.const 3)
        (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 3))
          (Primrec.const 2)
          (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 4))
            (Primrec.const 5)
            (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 5))
              (Primrec.const 4)
              (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 6))
                (Primrec.const 7)
                (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 7))
                  (Primrec.const 6) Primrec.id)))))))

theorem formulaOutputTag_primrec : Primrec₂ formulaOutputTag := by
  exact (Primrec.ite
    (Primrec.eq.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.const 2))
    (negateFormulaTag_primrec.comp Primrec.snd)
    Primrec.snd).to₂

theorem formulaQuantArm_primrec : Primrec₂ formulaQuantArm := by
  exact (Primrec.ite
    (Primrec.nat_lt.comp Primrec.fst (Primrec.const 8))
    (pairSucc_primrec.comp Primrec.fst Primrec.snd)
    (Primrec.const 0)).to₂

theorem formulaBinaryOrQuantArm_primrec :
    Primrec (fun q : (ℕ × ℕ) × ℕ ↦
      formulaBinaryOrQuantArm q.1.1 q.1.2 q.2) := by
  have hbin : Primrec (fun q : (ℕ × ℕ) × ℕ ↦
      pairSucc q.1.1 (Nat.pair q.1.2 q.2)) :=
    pairSucc_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have hquant : Primrec (fun q : (ℕ × ℕ) × ℕ ↦
      formulaQuantArm q.1.1 q.1.2) :=
    formulaQuantArm_primrec.comp
      (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  exact (Primrec.ite
    (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 6))
    hbin hquant).of_eq (fun q ↦ by rfl)

theorem formulaConstOrRestArm_primrec :
    Primrec (fun q : (ℕ × ℕ) × ℕ ↦
      formulaConstOrRestArm q.1.1 q.1.2 q.2) := by
  have hconst : Primrec (fun q : (ℕ × ℕ) × ℕ ↦ pairSucc q.1.1 0) :=
    pairSucc_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0)
  exact (Primrec.ite
    (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 4))
    hconst formulaBinaryOrQuantArm_primrec).of_eq (fun q ↦ by rfl)

theorem formulaAtomicOrRestArm_primrec :
    Primrec (fun q : ((ℕ × ℕ) × ℕ) × ℕ ↦
      formulaAtomicOrRestArm q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  have hatom : Primrec (fun q : ((ℕ × ℕ) × ℕ) × ℕ ↦
      pairSucc q.1.1.1 q.1.1.2) :=
    pairSucc_primrec.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hrest : Primrec (fun q : ((ℕ × ℕ) × ℕ) × ℕ ↦
      formulaConstOrRestArm q.1.1.1 q.1.2 q.2) :=
    formulaConstOrRestArm_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  exact (Primrec.ite
    (Primrec.nat_lt.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.const 2)) hatom hrest).of_eq (fun q ↦ by rfl)

theorem formulaStateAction_computable : Computable formulaStateAction :=
  formulaStateAction_primrec.to_comp

theorem formulaStateDepth_computable : Computable formulaStateDepth :=
  formulaStateDepth_primrec.to_comp

theorem formulaStateCode_computable : Computable formulaStateCode :=
  formulaStateCode_primrec.to_comp

theorem formulaAtomPayload_computable :
    Computable (fun q : (TermAction × ℕ) × ℕ ↦
      formulaAtomPayload q.1.1 q.1.2 q.2) :=
  formulaAtomPayload_primrec.to_comp

theorem formulaAtomicOrRestArm_computable :
    Computable (fun q : ((ℕ × ℕ) × ℕ) × ℕ ↦
      formulaAtomicOrRestArm q.1.1.1 q.1.1.2 q.1.2 q.2) :=
  formulaAtomicOrRestArm_primrec.to_comp

abbrev FormulaSuccessorInput := (FormulaState × List ℕ) × ℕ

@[irreducible] def formulaSuccessorTermInput
    (q : FormulaSuccessorInput) : (TermAction × ℕ) × ℕ :=
  ((formulaStateAction q.1.1, formulaStateDepth q.1.1), q.2)

theorem formulaSuccessorTermInput_eq (q : FormulaSuccessorInput) :
    formulaSuccessorTermInput q =
      ((formulaStateAction q.1.1, formulaStateDepth q.1.1), q.2) := by
  rw [formulaSuccessorTermInput]

@[irreducible] def formulaSuccessorPayload (q : FormulaSuccessorInput) : ℕ :=
  formulaAtomPayload (formulaSuccessorTermInput q).1.1
    (formulaSuccessorTermInput q).1.2 (formulaSuccessorTermInput q).2

theorem formulaSuccessorPayload_eq (q : FormulaSuccessorInput) :
    formulaSuccessorPayload q =
      formulaAtomPayload (formulaSuccessorTermInput q).1.1
        (formulaSuccessorTermInput q).1.2 (formulaSuccessorTermInput q).2 := by
  rw [formulaSuccessorPayload]

@[irreducible] def formulaSuccessorArgs
    (q : FormulaSuccessorInput) : ((ℕ × ℕ) × ℕ) × ℕ :=
  ((((formulaOutputTag (formulaStateAction q.1.1) q.2.unpair.1),
      formulaSuccessorPayload q), q.1.2.getD 0 0), q.1.2.getD 1 0)

theorem formulaSuccessorArgs_eq (q : FormulaSuccessorInput) :
    formulaSuccessorArgs q =
      ((((formulaOutputTag (formulaStateAction q.1.1) q.2.unpair.1),
        formulaSuccessorPayload q), q.1.2.getD 0 0),
          q.1.2.getD 1 0) := by
  rw [formulaSuccessorArgs]

@[irreducible] def formulaSuccessorValue (q : FormulaSuccessorInput) : ℕ :=
  formulaAtomicOrRestArm (formulaSuccessorArgs q).1.1.1
    (formulaSuccessorArgs q).1.1.2 (formulaSuccessorArgs q).1.2
    (formulaSuccessorArgs q).2

theorem formulaSuccessorValue_eq (q : FormulaSuccessorInput) :
    formulaSuccessorValue q =
      formulaAtomicOrRestArm (formulaSuccessorArgs q).1.1.1
        (formulaSuccessorArgs q).1.1.2 (formulaSuccessorArgs q).1.2
        (formulaSuccessorArgs q).2 := by
  rw [formulaSuccessorValue]

theorem formulaSuccessorTermInput_computable :
    Computable formulaSuccessorTermInput := by
  have hstate : Computable (fun q : FormulaSuccessorInput ↦ q.1.1) :=
    Computable.fst.comp Computable.fst
  have hraw : Computable (fun q : FormulaSuccessorInput ↦
      ((formulaStateAction q.1.1, formulaStateDepth q.1.1), q.2)) :=
    Computable.pair
      (Computable.pair
        (formulaStateAction_computable.comp hstate)
        (formulaStateDepth_computable.comp hstate))
      Computable.snd
  apply hraw.of_eq
  intro q
  exact (formulaSuccessorTermInput_eq q).symm

theorem formulaSuccessorPayload_computable :
    Computable formulaSuccessorPayload := by
  have hraw : Computable (fun q : FormulaSuccessorInput ↦
      formulaAtomPayload (formulaSuccessorTermInput q).1.1
        (formulaSuccessorTermInput q).1.2
        (formulaSuccessorTermInput q).2) :=
    formulaAtomPayload_computable.comp formulaSuccessorTermInput_computable
  apply hraw.of_eq
  intro q
  exact (formulaSuccessorPayload_eq q).symm

theorem formulaSuccessorTag_computable :
    Computable (fun q : FormulaSuccessorInput ↦
      formulaOutputTag (formulaStateAction q.1.1) q.2.unpair.1) :=
  formulaOutputTag_primrec.to_comp.comp
    (formulaStateAction_computable.comp
      (Computable.fst.comp Computable.fst))
    (Primrec.fst.to_comp.comp
      (Primrec.unpair.to_comp.comp Computable.snd))

theorem formulaSuccessorV0_computable :
    Computable (fun q : FormulaSuccessorInput ↦ q.1.2.getD 0 0) :=
  (Primrec.list_getD 0).to_comp.comp
    (Computable.snd.comp Computable.fst) (Computable.const 0)

theorem formulaSuccessorV1_computable :
    Computable (fun q : FormulaSuccessorInput ↦ q.1.2.getD 1 0) :=
  (Primrec.list_getD 0).to_comp.comp
    (Computable.snd.comp Computable.fst) (Computable.const 1)

theorem formulaSuccessorArgs_computable :
    Computable formulaSuccessorArgs := by
  have hraw : Computable (fun q : FormulaSuccessorInput ↦
      ((((formulaOutputTag (formulaStateAction q.1.1) q.2.unpair.1),
        formulaSuccessorPayload q), q.1.2.getD 0 0),
          q.1.2.getD 1 0)) :=
    Computable.pair
      (Computable.pair
        (Computable.pair formulaSuccessorTag_computable
          formulaSuccessorPayload_computable)
        formulaSuccessorV0_computable)
      formulaSuccessorV1_computable
  apply hraw.of_eq
  intro q
  exact (formulaSuccessorArgs_eq q).symm

theorem formulaSuccessorValue_computable :
    Computable formulaSuccessorValue := by
  have hraw : Computable (fun q : FormulaSuccessorInput ↦
      formulaAtomicOrRestArm (formulaSuccessorArgs q).1.1.1
        (formulaSuccessorArgs q).1.1.2 (formulaSuccessorArgs q).1.2
        (formulaSuccessorArgs q).2) :=
    formulaAtomicOrRestArm_computable.comp formulaSuccessorArgs_computable
  apply hraw.of_eq
  intro q
  exact (formulaSuccessorValue_eq q).symm

theorem formulaSuccessorValue_eq_transform (q : FormulaSuccessorInput) :
    formulaSuccessorValue q =
      formulaTransformSuccessor q.1.1 q.1.2 q.2 := by
  rw [formulaSuccessorValue_eq, formulaSuccessorArgs_eq,
    formulaSuccessorPayload_eq, formulaSuccessorTermInput_eq,
    formulaTransformSuccessor_eq]

theorem formulaTransformSuccessor_computable :
    Computable₂ (fun r : FormulaState × List ℕ => fun e : ℕ ↦
      formulaTransformSuccessor r.1 r.2 e) := by
  have hcurried : Computable₂ (fun r : FormulaState × List ℕ => fun e : ℕ ↦
      formulaSuccessorValue (r, e)) := formulaSuccessorValue_computable.to₂
  apply computable₂_of_eq hcurried
  intro r e
  exact formulaSuccessorValue_eq_transform (r, e)

@[irreducible] def formulaRawCases
    (r : FormulaState × List ℕ) : ℕ :=
  Nat.casesOn (motive := fun _ ↦ ℕ) (formulaStateCode r.1) 0
    (formulaTransformSuccessor r.1 r.2)

theorem formulaRawCases_eq (r : FormulaState × List ℕ) :
    formulaRawCases r =
      Nat.casesOn (motive := fun _ ↦ ℕ) (formulaStateCode r.1) 0
        (formulaTransformSuccessor r.1 r.2) := by
  rw [formulaRawCases]

theorem formulaRawCases_computable : Computable formulaRawCases := by
  have hcases : Computable (fun r : FormulaState × List ℕ ↦
      Nat.casesOn (motive := fun _ ↦ ℕ) (formulaStateCode r.1) 0
        (formulaTransformSuccessor r.1 r.2)) :=
    Computable.nat_casesOn
      (f := fun r : FormulaState × List ℕ ↦ formulaStateCode r.1)
      (g := fun _ ↦ (0 : ℕ))
      (h := fun r e ↦ formulaTransformSuccessor r.1 r.2 e)
      (formulaStateCode_computable.comp Computable.fst)
      (Computable.const 0) formulaTransformSuccessor_computable
  apply hcases.of_eq
  intro r
  exact (formulaRawCases_eq r).symm

theorem formulaTransformRaw_computable :
    Computable (fun r : FormulaState × List ℕ ↦
      formulaTransformRaw r.1 r.2) := by
  apply formulaRawCases_computable.of_eq
  intro r
  exact (formulaRawCases_eq r).trans
    (formulaTransformRaw_eq r.1 r.2).symm

theorem formulaTransformStep_computable : Computable₂ formulaTransformStep := by
  have h : Computable₂ (fun b vs ↦ formulaTransformRaw b vs) :=
    formulaTransformRaw_computable.to₂
  exact computable₂_of_eq h fun b vs ↦ (formulaTransformStep_eq b vs).symm

theorem formulaSuccessorTermInput_primrec :
    Primrec formulaSuccessorTermInput := by
  have hstate : Primrec (fun q : FormulaSuccessorInput ↦ q.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hraw : Primrec (fun q : FormulaSuccessorInput ↦
      ((formulaStateAction q.1.1, formulaStateDepth q.1.1), q.2)) :=
    Primrec.pair
      (Primrec.pair
        (formulaStateAction_primrec.comp hstate)
        (formulaStateDepth_primrec.comp hstate))
      Primrec.snd
  apply hraw.of_eq
  intro q
  exact (formulaSuccessorTermInput_eq q).symm

theorem formulaSuccessorPayload_primrec :
    Primrec formulaSuccessorPayload := by
  have hraw : Primrec (fun q : FormulaSuccessorInput ↦
      formulaAtomPayload (formulaSuccessorTermInput q).1.1
        (formulaSuccessorTermInput q).1.2
        (formulaSuccessorTermInput q).2) :=
    formulaAtomPayload_primrec.comp formulaSuccessorTermInput_primrec
  apply hraw.of_eq
  intro q
  exact (formulaSuccessorPayload_eq q).symm

theorem formulaSuccessorTag_primrec :
    Primrec (fun q : FormulaSuccessorInput ↦
      formulaOutputTag (formulaStateAction q.1.1) q.2.unpair.1) :=
  formulaOutputTag_primrec.comp
    (formulaStateAction_primrec.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))

theorem formulaSuccessorV0_primrec :
    Primrec (fun q : FormulaSuccessorInput ↦ q.1.2.getD 0 0) :=
  (Primrec.list_getD 0).comp
    (Primrec.snd.comp Primrec.fst) (Primrec.const 0)

theorem formulaSuccessorV1_primrec :
    Primrec (fun q : FormulaSuccessorInput ↦ q.1.2.getD 1 0) :=
  (Primrec.list_getD 0).comp
    (Primrec.snd.comp Primrec.fst) (Primrec.const 1)

theorem formulaSuccessorArgs_primrec :
    Primrec formulaSuccessorArgs := by
  have hraw : Primrec (fun q : FormulaSuccessorInput ↦
      ((((formulaOutputTag (formulaStateAction q.1.1) q.2.unpair.1),
        formulaSuccessorPayload q), q.1.2.getD 0 0),
          q.1.2.getD 1 0)) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.pair formulaSuccessorTag_primrec
          formulaSuccessorPayload_primrec)
        formulaSuccessorV0_primrec)
      formulaSuccessorV1_primrec
  apply hraw.of_eq
  intro q
  exact (formulaSuccessorArgs_eq q).symm

theorem formulaSuccessorValue_primrec :
    Primrec formulaSuccessorValue := by
  have hraw : Primrec (fun q : FormulaSuccessorInput ↦
      formulaAtomicOrRestArm (formulaSuccessorArgs q).1.1.1
        (formulaSuccessorArgs q).1.1.2 (formulaSuccessorArgs q).1.2
        (formulaSuccessorArgs q).2) :=
    formulaAtomicOrRestArm_primrec.comp formulaSuccessorArgs_primrec
  apply hraw.of_eq
  intro q
  exact (formulaSuccessorValue_eq q).symm

theorem formulaTransformSuccessor_primrec :
    Primrec₂ (fun r : FormulaState × List ℕ => fun e : ℕ ↦
      formulaTransformSuccessor r.1 r.2 e) := by
  have hcurried : Primrec₂ (fun r : FormulaState × List ℕ => fun e : ℕ ↦
      formulaSuccessorValue (r, e)) := formulaSuccessorValue_primrec.to₂
  apply hcurried.of_eq
  intro r e
  exact formulaSuccessorValue_eq_transform (r, e)

theorem formulaRawCases_primrec : Primrec formulaRawCases := by
  have hcases : Primrec (fun r : FormulaState × List ℕ ↦
      Nat.casesOn (motive := fun _ ↦ ℕ) (formulaStateCode r.1) 0
        (formulaTransformSuccessor r.1 r.2)) :=
    Primrec.nat_casesOn
      (f := fun r : FormulaState × List ℕ ↦ formulaStateCode r.1)
      (g := fun _ ↦ (0 : ℕ))
      (h := fun r e ↦ formulaTransformSuccessor r.1 r.2 e)
      (formulaStateCode_primrec.comp Primrec.fst)
      (Primrec.const 0) formulaTransformSuccessor_primrec
  apply hcases.of_eq
  intro r
  exact (formulaRawCases_eq r).symm

theorem formulaTransformRaw_primrec :
    Primrec (fun r : FormulaState × List ℕ ↦
      formulaTransformRaw r.1 r.2) := by
  apply formulaRawCases_primrec.of_eq
  intro r
  exact (formulaRawCases_eq r).trans
    (formulaTransformRaw_eq r.1 r.2).symm

theorem formulaTransformStep_primrec : Primrec₂ formulaTransformStep := by
  have h : Primrec₂ (fun b vs ↦ formulaTransformRaw b vs) :=
    formulaTransformRaw_primrec.to₂
  exact h.of_eq fun b vs ↦ (formulaTransformStep_eq b vs).symm

theorem formulaTransform_pack (a : TermAction) (depth code : ℕ) :
    formulaTransform (packFormulaState a depth code) =
      formulaTransformCode a depth code := by
  unfold formulaTransform
  rw [formulaStateAction_pack, formulaStateDepth_pack, formulaStateCode_pack]

theorem formulaSubArgs_transform_zero (b : FormulaState)
    (hcode : formulaStateCode b = 0) :
    (formulaSubArgs b).map formulaTransform = [] := by
  simp [formulaSubArgs, hcode, FFL.FirstOrder.Semiformula.subArgs]

theorem formulaSubArgs_transform_succ (b : FormulaState) (e : ℕ)
    (hcode : formulaStateCode b = e + 1) :
    (formulaSubArgs b).map formulaTransform =
      (if e.unpair.1 = 4 ∨ e.unpair.1 = 5 then
        [formulaTransformCode (formulaStateAction b) (formulaStateDepth b)
            e.unpair.2.unpair.1,
          formulaTransformCode (formulaStateAction b) (formulaStateDepth b)
            e.unpair.2.unpair.2]
      else if e.unpair.1 = 6 ∨ e.unpair.1 = 7 then
        [formulaTransformCode (formulaStateAction b)
            (formulaStateDepth b + 1) e.unpair.2]
      else []) := by
  rw [formulaSubArgs, hcode,
    FFL.FirstOrder.Semiformula.subArgs_succ, List.map_map]
  by_cases h45 : e.unpair.1 = 4 ∨ e.unpair.1 = 5
  · simp only [ite_eq_left h45, List.map_cons, List.map_nil,
      Function.comp_apply, formulaTransform_pack]
  · by_cases h67 : e.unpair.1 = 6 ∨ e.unpair.1 = 7
    · simp only [ite_eq_right h45, ite_eq_left h67, List.map_cons,
        List.map_nil, Function.comp_apply, formulaTransform_pack]
    · simp only [ite_eq_right h45, ite_eq_right h67, List.map_nil]

theorem formulaTransformStep_correct (b : FormulaState) :
    formulaTransformStep b ((formulaSubArgs b).map formulaTransform) =
      formulaTransform b := by
  cases hcode : formulaStateCode b with
  | zero =>
      rw [formulaTransformStep_eq, formulaTransformRaw_eq, hcode]
      simp [formulaTransform, hcode, formulaTransformCode]
  | succ e =>
      rw [formulaTransformStep_eq, formulaTransformRaw_eq, hcode]
      change formulaTransformSuccessor b
        ((formulaSubArgs b).map formulaTransform) e = formulaTransform b
      rw [formulaTransformSuccessor_eq]
      rw [formulaSubArgs_transform_succ b e hcode]
      simp only [formulaTransform, hcode, formulaTransformCode]
      rfl

theorem formulaTransform_primrec : Primrec formulaTransform :=
  Primrec.nat_omega_rec' formulaTransform
    (m := formulaStateCode) (l := formulaSubArgs)
    (g := fun b vs ↦ some (formulaTransformStep b vs))
    formulaStateCode_primrec formulaSubArgs_primrec
    (Primrec.option_some.comp formulaTransformStep_primrec)
    formulaSubArgs_ord
    (fun b ↦ congrArg some (formulaTransformStep_correct b))

theorem packFormulaState_primrec :
    Primrec (fun q : (TermAction × ℕ) × ℕ ↦
      packFormulaState q.1.1 q.1.2 q.2) := by
  exact (Primrec₂.natPair.comp
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec₂.natPair.comp
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec₂.natPair.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec₂.natPair.comp
          (Primrec.snd.comp Primrec.fst) Primrec.snd)))).of_eq (fun _ ↦ by rfl)

theorem formulaTransformCode_primrec :
    Primrec (fun q : (TermAction × ℕ) × ℕ ↦
      formulaTransformCode q.1.1 q.1.2 q.2) := by
  apply (formulaTransform_primrec.comp packFormulaState_primrec).of_eq
  intro q
  exact formulaTransform_pack q.1.1 q.1.2 q.2

namespace DirectTerm

theorem shiftFree_eq_mapFree {d : ℕ}
    (t : FailureOfComposition.Palomar.Arithmetic.Term ℕ d) :
    shiftFree t =
      FailureOfComposition.Palomar.Arithmetic.Term.mapFree Nat.succ t := by
  induction t <;>
    simp [shiftFree, FailureOfComposition.Palomar.Arithmetic.Term.mapFree,
      FailureOfComposition.Palomar.Arithmetic.Term.rewrite, *]

def dropBoundVar
    (replacement : FailureOfComposition.Palomar.Arithmetic.Term ℕ 0)
    (d : ℕ) (i : Fin (d + 1)) :
    FailureOfComposition.Palomar.Arithmetic.Term ℕ d :=
  if h : (i : ℕ) < d then .bvar ⟨i, h⟩ else liftClosed replacement

def dropBoundFree (shift : Bool) (d : ℕ) (x : ℕ) :
    FailureOfComposition.Palomar.Arithmetic.Term ℕ d :=
  .fvar (if shift then x + 1 else x)

theorem dropBound_eq_rewrite
    (replacement : FailureOfComposition.Palomar.Arithmetic.Term ℕ 0)
    (shift : Bool) (d : ℕ)
    (t : FailureOfComposition.Palomar.Arithmetic.Term ℕ (d + 1)) :
    dropBound replacement shift d t =
      FailureOfComposition.Palomar.Arithmetic.Term.rewrite
        (dropBoundVar replacement d) (dropBoundFree shift d) t := by
  induction t <;>
    simp [dropBound, dropBoundVar, dropBoundFree,
      FailureOfComposition.Palomar.Arithmetic.Term.rewrite, *]

theorem lift_liftClosed
    (replacement : FailureOfComposition.Palomar.Arithmetic.Term ℕ 0)
    (d : ℕ) :
    FailureOfComposition.Palomar.Arithmetic.Term.lift
        (liftClosed (d := d) replacement) =
      liftClosed (d := d + 1) replacement := by
  induction replacement generalizing d with
  | bvar i => exact Fin.elim0 i
  | fvar x => rfl
  | zero => rfl
  | one => rfl
  | add s t ihs iht =>
      change FailureOfComposition.Palomar.Arithmetic.Term.add
        (FailureOfComposition.Palomar.Arithmetic.Term.lift
          (liftClosed (d := d) s))
        (FailureOfComposition.Palomar.Arithmetic.Term.lift
          (liftClosed (d := d) t)) = _
      rw [ihs, iht]
      rfl
  | mul s t ihs iht =>
      change FailureOfComposition.Palomar.Arithmetic.Term.mul
        (FailureOfComposition.Palomar.Arithmetic.Term.lift
          (liftClosed (d := d) s))
        (FailureOfComposition.Palomar.Arithmetic.Term.lift
          (liftClosed (d := d) t)) = _
      rw [ihs, iht]
      rfl

@[simp] theorem liftClosed_zero
    (replacement : FailureOfComposition.Palomar.Arithmetic.Term ℕ 0) :
    liftClosed (d := 0) replacement = replacement := by
  induction replacement with
  | bvar i => exact Fin.elim0 i
  | fvar x => rfl
  | zero => rfl
  | one => rfl
  | add s t ihs iht => simp [liftClosed, ihs, iht]
  | mul s t ihs iht => simp [liftClosed, ihs, iht]

theorem underBinder_dropBoundVar
    (replacement : FailureOfComposition.Palomar.Arithmetic.Term ℕ 0)
    (d : ℕ) :
    FailureOfComposition.Palomar.Arithmetic.Term.underBinder
        (dropBoundVar replacement d) =
      dropBoundVar replacement (d + 1) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [FailureOfComposition.Palomar.Arithmetic.Term.underBinder,
      dropBoundVar]
  · by_cases hj : (j : ℕ) < d
    · simp [FailureOfComposition.Palomar.Arithmetic.Term.underBinder,
        dropBoundVar, hj, show (j : ℕ) + 1 < d + 1 by omega,
        FailureOfComposition.Palomar.Arithmetic.Term.lift]
    · have hjeq : (j : ℕ) = d := by omega
      simp [FailureOfComposition.Palomar.Arithmetic.Term.underBinder,
        dropBoundVar, hjeq, lift_liftClosed]

theorem lift_dropBoundFree (shift : Bool) (d : ℕ) (x : ℕ) :
    FailureOfComposition.Palomar.Arithmetic.Term.lift
        (dropBoundFree shift d x) =
      dropBoundFree shift (d + 1) x := by
  simp [dropBoundFree, FailureOfComposition.Palomar.Arithmetic.Term.lift]

theorem underBinder_bvar {n : ℕ} :
    FailureOfComposition.Palomar.Arithmetic.Term.underBinder
        (fun i : Fin n ↦
          (FailureOfComposition.Palomar.Arithmetic.Term.bvar i :
            FailureOfComposition.Palomar.Arithmetic.Term ℕ n)) =
      (fun i : Fin (n + 1) ↦
        (FailureOfComposition.Palomar.Arithmetic.Term.bvar i :
          FailureOfComposition.Palomar.Arithmetic.Term ℕ (n + 1))) := by
  funext i
  refine Fin.cases rfl (fun _ ↦ rfl) i

end DirectTerm

namespace DirectFormula

@[simp] theorem encode_verum {n : ℕ} :
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Formula.verum :
        FailureOfComposition.Palomar.Arithmetic.Formula ℕ n) =
      pairSucc 2 0 := rfl

@[simp] theorem encode_falsum {n : ℕ} :
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Formula.falsum :
        FailureOfComposition.Palomar.Arithmetic.Formula ℕ n) =
      pairSucc 3 0 := rfl

@[simp] theorem encode_equal {n : ℕ}
    (s t : FailureOfComposition.Palomar.Arithmetic.Term ℕ n) :
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Formula.equal s t) =
      pairSucc 0 (Nat.pair 2 (Nat.pair 0
        (listCode [Encodable.encode s, Encodable.encode t]))) := by
  change Encodable.encode
    (FailureOfComposition.Palomar.Arithmetic.Formula.toFoundation
      (FailureOfComposition.Palomar.Arithmetic.Formula.equal s t)) = _
  rfl

@[simp] theorem encode_nequal {n : ℕ}
    (s t : FailureOfComposition.Palomar.Arithmetic.Term ℕ n) :
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Formula.nequal s t) =
      pairSucc 1 (Nat.pair 2 (Nat.pair 0
        (listCode [Encodable.encode s, Encodable.encode t]))) := by
  change Encodable.encode
    (FailureOfComposition.Palomar.Arithmetic.Formula.toFoundation
      (FailureOfComposition.Palomar.Arithmetic.Formula.nequal s t)) = _
  rfl

@[simp] theorem encode_less {n : ℕ}
    (s t : FailureOfComposition.Palomar.Arithmetic.Term ℕ n) :
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Formula.less s t) =
      pairSucc 0 (Nat.pair 2 (Nat.pair 1
        (listCode [Encodable.encode s, Encodable.encode t]))) := by
  change Encodable.encode
    (FailureOfComposition.Palomar.Arithmetic.Formula.toFoundation
      (FailureOfComposition.Palomar.Arithmetic.Formula.less s t)) = _
  rfl

@[simp] theorem encode_nless {n : ℕ}
    (s t : FailureOfComposition.Palomar.Arithmetic.Term ℕ n) :
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Formula.nless s t) =
      pairSucc 1 (Nat.pair 2 (Nat.pair 1
        (listCode [Encodable.encode s, Encodable.encode t]))) := by
  change Encodable.encode
    (FailureOfComposition.Palomar.Arithmetic.Formula.toFoundation
      (FailureOfComposition.Palomar.Arithmetic.Formula.nless s t)) = _
  rfl

@[simp] theorem encode_and {n : ℕ}
    (p q : FailureOfComposition.Palomar.Arithmetic.Formula ℕ n) :
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Formula.and p q) =
      pairSucc 4 (Nat.pair (Encodable.encode p) (Encodable.encode q)) := rfl

@[simp] theorem encode_or {n : ℕ}
    (p q : FailureOfComposition.Palomar.Arithmetic.Formula ℕ n) :
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Formula.or p q) =
      pairSucc 5 (Nat.pair (Encodable.encode p) (Encodable.encode q)) := rfl

@[simp] theorem encode_all {n : ℕ}
    (p : FailureOfComposition.Palomar.Arithmetic.Formula ℕ (n + 1)) :
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Formula.all p) =
      pairSucc 6 (Encodable.encode p) := rfl

@[simp] theorem encode_exs {n : ℕ}
    (p : FailureOfComposition.Palomar.Arithmetic.Formula ℕ (n + 1)) :
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Formula.exs p) =
      pairSucc 7 (Encodable.encode p) := rfl

def shiftFree {d : ℕ} :
    FailureOfComposition.Palomar.Arithmetic.Formula ℕ d →
      FailureOfComposition.Palomar.Arithmetic.Formula ℕ d
  | .verum => .verum
  | .falsum => .falsum
  | .equal s t => .equal (DirectTerm.shiftFree s) (DirectTerm.shiftFree t)
  | .nequal s t => .nequal (DirectTerm.shiftFree s) (DirectTerm.shiftFree t)
  | .less s t => .less (DirectTerm.shiftFree s) (DirectTerm.shiftFree t)
  | .nless s t => .nless (DirectTerm.shiftFree s) (DirectTerm.shiftFree t)
  | .and p q => .and (shiftFree p) (shiftFree q)
  | .or p q => .or (shiftFree p) (shiftFree q)
  | .all p => .all (shiftFree p)
  | .exs p => .exs (shiftFree p)

def dropBound
    (replacement : FailureOfComposition.Palomar.Arithmetic.Term ℕ 0)
    (shift : Bool) (d : ℕ) :
    FailureOfComposition.Palomar.Arithmetic.Formula ℕ (d + 1) →
      FailureOfComposition.Palomar.Arithmetic.Formula ℕ d
  | .verum => .verum
  | .falsum => .falsum
  | .equal s t => .equal (DirectTerm.dropBound replacement shift d s)
      (DirectTerm.dropBound replacement shift d t)
  | .nequal s t => .nequal (DirectTerm.dropBound replacement shift d s)
      (DirectTerm.dropBound replacement shift d t)
  | .less s t => .less (DirectTerm.dropBound replacement shift d s)
      (DirectTerm.dropBound replacement shift d t)
  | .nless s t => .nless (DirectTerm.dropBound replacement shift d s)
      (DirectTerm.dropBound replacement shift d t)
  | .and p q => .and (dropBound replacement shift d p)
      (dropBound replacement shift d q)
  | .or p q => .or (dropBound replacement shift d p)
      (dropBound replacement shift d q)
  | .all p => .all (dropBound replacement shift (d + 1) p)
  | .exs p => .exs (dropBound replacement shift (d + 1) p)

theorem shiftFree_eq {d : ℕ}
    (p : FailureOfComposition.Palomar.Arithmetic.Formula ℕ d) :
    shiftFree p = FailureOfComposition.Palomar.Arithmetic.Formula.shiftFree p := by
  induction p with
  | verum => rfl
  | falsum => rfl
  | equal s t =>
      simp [shiftFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.shiftFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.mapFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite,
        FailureOfComposition.Palomar.Arithmetic.Term.mapFree,
        DirectTerm.shiftFree_eq_mapFree]
  | nequal s t =>
      simp [shiftFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.shiftFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.mapFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite,
        FailureOfComposition.Palomar.Arithmetic.Term.mapFree,
        DirectTerm.shiftFree_eq_mapFree]
  | less s t =>
      simp [shiftFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.shiftFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.mapFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite,
        FailureOfComposition.Palomar.Arithmetic.Term.mapFree,
        DirectTerm.shiftFree_eq_mapFree]
  | nless s t =>
      simp [shiftFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.shiftFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.mapFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite,
        FailureOfComposition.Palomar.Arithmetic.Term.mapFree,
        DirectTerm.shiftFree_eq_mapFree]
  | and p q ihp ihq =>
      simp [shiftFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.shiftFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.mapFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite, ihp, ihq]
  | or p q ihp ihq =>
      simp [shiftFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.shiftFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.mapFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite, ihp, ihq]
  | all p ih =>
      simp [shiftFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.shiftFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.mapFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite,
        FailureOfComposition.Palomar.Arithmetic.Term.lift,
        DirectTerm.underBinder_bvar, ih]
      congr 1
  | exs p ih =>
      simp [shiftFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.shiftFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.mapFree,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite,
        FailureOfComposition.Palomar.Arithmetic.Term.lift,
        DirectTerm.underBinder_bvar, ih]
      congr 1

theorem encode_shiftFree (depth : ℕ) {d : ℕ}
    (p : FailureOfComposition.Palomar.Arithmetic.Formula ℕ d) :
    formulaTransformCode ((0, 0), 1) depth (Encodable.encode p) =
      Encodable.encode (shiftFree p) := by
  induction p generalizing depth with
  | verum =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        pairSucc, shiftFree]
  | falsum =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        pairSucc, shiftFree]
  | equal s t =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaAtomPayload, transformTermVec,
        DirectTerm.encode_shiftFree, listCode, Nat.natToList, shiftFree,
        pairSucc]
  | nequal s t =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaAtomPayload, transformTermVec,
        DirectTerm.encode_shiftFree, listCode, Nat.natToList, shiftFree,
        pairSucc]
  | less s t =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaAtomPayload, transformTermVec,
        DirectTerm.encode_shiftFree, listCode, Nat.natToList, shiftFree,
        pairSucc]
  | nless s t =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaAtomPayload, transformTermVec,
        DirectTerm.encode_shiftFree, listCode, Nat.natToList, shiftFree,
        pairSucc]
  | and p q ihp ihq =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        formulaBinaryOrQuantArm, shiftFree, ihp, ihq, pairSucc]
  | or p q ihp ihq =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        formulaBinaryOrQuantArm, shiftFree, ihp, ihq, pairSucc]
  | all p ih =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        formulaBinaryOrQuantArm, formulaQuantArm, shiftFree, ih,
        pairSucc]
  | exs p ih =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        formulaBinaryOrQuantArm, formulaQuantArm, shiftFree, ih,
        pairSucc]

def dropBoundCast
    (replacement : FailureOfComposition.Palomar.Arithmetic.Term ℕ 0)
    (shift : Bool) (d : ℕ) {n : ℕ} (h : n = d + 1)
    (p : FailureOfComposition.Palomar.Arithmetic.Formula ℕ n) :
    FailureOfComposition.Palomar.Arithmetic.Formula ℕ d :=
  dropBound replacement shift d
    (cast (congrArg (FailureOfComposition.Palomar.Arithmetic.Formula ℕ) h) p)

theorem dropBoundCast_eq_rewrite
    (replacement : FailureOfComposition.Palomar.Arithmetic.Term ℕ 0)
    (shift : Bool) {n : ℕ}
    (p : FailureOfComposition.Palomar.Arithmetic.Formula ℕ n) :
    ∀ (d : ℕ) (h : n = d + 1),
      dropBoundCast replacement shift d h p =
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite
          (DirectTerm.dropBoundVar replacement d)
          (DirectTerm.dropBoundFree shift d)
          (cast
            (congrArg (FailureOfComposition.Palomar.Arithmetic.Formula ℕ) h)
            p) := by
  induction p with
  | verum =>
      intro d h
      cases h
      simp [dropBoundCast, dropBound,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite]
  | falsum =>
      intro d h
      cases h
      simp [dropBoundCast, dropBound,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite]
  | equal s t =>
      intro d h
      cases h
      simp [dropBoundCast, dropBound,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite,
        DirectTerm.dropBound_eq_rewrite]
  | nequal s t =>
      intro d h
      cases h
      simp [dropBoundCast, dropBound,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite,
        DirectTerm.dropBound_eq_rewrite]
  | less s t =>
      intro d h
      cases h
      simp [dropBoundCast, dropBound,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite,
        DirectTerm.dropBound_eq_rewrite]
  | nless s t =>
      intro d h
      cases h
      simp [dropBoundCast, dropBound,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite,
        DirectTerm.dropBound_eq_rewrite]
  | and p q ihp ihq =>
      intro d h
      have hp := ihp d h
      have hq := ihq d h
      cases h
      have hp' : dropBound replacement shift d p =
          FailureOfComposition.Palomar.Arithmetic.Formula.rewrite
            (DirectTerm.dropBoundVar replacement d)
            (DirectTerm.dropBoundFree shift d) p := by
        simpa [dropBoundCast] using hp
      have hq' : dropBound replacement shift d q =
          FailureOfComposition.Palomar.Arithmetic.Formula.rewrite
            (DirectTerm.dropBoundVar replacement d)
            (DirectTerm.dropBoundFree shift d) q := by
        simpa [dropBoundCast] using hq
      simp [dropBoundCast, dropBound,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite, hp', hq']
  | or p q ihp ihq =>
      intro d h
      have hp := ihp d h
      have hq := ihq d h
      cases h
      have hp' : dropBound replacement shift d p =
          FailureOfComposition.Palomar.Arithmetic.Formula.rewrite
            (DirectTerm.dropBoundVar replacement d)
            (DirectTerm.dropBoundFree shift d) p := by
        simpa [dropBoundCast] using hp
      have hq' : dropBound replacement shift d q =
          FailureOfComposition.Palomar.Arithmetic.Formula.rewrite
            (DirectTerm.dropBoundVar replacement d)
            (DirectTerm.dropBoundFree shift d) q := by
        simpa [dropBoundCast] using hq
      simp [dropBoundCast, dropBound,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite, hp', hq']
  | all p ih =>
      intro d h
      have hp := ih (d + 1) (by omega)
      cases h
      have hp' : dropBound replacement shift (d + 1) p =
          FailureOfComposition.Palomar.Arithmetic.Formula.rewrite
            (DirectTerm.dropBoundVar replacement (d + 1))
            (DirectTerm.dropBoundFree shift (d + 1)) p := by
        simpa [dropBoundCast] using hp
      simp [dropBoundCast, dropBound,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite, hp',
        DirectTerm.underBinder_dropBoundVar,
        DirectTerm.lift_dropBoundFree]
  | exs p ih =>
      intro d h
      have hp := ih (d + 1) (by omega)
      cases h
      have hp' : dropBound replacement shift (d + 1) p =
          FailureOfComposition.Palomar.Arithmetic.Formula.rewrite
            (DirectTerm.dropBoundVar replacement (d + 1))
            (DirectTerm.dropBoundFree shift (d + 1)) p := by
        simpa [dropBoundCast] using hp
      simp [dropBoundCast, dropBound,
        FailureOfComposition.Palomar.Arithmetic.Formula.rewrite, hp',
        DirectTerm.underBinder_dropBoundVar,
        DirectTerm.lift_dropBoundFree]

theorem dropBound_eq_rewrite
    (replacement : FailureOfComposition.Palomar.Arithmetic.Term ℕ 0)
    (shift : Bool) (d : ℕ)
    (p : FailureOfComposition.Palomar.Arithmetic.Formula ℕ (d + 1)) :
    dropBound replacement shift d p =
      FailureOfComposition.Palomar.Arithmetic.Formula.rewrite
        (DirectTerm.dropBoundVar replacement d)
        (DirectTerm.dropBoundFree shift d) p := by
  simpa [dropBoundCast] using
    dropBoundCast_eq_rewrite replacement shift p d rfl

theorem dropBound_free
    (p : FailureOfComposition.Palomar.Arithmetic.Semiproposition 1) :
    dropBound
        (FailureOfComposition.Palomar.Arithmetic.Term.fvar 0) true 0 p =
      FailureOfComposition.Palomar.Arithmetic.Formula.free p := by
  rw [dropBound_eq_rewrite]
  unfold FailureOfComposition.Palomar.Arithmetic.Formula.free
  congr 1

theorem dropBound_substOne
    (p : FailureOfComposition.Palomar.Arithmetic.Semiproposition 1)
    (t : FailureOfComposition.Palomar.Arithmetic.SyntacticTerm 0) :
    dropBound t false 0 p =
      FailureOfComposition.Palomar.Arithmetic.Formula.substOne p t := by
  rw [dropBound_eq_rewrite]
  unfold FailureOfComposition.Palomar.Arithmetic.Formula.substOne
  congr 1
  funext i
  simp [DirectTerm.dropBoundVar]

theorem encode_dropBoundCast
    (replacement : FailureOfComposition.Palomar.Arithmetic.Term ℕ 0)
    (shift : Bool) {n : ℕ}
    (p : FailureOfComposition.Palomar.Arithmetic.Formula ℕ n) :
    ∀ (d : ℕ) (h : n = d + 1),
    formulaTransformCode
        ((1, Encodable.encode replacement), if shift then 1 else 0)
        d (Encodable.encode p) =
      Encodable.encode (dropBoundCast replacement shift d h p) := by
  induction p with
  | verum =>
      intro d h
      cases h
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        pairSucc, dropBoundCast, dropBound]
  | falsum =>
      intro d h
      cases h
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        pairSucc, dropBoundCast, dropBound]
  | equal s t =>
      intro d h
      cases h
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaAtomPayload, transformTermVec,
        DirectTerm.encode_dropBound, listCode, Nat.natToList,
        dropBoundCast, dropBound, pairSucc]
  | nequal s t =>
      intro d h
      cases h
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaAtomPayload, transformTermVec,
        DirectTerm.encode_dropBound, listCode, Nat.natToList,
        dropBoundCast, dropBound, pairSucc]
  | less s t =>
      intro d h
      cases h
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaAtomPayload, transformTermVec,
        DirectTerm.encode_dropBound, listCode, Nat.natToList,
        dropBoundCast, dropBound, pairSucc]
  | nless s t =>
      intro d h
      cases h
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaAtomPayload, transformTermVec,
        DirectTerm.encode_dropBound, listCode, Nat.natToList,
        dropBoundCast, dropBound, pairSucc]
  | and p q ihp ihq =>
      intro d h
      have hp := ihp d h
      have hq := ihq d h
      cases h
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        formulaBinaryOrQuantArm, dropBoundCast, dropBound, hp, hq,
        pairSucc]
  | or p q ihp ihq =>
      intro d h
      have hp := ihp d h
      have hq := ihq d h
      cases h
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        formulaBinaryOrQuantArm, dropBoundCast, dropBound, hp, hq,
        pairSucc]
  | all p ih =>
      intro d h
      have hp := ih (d + 1) (by omega)
      cases h
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        formulaBinaryOrQuantArm, formulaQuantArm, dropBoundCast,
        dropBound, hp, pairSucc]
  | exs p ih =>
      intro d h
      have hp := ih (d + 1) (by omega)
      cases h
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        formulaBinaryOrQuantArm, formulaQuantArm, dropBoundCast,
        dropBound, hp, pairSucc]

theorem encode_dropBound
    (replacement : FailureOfComposition.Palomar.Arithmetic.Term ℕ 0)
    (shift : Bool) (d : ℕ)
    (p : FailureOfComposition.Palomar.Arithmetic.Formula ℕ (d + 1)) :
    formulaTransformCode
        ((1, Encodable.encode replacement), if shift then 1 else 0)
        d (Encodable.encode p) =
      Encodable.encode (dropBound replacement shift d p) := by
  simpa [dropBoundCast] using
    encode_dropBoundCast replacement shift p d rfl

theorem encode_actual_shiftFree {d : ℕ}
    (p : FailureOfComposition.Palomar.Arithmetic.Formula ℕ d) :
    formulaTransformCode ((0, 0), 1) 0 (Encodable.encode p) =
      Encodable.encode
        (FailureOfComposition.Palomar.Arithmetic.Formula.shiftFree p) := by
  exact (encode_shiftFree 0 p).trans (congrArg Encodable.encode
    (shiftFree_eq p))

theorem encode_actual_free
    (p : FailureOfComposition.Palomar.Arithmetic.Semiproposition 1) :
    formulaTransformCode
        ((1, Encodable.encode
          (FailureOfComposition.Palomar.Arithmetic.Term.fvar 0 :
            FailureOfComposition.Palomar.Arithmetic.SyntacticTerm 0)), 1)
        0 (Encodable.encode p) =
      Encodable.encode
        (FailureOfComposition.Palomar.Arithmetic.Formula.free p) := by
  exact (encode_dropBound
    (FailureOfComposition.Palomar.Arithmetic.Term.fvar 0) true 0 p).trans
      (congrArg Encodable.encode (dropBound_free p))

theorem encode_actual_substOne
    (p : FailureOfComposition.Palomar.Arithmetic.Semiproposition 1)
    (t : FailureOfComposition.Palomar.Arithmetic.SyntacticTerm 0) :
    formulaTransformCode ((1, Encodable.encode t), 0) 0
        (Encodable.encode p) =
      Encodable.encode
        (FailureOfComposition.Palomar.Arithmetic.Formula.substOne p t) := by
  exact (encode_dropBound t false 0 p).trans
    (congrArg Encodable.encode (dropBound_substOne p t))

theorem actual_shiftFree_primrec :
    Primrec
      (FailureOfComposition.Palomar.Arithmetic.Formula.shiftFree :
        FailureOfComposition.Palomar.Arithmetic.Proposition →
          FailureOfComposition.Palomar.Arithmetic.Proposition) := by
  apply Primrec.encode_iff.mp
  have hcode : Primrec
      (fun p : FailureOfComposition.Palomar.Arithmetic.Proposition ↦
        formulaTransformCode ((0, 0), 1) 0 (Encodable.encode p)) :=
    formulaTransformCode_primrec.comp
      (Primrec.pair
        (Primrec.pair (Primrec.const ((0, 0), 1)) (Primrec.const 0))
        Primrec.encode)
  exact hcode.of_eq fun p ↦ encode_actual_shiftFree p

theorem actual_free_primrec :
    Primrec
      (FailureOfComposition.Palomar.Arithmetic.Formula.free :
        FailureOfComposition.Palomar.Arithmetic.Semiproposition 1 →
          FailureOfComposition.Palomar.Arithmetic.Proposition) := by
  apply Primrec.encode_iff.mp
  let replacementCode := Encodable.encode
    (FailureOfComposition.Palomar.Arithmetic.Term.fvar 0 :
      FailureOfComposition.Palomar.Arithmetic.SyntacticTerm 0)
  have hcode : Primrec
      (fun p : FailureOfComposition.Palomar.Arithmetic.Semiproposition 1 ↦
        formulaTransformCode ((1, replacementCode), 1) 0
          (Encodable.encode p)) :=
    formulaTransformCode_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.const ((1, replacementCode), 1)) (Primrec.const 0))
        Primrec.encode)
  apply hcode.of_eq
  intro p
  exact encode_actual_free p

theorem actual_substOne_primrec :
    Primrec₂
      (FailureOfComposition.Palomar.Arithmetic.Formula.substOne :
        FailureOfComposition.Palomar.Arithmetic.Semiproposition 1 →
          FailureOfComposition.Palomar.Arithmetic.SyntacticTerm 0 →
            FailureOfComposition.Palomar.Arithmetic.Proposition) := by
  apply Primrec₂.encode_iff.mp
  have hcode : Primrec
      (fun q : FailureOfComposition.Palomar.Arithmetic.Semiproposition 1 ×
          FailureOfComposition.Palomar.Arithmetic.SyntacticTerm 0 ↦
        formulaTransformCode ((1, Encodable.encode q.2), 0) 0
          (Encodable.encode q.1)) :=
    formulaTransformCode_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.pair
            (Primrec.pair (Primrec.const 1)
              (Primrec.encode.comp Primrec.snd))
            (Primrec.const 0))
          (Primrec.const 0))
        (Primrec.encode.comp Primrec.fst))
  exact (hcode.of_eq fun q ↦ encode_actual_substOne q.1 q.2).to₂

theorem encode_actual_neg (depth : ℕ) {d : ℕ}
    (p : FailureOfComposition.Palomar.Arithmetic.Formula ℕ d) :
    formulaTransformCode ((2, 0), 0) depth (Encodable.encode p) =
      Encodable.encode
        (FailureOfComposition.Palomar.Arithmetic.Formula.neg p) := by
  induction p generalizing depth with
  | verum =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        formulaOutputTag, negateFormulaTag,
        FailureOfComposition.Palomar.Arithmetic.Formula.neg, pairSucc]
  | falsum =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        formulaOutputTag, negateFormulaTag,
        FailureOfComposition.Palomar.Arithmetic.Formula.neg, pairSucc]
  | equal s t =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaAtomPayload, transformTermVec,
        formulaOutputTag, negateFormulaTag, DirectTerm.encode_identity,
        listCode, Nat.natToList,
        FailureOfComposition.Palomar.Arithmetic.Formula.neg, pairSucc]
  | nequal s t =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaAtomPayload, transformTermVec,
        formulaOutputTag, negateFormulaTag, DirectTerm.encode_identity,
        listCode, Nat.natToList,
        FailureOfComposition.Palomar.Arithmetic.Formula.neg, pairSucc]
  | less s t =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaAtomPayload, transformTermVec,
        formulaOutputTag, negateFormulaTag, DirectTerm.encode_identity,
        listCode, Nat.natToList,
        FailureOfComposition.Palomar.Arithmetic.Formula.neg, pairSucc]
  | nless s t =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaAtomPayload, transformTermVec,
        formulaOutputTag, negateFormulaTag, DirectTerm.encode_identity,
        listCode, Nat.natToList,
        FailureOfComposition.Palomar.Arithmetic.Formula.neg, pairSucc]
  | and p q ihp ihq =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        formulaBinaryOrQuantArm, formulaOutputTag, negateFormulaTag,
        FailureOfComposition.Palomar.Arithmetic.Formula.neg, ihp, ihq,
        pairSucc]
  | or p q ihp ihq =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        formulaBinaryOrQuantArm, formulaOutputTag, negateFormulaTag,
        FailureOfComposition.Palomar.Arithmetic.Formula.neg, ihp, ihq,
        pairSucc]
  | all p ih =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        formulaBinaryOrQuantArm, formulaQuantArm, formulaOutputTag,
        negateFormulaTag,
        FailureOfComposition.Palomar.Arithmetic.Formula.neg, ih,
        pairSucc]
  | exs p ih =>
      simp [formulaTransformCode, formulaTransformBody,
        formulaAtomicOrRestArm, formulaConstOrRestArm,
        formulaBinaryOrQuantArm, formulaQuantArm, formulaOutputTag,
        negateFormulaTag,
        FailureOfComposition.Palomar.Arithmetic.Formula.neg, ih,
        pairSucc]

theorem actual_neg_primrec {d : ℕ} :
    Primrec
      (FailureOfComposition.Palomar.Arithmetic.Formula.neg :
        FailureOfComposition.Palomar.Arithmetic.Formula ℕ d →
          FailureOfComposition.Palomar.Arithmetic.Formula ℕ d) := by
  apply Primrec.encode_iff.mp
  have hcode : Primrec
      (fun p : FailureOfComposition.Palomar.Arithmetic.Formula ℕ d ↦
        formulaTransformCode ((2, 0), 0) 0 (Encodable.encode p)) :=
    formulaTransformCode_primrec.comp
      (Primrec.pair
        (Primrec.pair (Primrec.const ((2, 0), 0)) (Primrec.const 0))
        Primrec.encode)
  exact hcode.of_eq fun p ↦ encode_actual_neg 0 p

end DirectFormula

theorem atomFormulaCode_primrec {d : ℕ} (tag symbol : ℕ) :
    Primrec₂ (fun s t : FailureOfComposition.Palomar.Arithmetic.Term ℕ d ↦
      pairSucc tag (Nat.pair 2 (Nat.pair symbol
        (listCode [Encodable.encode s, Encodable.encode t])))) := by
  have hlist : Primrec
      (fun q : FailureOfComposition.Palomar.Arithmetic.Term ℕ d ×
          FailureOfComposition.Palomar.Arithmetic.Term ℕ d ↦
        listCode [Encodable.encode q.1, Encodable.encode q.2]) :=
    listCode_primrec.comp
      (Primrec.list_cons.comp
        (Primrec.encode.comp Primrec.fst)
        (Primrec.list_cons.comp
          (Primrec.encode.comp Primrec.snd) (Primrec.const [])))
  exact (pairSucc_primrec.comp (Primrec.const tag)
    (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.const symbol) hlist))).to₂

theorem formulaEqual_primrec {d : ℕ} :
    Primrec₂
      (FailureOfComposition.Palomar.Arithmetic.Formula.equal :
        FailureOfComposition.Palomar.Arithmetic.Term ℕ d →
          FailureOfComposition.Palomar.Arithmetic.Term ℕ d →
            FailureOfComposition.Palomar.Arithmetic.Formula ℕ d) := by
  apply Primrec₂.encode_iff.mp
  exact (atomFormulaCode_primrec 0 0).of_eq fun s t ↦
    (DirectFormula.encode_equal s t).symm

theorem formulaNequal_primrec {d : ℕ} :
    Primrec₂
      (FailureOfComposition.Palomar.Arithmetic.Formula.nequal :
        FailureOfComposition.Palomar.Arithmetic.Term ℕ d →
          FailureOfComposition.Palomar.Arithmetic.Term ℕ d →
            FailureOfComposition.Palomar.Arithmetic.Formula ℕ d) := by
  apply Primrec₂.encode_iff.mp
  exact (atomFormulaCode_primrec 1 0).of_eq fun s t ↦
    (DirectFormula.encode_nequal s t).symm

theorem formulaLess_primrec {d : ℕ} :
    Primrec₂
      (FailureOfComposition.Palomar.Arithmetic.Formula.less :
        FailureOfComposition.Palomar.Arithmetic.Term ℕ d →
          FailureOfComposition.Palomar.Arithmetic.Term ℕ d →
            FailureOfComposition.Palomar.Arithmetic.Formula ℕ d) := by
  apply Primrec₂.encode_iff.mp
  exact (atomFormulaCode_primrec 0 1).of_eq fun s t ↦
    (DirectFormula.encode_less s t).symm

theorem formulaNless_primrec {d : ℕ} :
    Primrec₂
      (FailureOfComposition.Palomar.Arithmetic.Formula.nless :
        FailureOfComposition.Palomar.Arithmetic.Term ℕ d →
          FailureOfComposition.Palomar.Arithmetic.Term ℕ d →
            FailureOfComposition.Palomar.Arithmetic.Formula ℕ d) := by
  apply Primrec₂.encode_iff.mp
  exact (atomFormulaCode_primrec 1 1).of_eq fun s t ↦
    (DirectFormula.encode_nless s t).symm

theorem binaryFormulaCode_primrec {d : ℕ} (tag : ℕ) :
    Primrec₂
      (fun p q : FailureOfComposition.Palomar.Arithmetic.Formula ℕ d ↦
        pairSucc tag (Nat.pair (Encodable.encode p) (Encodable.encode q))) := by
  exact (pairSucc_primrec.comp (Primrec.const tag)
    (Primrec₂.natPair.comp
      (Primrec.encode.comp Primrec.fst)
      (Primrec.encode.comp Primrec.snd))).to₂

theorem formulaAnd_primrec {d : ℕ} :
    Primrec₂
      (FailureOfComposition.Palomar.Arithmetic.Formula.and :
        FailureOfComposition.Palomar.Arithmetic.Formula ℕ d →
          FailureOfComposition.Palomar.Arithmetic.Formula ℕ d →
            FailureOfComposition.Palomar.Arithmetic.Formula ℕ d) := by
  apply Primrec₂.encode_iff.mp
  exact (binaryFormulaCode_primrec 4).of_eq fun p q ↦
    (DirectFormula.encode_and p q).symm

theorem formulaOr_primrec {d : ℕ} :
    Primrec₂
      (FailureOfComposition.Palomar.Arithmetic.Formula.or :
        FailureOfComposition.Palomar.Arithmetic.Formula ℕ d →
          FailureOfComposition.Palomar.Arithmetic.Formula ℕ d →
            FailureOfComposition.Palomar.Arithmetic.Formula ℕ d) := by
  apply Primrec₂.encode_iff.mp
  exact (binaryFormulaCode_primrec 5).of_eq fun p q ↦
    (DirectFormula.encode_or p q).symm

theorem formulaAll_primrec {d : ℕ} :
    Primrec
      (FailureOfComposition.Palomar.Arithmetic.Formula.all :
        FailureOfComposition.Palomar.Arithmetic.Formula ℕ (d + 1) →
          FailureOfComposition.Palomar.Arithmetic.Formula ℕ d) := by
  apply Primrec.encode_iff.mp
  exact (pairSucc_primrec.comp (Primrec.const 6) Primrec.encode).of_eq
    fun p ↦ (DirectFormula.encode_all p).symm

theorem formulaExs_primrec {d : ℕ} :
    Primrec
      (FailureOfComposition.Palomar.Arithmetic.Formula.exs :
        FailureOfComposition.Palomar.Arithmetic.Formula ℕ (d + 1) →
          FailureOfComposition.Palomar.Arithmetic.Formula ℕ d) := by
  apply Primrec.encode_iff.mp
  exact (pairSucc_primrec.comp (Primrec.const 7) Primrec.encode).of_eq
    fun p ↦ (DirectFormula.encode_exs p).symm

theorem encode_embed
    (p : FailureOfComposition.Palomar.Arithmetic.Sentence) :
    Encodable.encode
        (FailureOfComposition.Palomar.Arithmetic.Formula.embed p) =
      Encodable.encode p := by
  change Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Formula.toFoundation
        (FailureOfComposition.Palomar.Arithmetic.Formula.embed p)) =
    Encodable.encode
      (FailureOfComposition.Palomar.Arithmetic.Formula.toFoundation p)
  simp

theorem formulaEmbed_primrec :
    Primrec
      (FailureOfComposition.Palomar.Arithmetic.Formula.embed :
        FailureOfComposition.Palomar.Arithmetic.Sentence →
          FailureOfComposition.Palomar.Arithmetic.Proposition) := by
  apply Primrec.encode_iff.mp
  exact Primrec.encode.of_eq fun p ↦ (encode_embed p).symm

abbrev DerivationInstruction :=
  ℕ × List FailureOfComposition.Palomar.Arithmetic.Proposition ×
    List FailureOfComposition.Palomar.Arithmetic.Proposition ×
    FailureOfComposition.Palomar.Arithmetic.Proposition ×
    FailureOfComposition.Palomar.Arithmetic.Proposition ×
    FailureOfComposition.Palomar.Arithmetic.Semiproposition 1 ×
    FailureOfComposition.Palomar.Arithmetic.SyntacticTerm 0 ×
    FailureOfComposition.Palomar.Arithmetic.SyntacticTerm 0

def instructionTag (i : DerivationInstruction) : ℕ := i.1
def instructionGamma (i : DerivationInstruction) :
    List FailureOfComposition.Palomar.Arithmetic.Proposition := i.2.1
def instructionDelta (i : DerivationInstruction) :
    List FailureOfComposition.Palomar.Arithmetic.Proposition := i.2.2.1
def instructionP (i : DerivationInstruction) :
    FailureOfComposition.Palomar.Arithmetic.Proposition := i.2.2.2.1
def instructionQ (i : DerivationInstruction) :
    FailureOfComposition.Palomar.Arithmetic.Proposition := i.2.2.2.2.1
def instructionR (i : DerivationInstruction) :
    FailureOfComposition.Palomar.Arithmetic.Semiproposition 1 :=
  i.2.2.2.2.2.1
def instructionS (i : DerivationInstruction) :
    FailureOfComposition.Palomar.Arithmetic.SyntacticTerm 0 :=
  i.2.2.2.2.2.2.1
def instructionT (i : DerivationInstruction) :
    FailureOfComposition.Palomar.Arithmetic.SyntacticTerm 0 :=
  i.2.2.2.2.2.2.2

def mkInstruction (tag : ℕ)
    (gamma delta : List FailureOfComposition.Palomar.Arithmetic.Proposition)
    (p q : FailureOfComposition.Palomar.Arithmetic.Proposition)
    (r : FailureOfComposition.Palomar.Arithmetic.Semiproposition 1)
    (s t : FailureOfComposition.Palomar.Arithmetic.SyntacticTerm 0) :
    DerivationInstruction :=
  (tag, gamma, delta, p, q, r, s, t)

def rulePremises (i : DerivationInstruction) :
    List (List FailureOfComposition.Palomar.Arithmetic.Proposition) :=
  if instructionTag i = 0 then []
  else if instructionTag i = 1 then []
  else if instructionTag i = 2 then
    [instructionDelta i ++
        [FailureOfComposition.Palomar.Arithmetic.Formula.neg (instructionP i)],
      instructionGamma i ++ [instructionP i]]
  else if instructionTag i = 3 then
    [instructionGamma i ++ [instructionP i, instructionP i]]
  else if instructionTag i = 4 then [instructionGamma i]
  else if instructionTag i = 5 then []
  else if instructionTag i = 6 then
    [instructionGamma i ++ [instructionP i, instructionQ i]]
  else if instructionTag i = 7 then
    [instructionGamma i ++ [instructionQ i],
      instructionGamma i ++ [instructionP i]]
  else if instructionTag i = 8 then
    [(instructionGamma i).map
        FailureOfComposition.Palomar.Arithmetic.Formula.shiftFree ++
      [FailureOfComposition.Palomar.Arithmetic.Formula.free (instructionR i)]]
  else if instructionTag i = 9 then
    [instructionGamma i ++
      [FailureOfComposition.Palomar.Arithmetic.Formula.substOne
        (instructionR i) (instructionS i)]]
  else if instructionTag i = 10 then
    [instructionGamma i ++ [instructionP i, instructionQ i] ++
      instructionDelta i]
  else []

def ruleConclusion (i : DerivationInstruction) :
    List FailureOfComposition.Palomar.Arithmetic.Proposition :=
  if instructionTag i = 0 then
    [FailureOfComposition.Palomar.Arithmetic.Formula.equal
        (instructionS i) (instructionT i),
      FailureOfComposition.Palomar.Arithmetic.Formula.nequal
        (instructionS i) (instructionT i)]
  else if instructionTag i = 1 then
    [FailureOfComposition.Palomar.Arithmetic.Formula.less
        (instructionS i) (instructionT i),
      FailureOfComposition.Palomar.Arithmetic.Formula.nless
        (instructionS i) (instructionT i)]
  else if instructionTag i = 2 then instructionGamma i ++ instructionDelta i
  else if instructionTag i = 3 then instructionGamma i ++ [instructionP i]
  else if instructionTag i = 4 then instructionGamma i ++ [instructionP i]
  else if instructionTag i = 5 then
    [FailureOfComposition.Palomar.Arithmetic.Formula.verum]
  else if instructionTag i = 6 then
    instructionGamma i ++
      [FailureOfComposition.Palomar.Arithmetic.Formula.or
        (instructionP i) (instructionQ i)]
  else if instructionTag i = 7 then
    instructionGamma i ++
      [FailureOfComposition.Palomar.Arithmetic.Formula.and
        (instructionP i) (instructionQ i)]
  else if instructionTag i = 8 then
    instructionGamma i ++
      [FailureOfComposition.Palomar.Arithmetic.Formula.all (instructionR i)]
  else if instructionTag i = 9 then
    instructionGamma i ++
      [FailureOfComposition.Palomar.Arithmetic.Formula.exs (instructionR i)]
  else if instructionTag i = 10 then
    instructionGamma i ++ [instructionQ i, instructionP i] ++
      instructionDelta i
  else []

abbrev DerivationStack :=
  List (List FailureOfComposition.Palomar.Arithmetic.Proposition)

def applyInstruction (i : DerivationInstruction)
    (stack : DerivationStack) : Option DerivationStack :=
  if instructionTag i < 11 then
    let premises := rulePremises i
    if stack.take premises.length = premises then
      some (ruleConclusion i :: stack.drop premises.length)
    else none
  else none

def derivationMachineStep (state : Option DerivationStack)
    (i : DerivationInstruction) : Option DerivationStack :=
  state.bind (applyInstruction i)

def runDerivationProgram (program : List DerivationInstruction) :
    Option DerivationStack :=
  program.foldl derivationMachineStep (some [])

theorem instructionTag_primrec : Primrec instructionTag := Primrec.fst
theorem instructionGamma_primrec : Primrec instructionGamma :=
  Primrec.fst.comp Primrec.snd
theorem instructionDelta_primrec : Primrec instructionDelta :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem instructionP_primrec : Primrec instructionP :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem instructionQ_primrec : Primrec instructionQ :=
  Primrec.fst.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
theorem instructionR_primrec : Primrec instructionR :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
theorem instructionS_primrec : Primrec instructionS :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
theorem instructionT_primrec : Primrec instructionT :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

theorem rulePremises_primrec : Primrec rulePremises := by
  let P := FailureOfComposition.Palomar.Arithmetic.Proposition
  let LP := List FailureOfComposition.Palomar.Arithmetic.Proposition
  have hnil : Primrec (fun _ : DerivationInstruction ↦ ([] : List LP)) :=
    Primrec.const []
  have hnegP : Primrec (fun i : DerivationInstruction ↦
      FailureOfComposition.Palomar.Arithmetic.Formula.neg (instructionP i)) :=
    DirectFormula.actual_neg_primrec.comp instructionP_primrec
  have hsingleP : Primrec (fun i : DerivationInstruction ↦
      [instructionP i]) :=
    Primrec.list_cons.comp instructionP_primrec (Primrec.const [])
  have hsingleQ : Primrec (fun i : DerivationInstruction ↦
      [instructionQ i]) :=
    Primrec.list_cons.comp instructionQ_primrec (Primrec.const [])
  have hsingleNegP : Primrec (fun i : DerivationInstruction ↦
      [FailureOfComposition.Palomar.Arithmetic.Formula.neg (instructionP i)]) :=
    Primrec.list_cons.comp hnegP (Primrec.const [])
  have hgammaP : Primrec (fun i : DerivationInstruction ↦
      instructionGamma i ++ [instructionP i]) :=
    Primrec.list_append.comp instructionGamma_primrec hsingleP
  have hgammaQ : Primrec (fun i : DerivationInstruction ↦
      instructionGamma i ++ [instructionQ i]) :=
    Primrec.list_append.comp instructionGamma_primrec hsingleQ
  have hdeltaNegP : Primrec (fun i : DerivationInstruction ↦
      instructionDelta i ++
        [FailureOfComposition.Palomar.Arithmetic.Formula.neg (instructionP i)]) :=
    Primrec.list_append.comp instructionDelta_primrec hsingleNegP
  have hcut : Primrec (fun i : DerivationInstruction ↦
      [instructionDelta i ++
          [FailureOfComposition.Palomar.Arithmetic.Formula.neg (instructionP i)],
        instructionGamma i ++ [instructionP i]]) :=
    Primrec.list_cons.comp hdeltaNegP
      (Primrec.list_cons.comp hgammaP (Primrec.const []))
  have hPP : Primrec (fun i : DerivationInstruction ↦
      [instructionP i, instructionP i]) :=
    Primrec.list_cons.comp instructionP_primrec
      (Primrec.list_cons.comp instructionP_primrec (Primrec.const []))
  have hcontractionPremise : Primrec (fun i : DerivationInstruction ↦
      instructionGamma i ++ [instructionP i, instructionP i]) :=
    Primrec.list_append.comp instructionGamma_primrec hPP
  have hcontraction : Primrec (fun i : DerivationInstruction ↦
      [instructionGamma i ++ [instructionP i, instructionP i]]) :=
    Primrec.list_cons.comp hcontractionPremise (Primrec.const [])
  have hweakening : Primrec (fun i : DerivationInstruction ↦
      [instructionGamma i]) :=
    Primrec.list_cons.comp instructionGamma_primrec (Primrec.const [])
  have hPQ : Primrec (fun i : DerivationInstruction ↦
      [instructionP i, instructionQ i]) :=
    Primrec.list_cons.comp instructionP_primrec
      (Primrec.list_cons.comp instructionQ_primrec (Primrec.const []))
  have horPremise : Primrec (fun i : DerivationInstruction ↦
      instructionGamma i ++ [instructionP i, instructionQ i]) :=
    Primrec.list_append.comp instructionGamma_primrec hPQ
  have hor : Primrec (fun i : DerivationInstruction ↦
      [instructionGamma i ++ [instructionP i, instructionQ i]]) :=
    Primrec.list_cons.comp horPremise (Primrec.const [])
  have hand : Primrec (fun i : DerivationInstruction ↦
      [instructionGamma i ++ [instructionQ i],
        instructionGamma i ++ [instructionP i]]) :=
    Primrec.list_cons.comp hgammaQ
      (Primrec.list_cons.comp hgammaP (Primrec.const []))
  have hshiftGamma : Primrec (fun i : DerivationInstruction ↦
      (instructionGamma i).map
        FailureOfComposition.Palomar.Arithmetic.Formula.shiftFree) :=
    Primrec.list_map instructionGamma_primrec
      (DirectFormula.actual_shiftFree_primrec.comp Primrec.snd).to₂
  have hfreeR : Primrec (fun i : DerivationInstruction ↦
      FailureOfComposition.Palomar.Arithmetic.Formula.free
        (instructionR i)) :=
    DirectFormula.actual_free_primrec.comp instructionR_primrec
  have hallPremise : Primrec (fun i : DerivationInstruction ↦
      (instructionGamma i).map
          FailureOfComposition.Palomar.Arithmetic.Formula.shiftFree ++
        [FailureOfComposition.Palomar.Arithmetic.Formula.free
          (instructionR i)]) :=
    Primrec.list_append.comp hshiftGamma
      (Primrec.list_cons.comp hfreeR (Primrec.const []))
  have hall : Primrec (fun i : DerivationInstruction ↦
      [(instructionGamma i).map
          FailureOfComposition.Palomar.Arithmetic.Formula.shiftFree ++
        [FailureOfComposition.Palomar.Arithmetic.Formula.free
          (instructionR i)]]) :=
    Primrec.list_cons.comp hallPremise (Primrec.const [])
  have hsubstR : Primrec (fun i : DerivationInstruction ↦
      FailureOfComposition.Palomar.Arithmetic.Formula.substOne
        (instructionR i) (instructionS i)) :=
    DirectFormula.actual_substOne_primrec.comp
      instructionR_primrec instructionS_primrec
  have hexsPremise : Primrec (fun i : DerivationInstruction ↦
      instructionGamma i ++
        [FailureOfComposition.Palomar.Arithmetic.Formula.substOne
          (instructionR i) (instructionS i)]) :=
    Primrec.list_append.comp instructionGamma_primrec
      (Primrec.list_cons.comp hsubstR (Primrec.const []))
  have hexs : Primrec (fun i : DerivationInstruction ↦
      [instructionGamma i ++
        [FailureOfComposition.Palomar.Arithmetic.Formula.substOne
          (instructionR i) (instructionS i)]]) :=
    Primrec.list_cons.comp hexsPremise (Primrec.const [])
  have hswapPrefix : Primrec (fun i : DerivationInstruction ↦
      instructionGamma i ++ [instructionP i, instructionQ i]) :=
    Primrec.list_append.comp instructionGamma_primrec hPQ
  have hswapPremise : Primrec (fun i : DerivationInstruction ↦
      instructionGamma i ++ [instructionP i, instructionQ i] ++
        instructionDelta i) :=
    Primrec.list_append.comp hswapPrefix instructionDelta_primrec
  have hswap : Primrec (fun i : DerivationInstruction ↦
      [instructionGamma i ++ [instructionP i, instructionQ i] ++
        instructionDelta i]) :=
    Primrec.list_cons.comp hswapPremise (Primrec.const [])
  have htag (k : ℕ) : PrimrecPred (fun i : DerivationInstruction ↦
      instructionTag i = k) :=
    Primrec.eq.comp instructionTag_primrec (Primrec.const k)
  exact (Primrec.ite (htag 0) hnil
    (Primrec.ite (htag 1) hnil
      (Primrec.ite (htag 2) hcut
        (Primrec.ite (htag 3) hcontraction
          (Primrec.ite (htag 4) hweakening
            (Primrec.ite (htag 5) hnil
              (Primrec.ite (htag 6) hor
                (Primrec.ite (htag 7) hand
                  (Primrec.ite (htag 8) hall
                    (Primrec.ite (htag 9) hexs
                      (Primrec.ite (htag 10) hswap hnil))))))))))).of_eq
    (fun _ ↦ by rfl)

theorem ruleConclusion_primrec : Primrec ruleConclusion := by
  let P := FailureOfComposition.Palomar.Arithmetic.Proposition
  have hequal : Primrec (fun i : DerivationInstruction ↦
      FailureOfComposition.Palomar.Arithmetic.Formula.equal
        (instructionS i) (instructionT i)) :=
    formulaEqual_primrec.comp instructionS_primrec instructionT_primrec
  have hnequal : Primrec (fun i : DerivationInstruction ↦
      FailureOfComposition.Palomar.Arithmetic.Formula.nequal
        (instructionS i) (instructionT i)) :=
    formulaNequal_primrec.comp instructionS_primrec instructionT_primrec
  have hless : Primrec (fun i : DerivationInstruction ↦
      FailureOfComposition.Palomar.Arithmetic.Formula.less
        (instructionS i) (instructionT i)) :=
    formulaLess_primrec.comp instructionS_primrec instructionT_primrec
  have hnless : Primrec (fun i : DerivationInstruction ↦
      FailureOfComposition.Palomar.Arithmetic.Formula.nless
        (instructionS i) (instructionT i)) :=
    formulaNless_primrec.comp instructionS_primrec instructionT_primrec
  have hidEqual : Primrec (fun i : DerivationInstruction ↦
      [FailureOfComposition.Palomar.Arithmetic.Formula.equal
          (instructionS i) (instructionT i),
        FailureOfComposition.Palomar.Arithmetic.Formula.nequal
          (instructionS i) (instructionT i)]) :=
    Primrec.list_cons.comp hequal
      (Primrec.list_cons.comp hnequal (Primrec.const []))
  have hidLess : Primrec (fun i : DerivationInstruction ↦
      [FailureOfComposition.Palomar.Arithmetic.Formula.less
          (instructionS i) (instructionT i),
        FailureOfComposition.Palomar.Arithmetic.Formula.nless
          (instructionS i) (instructionT i)]) :=
    Primrec.list_cons.comp hless
      (Primrec.list_cons.comp hnless (Primrec.const []))
  have hcut : Primrec (fun i : DerivationInstruction ↦
      instructionGamma i ++ instructionDelta i) :=
    Primrec.list_append.comp instructionGamma_primrec instructionDelta_primrec
  have hsingleP : Primrec (fun i : DerivationInstruction ↦
      [instructionP i]) :=
    Primrec.list_cons.comp instructionP_primrec (Primrec.const [])
  have hgammaP : Primrec (fun i : DerivationInstruction ↦
      instructionGamma i ++ [instructionP i]) :=
    Primrec.list_append.comp instructionGamma_primrec hsingleP
  have hverum : Primrec (fun _ : DerivationInstruction ↦
      ([FailureOfComposition.Palomar.Arithmetic.Formula.verum] : List P)) :=
    Primrec.const [FailureOfComposition.Palomar.Arithmetic.Formula.verum]
  have horFormula : Primrec (fun i : DerivationInstruction ↦
      FailureOfComposition.Palomar.Arithmetic.Formula.or
        (instructionP i) (instructionQ i)) :=
    formulaOr_primrec.comp instructionP_primrec instructionQ_primrec
  have handFormula : Primrec (fun i : DerivationInstruction ↦
      FailureOfComposition.Palomar.Arithmetic.Formula.and
        (instructionP i) (instructionQ i)) :=
    formulaAnd_primrec.comp instructionP_primrec instructionQ_primrec
  have hallFormula : Primrec (fun i : DerivationInstruction ↦
      FailureOfComposition.Palomar.Arithmetic.Formula.all
        (instructionR i)) :=
    formulaAll_primrec.comp instructionR_primrec
  have hexsFormula : Primrec (fun i : DerivationInstruction ↦
      FailureOfComposition.Palomar.Arithmetic.Formula.exs
        (instructionR i)) :=
    formulaExs_primrec.comp instructionR_primrec
  have hor : Primrec (fun i : DerivationInstruction ↦
      instructionGamma i ++
        [FailureOfComposition.Palomar.Arithmetic.Formula.or
          (instructionP i) (instructionQ i)]) :=
    Primrec.list_append.comp instructionGamma_primrec
      (Primrec.list_cons.comp horFormula (Primrec.const []))
  have hand : Primrec (fun i : DerivationInstruction ↦
      instructionGamma i ++
        [FailureOfComposition.Palomar.Arithmetic.Formula.and
          (instructionP i) (instructionQ i)]) :=
    Primrec.list_append.comp instructionGamma_primrec
      (Primrec.list_cons.comp handFormula (Primrec.const []))
  have hall : Primrec (fun i : DerivationInstruction ↦
      instructionGamma i ++
        [FailureOfComposition.Palomar.Arithmetic.Formula.all
          (instructionR i)]) :=
    Primrec.list_append.comp instructionGamma_primrec
      (Primrec.list_cons.comp hallFormula (Primrec.const []))
  have hexs : Primrec (fun i : DerivationInstruction ↦
      instructionGamma i ++
        [FailureOfComposition.Palomar.Arithmetic.Formula.exs
          (instructionR i)]) :=
    Primrec.list_append.comp instructionGamma_primrec
      (Primrec.list_cons.comp hexsFormula (Primrec.const []))
  have hQP : Primrec (fun i : DerivationInstruction ↦
      [instructionQ i, instructionP i]) :=
    Primrec.list_cons.comp instructionQ_primrec
      (Primrec.list_cons.comp instructionP_primrec (Primrec.const []))
  have hswapPrefix : Primrec (fun i : DerivationInstruction ↦
      instructionGamma i ++ [instructionQ i, instructionP i]) :=
    Primrec.list_append.comp instructionGamma_primrec hQP
  have hswap : Primrec (fun i : DerivationInstruction ↦
      instructionGamma i ++ [instructionQ i, instructionP i] ++
        instructionDelta i) :=
    Primrec.list_append.comp hswapPrefix instructionDelta_primrec
  have hnil : Primrec (fun _ : DerivationInstruction ↦ ([] : List P)) :=
    Primrec.const []
  have htag (k : ℕ) : PrimrecPred (fun i : DerivationInstruction ↦
      instructionTag i = k) :=
    Primrec.eq.comp instructionTag_primrec (Primrec.const k)
  exact (Primrec.ite (htag 0) hidEqual
    (Primrec.ite (htag 1) hidLess
      (Primrec.ite (htag 2) hcut
        (Primrec.ite (htag 3) hgammaP
          (Primrec.ite (htag 4) hgammaP
            (Primrec.ite (htag 5) hverum
              (Primrec.ite (htag 6) hor
                (Primrec.ite (htag 7) hand
                  (Primrec.ite (htag 8) hall
                    (Primrec.ite (htag 9) hexs
                      (Primrec.ite (htag 10) hswap hnil))))))))))).of_eq
    (fun _ ↦ by rfl)

theorem applyInstruction_primrec : Primrec₂ applyInstruction := by
  let Q := DerivationInstruction × DerivationStack
  have hpremises : Primrec (fun q : Q ↦ rulePremises q.1) :=
    rulePremises_primrec.comp Primrec.fst
  have hlength : Primrec (fun q : Q ↦ (rulePremises q.1).length) :=
    Primrec.list_length.comp hpremises
  have htake : Primrec (fun q : Q ↦
      q.2.take (rulePremises q.1).length) :=
    Primrec.list_take.comp hlength Primrec.snd
  have hdrop : Primrec (fun q : Q ↦
      q.2.drop (rulePremises q.1).length) :=
    Primrec.list_drop.comp hlength Primrec.snd
  have hmatch : PrimrecPred (fun q : Q ↦
      q.2.take (rulePremises q.1).length = rulePremises q.1) :=
    Primrec.eq.comp htake hpremises
  have hknown : PrimrecPred (fun q : Q ↦ instructionTag q.1 < 11) :=
    Primrec.nat_lt.comp (instructionTag_primrec.comp Primrec.fst)
      (Primrec.const 11)
  have hsuccess : Primrec (fun q : Q ↦
      some (ruleConclusion q.1 ::
        q.2.drop (rulePremises q.1).length)) :=
    Primrec.option_some.comp
      (Primrec.list_cons.comp
        (ruleConclusion_primrec.comp Primrec.fst) hdrop)
  have hfailure : Primrec (fun _ : Q ↦
      (none : Option DerivationStack)) := Primrec.const none
  exact (Primrec.ite hknown (Primrec.ite hmatch hsuccess hfailure)
    hfailure).to₂.of_eq fun i stack ↦ by rfl

theorem derivationMachineStep_primrec :
    Primrec₂ derivationMachineStep := by
  have hsome : Primrec₂
      (fun q : Option DerivationStack × DerivationInstruction =>
        fun stack : DerivationStack ↦ applyInstruction q.2 stack) :=
    (applyInstruction_primrec.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hcases := Primrec.option_casesOn
    (o := fun q : Option DerivationStack × DerivationInstruction ↦ q.1)
    (f := fun _ ↦ (none : Option DerivationStack))
    (g := fun q stack ↦ applyInstruction q.2 stack)
    Primrec.fst (Primrec.const none) hsome
  exact hcases.to₂.of_eq fun state i ↦ by cases state <;> rfl

theorem runDerivationProgram_primrec : Primrec runDerivationProgram := by
  have hfold : Primrec (fun program : List DerivationInstruction ↦
      program.foldl derivationMachineStep (some [])) := by
    exact Primrec.list_foldl Primrec.id (Primrec.const (some []))
      ((derivationMachineStep_primrec.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂)
  exact hfold

def ListDerivable
    (l : List FailureOfComposition.Palomar.Arithmetic.Proposition) : Prop :=
  Nonempty (FailureOfComposition.Palomar.Arithmetic.Derivation
    (l : Multiset FailureOfComposition.Palomar.Arithmetic.Proposition))

private theorem coe_pair (p q : Proposition) :
    (([p, q] : List Proposition) : Multiset Proposition) =
      Sequent.pair p q := by
  rw [show ([p, q] : List Proposition) = p :: [q] by rfl]
  rw [← Multiset.cons_coe]
  rw [show ([q] : List Proposition) = q :: [] by rfl]
  rw [← Multiset.cons_coe]
  rfl

private theorem coe_append (gamma delta : List Proposition) :
    ((gamma ++ delta : List Proposition) : Multiset Proposition) =
      (gamma : Multiset Proposition) + (delta : Multiset Proposition) := by
  rw [← Multiset.coe_add]

private theorem coe_append_singleton
    (gamma : List Proposition) (p : Proposition) :
    ((gamma ++ [p] : List Proposition) : Multiset Proposition) =
      (gamma : Multiset Proposition) + Sequent.singleton p := by
  rw [← Multiset.coe_add]
  rfl

private theorem coe_append_pair
    (gamma : List Proposition) (p q : Proposition) :
    ((gamma ++ [p, q] : List Proposition) : Multiset Proposition) =
      (gamma : Multiset Proposition) + Sequent.pair p q := by
  rw [← Multiset.coe_add]
  rfl

private theorem coe_map_shift_append_singleton
    (gamma : List Proposition) (p : Semiproposition 1) :
    (((gamma.map Formula.shiftFree) ++ [p.free] : List Proposition) :
      Multiset Proposition) =
      Sequent.shiftFree (gamma : Multiset Proposition) +
        Sequent.singleton p.free := by
  rw [← Multiset.coe_add]
  rfl

private theorem coe_adjacent_swap
    (gamma delta : List Proposition) (p q : Proposition) :
    ((gamma ++ [p, q] ++ delta : List Proposition) :
      Multiset Proposition) =
      ((gamma ++ [q, p] ++ delta : List Proposition) :
        Multiset Proposition) := by
  calc
    ((gamma ++ [p, q] ++ delta : List Proposition) :
        Multiset Proposition) =
        ((gamma ++ [p, q] : List Proposition) : Multiset Proposition) +
          (delta : Multiset Proposition) := coe_append _ _
    _ = ((gamma : Multiset Proposition) + Sequent.pair p q) +
          (delta : Multiset Proposition) := by rw [coe_append_pair]
    _ = ((gamma : Multiset Proposition) + Sequent.pair q p) +
          (delta : Multiset Proposition) := by
      exact congrArg
        (fun s : Multiset Proposition ↦
          ((gamma : Multiset Proposition) + s) +
            (delta : Multiset Proposition))
        (Multiset.cons_swap p q 0)
    _ = ((gamma ++ [q, p] : List Proposition) : Multiset Proposition) +
          (delta : Multiset Proposition) := by rw [coe_append_pair]
    _ = ((gamma ++ [q, p] ++ delta : List Proposition) :
          Multiset Proposition) := (coe_append _ _).symm

theorem rule_sound (i : DerivationInstruction)
    (hknown : instructionTag i < 11)
    (hpremises : ∀ l ∈ rulePremises i, ListDerivable l) :
    ListDerivable (ruleConclusion i) := by
  have hcases : instructionTag i = 0 ∨ instructionTag i = 1 ∨
      instructionTag i = 2 ∨ instructionTag i = 3 ∨
      instructionTag i = 4 ∨ instructionTag i = 5 ∨
      instructionTag i = 6 ∨ instructionTag i = 7 ∨
      instructionTag i = 8 ∨ instructionTag i = 9 ∨
      instructionTag i = 10 := by
    omega
  rcases hcases with htag | htag | htag | htag | htag | htag |
    htag | htag | htag | htag | htag
  · unfold ListDerivable
    rw [show ruleConclusion i =
        [Formula.equal (instructionS i) (instructionT i),
          Formula.nequal (instructionS i) (instructionT i)] by
      simp [ruleConclusion, htag], coe_pair]
    refine ⟨?_⟩
    exact FailureOfComposition.Palomar.Arithmetic.Derivation.identityEqual
      (instructionS i) (instructionT i)
  · unfold ListDerivable
    rw [show ruleConclusion i =
        [Formula.less (instructionS i) (instructionT i),
          Formula.nless (instructionS i) (instructionT i)] by
      simp [ruleConclusion, htag], coe_pair]
    refine ⟨?_⟩
    exact FailureOfComposition.Palomar.Arithmetic.Derivation.identityLess
      (instructionS i) (instructionT i)
  · have h :
        ListDerivable (instructionDelta i ++ [Formula.neg (instructionP i)]) ∧
          ListDerivable (instructionGamma i ++ [instructionP i]) := by
      simpa [rulePremises, htag] using hpremises
    rcases h with ⟨⟨d₂⟩, ⟨d₁⟩⟩
    rw [coe_append_singleton] at d₁ d₂
    unfold ListDerivable
    rw [show ruleConclusion i = instructionGamma i ++ instructionDelta i by
      simp [ruleConclusion, htag], coe_append]
    refine ⟨?_⟩
    exact FailureOfComposition.Palomar.Arithmetic.Derivation.cut d₁ d₂
  · have h : ListDerivable
        (instructionGamma i ++ [instructionP i, instructionP i]) := by
      simpa [rulePremises, htag] using hpremises
    rcases h with ⟨d⟩
    rw [coe_append_pair] at d
    unfold ListDerivable
    rw [show ruleConclusion i = instructionGamma i ++ [instructionP i] by
      simp [ruleConclusion, htag], coe_append_singleton]
    refine ⟨?_⟩
    exact FailureOfComposition.Palomar.Arithmetic.Derivation.contraction d
  · have h : ListDerivable (instructionGamma i) := by
      simpa [rulePremises, htag] using hpremises
    rcases h with ⟨d⟩
    unfold ListDerivable
    rw [show ruleConclusion i = instructionGamma i ++ [instructionP i] by
      simp [ruleConclusion, htag], coe_append_singleton]
    refine ⟨?_⟩
    exact FailureOfComposition.Palomar.Arithmetic.Derivation.weakening
      (p := instructionP i) d
  · unfold ListDerivable
    refine ⟨?_⟩
    simpa [ruleConclusion, htag,
      FailureOfComposition.Palomar.Arithmetic.Sequent.singleton] using
      FailureOfComposition.Palomar.Arithmetic.Derivation.verum
  · have h : ListDerivable
        (instructionGamma i ++ [instructionP i, instructionQ i]) := by
      simpa [rulePremises, htag] using hpremises
    rcases h with ⟨d⟩
    rw [coe_append_pair] at d
    unfold ListDerivable
    rw [show ruleConclusion i = instructionGamma i ++
        [Formula.or (instructionP i) (instructionQ i)] by
      simp [ruleConclusion, htag], coe_append_singleton]
    refine ⟨?_⟩
    exact FailureOfComposition.Palomar.Arithmetic.Derivation.or d
  · have h :
        ListDerivable (instructionGamma i ++ [instructionQ i]) ∧
          ListDerivable (instructionGamma i ++ [instructionP i]) := by
      simpa [rulePremises, htag] using hpremises
    rcases h with ⟨⟨d₂⟩, ⟨d₁⟩⟩
    rw [coe_append_singleton] at d₁ d₂
    unfold ListDerivable
    rw [show ruleConclusion i = instructionGamma i ++
        [Formula.and (instructionP i) (instructionQ i)] by
      simp [ruleConclusion, htag], coe_append_singleton]
    refine ⟨?_⟩
    exact FailureOfComposition.Palomar.Arithmetic.Derivation.and d₁ d₂
  · have h : ListDerivable
        ((instructionGamma i).map Formula.shiftFree ++
          [Formula.free (instructionR i)]) := by
      simpa [rulePremises, htag] using hpremises
    rcases h with ⟨d⟩
    rw [coe_map_shift_append_singleton] at d
    unfold ListDerivable
    rw [show ruleConclusion i = instructionGamma i ++
        [Formula.all (instructionR i)] by
      simp [ruleConclusion, htag], coe_append_singleton]
    refine ⟨?_⟩
    exact FailureOfComposition.Palomar.Arithmetic.Derivation.all d
  · have h : ListDerivable
        (instructionGamma i ++
          [Formula.substOne (instructionR i) (instructionS i)]) := by
      simpa [rulePremises, htag] using hpremises
    rcases h with ⟨d⟩
    rw [coe_append_singleton] at d
    unfold ListDerivable
    rw [show ruleConclusion i = instructionGamma i ++
        [Formula.exs (instructionR i)] by
      simp [ruleConclusion, htag], coe_append_singleton]
    refine ⟨?_⟩
    exact FailureOfComposition.Palomar.Arithmetic.Derivation.exs
      (t := instructionS i) d
  · have h : ListDerivable
        (instructionGamma i ++ [instructionP i, instructionQ i] ++
          instructionDelta i) := by
      simpa [rulePremises, htag] using hpremises
    rcases h with ⟨d⟩
    unfold ListDerivable
    rw [show ruleConclusion i = instructionGamma i ++
        [instructionQ i, instructionP i] ++ instructionDelta i by
      simp [ruleConclusion, htag]]
    refine ⟨?_⟩
    rw [← coe_adjacent_swap (instructionGamma i) (instructionDelta i)
      (instructionP i) (instructionQ i)]
    exact d

def StackDerivable (stack : DerivationStack) : Prop :=
  ∀ l ∈ stack, ListDerivable l

theorem applyInstruction_sound {i : DerivationInstruction}
    {stack stack' : DerivationStack}
    (hstep : applyInstruction i stack = some stack')
    (hstack : StackDerivable stack) : StackDerivable stack' := by
  unfold applyInstruction at hstep
  split at hstep
  next hknown =>
    dsimp only at hstep
    split at hstep
    next hmatch =>
      injection hstep with hstack'
      subst stack'
      intro l hl
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · apply rule_sound i hknown
        intro premise hpremise
        apply hstack premise
        apply List.mem_of_mem_take
        rw [hmatch]
        exact hpremise
      · apply hstack l
        exact List.mem_of_mem_drop hl
    next hnomatch => contradiction
  next hunknown => contradiction

@[simp] theorem foldl_derivationMachineStep_none
    (program : List DerivationInstruction) :
    program.foldl derivationMachineStep none = none := by
  induction program with
  | nil => rfl
  | cons i program ih =>
      simp only [List.foldl_cons, derivationMachineStep, Option.bind_none, ih]

theorem runDerivationProgramFrom_sound
    (program : List DerivationInstruction) {stack stack' : DerivationStack}
    (hstack : StackDerivable stack)
    (hrun : program.foldl derivationMachineStep (some stack) = some stack') :
    StackDerivable stack' := by
  induction program generalizing stack with
  | nil =>
      simp only [List.foldl_nil] at hrun
      injection hrun with h
      subst stack'
      exact hstack
  | cons i program ih =>
      simp only [List.foldl_cons] at hrun
      cases hstep : applyInstruction i stack with
      | none =>
          simp [derivationMachineStep, hstep] at hrun
      | some next =>
          apply ih (applyInstruction_sound hstep hstack)
          simpa [derivationMachineStep, hstep] using hrun

theorem runDerivationProgram_sound {program : List DerivationInstruction}
    {stack : DerivationStack}
    (hrun : runDerivationProgram program = some stack) :
    StackDerivable stack := by
  apply runDerivationProgramFrom_sound program (stack := [])
  · intro l hl
    simp at hl
  · exact hrun

def exchangeInstruction (gamma delta : List Proposition)
    (p q : Proposition) : DerivationInstruction :=
  mkInstruction 10 gamma delta p q Formula.verum Term.zero Term.zero

@[simp] theorem derivationMachineStep_exchange
    (gamma delta : List Proposition) (p q : Proposition)
    (stack : DerivationStack) :
    derivationMachineStep
        (some ((gamma ++ [p, q] ++ delta) :: stack))
        (exchangeInstruction gamma delta p q) =
      some ((gamma ++ [q, p] ++ delta) :: stack) := by
  simp [derivationMachineStep, applyInstruction, exchangeInstruction,
    rulePremises, ruleConclusion, mkInstruction, instructionTag,
    instructionGamma, instructionDelta, instructionP, instructionQ]

theorem permutation_executable {l₁ l₂ : List Proposition}
    (hperm : l₁.Perm l₂) (gamma : List Proposition) :
    ∃ program : List DerivationInstruction, ∀ stack : DerivationStack,
      program.foldl derivationMachineStep
          (some ((gamma ++ l₁) :: stack)) =
        some ((gamma ++ l₂) :: stack) := by
  induction hperm generalizing gamma with
  | nil =>
      exact ⟨[], fun _ ↦ rfl⟩
  | cons a hperm ih =>
      obtain ⟨program, hprogram⟩ := ih (gamma ++ [a])
      refine ⟨program, ?_⟩
      intro stack
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        hprogram stack
  | swap a b l =>
      refine ⟨[exchangeInstruction gamma l b a], ?_⟩
      intro stack
      simpa only [List.foldl_cons, List.foldl_nil, List.append_assoc,
        List.cons_append, List.nil_append] using
        derivationMachineStep_exchange gamma l b a stack
  | trans h₁ h₂ ih₁ ih₂ =>
      obtain ⟨program₁, hprogram₁⟩ := ih₁ gamma
      obtain ⟨program₂, hprogram₂⟩ := ih₂ gamma
      refine ⟨program₁ ++ program₂, ?_⟩
      intro stack
      rw [List.foldl_append, hprogram₁ stack, hprogram₂ stack]

def identityEqualInstruction (s t : SyntacticTerm 0) :
    DerivationInstruction :=
  mkInstruction 0 [] [] Formula.verum Formula.verum Formula.verum s t

def identityLessInstruction (s t : SyntacticTerm 0) :
    DerivationInstruction :=
  mkInstruction 1 [] [] Formula.verum Formula.verum Formula.verum s t

def cutInstruction (gamma delta : List Proposition) (p : Proposition) :
    DerivationInstruction :=
  mkInstruction 2 gamma delta p Formula.verum Formula.verum Term.zero Term.zero

def contractionInstruction (gamma : List Proposition) (p : Proposition) :
    DerivationInstruction :=
  mkInstruction 3 gamma [] p Formula.verum Formula.verum Term.zero Term.zero

def weakeningInstruction (gamma : List Proposition) (p : Proposition) :
    DerivationInstruction :=
  mkInstruction 4 gamma [] p Formula.verum Formula.verum Term.zero Term.zero

def verumInstruction : DerivationInstruction :=
  mkInstruction 5 [] [] Formula.verum Formula.verum Formula.verum Term.zero Term.zero

def orInstruction (gamma : List Proposition) (p q : Proposition) :
    DerivationInstruction :=
  mkInstruction 6 gamma [] p q Formula.verum Term.zero Term.zero

def andInstruction (gamma : List Proposition) (p q : Proposition) :
    DerivationInstruction :=
  mkInstruction 7 gamma [] p q Formula.verum Term.zero Term.zero

def allInstruction (gamma : List Proposition) (p : Semiproposition 1) :
    DerivationInstruction :=
  mkInstruction 8 gamma [] Formula.verum Formula.verum p Term.zero Term.zero

def exsInstruction (gamma : List Proposition) (p : Semiproposition 1)
    (t : SyntacticTerm 0) : DerivationInstruction :=
  mkInstruction 9 gamma [] Formula.verum Formula.verum p t Term.zero

theorem derivationMachineStep_rule (i : DerivationInstruction)
    (hknown : instructionTag i < 11) (stack : DerivationStack) :
    derivationMachineStep
        (some (rulePremises i ++ stack)) i =
      some (ruleConclusion i :: stack) := by
  simp [derivationMachineStep, applyInstruction, hknown]

def ProgramProduces (program : List DerivationInstruction)
    (conclusion : List Proposition) : Prop :=
  ∀ stack : DerivationStack,
    program.foldl derivationMachineStep (some stack) =
      some (conclusion :: stack)

theorem programProduces_nilRule (i : DerivationInstruction)
    (hknown : instructionTag i < 11) (hpremises : rulePremises i = []) :
    ProgramProduces [i] (ruleConclusion i) := by
  intro stack
  simpa [hpremises] using derivationMachineStep_rule i hknown stack

theorem programProduces_unaryRule
    {program : List DerivationInstruction} {premise : List Proposition}
    (hprogram : ProgramProduces program premise)
    (i : DerivationInstruction) (hknown : instructionTag i < 11)
    (hpremises : rulePremises i = [premise]) :
    ProgramProduces (program ++ [i]) (ruleConclusion i) := by
  intro stack
  rw [List.foldl_append, hprogram stack]
  simpa [hpremises] using derivationMachineStep_rule i hknown stack

theorem programProduces_binaryRule
    {program₁ program₂ : List DerivationInstruction}
    {premise₁ premise₂ : List Proposition}
    (hprogram₁ : ProgramProduces program₁ premise₁)
    (hprogram₂ : ProgramProduces program₂ premise₂)
    (i : DerivationInstruction) (hknown : instructionTag i < 11)
    (hpremises : rulePremises i = [premise₂, premise₁]) :
    ProgramProduces (program₁ ++ program₂ ++ [i]) (ruleConclusion i) := by
  intro stack
  rw [List.foldl_append, List.foldl_append, hprogram₁ stack,
    hprogram₂ (premise₁ :: stack)]
  simpa [hpremises] using derivationMachineStep_rule i hknown stack

theorem programProduces_reorder
    {program : List DerivationInstruction} {l₁ l₂ : List Proposition}
    (hprogram : ProgramProduces program l₁)
    (heq : (l₁ : Multiset Proposition) = (l₂ : Multiset Proposition)) :
    ∃ program' : List DerivationInstruction, ProgramProduces program' l₂ := by
  have hperm : l₁.Perm l₂ := Multiset.coe_eq_coe.mp heq
  obtain ⟨exchange, hexchange⟩ := permutation_executable hperm []
  refine ⟨program ++ exchange, ?_⟩
  intro stack
  rw [List.foldl_append, hprogram stack]
  simpa only [List.nil_append] using hexchange stack

theorem derivation_serializable {Γ : Sequent}
    (d : Derivation Γ) (l : List Proposition)
    (hl : (l : Multiset Proposition) = Γ) :
    ∃ program : List DerivationInstruction, ProgramProduces program l := by
  induction d generalizing l with
  | identityEqual s t =>
      let i := identityEqualInstruction s t
      have hprogram : ProgramProduces [i] (ruleConclusion i) :=
        programProduces_nilRule i (by simp [i, identityEqualInstruction,
          mkInstruction, instructionTag]) (by
            rfl)
      apply programProduces_reorder hprogram
      rw [show ruleConclusion i = [Formula.equal s t, Formula.nequal s t] by
        rfl, coe_pair]
      exact hl.symm
  | identityLess s t =>
      let i := identityLessInstruction s t
      have hprogram : ProgramProduces [i] (ruleConclusion i) :=
        programProduces_nilRule i (by simp [i, identityLessInstruction,
          mkInstruction, instructionTag]) (by
            rfl)
      apply programProduces_reorder hprogram
      rw [show ruleConclusion i = [Formula.less s t, Formula.nless s t] by
        rfl, coe_pair]
      exact hl.symm
  | @cut Γ Δ p d₁ d₂ ih₁ ih₂ =>
      let gamma := Γ.toList
      let delta := Δ.toList
      obtain ⟨program₁, hprogram₁⟩ := ih₁ (gamma ++ [p]) (by
        rw [coe_append_singleton, Multiset.coe_toList])
      obtain ⟨program₂, hprogram₂⟩ := ih₂ (delta ++ [p.neg]) (by
        rw [coe_append_singleton, Multiset.coe_toList])
      let i := cutInstruction gamma delta p
      have hprogram : ProgramProduces
          (program₁ ++ program₂ ++ [i]) (ruleConclusion i) :=
        programProduces_binaryRule hprogram₁ hprogram₂ i
          (by simp [i, cutInstruction, mkInstruction, instructionTag]) (by
            rfl)
      apply programProduces_reorder hprogram
      have hnatural :
          ((ruleConclusion i : List Proposition) : Multiset Proposition) =
            Γ + Δ := by
        rw [show ruleConclusion i = gamma ++ delta by rfl, coe_append]
        simp [gamma, delta]
      exact hnatural.trans hl.symm
  | @contraction Γ p d ih =>
      let gamma := Γ.toList
      obtain ⟨program, hprogram⟩ := ih (gamma ++ [p, p]) (by
        rw [coe_append_pair, Multiset.coe_toList])
      let i := contractionInstruction gamma p
      have hresult : ProgramProduces (program ++ [i]) (ruleConclusion i) :=
        programProduces_unaryRule hprogram i
          (by simp [i, contractionInstruction, mkInstruction, instructionTag])
          (by rfl)
      apply programProduces_reorder hresult
      have hnatural :
          ((ruleConclusion i : List Proposition) : Multiset Proposition) =
            Γ + Sequent.singleton p := by
        rw [show ruleConclusion i = gamma ++ [p] by rfl,
          coe_append_singleton, Multiset.coe_toList]
      exact hnatural.trans hl.symm
  | @weakening Γ p d ih =>
      let gamma := Γ.toList
      obtain ⟨program, hprogram⟩ := ih gamma (by
        exact Multiset.coe_toList Γ)
      let i := weakeningInstruction gamma p
      have hresult : ProgramProduces (program ++ [i]) (ruleConclusion i) :=
        programProduces_unaryRule hprogram i
          (by simp [i, weakeningInstruction, mkInstruction, instructionTag])
          (by rfl)
      apply programProduces_reorder hresult
      have hnatural :
          ((ruleConclusion i : List Proposition) : Multiset Proposition) =
            Γ + Sequent.singleton p := by
        rw [show ruleConclusion i = gamma ++ [p] by rfl,
          coe_append_singleton, Multiset.coe_toList]
      exact hnatural.trans hl.symm
  | verum =>
      let i := verumInstruction
      have hprogram : ProgramProduces [i] (ruleConclusion i) :=
        programProduces_nilRule i
          (by simp [i, verumInstruction, mkInstruction, instructionTag])
          (by rfl)
      apply programProduces_reorder hprogram
      have hnatural :
          ((ruleConclusion i : List Proposition) : Multiset Proposition) =
            Sequent.singleton Formula.verum := by
        rfl
      exact hnatural.trans hl.symm
  | @or Γ p q d ih =>
      let gamma := Γ.toList
      obtain ⟨program, hprogram⟩ := ih (gamma ++ [p, q]) (by
        rw [coe_append_pair, Multiset.coe_toList])
      let i := orInstruction gamma p q
      have hresult : ProgramProduces (program ++ [i]) (ruleConclusion i) :=
        programProduces_unaryRule hprogram i
          (by simp [i, orInstruction, mkInstruction, instructionTag])
          (by rfl)
      apply programProduces_reorder hresult
      have hnatural :
          ((ruleConclusion i : List Proposition) : Multiset Proposition) =
            Γ + Sequent.singleton (Formula.or p q) := by
        rw [show ruleConclusion i = gamma ++ [Formula.or p q] by rfl,
          coe_append_singleton, Multiset.coe_toList]
      exact hnatural.trans hl.symm
  | @and Γ p q d₁ d₂ ih₁ ih₂ =>
      let gamma := Γ.toList
      obtain ⟨program₁, hprogram₁⟩ := ih₁ (gamma ++ [p]) (by
        rw [coe_append_singleton, Multiset.coe_toList])
      obtain ⟨program₂, hprogram₂⟩ := ih₂ (gamma ++ [q]) (by
        rw [coe_append_singleton, Multiset.coe_toList])
      let i := andInstruction gamma p q
      have hresult : ProgramProduces
          (program₁ ++ program₂ ++ [i]) (ruleConclusion i) :=
        programProduces_binaryRule hprogram₁ hprogram₂ i
          (by simp [i, andInstruction, mkInstruction, instructionTag])
          (by rfl)
      apply programProduces_reorder hresult
      have hnatural :
          ((ruleConclusion i : List Proposition) : Multiset Proposition) =
            Γ + Sequent.singleton (Formula.and p q) := by
        rw [show ruleConclusion i = gamma ++ [Formula.and p q] by rfl,
          coe_append_singleton, Multiset.coe_toList]
      exact hnatural.trans hl.symm
  | @all Γ p d ih =>
      let gamma := Γ.toList
      obtain ⟨program, hprogram⟩ :=
        ih (gamma.map Formula.shiftFree ++ [p.free]) (by
          rw [coe_map_shift_append_singleton, Multiset.coe_toList])
      let i := allInstruction gamma p
      have hresult : ProgramProduces (program ++ [i]) (ruleConclusion i) :=
        programProduces_unaryRule hprogram i
          (by simp [i, allInstruction, mkInstruction, instructionTag])
          (by rfl)
      apply programProduces_reorder hresult
      have hnatural :
          ((ruleConclusion i : List Proposition) : Multiset Proposition) =
            Γ + Sequent.singleton (Formula.all p) := by
        rw [show ruleConclusion i = gamma ++ [Formula.all p] by rfl,
          coe_append_singleton, Multiset.coe_toList]
      exact hnatural.trans hl.symm
  | @exs Γ p t d ih =>
      let gamma := Γ.toList
      obtain ⟨program, hprogram⟩ := ih (gamma ++ [p.substOne t]) (by
        rw [coe_append_singleton, Multiset.coe_toList])
      let i := exsInstruction gamma p t
      have hresult : ProgramProduces (program ++ [i]) (ruleConclusion i) :=
        programProduces_unaryRule hprogram i
          (by simp [i, exsInstruction, mkInstruction, instructionTag])
          (by rfl)
      apply programProduces_reorder hresult
      have hnatural :
          ((ruleConclusion i : List Proposition) : Multiset Proposition) =
            Γ + Sequent.singleton (Formula.exs p) := by
        rw [show ruleConclusion i = gamma ++ [Formula.exs p] by rfl,
          coe_append_singleton, Multiset.coe_toList]
      exact hnatural.trans hl.symm

def proofSequentList (p : Sentence) (axioms : List Sentence) :
    List Proposition :=
  [p.embed] ++ axioms.map (fun q ↦ q.embed.neg)

theorem coe_proofSequentList (p : Sentence) (axioms : List Sentence) :
    ((proofSequentList p axioms : List Proposition) : Multiset Proposition) =
      Sequent.singleton p.embed +
        Sequent.negateSentences (axioms : Multiset Sentence) := by
  rw [proofSequentList, coe_append]
  rw [← Multiset.map_coe]
  rfl

abbrev DirectProofCertificate :=
  Sentence × List Sentence × List DerivationInstruction

def certificateSentence (c : DirectProofCertificate) : Sentence := c.1
def certificateAxioms (c : DirectProofCertificate) : List Sentence := c.2.1
def certificateProgram (c : DirectProofCertificate) :
    List DerivationInstruction := c.2.2

def AcceptedProofCertificate (T : Theory) (n : ℕ)
    (c : DirectProofCertificate) : Prop :=
  Coding.sentenceCode (certificateSentence c) = n ∧
  (∀ q ∈ certificateAxioms c, q ∈ T) ∧
  runDerivationProgram (certificateProgram c) =
    some [proofSequentList (certificateSentence c) (certificateAxioms c)]

def DirectTheoremCodes (T : Theory) (n : ℕ) : Prop :=
  ∃ p : Sentence, Coding.sentenceCode p = n ∧ Provable T p

theorem acceptedProofCertificate_sound {T : Theory} {n : ℕ}
    {c : DirectProofCertificate} (h : AcceptedProofCertificate T n c) :
    DirectTheoremCodes T n := by
  rcases h with ⟨hcode, haxioms, hrun⟩
  let p := certificateSentence c
  let axioms := certificateAxioms c
  let target := proofSequentList p axioms
  have hstack : StackDerivable [target] := by
    apply runDerivationProgram_sound
    exact hrun
  have htarget : ListDerivable target := hstack target (by simp)
  rcases htarget with ⟨d⟩
  refine ⟨p, hcode, ⟨{
    axioms := (axioms : Multiset Sentence)
    axioms_mem := ?_
    derivation := ?_
  }⟩⟩
  · intro q hq
    apply haxioms q
    simpa [axioms] using hq
  · rw [coe_proofSequentList] at d
    exact d

theorem acceptedProofCertificate_complete {T : Theory} {n : ℕ}
    (h : DirectTheoremCodes T n) :
    ∃ c : DirectProofCertificate, AcceptedProofCertificate T n c := by
  rcases h with ⟨p, hcode, ⟨proof⟩⟩
  let axioms := proof.axioms.toList
  let target := proofSequentList p axioms
  have htarget : (target : Multiset Proposition) =
      Sequent.singleton p.embed + Sequent.negateSentences proof.axioms := by
    rw [coe_proofSequentList]
    simp [axioms]
  obtain ⟨program, hprogram⟩ :=
    derivation_serializable proof.derivation target htarget
  let c : DirectProofCertificate := (p, axioms, program)
  refine ⟨c, hcode, ?_, ?_⟩
  · intro q hq
    apply proof.axioms_mem q
    simpa [c, certificateAxioms, axioms] using hq
  · simpa [c, certificateProgram, certificateSentence, certificateAxioms,
      target, runDerivationProgram] using hprogram []

theorem sentenceCode_eq_encode (p : Sentence) :
    Coding.sentenceCode p = Encodable.encode p := by
  change Coding.formulaCode p = Encodable.encode p
  rw [Coding.formulaCode_eq_encode]
  rfl

theorem sentenceCode_primrec : Primrec Coding.sentenceCode := by
  exact Primrec.encode.of_eq fun p ↦ (sentenceCode_eq_encode p).symm

theorem syntacticTermAdd_primrec :
    Primrec₂ (FailureOfComposition.Palomar.Arithmetic.Term.add :
      SyntacticTerm 0 → SyntacticTerm 0 → SyntacticTerm 0) := by
  have hargs : Primrec (fun q : SyntacticTerm 0 × SyntacticTerm 0 ↦
      listCode [Encodable.encode q.1, Encodable.encode q.2]) :=
    listCode_primrec.comp
      (Primrec.list_cons.comp (Primrec.encode.comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.encode.comp Primrec.snd)
          (Primrec.const [])))
  have hcode : Primrec₂ (fun s t : SyntacticTerm 0 ↦
      pairSucc 2 (Nat.pair 2 (Nat.pair 0
        (listCode [Encodable.encode s, Encodable.encode t])))) :=
    (pairSucc_primrec.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.const 2)
        (Primrec₂.natPair.comp (Primrec.const 0) hargs))).to₂
  apply Primrec₂.encode_iff.mp
  exact hcode.of_eq fun s t ↦ (DirectTerm.encode_add s t).symm

def syntacticNumeral : ℕ → SyntacticTerm 0 :=
  Nat.rec FailureOfComposition.Palomar.Arithmetic.Term.zero fun n t ↦
    if n = 0 then FailureOfComposition.Palomar.Arithmetic.Term.one
    else FailureOfComposition.Palomar.Arithmetic.Term.add t
      FailureOfComposition.Palomar.Arithmetic.Term.one

theorem syntacticNumeral_primrec : Primrec syntacticNumeral := by
  have hstep : Primrec₂ (fun n : ℕ ↦ fun t : SyntacticTerm 0 ↦
      if n = 0 then FailureOfComposition.Palomar.Arithmetic.Term.one
      else FailureOfComposition.Palomar.Arithmetic.Term.add t
        FailureOfComposition.Palomar.Arithmetic.Term.one) := by
    exact (Primrec.ite
      (Primrec.eq.comp Primrec.fst (Primrec.const 0))
      (Primrec.const FailureOfComposition.Palomar.Arithmetic.Term.one)
      (syntacticTermAdd_primrec.comp Primrec.snd
        (Primrec.const FailureOfComposition.Palomar.Arithmetic.Term.one))).to₂
  exact Primrec.nat_rec₁
    FailureOfComposition.Palomar.Arithmetic.Term.zero hstep

theorem syntacticNumeral_eq (n : ℕ) :
    syntacticNumeral n =
      FailureOfComposition.Palomar.Arithmetic.Term.numeral n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n =>
          change FailureOfComposition.Palomar.Arithmetic.Term.add
              (syntacticNumeral (n + 1))
              FailureOfComposition.Palomar.Arithmetic.Term.one =
            FailureOfComposition.Palomar.Arithmetic.Term.add
              (FailureOfComposition.Palomar.Arithmetic.Term.numeral (n + 1))
              FailureOfComposition.Palomar.Arithmetic.Term.one
          rw [ih]

theorem termNumeral_primrec :
    Primrec (FailureOfComposition.Palomar.Arithmetic.Term.numeral :
      ℕ → SyntacticTerm 0) :=
  syntacticNumeral_primrec.of_eq syntacticNumeral_eq

theorem provable_re_of_direct_theorem_codes (T : Theory)
    (hT : REPred (DirectTheoremCodes T)) :
    REPred (Provable T) := by
  apply REPred.of_eq (hT.comp sentenceCode_primrec.to_comp)
  intro p
  simp only [DirectTheoremCodes, sentenceCode_eq_encode,
    Encodable.encode_inj]
  simp

theorem proofSequentList_primrec : Primrec₂ proofSequentList := by
  have hnegEmbed : Primrec (fun p : Sentence ↦ p.embed.neg) :=
    DirectFormula.actual_neg_primrec.comp formulaEmbed_primrec
  have hmap : Primrec (fun axioms : List Sentence ↦
      axioms.map (fun p ↦ p.embed.neg)) :=
    Primrec.list_map Primrec.id (hnegEmbed.comp Primrec.snd).to₂
  have hsingleton : Primrec (fun p : Sentence ↦ [p.embed]) :=
    Primrec.list_cons.comp formulaEmbed_primrec (Primrec.const [])
  have hpair : Primrec (fun q : Sentence × List Sentence ↦
      proofSequentList q.1 q.2) :=
    Primrec.list_append.comp
      (hsingleton.comp Primrec.fst) (hmap.comp Primrec.snd)
  exact hpair.to₂

theorem certificateSentence_primrec : Primrec certificateSentence :=
  Primrec.fst

theorem certificateAxioms_primrec : Primrec certificateAxioms :=
  Primrec.fst.comp Primrec.snd

theorem certificateProgram_primrec : Primrec certificateProgram :=
  Primrec.snd.comp Primrec.snd

private theorem re_forall_mem_list_direct
    {α : Type*} [Primcodable α] [Inhabited α]
    {p : α → Prop} (hp : REPred p) :
    REPred (fun l : List α ↦ ∀ a ∈ l, p a) := by
  obtain ⟨f, hf, hfp⟩ := REPred.iff'.mp hp
  let test (l : List α) (n : ℕ) : Part Unit :=
    Nat.rec (Part.some ())
      (fun i r ↦ r.bind (fun _ ↦ f (l.getD i default))) n
  have ht : Partrec (fun l : List α ↦ test l l.length) := by
    exact Partrec.nat_rec Computable.list_length (Partrec.const' (Part.some ()))
      ((hf.comp ((Primrec.list_getD default).to_comp.comp Computable.fst
        (Computable.fst.comp Computable.snd))).to₂)
  have htest (l : List α) (n : ℕ) :
      (test l n).Dom ↔ ∀ i < n, p (l.getD i default) := by
    induction n with
    | zero => simp [test]
    | succ n ih =>
      change (∃ _ : (test l n).Dom, (f (l.getD n default)).Dom) ↔ _
      simp only [exists_prop, ih, ← hfp, Nat.forall_lt_succ_right]
  apply REPred.of_eq ht.dom_re
  intro l
  rw [htest]
  constructor
  · intro h a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    simpa only [List.getD_eq_getElem l default hi] using h i hi
  · intro h i hi
    rw [List.getD_eq_getElem l default hi]
    exact h _ (List.getElem_mem hi)

local instance sentenceInhabited : Inhabited Sentence :=
  ⟨Formula.verum⟩

theorem direct_theorem_codes_re_of_axiom_codes (T : Theory)
    (hT : REPred (FailureOfComposition.Palomar.Arithmetic.AxiomCodes T)) :
    REPred (DirectTheoremCodes T) := by
  have hmembership : REPred (fun p : Sentence ↦ p ∈ T) := by
    apply REPred.of_eq (hT.comp sentenceCode_primrec.to_comp)
    intro p
    simp only [FailureOfComposition.Palomar.Arithmetic.AxiomCodes,
      sentenceCode_eq_encode, Encodable.encode_inj]
    simp
  have hfinite : REPred (fun axioms : List Sentence ↦
      ∀ p ∈ axioms, p ∈ T) :=
    re_forall_mem_list_direct hmembership
  let Q := ℕ × DirectProofCertificate
  have hcode : REPred (fun q : Q ↦
      Coding.sentenceCode (certificateSentence q.2) = q.1) :=
    (Primrec.eq.comp
      (sentenceCode_primrec.comp
        (certificateSentence_primrec.comp Primrec.snd))
      Primrec.fst).computablePred.to_re
  have haxioms : REPred (fun q : Q ↦
      ∀ p ∈ certificateAxioms q.2, p ∈ T) :=
    hfinite.comp
      (certificateAxioms_primrec.comp Primrec.snd).to_comp
  have htarget : Primrec (fun q : Q ↦
      proofSequentList (certificateSentence q.2)
        (certificateAxioms q.2)) :=
    proofSequentList_primrec.comp
      (certificateSentence_primrec.comp Primrec.snd)
      (certificateAxioms_primrec.comp Primrec.snd)
  have htargetStack : Primrec (fun q : Q ↦
      some [proofSequentList (certificateSentence q.2)
        (certificateAxioms q.2)]) :=
    Primrec.option_some.comp
      (Primrec.list_cons.comp htarget (Primrec.const []))
  have hrun : REPred (fun q : Q ↦
      runDerivationProgram (certificateProgram q.2) =
        some [proofSequentList (certificateSentence q.2)
          (certificateAxioms q.2)]) :=
    (Primrec.eq.comp
      (runDerivationProgram_primrec.comp
        (certificateProgram_primrec.comp Primrec.snd))
      htargetStack).computablePred.to_re
  have haccepted : REPred (fun q : Q ↦
      AcceptedProofCertificate T q.1 q.2) := by
    exact hcode.and (haxioms.and hrun)
  apply REPred.of_eq haccepted.projection
  intro n
  constructor
  · rintro ⟨c, hc⟩
    exact acceptedProofCertificate_sound hc
  · intro hn
    exact acceptedProofCertificate_complete hn

theorem provable_re_of_axiom_codes (T : Theory)
    (hT : REPred (FailureOfComposition.Palomar.Arithmetic.AxiomCodes T)) :
    REPred (Provable T) :=
  provable_re_of_direct_theorem_codes T
    (direct_theorem_codes_re_of_axiom_codes T hT)

theorem directTheoremCodes_toFoundation_iff (T : Theory) (n : ℕ) :
    DirectTheoremCodes T n ↔
      FailureOfComposition.TheoremCodes
        (TheoryCorrespondence.toFoundation T) n := by
  constructor
  · rintro ⟨p, hcode, hp⟩
    refine ⟨p.toFoundation, ?_, (provable_toFoundation_iff T p).mp hp⟩
    simpa only [Coding.formulaCode_eq_encode,
      Sentence.quote_eq_encode_nat] using hcode
  · rintro ⟨p, hcode, hp⟩
    let q := Formula.ofFoundation p
    refine ⟨q, ?_, (provable_toFoundation_iff T q).mpr ?_⟩
    · simpa only [q, Coding.formulaCode_eq_encode,
        Formula.toFoundation_ofFoundation,
        Sentence.quote_eq_encode_nat] using hcode
    · change Nonempty (FFL.FirstOrder.Theory.Proof
        (TheoryCorrespondence.toFoundation T) p) at hp
      simpa [q] using hp

theorem theoremCodes_toFoundation_re_of_axiom_codes (T : Theory)
    (hT : REPred (FailureOfComposition.Palomar.Arithmetic.AxiomCodes T)) :
    REPred (FailureOfComposition.TheoremCodes
      (TheoryCorrespondence.toFoundation T)) := by
  apply REPred.of_eq (direct_theorem_codes_re_of_axiom_codes T hT)
  intro n
  exact directTheoremCodes_toFoundation_iff T n

end FailureOfComposition.Palomar.DirectDerivationEnumeration
