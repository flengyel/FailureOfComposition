/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel

The syntax and calculus in this file are adapted to the arithmetic specialization
of FormalizedFormalLogic/Foundation's first-order syntax and LK calculus.  The
Foundation sources are Apache-2.0 licensed; the relevant upstream files are
`Foundation/Syntax/Predicate/Term.lean`,
`Foundation/FirstOrder/Syntax/Classical/Formula.lean`, and
`Foundation/FirstOrder/LK/Basic.lean` at revision
e72cfe981aa65166f37fa4e2584f4806bc48d72f.
-/
import Mathlib.Computability.RE
import Mathlib.Data.Fin.VecNotation

/-!
# Explicit arithmetic statement interface (development source)

This module uses only a permitted Mathlib import.  It is a development source
for the arithmetic definitions that must ultimately be inlined into the
Palomar Challenge: a candidate-local import of this module is not itself an
eligible final boundary.

Terms use separate free variables and de Bruijn bound variables.  Formulas are
in negation-normal form.  `Derivation` is a genuine one-sided classical
first-order sequent calculus, and `Proof` records the finite theory axioms used
by a derivation.  No semantic consequence relation or supplied realization
field is used.
-/

set_option autoImplicit false

namespace FailureOfComposition.Palomar.Arithmetic

/-! Named low finite indices keep duplicated Challenge definitions independent
of elaborator-generated proof declarations. -/

def fin0 {n : ℕ} : Fin (n + 1) :=
  ⟨0, Nat.zero_lt_succ n⟩

def fin1 {n : ℕ} : Fin (n + 2) :=
  (fin0 (n := n)).succ

def fin2 {n : ℕ} : Fin (n + 3) :=
  (fin1 (n := n)).succ

def fin3 {n : ℕ} : Fin (n + 4) :=
  (fin2 (n := n)).succ

inductive Term (ξ : Type) : ℕ → Type
  | bvar {n : ℕ} : Fin n → Term ξ n
  | fvar {n : ℕ} : ξ → Term ξ n
  | zero {n : ℕ} : Term ξ n
  | one {n : ℕ} : Term ξ n
  | add {n : ℕ} : Term ξ n → Term ξ n → Term ξ n
  | mul {n : ℕ} : Term ξ n → Term ξ n → Term ξ n
  deriving DecidableEq

abbrev ClosedTerm (n : ℕ) := Term Empty n
abbrev SyntacticTerm (n : ℕ) := Term ℕ n

namespace Term

variable {ξ ξ' : Type} {n m : ℕ}

def rewrite (b : Fin n → Term ξ' m) (f : ξ → Term ξ' m) :
    Term ξ n → Term ξ' m
  | bvar i => b i
  | fvar x => f x
  | zero => zero
  | one => one
  | add s t => add (rewrite b f s) (rewrite b f t)
  | mul s t => mul (rewrite b f s) (rewrite b f t)

@[simp] theorem rewrite_bvar (b : Fin n → Term ξ' m) (f : ξ → Term ξ' m)
    (i : Fin n) : rewrite b f (bvar i) = b i := rfl

@[simp] theorem rewrite_fvar (b : Fin n → Term ξ' m) (f : ξ → Term ξ' m)
    (x : ξ) : rewrite b f (fvar x) = f x := rfl

def lift : Term ξ n → Term ξ (n + 1) :=
  rewrite (fun i ↦ bvar i.succ) fvar

def underBinder (b : Fin n → Term ξ' m) : Fin (n + 1) → Term ξ' (m + 1) :=
  Fin.cases (bvar fin0) fun i ↦ (b i).lift

def mapFree (f : ξ → ξ') : Term ξ n → Term ξ' n :=
  rewrite bvar (fvar ∘ f)

def numeral : ℕ → Term ξ n
  | 0 => zero
  | 1 => one
  | k + 2 => add (numeral (k + 1)) one

@[simp] theorem rewrite_numeral (b : Fin n → Term ξ' m) (f : ξ → Term ξ' m)
    (k : ℕ) : rewrite b f (numeral k) = numeral k := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k _ ih => simp only [numeral, rewrite, ih]

end Term

inductive Formula (ξ : Type) : ℕ → Type
  | verum {n : ℕ} : Formula ξ n
  | falsum {n : ℕ} : Formula ξ n
  | equal {n : ℕ} : Term ξ n → Term ξ n → Formula ξ n
  | nequal {n : ℕ} : Term ξ n → Term ξ n → Formula ξ n
  | less {n : ℕ} : Term ξ n → Term ξ n → Formula ξ n
  | nless {n : ℕ} : Term ξ n → Term ξ n → Formula ξ n
  | and {n : ℕ} : Formula ξ n → Formula ξ n → Formula ξ n
  | or {n : ℕ} : Formula ξ n → Formula ξ n → Formula ξ n
  | all {n : ℕ} : Formula ξ (n + 1) → Formula ξ n
  | exs {n : ℕ} : Formula ξ (n + 1) → Formula ξ n
  deriving DecidableEq

abbrev Sentence := Formula Empty 0
abbrev Proposition := Formula ℕ 0
abbrev Semiproposition (n : ℕ) := Formula ℕ n

namespace Formula

variable {ξ ξ' : Type} {n m : ℕ}

def neg {n : ℕ} (p : Formula ξ n) : Formula ξ n :=
  match p with
  | verum => falsum
  | falsum => verum
  | equal s t => nequal s t
  | nequal s t => equal s t
  | less s t => nless s t
  | nless s t => less s t
  | and p q => or (neg p) (neg q)
  | or p q => and (neg p) (neg q)
  | all p => exs (neg p)
  | exs p => all (neg p)

@[simp] theorem neg_neg (p : Formula ξ n) : neg (neg p) = p := by
  induction p <;> simp [neg, *]

def rewrite {n m : ℕ} (b : Fin n → Term ξ' m) (f : ξ → Term ξ' m)
    (p : Formula ξ n) : Formula ξ' m :=
  match p with
  | verum => verum
  | falsum => falsum
  | equal s t => equal (s.rewrite b f) (t.rewrite b f)
  | nequal s t => nequal (s.rewrite b f) (t.rewrite b f)
  | less s t => less (s.rewrite b f) (t.rewrite b f)
  | nless s t => nless (s.rewrite b f) (t.rewrite b f)
  | and p q => and (rewrite b f p) (rewrite b f q)
  | or p q => or (rewrite b f p) (rewrite b f q)
  | all p => all (rewrite (Term.underBinder b) (fun x ↦ (f x).lift) p)
  | exs p => exs (rewrite (Term.underBinder b) (fun x ↦ (f x).lift) p)

def subst (p : Formula ξ n) (v : Fin n → Term ξ m) : Formula ξ m :=
  rewrite v Term.fvar p

def mapFree (f : ξ → ξ') (p : Formula ξ n) : Formula ξ' n :=
  rewrite Term.bvar (Term.fvar ∘ f) p

def embed (p : Formula Empty n) : Formula ℕ n := mapFree Empty.elim p

def shiftFree (p : Formula ℕ n) : Formula ℕ n := mapFree Nat.succ p

def free (p : Formula ℕ 1) : Proposition :=
  rewrite (fun _ ↦ Term.fvar 0) (Term.fvar ∘ Nat.succ) p

def substOne (p : Formula ℕ 1) (t : SyntacticTerm 0) : Proposition :=
  rewrite (fun _ ↦ t) Term.fvar p

def imply (p q : Formula ξ n) : Formula ξ n := or (neg p) q

end Formula

abbrev Theory := Set Sentence
abbrev Sequent := Multiset Proposition

namespace Sequent

def singleton (p : Proposition) : Sequent := p ::ₘ 0

def pair (p q : Proposition) : Sequent := p ::ₘ q ::ₘ 0

def shiftFree (Γ : Sequent) : Sequent := Γ.map Formula.shiftFree

def negateSentences (Γ : Multiset Sentence) : Sequent :=
  Γ.map fun p ↦ Formula.neg p.embed

end Sequent

/-- One-sided classical first-order LK over explicit arithmetic syntax. -/
inductive Derivation : Sequent → Type
  | identityEqual (s t : SyntacticTerm 0) :
      Derivation (Sequent.pair (.equal s t) (.nequal s t))
  | identityLess (s t : SyntacticTerm 0) :
      Derivation (Sequent.pair (.less s t) (.nless s t))
  | cut {Γ Δ : Sequent} {p : Proposition} :
      Derivation (Γ + Sequent.singleton p) →
      Derivation (Δ + Sequent.singleton p.neg) → Derivation (Γ + Δ)
  | contraction {Γ : Sequent} {p : Proposition} :
      Derivation (Γ + Sequent.pair p p) → Derivation (Γ + Sequent.singleton p)
  | weakening {Γ : Sequent} {p : Proposition} :
      Derivation Γ → Derivation (Γ + Sequent.singleton p)
  | verum : Derivation (Sequent.singleton .verum)
  | or {Γ : Sequent} {p q : Proposition} :
      Derivation (Γ + Sequent.pair p q) →
      Derivation (Γ + Sequent.singleton (.or p q))
  | and {Γ : Sequent} {p q : Proposition} :
      Derivation (Γ + Sequent.singleton p) →
      Derivation (Γ + Sequent.singleton q) →
      Derivation (Γ + Sequent.singleton (.and p q))
  | all {Γ : Sequent} {p : Semiproposition 1} :
      Derivation (Γ.shiftFree + Sequent.singleton p.free) →
      Derivation (Γ + Sequent.singleton (.all p))
  | exs {Γ : Sequent} {p : Semiproposition 1} {t : SyntacticTerm 0} :
      Derivation (Γ + Sequent.singleton (p.substOne t)) →
      Derivation (Γ + Sequent.singleton (.exs p))

/-- A proof records exactly the finite multiset of theory axioms it uses. -/
structure Proof (T : Theory) (p : Sentence) where
  axioms : Multiset Sentence
  axioms_mem : ∀ q ∈ axioms, q ∈ T
  derivation :
    Derivation (Sequent.singleton p.embed + Sequent.negateSentences axioms)

def Provable (T : Theory) (p : Sentence) : Prop := Nonempty (Proof T p)

def Consistent (T : Theory) : Prop := ¬Provable T .falsum

/-- Deductive extension, not literal inclusion of axiom sets. -/
def DeductivelyExtends (U T : Theory) : Prop :=
  ∀ {p : Sentence}, Provable U p → Provable T p

/-! ## Peano arithmetic -/

namespace Term

variable {n : ℕ}

def freeVariables : {n : ℕ} → Term ℕ n → Finset ℕ
  | _, .bvar _ => ∅
  | _, .fvar x => {x}
  | _, .zero => ∅
  | _, .one => ∅
  | _, .add s t => freeVariables s ∪ freeVariables t
  | _, .mul s t => freeVariables s ∪ freeVariables t

end Term

namespace Formula

variable {ξ : Type} {n : ℕ}

def freeVariables : {n : ℕ} → Formula ℕ n → Finset ℕ
  | _, .verum => ∅
  | _, .falsum => ∅
  | _, .equal s t => s.freeVariables ∪ t.freeVariables
  | _, .nequal s t => s.freeVariables ∪ t.freeVariables
  | _, .less s t => s.freeVariables ∪ t.freeVariables
  | _, .nless s t => s.freeVariables ∪ t.freeVariables
  | _, .and p q => freeVariables p ∪ freeVariables q
  | _, .or p q => freeVariables p ∪ freeVariables q
  | _, .all p => freeVariables p
  | _, .exs p => freeVariables p

/-- One more than the largest free-variable index, or zero when there are no
free variables.  This is the convention used by the maintained syntax. -/
def fvSup (p : Formula ℕ n) : ℕ :=
  (p.freeVariables.max).recBotCoe 0 Nat.succ

/-- Replace the first `m` free variables by bound variables.  The fallback is
irrelevant for `m = p.fvSup`, but makes the operation total. -/
def fixFree (m : ℕ) (p : Proposition) : Formula Empty m :=
  p.rewrite Fin.elim0 fun x ↦
    if h : x < m then Term.bvar ⟨x, h⟩ else Term.zero

def allClosure {n : ℕ} (p : Formula ξ n) : Formula ξ 0 :=
  @Nat.rec (fun n ↦ Formula ξ n → Formula ξ 0)
    (fun q ↦ q) (fun _ ih q ↦ ih (.all q)) n p

def univClosure (p : Proposition) : Sentence :=
  allClosure (fixFree p.fvSup p)

/-- The full successor-induction formula before its parameter closure. -/
def succInd (p : Semiproposition 1) : Proposition :=
  imply (p.substOne .zero)
    (imply
      (.all (imply p (p.subst fun _ ↦ .add (.bvar fin0) .one)))
      (.all p))

end Formula

namespace Equality

def refl : Sentence :=
  .all (.equal (.bvar fin0) (.bvar fin0))

def symm : Sentence :=
  Formula.allClosure
    (show Formula Empty 2 from
      .imply (.equal (.bvar fin1) (.bvar fin0))
        (.equal (.bvar fin0) (.bvar fin1)))

def trans : Sentence :=
  Formula.allClosure
    (show Formula Empty 3 from
      .imply (.equal (.bvar fin2) (.bvar fin1))
        (.imply (.equal (.bvar fin1) (.bvar fin0))
          (.equal (.bvar fin2) (.bvar fin0))))

def zeroExt : Sentence :=
  .imply .verum (.equal .zero .zero)

def oneExt : Sentence :=
  .imply .verum (.equal .one .one)

def binaryCongruenceHyp : Formula Empty 4 :=
  .and (.equal (.bvar fin0) (.bvar fin2))
    (.and (.equal (.bvar fin1) (.bvar fin3)) .verum)

def addExt : Sentence :=
  Formula.allClosure
    (show Formula Empty 4 from .imply binaryCongruenceHyp
      (.equal (.add (.bvar fin0) (.bvar fin1))
        (.add (.bvar fin2) (.bvar fin3))))

def mulExt : Sentence :=
  Formula.allClosure
    (show Formula Empty 4 from .imply binaryCongruenceHyp
      (.equal (.mul (.bvar fin0) (.bvar fin1))
        (.mul (.bvar fin2) (.bvar fin3))))

def equalExt : Sentence :=
  Formula.allClosure
    (show Formula Empty 4 from .imply binaryCongruenceHyp
      (.imply (.equal (.bvar fin0) (.bvar fin1))
        (.equal (.bvar fin2) (.bvar fin3))))

def lessExt : Sentence :=
  Formula.allClosure
    (show Formula Empty 4 from .imply binaryCongruenceHyp
      (.imply (.less (.bvar fin0) (.bvar fin1))
        (.less (.bvar fin2) (.bvar fin3))))

end Equality

inductive EqualityAxiom : Theory
  | refl : EqualityAxiom Equality.refl
  | symm : EqualityAxiom Equality.symm
  | trans : EqualityAxiom Equality.trans
  | zeroExt : EqualityAxiom Equality.zeroExt
  | oneExt : EqualityAxiom Equality.oneExt
  | addExt : EqualityAxiom Equality.addExt
  | mulExt : EqualityAxiom Equality.mulExt
  | equalExt : EqualityAxiom Equality.equalExt
  | lessExt : EqualityAxiom Equality.lessExt

namespace PeanoMinus.Axiom

def addZero : Sentence :=
  .all (.equal (.add (.bvar fin0) .zero) (.bvar fin0))

def addAssoc : Sentence :=
  Formula.allClosure
    (show Formula Empty 3 from
      .equal (.add (.add (.bvar fin2) (.bvar fin1)) (.bvar fin0))
      (.add (.bvar fin2) (.add (.bvar fin1) (.bvar fin0))))

def addComm : Sentence :=
  Formula.allClosure
    (show Formula Empty 2 from
      .equal (.add (.bvar fin1) (.bvar fin0))
      (.add (.bvar fin0) (.bvar fin1)))

def addEqOfLt : Sentence :=
  Formula.allClosure
    (show Formula Empty 2 from
      .imply (.less (.bvar fin1) (.bvar fin0))
      (.exs (.equal (.add (.bvar fin2) (.bvar fin0)) (.bvar fin1))))

def zeroLe : Sentence :=
  .all (.or (.equal .zero (.bvar fin0)) (.less .zero (.bvar fin0)))

def zeroLtOne : Sentence :=
  .less .zero .one

def oneLeOfZeroLt : Sentence :=
  .all (.imply (.less .zero (.bvar fin0))
    (.or (.equal .one (.bvar fin0)) (.less .one (.bvar fin0))))

def addLtAdd : Sentence :=
  Formula.allClosure
    (show Formula Empty 3 from
      .imply (.less (.bvar fin2) (.bvar fin1))
      (.less (.add (.bvar fin2) (.bvar fin0))
        (.add (.bvar fin1) (.bvar fin0))))

def mulZero : Sentence :=
  .all (.equal (.mul (.bvar fin0) .zero) .zero)

def mulOne : Sentence :=
  .all (.equal (.mul (.bvar fin0) .one) (.bvar fin0))

def mulAssoc : Sentence :=
  Formula.allClosure
    (show Formula Empty 3 from
      .equal (.mul (.mul (.bvar fin2) (.bvar fin1)) (.bvar fin0))
      (.mul (.bvar fin2) (.mul (.bvar fin1) (.bvar fin0))))

def mulComm : Sentence :=
  Formula.allClosure
    (show Formula Empty 2 from
      .equal (.mul (.bvar fin1) (.bvar fin0))
      (.mul (.bvar fin0) (.bvar fin1)))

def mulLtMul : Sentence :=
  Formula.allClosure
    (show Formula Empty 3 from .imply
      (.and (.less (.bvar fin2) (.bvar fin1)) (.less .zero (.bvar fin0)))
      (.less (.mul (.bvar fin2) (.bvar fin0))
        (.mul (.bvar fin1) (.bvar fin0))))

def distr : Sentence :=
  Formula.allClosure
    (show Formula Empty 3 from
      .equal (.mul (.bvar fin2) (.add (.bvar fin1) (.bvar fin0)))
      (.add (.mul (.bvar fin2) (.bvar fin1))
        (.mul (.bvar fin2) (.bvar fin0))))

def ltIrrefl : Sentence :=
  .all (.nless (.bvar fin0) (.bvar fin0))

def ltTrans : Sentence :=
  Formula.allClosure
    (show Formula Empty 3 from .imply
      (.and (.less (.bvar fin2) (.bvar fin1))
        (.less (.bvar fin1) (.bvar fin0)))
      (.less (.bvar fin2) (.bvar fin0)))

def ltTri : Sentence :=
  Formula.allClosure
    (show Formula Empty 2 from
      .or (.less (.bvar fin1) (.bvar fin0))
      (.or (.equal (.bvar fin1) (.bvar fin0))
        (.less (.bvar fin0) (.bvar fin1))))

end PeanoMinus.Axiom

inductive PeanoMinus : Theory
  | equal {p : Sentence} : EqualityAxiom p → PeanoMinus p
  | addZero : PeanoMinus PeanoMinus.Axiom.addZero
  | addAssoc : PeanoMinus PeanoMinus.Axiom.addAssoc
  | addComm : PeanoMinus PeanoMinus.Axiom.addComm
  | addEqOfLt : PeanoMinus PeanoMinus.Axiom.addEqOfLt
  | zeroLe : PeanoMinus PeanoMinus.Axiom.zeroLe
  | zeroLtOne : PeanoMinus PeanoMinus.Axiom.zeroLtOne
  | oneLeOfZeroLt : PeanoMinus PeanoMinus.Axiom.oneLeOfZeroLt
  | addLtAdd : PeanoMinus PeanoMinus.Axiom.addLtAdd
  | mulZero : PeanoMinus PeanoMinus.Axiom.mulZero
  | mulOne : PeanoMinus PeanoMinus.Axiom.mulOne
  | mulAssoc : PeanoMinus PeanoMinus.Axiom.mulAssoc
  | mulComm : PeanoMinus PeanoMinus.Axiom.mulComm
  | mulLtMul : PeanoMinus PeanoMinus.Axiom.mulLtMul
  | distr : PeanoMinus PeanoMinus.Axiom.distr
  | ltIrrefl : PeanoMinus PeanoMinus.Axiom.ltIrrefl
  | ltTrans : PeanoMinus PeanoMinus.Axiom.ltTrans
  | ltTri : PeanoMinus PeanoMinus.Axiom.ltTri

inductive Peano : Theory
  | minus {p : Sentence} : PeanoMinus p → Peano p
  | induction (p : Semiproposition 1) :
      Peano (Formula.univClosure (Formula.succInd p))

/-! ## Effective codes for closed arithmetic syntax -/

namespace Coding

/-- The length-delimited vector code used by the maintained arithmetic syntax. -/
def vecCode {k : ℕ} (v : Fin k → ℕ) : ℕ :=
  @Nat.rec (fun k ↦ (Fin k → ℕ) → ℕ)
    (fun _ ↦ 0)
    (fun _ ih w ↦ Nat.pair (w fin0) (ih fun i ↦ w i.succ) + 1) k v

def vecCodeTwo (a b : ℕ) : ℕ :=
  Nat.pair a (Nat.pair b 0 + 1) + 1

def termCode {n : ℕ} : ClosedTerm n → ℕ
  | .bvar i => Nat.pair 0 i + 1
  | .fvar x => Empty.elim x
  | .zero => Nat.pair 2 (Nat.pair 0 (Nat.pair 0 0)) + 1
  | .one => Nat.pair 2 (Nat.pair 0 (Nat.pair 1 0)) + 1
  | .add s t =>
      Nat.pair 2 (Nat.pair 2 (Nat.pair 0 (vecCodeTwo (termCode s) (termCode t)))) + 1
  | .mul s t =>
      Nat.pair 2 (Nat.pair 2 (Nat.pair 1 (vecCodeTwo (termCode s) (termCode t)))) + 1

def formulaCode {n : ℕ} : Formula Empty n → ℕ
  | .verum => Nat.pair 2 0 + 1
  | .falsum => Nat.pair 3 0 + 1
  | .equal s t =>
      Nat.pair 0 (Nat.pair 2 (Nat.pair 0 (vecCodeTwo (termCode s) (termCode t)))) + 1
  | .nequal s t =>
      Nat.pair 1 (Nat.pair 2 (Nat.pair 0 (vecCodeTwo (termCode s) (termCode t)))) + 1
  | .less s t =>
      Nat.pair 0 (Nat.pair 2 (Nat.pair 1 (vecCodeTwo (termCode s) (termCode t)))) + 1
  | .nless s t =>
      Nat.pair 1 (Nat.pair 2 (Nat.pair 1 (vecCodeTwo (termCode s) (termCode t)))) + 1
  | .and p q => Nat.pair 4 (Nat.pair (formulaCode p) (formulaCode q)) + 1
  | .or p q => Nat.pair 5 (Nat.pair (formulaCode p) (formulaCode q)) + 1
  | .all p => Nat.pair 6 (formulaCode p) + 1
  | .exs p => Nat.pair 7 (formulaCode p) + 1

abbrev sentenceCode (p : Sentence) : ℕ := formulaCode p

end Coding

/-- Codes of the actual axioms of `T`, not codes of its deductive closure. -/
def AxiomCodes (T : Theory) (n : ℕ) : Prop :=
  ∃ p : Sentence, Coding.sentenceCode p = n ∧ p ∈ T

namespace Term

variable {ξ : Type} {n : ℕ}

/-- Evaluation of an independent arithmetic term in the standard naturals. -/
def standardEval (b : Fin n → ℕ) (f : ξ → ℕ) : Term ξ n → ℕ
  | .bvar i => b i
  | .fvar x => f x
  | .zero => 0
  | .one => 1
  | .add s t => standardEval b f s + standardEval b f t
  | .mul s t => standardEval b f s * standardEval b f t

end Term

namespace Formula

variable {ξ : Type} {n : ℕ}

/-- Standard truth under assignments for bound and free variables. -/
def standardEval {ξ : Type} : {n : ℕ} →
    (Fin n → ℕ) → (ξ → ℕ) → Formula ξ n → Prop
  | _, _, _, .verum => True
  | _, _, _, .falsum => False
  | _, b, f, .equal s t => s.standardEval b f = t.standardEval b f
  | _, b, f, .nequal s t => s.standardEval b f ≠ t.standardEval b f
  | _, b, f, .less s t => s.standardEval b f < t.standardEval b f
  | _, b, f, .nless s t => ¬s.standardEval b f < t.standardEval b f
  | _, b, f, .and p q => standardEval b f p ∧ standardEval b f q
  | _, b, f, .or p q => standardEval b f p ∨ standardEval b f q
  | _, b, f, .all p => ∀ x : ℕ, standardEval (Matrix.vecCons x b) f p
  | _, b, f, .exs p => ∃ x : ℕ, standardEval (Matrix.vecCons x b) f p

/-- A bounded universal quantifier in the independent syntax. -/
def ball (t : Term ξ n) (p : Formula ξ (n + 1)) : Formula ξ n :=
  .all (.or (.nless (.bvar fin0) t.lift) p)

/-- A bounded existential quantifier in the independent syntax. -/
def bexs (t : Term ξ n) (p : Formula ξ (n + 1)) : Formula ξ n :=
  .exs (.and (.less (.bvar fin0) t.lift) p)

end Formula

/-- Truth of a closed independent arithmetic formula in standard naturals. -/
def StandardTrue (p : Sentence) : Prop :=
  Formula.standardEval Fin.elim0 Empty.elim p

namespace Hierarchy

/-- Bounded arithmetic formulas in negation-normal form. -/
inductive DeltaZero {ξ : Type} : {n : ℕ} → Formula ξ n → Prop
  | verum : DeltaZero .verum
  | falsum : DeltaZero .falsum
  | equal {n : ℕ} (s t : Term ξ n) : DeltaZero (.equal s t)
  | nequal {n : ℕ} (s t : Term ξ n) : DeltaZero (.nequal s t)
  | less {n : ℕ} (s t : Term ξ n) : DeltaZero (.less s t)
  | nless {n : ℕ} (s t : Term ξ n) : DeltaZero (.nless s t)
  | and {n : ℕ} {p q : Formula ξ n} :
      DeltaZero p → DeltaZero q → DeltaZero (.and p q)
  | or {n : ℕ} {p q : Formula ξ n} :
      DeltaZero p → DeltaZero q → DeltaZero (.or p q)
  | ball {n : ℕ} {p : Formula ξ (n + 1)} (t : Term ξ n) :
      DeltaZero p → DeltaZero (Formula.ball t p)
  | bexs {n : ℕ} {p : Formula ξ (n + 1)} (t : Term ξ n) :
      DeltaZero p → DeltaZero (Formula.bexs t p)

/-- Π₁ formulas: bounded formulas closed under Boolean connectives, bounded
quantifiers, and unbounded universal quantification. -/
inductive PiOne {ξ : Type} : {n : ℕ} → Formula ξ n → Prop
  | delta {n : ℕ} {p : Formula ξ n} : DeltaZero p → PiOne p
  | and {n : ℕ} {p q : Formula ξ n} :
      PiOne p → PiOne q → PiOne (.and p q)
  | or {n : ℕ} {p q : Formula ξ n} :
      PiOne p → PiOne q → PiOne (.or p q)
  | ball {n : ℕ} {p : Formula ξ (n + 1)} (t : Term ξ n) :
      PiOne p → PiOne (Formula.ball t p)
  | bexs {n : ℕ} {p : Formula ξ (n + 1)} (t : Term ξ n) :
      PiOne p → PiOne (Formula.bexs t p)
  | all {n : ℕ} {p : Formula ξ (n + 1)} : PiOne p → PiOne (.all p)

end Hierarchy

/-- Every true independent Π₁ sentence is derivable in the theory. -/
def PiOneComplete (T : Theory) : Prop :=
  ∀ p : Sentence, Hierarchy.PiOne p → StandardTrue p → Provable T p


end FailureOfComposition.Palomar.Arithmetic
