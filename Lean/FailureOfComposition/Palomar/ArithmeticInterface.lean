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
  Fin.cases (bvar 0) fun i ↦ (b i).lift

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

def allClosure : {n : ℕ} → Formula ξ n → Formula ξ 0
  | 0, p => p
  | _n + 1, p => allClosure (.all p)

def univClosure (p : Proposition) : Sentence :=
  allClosure (fixFree p.fvSup p)

/-- The full successor-induction formula before its parameter closure. -/
def succInd (p : Semiproposition 1) : Proposition :=
  imply (p.substOne .zero)
    (imply
      (.all (imply p (p.subst fun _ ↦ .add (.bvar 0) .one)))
      (.all p))

end Formula

namespace Equality

def refl : Sentence :=
  .all (.equal (.bvar 0) (.bvar 0))

def symm : Sentence :=
  Formula.allClosure
    (show Formula Empty 2 from
      .imply (.equal (.bvar 1) (.bvar 0))
        (.equal (.bvar 0) (.bvar 1)))

def trans : Sentence :=
  Formula.allClosure
    (show Formula Empty 3 from
      .imply (.equal (.bvar 2) (.bvar 1))
        (.imply (.equal (.bvar 1) (.bvar 0))
          (.equal (.bvar 2) (.bvar 0))))

def zeroExt : Sentence :=
  .imply .verum (.equal .zero .zero)

def oneExt : Sentence :=
  .imply .verum (.equal .one .one)

def binaryCongruenceHyp : Formula Empty 4 :=
  .and (.equal (.bvar 0) (.bvar 2))
    (.and (.equal (.bvar 1) (.bvar 3)) .verum)

def addExt : Sentence :=
  Formula.allClosure
    (show Formula Empty 4 from .imply binaryCongruenceHyp
      (.equal (.add (.bvar 0) (.bvar 1))
        (.add (.bvar 2) (.bvar 3))))

def mulExt : Sentence :=
  Formula.allClosure
    (show Formula Empty 4 from .imply binaryCongruenceHyp
      (.equal (.mul (.bvar 0) (.bvar 1))
        (.mul (.bvar 2) (.bvar 3))))

def equalExt : Sentence :=
  Formula.allClosure
    (show Formula Empty 4 from .imply binaryCongruenceHyp
      (.imply (.equal (.bvar 0) (.bvar 1))
        (.equal (.bvar 2) (.bvar 3))))

def lessExt : Sentence :=
  Formula.allClosure
    (show Formula Empty 4 from .imply binaryCongruenceHyp
      (.imply (.less (.bvar 0) (.bvar 1))
        (.less (.bvar 2) (.bvar 3))))

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
  .all (.equal (.add (.bvar 0) .zero) (.bvar 0))

def addAssoc : Sentence :=
  Formula.allClosure
    (show Formula Empty 3 from
      .equal (.add (.add (.bvar 2) (.bvar 1)) (.bvar 0))
      (.add (.bvar 2) (.add (.bvar 1) (.bvar 0))))

def addComm : Sentence :=
  Formula.allClosure
    (show Formula Empty 2 from
      .equal (.add (.bvar 1) (.bvar 0))
      (.add (.bvar 0) (.bvar 1)))

def addEqOfLt : Sentence :=
  Formula.allClosure
    (show Formula Empty 2 from
      .imply (.less (.bvar 1) (.bvar 0))
      (.exs (.equal (.add (.bvar 2) (.bvar 0)) (.bvar 1))))

def zeroLe : Sentence :=
  .all (.or (.equal .zero (.bvar 0)) (.less .zero (.bvar 0)))

def zeroLtOne : Sentence :=
  .less .zero .one

def oneLeOfZeroLt : Sentence :=
  .all (.imply (.less .zero (.bvar 0))
    (.or (.equal .one (.bvar 0)) (.less .one (.bvar 0))))

def addLtAdd : Sentence :=
  Formula.allClosure
    (show Formula Empty 3 from
      .imply (.less (.bvar 2) (.bvar 1))
      (.less (.add (.bvar 2) (.bvar 0))
        (.add (.bvar 1) (.bvar 0))))

def mulZero : Sentence :=
  .all (.equal (.mul (.bvar 0) .zero) .zero)

def mulOne : Sentence :=
  .all (.equal (.mul (.bvar 0) .one) (.bvar 0))

def mulAssoc : Sentence :=
  Formula.allClosure
    (show Formula Empty 3 from
      .equal (.mul (.mul (.bvar 2) (.bvar 1)) (.bvar 0))
      (.mul (.bvar 2) (.mul (.bvar 1) (.bvar 0))))

def mulComm : Sentence :=
  Formula.allClosure
    (show Formula Empty 2 from
      .equal (.mul (.bvar 1) (.bvar 0))
      (.mul (.bvar 0) (.bvar 1)))

def mulLtMul : Sentence :=
  Formula.allClosure
    (show Formula Empty 3 from .imply
      (.and (.less (.bvar 2) (.bvar 1)) (.less .zero (.bvar 0)))
      (.less (.mul (.bvar 2) (.bvar 0))
        (.mul (.bvar 1) (.bvar 0))))

def distr : Sentence :=
  Formula.allClosure
    (show Formula Empty 3 from
      .equal (.mul (.bvar 2) (.add (.bvar 1) (.bvar 0)))
      (.add (.mul (.bvar 2) (.bvar 1))
        (.mul (.bvar 2) (.bvar 0))))

def ltIrrefl : Sentence :=
  .all (.nless (.bvar 0) (.bvar 0))

def ltTrans : Sentence :=
  Formula.allClosure
    (show Formula Empty 3 from .imply
      (.and (.less (.bvar 2) (.bvar 1))
        (.less (.bvar 1) (.bvar 0)))
      (.less (.bvar 2) (.bvar 0)))

def ltTri : Sentence :=
  Formula.allClosure
    (show Formula Empty 2 from
      .or (.less (.bvar 1) (.bvar 0))
      (.or (.equal (.bvar 1) (.bvar 0))
        (.less (.bvar 0) (.bvar 1))))

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
def vecCode : {k : ℕ} → (Fin k → ℕ) → ℕ
  | 0, _ => 0
  | _k + 1, v => Nat.pair (v 0) (vecCode (fun i ↦ v i.succ)) + 1

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

end FailureOfComposition.Palomar.Arithmetic
