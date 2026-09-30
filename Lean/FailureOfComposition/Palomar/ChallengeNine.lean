/- Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0; authors: Florian Lengyel. Independent definitions are
adapted from Foundation e72cfe981aa65166f37fa4e2584f4806bc48d72f. -/
import Mathlib.Computability.RE
import Mathlib.Data.Fin.VecNotation
import Mathlib.Computability.PartrecCode
/-! Eligible cumulative statement boundary for all nine selected results. -/
set_option autoImplicit false
namespace FailureOfComposition.Palomar.Arithmetic
def fin0 {n : ℕ} : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
def fin1 {n : ℕ} : Fin (n + 2) := (fin0 (n := n)).succ
def fin2 {n : ℕ} : Fin (n + 3) := (fin1 (n := n)).succ
def fin3 {n : ℕ} : Fin (n + 4) := (fin2 (n := n)).succ
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
structure Proof (T : Theory) (p : Sentence) where
  axioms : Multiset Sentence
  axioms_mem : ∀ q ∈ axioms, q ∈ T
  derivation :
    Derivation (Sequent.singleton p.embed + Sequent.negateSentences axioms)
def Provable (T : Theory) (p : Sentence) : Prop := Nonempty (Proof T p)
def Consistent (T : Theory) : Prop := ¬Provable T .falsum
def DeductivelyExtends (U T : Theory) : Prop :=
  ∀ {p : Sentence}, Provable U p → Provable T p
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
def fvSup (p : Formula ℕ n) : ℕ :=
  (p.freeVariables.max).recBotCoe 0 Nat.succ
def fixFree (m : ℕ) (p : Proposition) : Formula Empty m :=
  p.rewrite Fin.elim0 fun x ↦
    if h : x < m then Term.bvar ⟨x, h⟩ else Term.zero
def allClosure {n : ℕ} (p : Formula ξ n) : Formula ξ 0 :=
  @Nat.rec (fun n ↦ Formula ξ n → Formula ξ 0)
    (fun q ↦ q) (fun _ ih q ↦ ih (.all q)) n p
def univClosure (p : Proposition) : Sentence :=
  allClosure (fixFree p.fvSup p)
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
namespace Coding
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
def AxiomCodes (T : Theory) (n : ℕ) : Prop :=
  ∃ p : Sentence, Coding.sentenceCode p = n ∧ p ∈ T
namespace Term
variable {ξ : Type} {n : ℕ}
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
def ball (t : Term ξ n) (p : Formula ξ (n + 1)) : Formula ξ n :=
  .all (.or (.nless (.bvar fin0) t.lift) p)
def bexs (t : Term ξ n) (p : Formula ξ (n + 1)) : Formula ξ n :=
  .exs (.and (.less (.bvar fin0) t.lift) p)
end Formula
def StandardTrue (p : Sentence) : Prop :=
  Formula.standardEval Fin.elim0 Empty.elim p
namespace Hierarchy
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
inductive SigmaOne {ξ : Type} : {n : ℕ} → Formula ξ n → Prop
  | delta {n : ℕ} {p : Formula ξ n} : DeltaZero p → SigmaOne p
  | and {n : ℕ} {p q : Formula ξ n} : SigmaOne p → SigmaOne q → SigmaOne (.and p q)
  | or {n : ℕ} {p q : Formula ξ n} : SigmaOne p → SigmaOne q → SigmaOne (.or p q)
  | ball {n : ℕ} {p : Formula ξ (n + 1)} (t : Term ξ n) :
      SigmaOne p → SigmaOne (Formula.ball t p)
  | bexs {n : ℕ} {p : Formula ξ (n + 1)} (t : Term ξ n) :
      SigmaOne p → SigmaOne (Formula.bexs t p)
  | exs {n : ℕ} {p : Formula ξ (n + 1)} : SigmaOne p → SigmaOne (.exs p)
end Hierarchy
def PiOneComplete (T : Theory) : Prop :=
  ∀ p : Sentence, Hierarchy.PiOne p → StandardTrue p → Provable T p
def SigmaOneSound (T : Theory) : Prop :=
  ∀ p : Sentence, Hierarchy.SigmaOne p → Provable T p → StandardTrue p
end FailureOfComposition.Palomar.Arithmetic
namespace FailureOfComposition.Palomar.Arithmetic.Evaluator
inductive Code : ℕ → Type
  | zero (n : ℕ) : Code n
  | one (n : ℕ) : Code n
  | add {n : ℕ} (i j : Fin n) : Code n
  | mul {n : ℕ} (i j : Fin n) : Code n
  | proj {n : ℕ} (i : Fin n) : Code n
  | equal {n : ℕ} (i j : Fin n) : Code n
  | lt {n : ℕ} (i j : Fin n) : Code n
  | comp {m n : ℕ} : Code n → (Fin n → Code m) → Code m
  | rfind {n : ℕ} : Code (n + 1) → Code n
namespace Compiler
def finConj {xi : Type} {n k : ℕ}
    (v : Fin k → Formula xi n) : Formula xi n :=
  @Nat.rec (fun k ↦ (Fin k → Formula xi n) → Formula xi n)
    (fun _ ↦ .verum)
    (fun _ ih w ↦ .and (w fin0) (ih fun i ↦ w i.succ)) k v
def exsClosure {xi : Type} {n : ℕ} (p : Formula xi n) : Formula xi 0 :=
  @Nat.rec (fun n ↦ Formula xi n → Formula xi 0)
    (fun q ↦ q) (fun _ ih q ↦ ih (.exs q)) n p
def codeAux : {k : ℕ} → Code k → Formula (Fin (k + 1)) 0
  | _, .zero _ => .equal (.fvar fin0) .zero
  | _, .one _ => .equal (.fvar fin0) .one
  | _, .add i j => .equal (.fvar fin0) (.add (.fvar i.succ) (.fvar j.succ))
  | _, .mul i j => .equal (.fvar fin0) (.mul (.fvar i.succ) (.fvar j.succ))
  | _, .proj i => .equal (.fvar fin0) (.fvar i.succ)
  | _, .equal i j =>
      .or
        (.and (.equal (.fvar i.succ) (.fvar j.succ))
          (.equal (.fvar fin0) .one))
        (.and (.nequal (.fvar i.succ) (.fvar j.succ))
          (.equal (.fvar fin0) .zero))
  | _, .lt i j =>
      .or
        (.and (.less (.fvar i.succ) (.fvar j.succ))
          (.equal (.fvar fin0) .one))
        (.and (.nless (.fvar i.succ) (.fvar j.succ))
          (.equal (.fvar fin0) .zero))
  | _, @Code.comp _ _ c d =>
      exsClosure
        (.and
          ((codeAux c).rewrite Fin.elim0
            (Fin.cases (.fvar fin0) fun i ↦ .bvar i))
          (finConj fun i ↦
            (codeAux (d i)).rewrite Fin.elim0
              (Fin.cases (.bvar i) fun j ↦ .fvar j.succ)))
  | _, @Code.rfind _ c =>
      .and
        ((codeAux c).rewrite Fin.elim0
          (Fin.cases .zero (Fin.cases (.fvar fin0) fun j ↦ .fvar j.succ)))
        (.all
          (.or (.nless (.bvar fin0) (.fvar fin0))
            (.exs
              (.and (.nequal (.bvar fin0) .zero)
                ((codeAux c).rewrite Fin.elim0
                  (Fin.cases (.bvar fin0)
                    (Fin.cases (.bvar fin1) fun j ↦ .fvar j.succ)))))))
def code {k : ℕ} (c : Code k) : Formula Empty (k + 1) :=
  (codeAux c).rewrite Fin.elim0 (fun i ↦ .bvar i)
end Compiler
namespace Construction
def codeSucc {n : ℕ} (d : Code n) : Code n :=
  (Code.add fin0 fin1).comp ![d, Code.one n]
def codeConst {n : ℕ} (m : ℕ) : Code n :=
  Nat.rec (.zero n) (fun _ d ↦ codeSucc d) m
def codeInv {n : ℕ} (d : Code n) : Code n :=
  (Code.equal fin0 fin1).comp ![d, Code.zero n]
def codePos {n : ℕ} (d : Code n) : Code n :=
  (Code.lt fin0 fin1).comp ![Code.zero n, d]
def codeAnd {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  (Code.lt fin0 fin1).comp ![Code.zero n, (Code.mul fin0 fin1).comp ![d₀, d₁]]
def codeOr {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  (Code.lt fin0 fin1).comp ![Code.zero n, (Code.add fin0 fin1).comp ![d₀, d₁]]
def codeEq {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  (Code.equal fin0 fin1).comp ![d₀, d₁]
def codeLt {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  (Code.lt fin0 fin1).comp ![d₀, d₁]
def codeAdd {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  (Code.add fin0 fin1).comp ![d₀, d₁]
def codeMul {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  (Code.mul fin0 fin1).comp ![d₀, d₁]
def codeLift {n : ℕ} (d : Code n) : Code (n + 1) :=
  d.comp fun i ↦ .proj i.succ
def codeHead {n : ℕ} : Code (n + 1) := .proj fin0
def codeIfPos {n : ℕ} (df dg dh : Code n) : Code n :=
  codeAdd (codeMul (codePos df) dg) (codeMul (codeInv df) dh)
def codeLe {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  codeOr (codeLt d₀ d₁) (codeEq d₀ d₁)
def codeRfindPos {n : ℕ} (d : Code (n + 1)) : Code n :=
  (codeInv (codePos d)).rfind
def codeBind {n : ℕ} (dg : Code n) (dc : Code (n + 1)) : Code n :=
  dc.comp (Fin.cases dg fun i ↦ .proj i)
def codeSub {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  codeRfindPos
    (codeOr
      (codeEq (codeAdd codeHead (codeLift d₁)) (codeLift d₀))
      (codeAnd (codeLt (codeLift d₀) (codeLift d₁))
        (codeEq codeHead (.zero _))))
def codeSqrt {n : ℕ} (d : Code n) : Code n :=
  codeRfindPos
    (codeAnd
      (codeOr (codeLt (codeMul codeHead codeHead) (codeLift d))
        (codeEq (codeMul codeHead codeHead) (codeLift d)))
      (codeLt (codeLift d)
        (codeMul (codeSucc codeHead) (codeSucc codeHead))))
def codeUnpair₁ {n : ℕ} (d : Code n) : Code n :=
  codeIfPos
    (codeLt (codeSub d (codeMul (codeSqrt d) (codeSqrt d))) (codeSqrt d))
    (codeSub d (codeMul (codeSqrt d) (codeSqrt d)))
    (codeSqrt d)
def codeUnpair₂ {n : ℕ} (d : Code n) : Code n :=
  codeIfPos
    (codeLt (codeSub d (codeMul (codeSqrt d) (codeSqrt d))) (codeSqrt d))
    (codeSqrt d)
    (codeSub (codeSub d (codeMul (codeSqrt d) (codeSqrt d))) (codeSqrt d))
def codeDvd {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  codeBind
    (codeRfindPos
      (codeOr (codeEq (codeMul codeHead (codeLift d₀)) (codeLift d₁))
        (codeLt (codeLift d₁) codeHead)))
    (codeLe codeHead (codeLift d₁))
def codeRem {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  codeRfindPos (codeDvd (codeLift d₁) (codeSub (codeLift d₀) codeHead))
def codeBeta {n : ℕ} (dn di : Code n) : Code n :=
  codeRem (codeUnpair₁ dn) (codeSucc (codeMul (codeSucc di) (codeUnpair₂ dn)))
def codePair {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  codeIfPos (codeLt d₀ d₁)
    (codeAdd (codeMul d₁ d₁) d₀)
    (codeAdd (codeAdd (codeMul d₀ d₀) d₀) d₁)
def codeBall {n : ℕ} (dphi : Code (n + 1)) (i : Fin n) : Code n :=
  codeBind
    (codeRfindPos (codeOr (codeInv dphi) (codeLe (codeLift (.proj i)) codeHead)))
    (codeEq codeHead (codeLift (.proj i)))
def precStepArgs {n : ℕ} : Fin (n + 2) → Code (n + 3) :=
  Fin.cases (.proj fin0)
    (Fin.cases (codeBeta (.proj fin1) (.proj fin0))
      fun j ↦ .proj j.succ.succ.succ)
def codePrecStep {n : ℕ} (dg : Code (n + 2)) : Code (n + 3) :=
  codeEq
    (codeBeta (.proj fin1) (codeSucc (.proj fin0)))
    (dg.comp precStepArgs)
def codeTailTail {n : ℕ} (df : Code n) : Code (n + 2) :=
  df.comp fun j ↦ .proj j.succ.succ
def codePrecPredicate {n : ℕ}
    (df : Code n) (dg : Code (n + 2)) : Code (n + 2) :=
  codeAnd
    (codeEq (codeBeta (.proj fin0) (codeConst 0)) (codeTailTail df))
    (codeBall (codePrecStep dg) fin1)
def codePrec {n : ℕ} (df : Code n) (dg : Code (n + 2)) : Code (n + 1) :=
  codeBind
    (codeRfindPos (codePrecPredicate df dg))
    (codeBeta codeHead (codeLift codeHead))
def codeListHead? {n : ℕ} (d : Code n) : Code n :=
  codeIfPos d
    (codeSucc (codeUnpair₁ (codeSub d (codeConst 1))))
    (.zero n)
def codeListTail {n : ℕ} (d : Code n) : Code n :=
  codeUnpair₂ (codeSub d (codeConst 1))
def codeListDrop {n : ℕ} (dlist didx : Code n) : Code n :=
  (codePrec (.proj fin0)
    (codeListTail (.proj fin1))).comp ![didx, dlist]
def codeListGet? {n : ℕ} (dlist didx : Code n) : Code n :=
  codeListHead? (codeListDrop dlist didx)
def codeListLength {n : ℕ} (dlist : Code n) : Code n :=
  codeRfindPos (codeInv (codeListDrop (codeLift dlist) codeHead))
def codeOptionBind {n : ℕ} (dopt : Code n) (dk : Code (n + 1)) : Code n :=
  codeIfPos dopt
    (codeBind (codeSub dopt (.one n)) dk)
    (.zero n)
def codeListNil {n : ℕ} : Code n := .zero n
def codeListCons {n : ℕ} (dx dt : Code n) : Code n :=
  codeSucc (codePair dx dt)
def codeListSnoc {r : ℕ} (dlist dx : Code r) : Code r :=
  codeBind (codeListLength dlist)
    (codePrec
      (codeListCons dx (codeListNil (n := r)))
      (codeListCons
        (codeSub
          (codeListGet? (codeLift (codeLift dlist))
            (codeSub (codeListLength (codeLift (codeLift dlist)))
              (codeSucc (.proj fin0))))
          (codeConst 1))
        (.proj fin1)))
def codeBodd {n : ℕ} (d : Code n) : Code n :=
  codeRem d (codeConst 2)
def codeDiv2Unary : Code 1 :=
  codePrec (.zero 0)
    (codeIfPos
      (codeBodd (.proj fin0))
      (codeSucc (.proj fin1))
      (.proj fin1))
def codeDiv2 {n : ℕ} (d : Code n) : Code n :=
  codeDiv2Unary.comp ![d]
def codePartrecTag {n : ℕ} (d : Code n) : Code n :=
  let r := codeSub d (codeConst 4)
  codeIfPos (codeLt d (codeConst 4)) d
    (codeAdd
      (codeAdd (codeConst 4) (codeMul (codeConst 2) (codeBodd r)))
      (codeBodd (codeDiv2 r)))
def codePartrecPayload {n : ℕ} (d : Code n) : Code n :=
  codeDiv2 (codeDiv2 (codeSub d (codeConst 4)))
def codePartrecPayload₁ {n : ℕ} (d : Code n) : Code n :=
  codeUnpair₁ (codePartrecPayload d)
def codePartrecPayload₂ {n : ℕ} (d : Code n) : Code n :=
  codeUnpair₂ (codePartrecPayload d)
def codeTableLookup {r : ℕ} (dtable dk dq dn : Code r) : Code r :=
  codeSub
    (codeListGet?
      (codeSub (codeListGet? dtable (codePair dk dq)) (codeConst 1))
      dn)
    (codeConst 1)
def codeBaseEvaluatorCell {r : ℕ} (dtable dn : Code r) : Code r :=
  let dp := codeListLength dtable
  let dk := codeUnpair₁ dp
  let dq := codeUnpair₂ dp
  let dtag := codePartrecTag dq
  codeIfPos dk
    (codeIfPos (codeEq dtag (codeConst 0))
      (codeConst 1)
      (codeIfPos (codeEq dtag (codeConst 1))
        (codeSucc (codeSucc dn))
        (codeIfPos (codeEq dtag (codeConst 2))
          (codeSucc (codeUnpair₁ dn))
          (codeIfPos (codeEq dtag (codeConst 3))
            (codeSucc (codeUnpair₂ dn))
            (codeConst 0)))))
    (codeConst 0)
def codePairEvaluatorCell {r : ℕ}
    (dtable dk dcf dcg dn : Code r) : Code r :=
  codeOptionBind
    (codeTableLookup dtable dk dcf dn)
    (codeOptionBind
      (codeTableLookup (codeLift dtable) (codeLift dk) (codeLift dcg) (codeLift dn))
      (codeSucc (codePair (.proj fin1) (.proj fin0))))
def codeCompEvaluatorCell {r : ℕ}
    (dtable dk dcf dcg dn : Code r) : Code r :=
  codeOptionBind
    (codeTableLookup dtable dk dcg dn)
    (codeTableLookup (codeLift dtable) (codeLift dk) (codeLift dcf) codeHead)
def codePrecEvaluatorCell {r : ℕ}
    (dtable dk' dq dcf dcg dn : Code r) : Code r :=
  let dk := codeSucc dk'
  let dz := codeUnpair₁ dn
  let dt := codeUnpair₂ dn
  let dy := codeSub dt (codeConst 1)
  codeIfPos dt
    (codeOptionBind
      (codeTableLookup dtable dk' dq (codePair dz dy))
      (codeTableLookup (codeLift dtable) (codeLift dk) (codeLift dcg)
        (codePair (codeLift dz) (codePair (codeLift dy) codeHead))))
    (codeTableLookup dtable dk dcf dz)
def codeRfindEvaluatorCell {r : ℕ}
    (dtable dk' dq dcf dn : Code r) : Code r :=
  let dk := codeSucc dk'
  let dz := codeUnpair₁ dn
  let dm := codeUnpair₂ dn
  codeOptionBind
    (codeTableLookup dtable dk dcf (codePair dz dm))
    (codeIfPos codeHead
      (codeTableLookup (codeLift dtable) (codeLift dk') (codeLift dq)
        (codePair (codeLift dz) (codeSucc (codeLift dm))))
      (codeSucc (codeLift dm)))
def codeEvaluatorCell {r : ℕ} (dtable dn : Code r) : Code r :=
  let dp := codeListLength dtable
  let dk := codeUnpair₁ dp
  let dk' := codeSub dk (codeConst 1)
  let dq := codeUnpair₂ dp
  let dtag := codePartrecTag dq
  let dcf := codePartrecPayload₁ dq
  let dcg := codePartrecPayload₂ dq
  let drfind := codePartrecPayload dq
  codeIfPos dk
    (codeIfPos (codeEq dtag (codeConst 4))
      (codePairEvaluatorCell dtable dk dcf dcg dn)
      (codeIfPos (codeEq dtag (codeConst 5))
        (codeCompEvaluatorCell dtable dk dcf dcg dn)
        (codeIfPos (codeEq dtag (codeConst 6))
          (codePrecEvaluatorCell dtable dk' dq dcf dcg dn)
          (codeIfPos (codeEq dtag (codeConst 7))
            (codeRfindEvaluatorCell dtable dk' dq drfind dn)
            (codeBaseEvaluatorCell dtable dn)))))
    (codeConst 0)
def codeEvaluatorRow {r : ℕ} (dtable : Code r) : Code r :=
  codeBind (codeUnpair₁ (codeListLength dtable))
    (codePrec
      (codeListNil (n := r))
      (codeListCons
        (codeEvaluatorCell (codeLift (codeLift dtable))
          (codeSub (codeUnpair₁ (codeListLength (codeLift (codeLift dtable))))
            (codeSucc (.proj fin0))))
        (.proj fin1)))
def codeEvaluatorTableStep {r : ℕ} (dtable : Code r) : Code r :=
  codeListSnoc dtable (codeEvaluatorRow dtable)
def codeEvaluatorHistory : Code 1 :=
  codePrec (codeListNil (n := 0))
    (codeEvaluatorTableStep (.proj fin1))
def codeHistoryEvaluator : Code 3 :=
  codeTableLookup
    (codeEvaluatorHistory.comp
      ![codeSucc (codePair (.proj fin0) (.proj fin1))])
    (.proj fin0) (.proj fin1) (.proj fin2)
end Construction
def certificateFormula : Formula Empty 4 :=
  (Compiler.code Construction.codeHistoryEvaluator).subst
    ![.add (.bvar fin3) .one, .bvar fin0, .bvar fin1, .bvar fin2]
abbrev Graph := Formula Empty 2
def eventualGraph (q : ℕ) : Graph :=
  .exs (certificateFormula.subst
    ![.bvar fin0, Term.numeral q, .bvar fin1, .bvar fin2])
def definedAt {n : ℕ} (F : Graph) (x : Term Empty n) : Formula Empty n :=
  .exs (F.subst
    (Fin.cases x.lift
      (Fin.cases (.bvar ⟨0, Nat.zero_lt_succ n⟩) Fin.elim0)))
def commonValueAt {n : ℕ} (F G : Graph) (x : Term Empty n) :
    Formula Empty n :=
  .exs (.and
    (F.subst (Fin.cases x.lift
      (Fin.cases (.bvar ⟨0, Nat.zero_lt_succ n⟩) Fin.elim0)))
    (G.subst (Fin.cases x.lift
      (Fin.cases (.bvar ⟨0, Nat.zero_lt_succ n⟩) Fin.elim0))))
def biimp {xi : Type} {n : ℕ} (p q : Formula xi n) : Formula xi n :=
  .and (.imply p q) (.imply q p)
def kleeneEqTerm {n : ℕ} (F G : Graph) (x : Term Empty n) :
    Formula Empty n :=
  .and (biimp (definedAt F x) (definedAt G x))
    (.imply (definedAt F x) (commonValueAt F G x))
def kleeneEqAt (F G : Graph) (n : ℕ) : Sentence :=
  kleeneEqTerm F G (Term.numeral n)
def uniformKleeneSentence (F G : Graph) : Sentence :=
  .all (kleeneEqTerm F G (.bvar fin0))
def identityIndex : ℕ := 48
def emptyIndex : ℕ := 11
def compIndex (f g : ℕ) : ℕ :=
  2 * (2 * Nat.pair f g + 1) + 4
def PointwiseIndex (T : Theory) (e d : ℕ) : Prop :=
  ∀ n : ℕ, Provable T (kleeneEqAt (eventualGraph e) (eventualGraph d) n)
def UniformIndex (T : Theory) (e d : ℕ) : Prop :=
  Provable T (uniformKleeneSentence (eventualGraph e) (eventualGraph d))
abbrev IndexQuotient (T : Theory) :=
  Quot (PointwiseIndex T)
def indexQuotientMk (T : Theory) (e : ℕ) : IndexQuotient T :=
  Quot.mk _ e
def actualEval (e x : ℕ) : Part ℕ :=
  Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) x
def RightCompatible (T : Theory) : Prop :=
  ∀ f h g : ℕ, PointwiseIndex T f h →
    PointwiseIndex T (compIndex f g) (compIndex h g)
def CompositionCongruence (T : Theory) : Prop :=
  ∀ f f' g g' : ℕ, PointwiseIndex T f f' → PointwiseIndex T g g' →
    PointwiseIndex T (compIndex f g) (compIndex f' g')
def AgreesWithExtensional (T : Theory) : Prop :=
  ∀ e d : ℕ, PointwiseIndex T e d ↔ actualEval e = actualEval d
def IsCompositionCongruence (R : ℕ → ℕ → Prop) : Prop :=
  Equivalence R ∧ ∀ a a' b b' : ℕ, R a a' → R b b' →
    R (compIndex a b) (compIndex a' b')
def GeneratedRel (T : Theory) (e d : ℕ) : Prop :=
  ∀ R : ℕ → ℕ → Prop, IsCompositionCongruence R →
    (∀ x y : ℕ, PointwiseIndex T x y → R x y) → R e d
abbrev GeneratedQuotient (T : Theory) := Quot (GeneratedRel T)
def generatedQuotientMk (T : Theory) (e : ℕ) : GeneratedQuotient T := Quot.mk _ e
instance generatedQuotientMul (T : Theory) : Mul (GeneratedQuotient T) where
  mul := Quot.lift₂ (fun e d ↦ generatedQuotientMk T (compIndex e d))
    (by intro a b b' hb; exact Quot.sound (fun R hR hbase ↦
      hR.2 a a b b' (hR.1.refl a) (hb R hR hbase)))
    (by intro a a' b ha; exact Quot.sound (fun R hR hbase ↦
      hR.2 a a' b b (ha R hR hbase) (hR.1.refl b)))
instance generatedQuotientOne (T : Theory) : One (GeneratedQuotient T) where
  one := generatedQuotientMk T identityIndex
def UnaryPartrec := { f : ℕ → Part ℕ // Nat.Partrec f }
namespace UnaryPartrec
instance : Mul UnaryPartrec where
  mul f g := ⟨fun x ↦ (g.val x).bind f.val, Nat.Partrec.comp f.property g.property⟩
instance : One UnaryPartrec where
  one := ⟨Part.some, Nat.Partrec.Code.exists_code.mpr
    ⟨Nat.Partrec.Code.id, funext Nat.Partrec.Code.eval_id⟩⟩
def ofIndex (e : ℕ) : UnaryPartrec := ⟨actualEval e,
  Nat.Partrec.Code.exists_code.mpr ⟨Denumerable.ofNat Nat.Partrec.Code e, rfl⟩⟩
end UnaryPartrec
namespace IndexCompiler
abbrev PCode := Nat.Partrec.Code
def addProgram : PCode :=
  .prec Nat.Partrec.Code.id (.comp .succ (.comp .right .right))
def mulProgram : PCode :=
  .prec .zero (.comp addProgram (.pair .left (.comp .right .right)))
def predProgram : PCode :=
  .comp (.prec .zero (.comp .left .right)) (.pair .zero Nat.Partrec.Code.id)
def subProgram : PCode :=
  .prec Nat.Partrec.Code.id (.comp predProgram (.comp .right .right))
def isZeroProgram : PCode :=
  .comp (.prec (Nat.Partrec.Code.const 1) .zero) (.pair .zero Nat.Partrec.Code.id)
def ltProgram : PCode :=
  .comp isZeroProgram (.comp subProgram (.pair (.comp .succ .left) .right))
def eqProgram : PCode :=
  .comp isZeroProgram (.comp addProgram
    (.pair subProgram (.comp subProgram (.pair .right .left))))
def projectionCode : (n : ℕ) → Fin n → PCode
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases .left (fun j => .comp (projectionCode n j) .right) i
def tupleCode : (n : ℕ) → (Fin n → PCode) → PCode
  | 0, _ => .zero
  | n + 1, d => .pair (d 0) (tupleCode n (fun i => d i.succ))
def swapCode : PCode := .pair .right .left
def searchZeroCode (c : PCode) : PCode :=
  .comp (.rfind' (.comp c swapCode)) (.pair Nat.Partrec.Code.id .zero)
def compile : {n : ℕ} → Code n → PCode
  | _, .zero _ => .zero
  | _, .one _ => Nat.Partrec.Code.const 1
  | n, .add i j => .comp addProgram
      (.pair (projectionCode n i) (projectionCode n j))
  | n, .mul i j => .comp mulProgram
      (.pair (projectionCode n i) (projectionCode n j))
  | n, .proj i => projectionCode n i
  | n, .equal i j => .comp eqProgram
      (.pair (projectionCode n i) (projectionCode n j))
  | n, .lt i j => .comp ltProgram
      (.pair (projectionCode n i) (projectionCode n j))
  | _, @Code.comp _ n c d => .comp (compile c)
      (tupleCode n (fun i => compile (d i)))
  | _, .rfind c => searchZeroCode (compile c)
def unaryCompile (c : Code 1) : PCode :=
  .comp (compile c) (.pair Nat.Partrec.Code.id .zero)
end IndexCompiler
open Construction
def historyCode (d : ℕ) : Code 1 :=
  codeHistoryEvaluator.comp ![Code.proj 0, codeConst d, codeConst d]
def guardCode (d : ℕ) : Code 1 :=
  codeBind (codeLift (historyCode d)).rfind (Code.proj 1)
def guardIndex (d : ℕ) : ℕ :=
  Encodable.encode (IndexCompiler.unaryCompile (guardCode d))
def WeaklyTotalIndex (T : Theory) (e : ℕ) : Prop :=
  ∀ d : ℕ, PointwiseIndex T (compIndex e d) emptyIndex → PointwiseIndex T d emptyIndex
def rangeOfGraph (F : Graph) : Graph :=
  .and (.equal (.bvar fin0) (.bvar fin1))
    (.exs (F.subst ![.bvar fin0, .bvar fin1]))
def rangeGraph (e : ℕ) : Graph :=
  rangeOfGraph (eventualGraph e)
def uniformGraphSentence (F G : Graph) : Sentence :=
  .all (.all (biimp
    (F.subst ![.bvar fin1, .bvar fin0])
    (G.subst ![.bvar fin1, .bvar fin0])))
def RangeRealizes (e r : ℕ) : Prop :=
  Provable Peano (uniformGraphSentence (eventualGraph r) (rangeGraph e))
noncomputable def rangeIndex (e : ℕ) : ℕ :=
  Classical.epsilon (RangeRealizes e)
end FailureOfComposition.Palomar.Arithmetic.Evaluator
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
  sorry
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
  sorry
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
  sorry
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
  sorry
theorem generated_congruence_classification
    (T : Arithmetic.Theory)
    (hPA : Arithmetic.DeductivelyExtends Arithmetic.Peano T) :
    (Arithmetic.SigmaOneSound T →
      ∀ e d : ℕ, Arithmetic.Evaluator.GeneratedRel T e d ↔
        Arithmetic.Evaluator.actualEval e = Arithmetic.Evaluator.actualEval d) ∧
    (¬Arithmetic.SigmaOneSound T →
      ∀ e d : ℕ, Arithmetic.Evaluator.GeneratedRel T e d) := by
  sorry
theorem weak_totality_counterexample
    (T : Arithmetic.Theory)
    (hPA : Arithmetic.DeductivelyExtends Arithmetic.Peano T)
    (hCons : Arithmetic.Consistent T)
    (hT : REPred (Arithmetic.AxiomCodes T)) :
    ∃ d : ℕ, Arithmetic.Evaluator.PointwiseIndex T
        (Arithmetic.Evaluator.guardIndex d) Arithmetic.Evaluator.identityIndex ∧
      ¬Arithmetic.Evaluator.WeaklyTotalIndex T (Arithmetic.Evaluator.guardIndex d) ∧
      Arithmetic.Evaluator.WeaklyTotalIndex T Arithmetic.Evaluator.identityIndex := by
  sorry
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
  sorry
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
  sorry
theorem generated_quotient_partial_recursive
    (T : Arithmetic.Theory) (hPA : Arithmetic.DeductivelyExtends Arithmetic.Peano T)
    (hT : Arithmetic.SigmaOneSound T) :
    ∃ E : Arithmetic.Evaluator.GeneratedQuotient T ≃*
        Arithmetic.Evaluator.UnaryPartrec,
      ∀ e : ℕ, E (Arithmetic.Evaluator.generatedQuotientMk T e) =
        Arithmetic.Evaluator.UnaryPartrec.ofIndex e := by
  sorry

end FailureOfComposition.Palomar
