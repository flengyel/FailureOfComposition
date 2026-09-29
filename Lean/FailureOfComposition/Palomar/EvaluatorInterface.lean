/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel

The arithmetic-code datatype and formula compiler in this file are adapted to
FormalizedFormalLogic/Foundation's `Nat.ArithPart₁.Code` and
`Foundation.FirstOrder.Arithmetic.R0.Representation` at revision
e72cfe981aa65166f37fa4e2584f4806bc48d72f.  The Foundation sources are
Apache-2.0 licensed.
-/
import FailureOfComposition.Palomar.ArithmeticInterface
import Mathlib.Data.Fin.VecNotation
import Mathlib.Computability.PartrecCode

/-!
# Independent evaluator statement interface

This permitted-import development source gives an explicit finite-arity
partial-recursive code language and compiles each code to the independent
arithmetic syntax.  Later declarations construct the repository's concrete
evaluator code without importing Foundation or maintained project proofs.
-/

set_option autoImplicit false

namespace FailureOfComposition.Palomar.Arithmetic.Evaluator

/-- The finite-arity partial-recursive code language used by the maintained
evaluator construction. -/
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

/-- Formula with free variables `output,input₀,...,inputₖ₋₁` defining a
successful computation of a code. -/
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

/-- The closed-bound-variable graph formula of a code.  Bound variable zero is
the output, followed by the code's inputs. -/
def code {k : ℕ} (c : Code k) : Formula Empty (k + 1) :=
  (codeAux c).rewrite Fin.elim0 (fun i ↦ .bvar i)

end Compiler

namespace Construction

/-! The following named combinators retain sharing in the explicit evaluator
code.  Their bodies match the maintained arithmetic-code construction. -/

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

/-- The evaluator certificate has arguments `stage,index,input,output`. -/
def certificateFormula : Formula Empty 4 :=
  (Compiler.code Construction.codeHistoryEvaluator).subst
    ![.add (.bvar fin3) .one, .bvar fin0, .bvar fin1, .bvar fin2]

abbrev Graph := Formula Empty 2

/-- The graph of a fixed external standard program index, existentially
quantifying the internal computation stage. -/
def eventualGraph (q : ℕ) : Graph :=
  .exs (certificateFormula.subst
    ![.bvar fin0, Term.numeral q, .bvar fin1, .bvar fin2])

/-! ## Program indices and the manuscript's two equality formulas -/

/-- Definedness of a graph at an arithmetic term. -/
def definedAt {n : ℕ} (F : Graph) (x : Term Empty n) : Formula Empty n :=
  .exs (F.subst
    (Fin.cases x.lift
      (Fin.cases (.bvar ⟨0, Nat.zero_lt_succ n⟩) Fin.elim0)))

/-- A value common to two graphs at an arithmetic term. -/
def commonValueAt {n : ℕ} (F G : Graph) (x : Term Empty n) :
    Formula Empty n :=
  .exs (.and
    (F.subst (Fin.cases x.lift
      (Fin.cases (.bvar ⟨0, Nat.zero_lt_succ n⟩) Fin.elim0)))
    (G.subst (Fin.cases x.lift
      (Fin.cases (.bvar ⟨0, Nat.zero_lt_succ n⟩) Fin.elim0))))

/-- Negation-normal-form biconditional. -/
def biimp {xi : Type} {n : ℕ} (p q : Formula xi n) : Formula xi n :=
  .and (.imply p q) (.imply q p)

/-- The manuscript's equality of partial computations at an arithmetic term:
agreement on definedness together with a common value when defined. -/
def kleeneEqTerm {n : ℕ} (F G : Graph) (x : Term Empty n) :
    Formula Empty n :=
  .and (biimp (definedAt F x) (definedAt G x))
    (.imply (definedAt F x) (commonValueAt F G x))

/-- Equality of partial computations at one external standard input. -/
def kleeneEqAt (F G : Graph) (n : ℕ) : Sentence :=
  kleeneEqTerm F G (Term.numeral n)

/-- One internally universally quantified equality of partial computations. -/
def uniformKleeneSentence (F G : Graph) : Sentence :=
  .all (kleeneEqTerm F G (.bvar fin0))

/-- Mathlib's fixed index for its identity program. -/
def identityIndex : ℕ := 48

/-- Mathlib's fixed index for the selected nowhere-defined program. -/
def emptyIndex : ℕ := 11

/-- The closed form of Mathlib's encoded program-composition constructor. -/
def compIndex (f g : ℕ) : ℕ :=
  2 * (2 * Nat.pair f g + 1) + 4

/-- Pointwise provability quantifies externally over standard natural inputs. -/
def PointwiseIndex (T : Theory) (e d : ℕ) : Prop :=
  ∀ n : ℕ, Provable T (kleeneEqAt (eventualGraph e) (eventualGraph d) n)

/-- Uniform provability is one universally quantified arithmetic sentence. -/
def UniformIndex (T : Theory) (e d : ℕ) : Prop :=
  Provable T (uniformKleeneSentence (eventualGraph e) (eventualGraph d))

/-- Quotient of program indices by the independent pointwise-provability
relation.  Its equivalence properties are proved on the Solution side. -/
abbrev IndexQuotient (T : Theory) :=
  Quot (PointwiseIndex T)

/-- The quotient class represented by a concrete program index. -/
def indexQuotientMk (T : Theory) (e : ℕ) : IndexQuotient T :=
  Quot.mk _ e


/-- The actual partial function denoted by a Mathlib program index. -/
def actualEval (e x : ℕ) : Part ℕ :=
  Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) x

/-- Right composition replaces the outer index and fixes the inner index. -/
def RightCompatible (T : Theory) : Prop :=
  ∀ f h g : ℕ, PointwiseIndex T f h →
    PointwiseIndex T (compIndex f g) (compIndex h g)

/-- Pointwise equality is preserved when both composition arguments change. -/
def CompositionCongruence (T : Theory) : Prop :=
  ∀ f f' g g' : ℕ, PointwiseIndex T f f' → PointwiseIndex T g g' →
    PointwiseIndex T (compIndex f g) (compIndex f' g')

/-- Pointwise provability agrees with equality of actual partial functions. -/
def AgreesWithExtensional (T : Theory) : Prop :=
  ∀ e d : ℕ, PointwiseIndex T e d ↔ actualEval e = actualEval d

/-- A relation is an equivalence relation compatible with the concrete
composition operation in both arguments. -/
def IsCompositionCongruence (R : ℕ → ℕ → Prop) : Prop :=
  Equivalence R ∧
    ∀ a a' b b' : ℕ, R a a' → R b b' →
      R (compIndex a b) (compIndex a' b')

/-- The least composition-compatible equivalence relation containing external
pointwise provability, expressed as the intersection of all such relations. -/
def GeneratedRel (T : Theory) (e d : ℕ) : Prop :=
  ∀ R : ℕ → ℕ → Prop, IsCompositionCongruence R →
    (∀ x y : ℕ, PointwiseIndex T x y → R x y) → R e d


end FailureOfComposition.Palomar.Arithmetic.Evaluator
