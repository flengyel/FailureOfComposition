/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.Palomar.ArithmeticInterface
import FailureOfComposition.TheoryEnumerability
import Foundation.FirstOrder.Arithmetic.Schemata
import Foundation.FirstOrder.LK.Basic

/-!
# Correspondence for the explicit Palomar arithmetic interface

This Solution-side development may import Foundation.  It gives executable
translations between the independent Mathlib-only syntax in
`ArithmeticInterface` and the maintained Foundation arithmetic syntax.  The
translations are inverse on terms and formulas; subsequent sections transport
rewriting and actual LK derivations.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.Palomar.Arithmetic

private theorem finset_biUnion_two {α : Type} [DecidableEq α]
    (v : Fin 2 → Finset α) :
    Finset.univ.biUnion v = v 0 ∪ v 1 := by
  rw [Finset.univ_fin2]
  simp

private theorem allClosure_cast {n n' : ℕ} (h : n = n')
    (p : ArithmeticSemiformula ℕ n) :
    ∀¹* (Rew.cast h ▹ p) = ∀¹* p := by
  cases h
  simp

namespace Term

variable {ξ ξ' : Type} {n m : ℕ}

def toFoundation : Term ξ n → ArithmeticSemiterm ξ n
  | .bvar i => .bvar i
  | .fvar x => .fvar x
  | .zero => .func Language.ORing.Func.zero ![]
  | .one => .func Language.ORing.Func.one ![]
  | .add s t => .func Language.ORing.Func.add ![toFoundation s, toFoundation t]
  | .mul s t => .func Language.ORing.Func.mul ![toFoundation s, toFoundation t]

def ofFoundation : ArithmeticSemiterm ξ n → Term ξ n
  | .bvar i => .bvar i
  | .fvar x => .fvar x
  | .func Language.ORing.Func.zero _ => .zero
  | .func Language.ORing.Func.one _ => .one
  | .func Language.ORing.Func.add v => .add (ofFoundation (v 0)) (ofFoundation (v 1))
  | .func Language.ORing.Func.mul v => .mul (ofFoundation (v 0)) (ofFoundation (v 1))

@[simp] theorem ofFoundation_toFoundation (t : Term ξ n) :
    ofFoundation (toFoundation t) = t := by
  induction t <;> simp [toFoundation, ofFoundation, *]

@[simp] theorem toFoundation_ofFoundation (t : ArithmeticSemiterm ξ n) :
    toFoundation (ofFoundation t) = t := by
  induction t with
  | bvar i => rfl
  | fvar x => rfl
  | @func k f v ih =>
      cases f <;> simp [ofFoundation, toFoundation, Matrix.empty_eq, funext_iff, ih]

def equivalence : Term ξ n ≃ ArithmeticSemiterm ξ n where
  toFun := toFoundation
  invFun := ofFoundation
  left_inv := ofFoundation_toFoundation
  right_inv := toFoundation_ofFoundation

@[simp] theorem toFoundation_rewrite
    (b : Fin n → Term ξ' m) (f : ξ → Term ξ' m) (t : Term ξ n) :
    toFoundation (t.rewrite b f) =
      Rew.bind (toFoundation ∘ b) (toFoundation ∘ f) (toFoundation t) := by
  induction t <;>
    simp [Term.rewrite, toFoundation, Rew.func, Function.comp_def,
      Matrix.empty_eq, Matrix.fun_eq_vec_two, *]

@[simp] theorem ofFoundation_bind
    (b : Fin n → ArithmeticSemiterm ξ' m)
    (f : ξ → ArithmeticSemiterm ξ' m) (t : ArithmeticSemiterm ξ n) :
    ofFoundation (Rew.bind b f t) =
      (ofFoundation t).rewrite (ofFoundation ∘ b) (ofFoundation ∘ f) := by
  induction t with
  | bvar i => rfl
  | fvar x => rfl
  | @func k g v ih =>
      cases g <;>
        simp [Rew.func, ofFoundation, Term.rewrite, Function.comp_def,
          Matrix.empty_eq, ih]

@[simp] theorem toFoundation_lift (t : Term ξ n) :
    toFoundation t.lift = Rew.bShift (toFoundation t) := by
  induction t <;>
    simp [Term.lift, Term.rewrite, toFoundation, Rew.bShift, Rew.map,
      Rew.func, Function.comp_def, Matrix.empty_eq, Matrix.fun_eq_vec_two, *]

@[simp] theorem toFoundation_underBinder
    (b : Fin n → Term ξ' m) (i : Fin (n + 1)) :
    toFoundation (underBinder b i) =
      Fin.cases (Semiterm.bvar 0)
        (fun j ↦ Rew.bShift (toFoundation (b j))) i := by
  refine Fin.cases rfl (fun j ↦ ?_) i
  simp [underBinder]

@[simp] theorem toFoundation_numeral (k : ℕ) :
    toFoundation (numeral (ξ := ξ) (n := n) k) =
      Semiterm.Operator.numeral ℒₒᵣ k := by
  induction k using Nat.twoStepInduction with
  | zero =>
      have hz : (Language.Zero.zero (L := ℒₒᵣ)) = Language.ORing.Func.zero := rfl
      simp [numeral, toFoundation, Semiterm.Operator.numeral_zero,
        Semiterm.Operator.const, Semiterm.Operator.operator,
        Semiterm.Operator.Zero.term_eq, hz, Rew.func, Matrix.empty_eq]
  | one =>
      have ho : (Language.One.one (L := ℒₒᵣ)) = Language.ORing.Func.one := rfl
      simp [numeral, toFoundation, Semiterm.Operator.numeral_one,
        Semiterm.Operator.const, Semiterm.Operator.operator,
        Semiterm.Operator.One.term_eq, ho, Rew.func, Matrix.empty_eq]
  | more k _ ih =>
      have ho : (Language.One.one (L := ℒₒᵣ)) = Language.ORing.Func.one := rfl
      have ha : (Language.Add.add (L := ℒₒᵣ)) = Language.ORing.Func.add := rfl
      rw [numeral, toFoundation, ih, Semiterm.Operator.numeral_add_two]
      change _ = (Semiterm.Operator.Add.add.comp
        ![Semiterm.Operator.numeral ℒₒᵣ (k + 1), Semiterm.Operator.One.one]).operator ![]
      rw [Semiterm.Operator.operator_comp]
      simp only [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
        ha, Rew.func]
      congr
      funext i
      refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun z ↦ Fin.elim0 z) j) i
      · rfl
      · simp [toFoundation, Semiterm.Operator.One.term_eq, ho, Rew.func,
          Matrix.empty_eq, Function.comp_def]

theorem toFoundation_zero :
    toFoundation (.zero : Term ξ n) =
      Semiterm.numeral (L := ℒₒᵣ) (ξ := ξ) (n := n) 0 := by
  simpa only [Term.numeral] using
    (toFoundation_numeral (ξ := ξ) (n := n) 0)

theorem toFoundation_one :
    toFoundation (.one : Term ξ n) =
      Semiterm.numeral (L := ℒₒᵣ) (ξ := ξ) (n := n) 1 := by
  simpa only [Term.numeral] using
    (toFoundation_numeral (ξ := ξ) (n := n) 1)

theorem toFoundation_bvar (i : Fin n) :
    toFoundation (.bvar i : Term ξ n) =
      (#i : ArithmeticSemiterm ξ n) := rfl

theorem toFoundation_fvar (x : ξ) :
    toFoundation (.fvar x : Term ξ n) =
      (&x : ArithmeticSemiterm ξ n) := rfl

theorem toFoundation_add (s t : Term ξ n) :
    toFoundation (.add s t) =
      Semiterm.Operator.Add.add.operator ![toFoundation s, toFoundation t] := by
  simp [toFoundation, Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]
  rfl

theorem toFoundation_mul (s t : Term ξ n) :
    toFoundation (.mul s t) =
      Semiterm.Operator.Mul.mul.operator ![toFoundation s, toFoundation t] := by
  simp [toFoundation, Semiterm.Operator.operator,
    Semiterm.Operator.Mul.term_eq, Rew.func, Matrix.fun_eq_vec_two]
  rfl

@[simp] theorem toFoundation_freeVariables (t : Term ℕ n) :
    (toFoundation t).freeVariables = t.freeVariables := by
  induction t <;>
    simp [Term.freeVariables, toFoundation, Semiterm.freeVariables_func,
      finset_biUnion_two, Matrix.fun_eq_vec_two, *]

end Term

namespace Formula

variable {ξ ξ' : Type} {n m : ℕ}

def toFoundation {n : ℕ} (p : Formula ξ n) : ArithmeticSemiformula ξ n :=
  match p with
  | .verum => .verum
  | .falsum => .falsum
  | .equal s t => .rel Language.ORing.Rel.eq ![s.toFoundation, t.toFoundation]
  | .nequal s t => .nrel Language.ORing.Rel.eq ![s.toFoundation, t.toFoundation]
  | .less s t => .rel Language.ORing.Rel.lt ![s.toFoundation, t.toFoundation]
  | .nless s t => .nrel Language.ORing.Rel.lt ![s.toFoundation, t.toFoundation]
  | .and p q => .and (toFoundation p) (toFoundation q)
  | .or p q => .or (toFoundation p) (toFoundation q)
  | .all p => .all (toFoundation p)
  | .exs p => .exs (toFoundation p)

def ofFoundation {n : ℕ} (p : ArithmeticSemiformula ξ n) : Formula ξ n :=
  match p with
  | .verum => .verum
  | .falsum => .falsum
  | .rel Language.ORing.Rel.eq v => .equal (Term.ofFoundation (v 0)) (Term.ofFoundation (v 1))
  | .nrel Language.ORing.Rel.eq v => .nequal (Term.ofFoundation (v 0)) (Term.ofFoundation (v 1))
  | .rel Language.ORing.Rel.lt v => .less (Term.ofFoundation (v 0)) (Term.ofFoundation (v 1))
  | .nrel Language.ORing.Rel.lt v => .nless (Term.ofFoundation (v 0)) (Term.ofFoundation (v 1))
  | .and p q => .and (ofFoundation p) (ofFoundation q)
  | .or p q => .or (ofFoundation p) (ofFoundation q)
  | .all p => .all (ofFoundation p)
  | .exs p => .exs (ofFoundation p)

theorem toFoundation_and (p q : Formula ξ n) :
    toFoundation (.and p q) = toFoundation p ⋏ toFoundation q := rfl

theorem toFoundation_or (p q : Formula ξ n) :
    toFoundation (.or p q) = toFoundation p ⋎ toFoundation q := rfl

theorem toFoundation_all (p : Formula ξ (n + 1)) :
    toFoundation (.all p) = ∀¹ toFoundation p := rfl

theorem toFoundation_exs (p : Formula ξ (n + 1)) :
    toFoundation (.exs p) = ∃¹ toFoundation p := rfl

theorem toFoundation_equal (s t : Term ξ n) :
    toFoundation (.equal s t) =
      Semiformula.Operator.Eq.eq.operator
        ![Term.toFoundation s, Term.toFoundation t] := by
  symm
  exact Semiformula.Operator.eq_def _ _

theorem toFoundation_less (s t : Term ξ n) :
    toFoundation (.less s t) =
      Semiformula.Operator.LT.lt.operator
        ![Term.toFoundation s, Term.toFoundation t] := by
  symm
  exact Semiformula.Operator.lt_def _ _

@[simp] theorem ofFoundation_toFoundation (p : Formula ξ n) :
    ofFoundation (toFoundation p) = p := by
  induction p <;> simp [toFoundation, ofFoundation, *]

@[simp] theorem toFoundation_ofFoundation (p : ArithmeticSemiformula ξ n) :
    toFoundation (ofFoundation p) = p := by
  induction p with
  | verum => rfl
  | falsum => rfl
  | @rel k arity r v =>
      cases r <;>
        simp only [ofFoundation, toFoundation, Term.toFoundation_ofFoundation] <;>
        congr <;>
        funext i <;>
        exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun z ↦ Fin.elim0 z) j) i
  | @nrel k arity r v =>
      cases r <;>
        simp only [ofFoundation, toFoundation, Term.toFoundation_ofFoundation] <;>
        congr <;>
        funext i <;>
        exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun z ↦ Fin.elim0 z) j) i
  | and p q ihp ihq => simp [ofFoundation, toFoundation, ihp, ihq]
  | or p q ihp ihq => simp [ofFoundation, toFoundation, ihp, ihq]
  | all p ih => simp [ofFoundation, toFoundation, ih]
  | exs p ih => simp [ofFoundation, toFoundation, ih]

def equivalence : Formula ξ n ≃ ArithmeticSemiformula ξ n where
  toFun := toFoundation
  invFun := ofFoundation
  left_inv := ofFoundation_toFoundation
  right_inv := toFoundation_ofFoundation

theorem toFoundation_injective :
    Function.Injective (@toFoundation ξ n) := equivalence.injective

@[simp] theorem toFoundation_rewrite
    (b : Fin n → Term ξ' m) (f : ξ → Term ξ' m) (p : Formula ξ n) :
    toFoundation (p.rewrite b f) =
      Semiformula.rewAux
        (Rew.bind (Term.toFoundation ∘ b) (Term.toFoundation ∘ f))
        (toFoundation p) := by
  induction p generalizing m with
  | verum =>
      change Semiformula.verum = Semiformula.verum
      rfl
  | falsum =>
      change Semiformula.falsum = Semiformula.falsum
      rfl
  | equal s t =>
      simp [Formula.rewrite, toFoundation, Semiformula.rewAux,
        Term.toFoundation_rewrite, Function.comp_def, Matrix.fun_eq_vec_two]
  | nequal s t =>
      simp [Formula.rewrite, toFoundation, Semiformula.rewAux,
        Term.toFoundation_rewrite, Function.comp_def, Matrix.fun_eq_vec_two]
  | less s t =>
      simp [Formula.rewrite, toFoundation, Semiformula.rewAux,
        Term.toFoundation_rewrite, Function.comp_def, Matrix.fun_eq_vec_two]
  | nless s t =>
      simp [Formula.rewrite, toFoundation, Semiformula.rewAux,
        Term.toFoundation_rewrite, Function.comp_def, Matrix.fun_eq_vec_two]
  | and p q ihp ihq =>
      change Semiformula.and _ _ = Semiformula.and _ _
      rw [ihp, ihq]
  | or p q ihp ihq =>
      change Semiformula.or _ _ = Semiformula.or _ _
      rw [ihp, ihq]
  | all p ih =>
      change Semiformula.all _ = Semiformula.all _
      congr 1
      rw [ih]
      apply congrArg (fun ω ↦ Semiformula.rewAux ω (toFoundation p))
      rw [Rew.q_bind]
      apply Rew.ext <;> intro x
      · cases x using Fin.cases <;> simp [Function.comp_def]
      · simp [Function.comp_def]
  | exs p ih =>
      change Semiformula.exs _ = Semiformula.exs _
      congr 1
      rw [ih]
      apply congrArg (fun ω ↦ Semiformula.rewAux ω (toFoundation p))
      rw [Rew.q_bind]
      apply Rew.ext <;> intro x
      · cases x using Fin.cases <;> simp [Function.comp_def]
      · simp [Function.comp_def]

@[simp] theorem toFoundation_subst
    (p : Formula ξ n) (v : Fin n → Term ξ m) :
    toFoundation (p.subst v) =
      Rewriting.subst (toFoundation p) (Term.toFoundation ∘ v) := by
  change toFoundation (p.subst v) =
    Semiformula.rewAux (Rew.subst (Term.toFoundation ∘ v)) (toFoundation p)
  rw [Formula.subst, toFoundation_rewrite]
  apply congrArg (fun ω ↦ Semiformula.rewAux ω (toFoundation p))
  apply Rew.ext <;> intro x <;> rfl

@[simp] theorem toFoundation_mapFree (f : ξ → ξ') (p : Formula ξ n) :
    toFoundation (p.mapFree f) =
      Rew.rewriteMap (L := ℒₒᵣ) f ▹ toFoundation p := by
  change toFoundation (p.mapFree f) =
    Semiformula.rewAux (Rew.rewriteMap (L := ℒₒᵣ) f) (toFoundation p)
  rw [Formula.mapFree, toFoundation_rewrite]
  apply congrArg (fun ω ↦ Semiformula.rewAux ω (toFoundation p))
  apply Rew.ext <;> intro x <;> rfl

@[simp] theorem toFoundation_embed (p : Formula Empty n) :
    toFoundation p.embed = (Rewriting.emb (toFoundation p) : ArithmeticSemiformula ℕ n) := by
  change toFoundation p.embed = Semiformula.rewAux Rew.emb (toFoundation p)
  rw [Formula.embed, Formula.mapFree, toFoundation_rewrite]
  apply congrArg (fun ω ↦ Semiformula.rewAux ω (toFoundation p))
  apply Rew.ext
  · intro x
    rfl
  · intro x
    exact Empty.elim x

@[simp] theorem toFoundation_shiftFree (p : Formula ℕ n) :
    toFoundation p.shiftFree = Rewriting.shift (toFoundation p) := by
  change toFoundation p.shiftFree = Semiformula.rewAux Rew.shift (toFoundation p)
  rw [Formula.shiftFree, Formula.mapFree, toFoundation_rewrite]
  apply congrArg (fun ω ↦ Semiformula.rewAux ω (toFoundation p))
  apply Rew.ext <;> intro x <;> rfl

@[simp] theorem toFoundation_free (p : Formula ℕ 1) :
    toFoundation p.free = Rewriting.free (toFoundation p) := by
  change toFoundation p.free = Semiformula.rewAux Rew.free (toFoundation p)
  rw [Formula.free, toFoundation_rewrite]
  apply congrArg (fun ω ↦ Semiformula.rewAux ω (toFoundation p))
  apply Rew.ext
  · intro x
    refine Fin.cases rfl (fun z ↦ Fin.elim0 z) x
  · intro x
    rfl

@[simp] theorem toFoundation_substOne (p : Formula ℕ 1) (t : SyntacticTerm 0) :
    toFoundation (p.substOne t) =
      Rewriting.subst (toFoundation p) ![Term.toFoundation t] := by
  change toFoundation (p.substOne t) =
    Semiformula.rewAux (Rew.subst ![Term.toFoundation t]) (toFoundation p)
  rw [Formula.substOne, toFoundation_rewrite]
  apply congrArg (fun ω ↦ Semiformula.rewAux ω (toFoundation p))
  apply Rew.ext
  · intro x
    refine Fin.cases rfl (fun z ↦ Fin.elim0 z) x
  · intro x
    rfl

@[simp] theorem toFoundation_neg (p : Formula ξ n) :
    toFoundation p.neg = FFL.FirstOrder.Semiformula.neg (toFoundation p) := by
  induction p <;> simp [neg, toFoundation, FFL.FirstOrder.Semiformula.neg, *]

@[simp] theorem toFoundation_imply (p q : Formula ξ n) :
    toFoundation (Formula.imply p q) = toFoundation p 🡒 toFoundation q := by
  unfold Formula.imply
  rw [toFoundation_or, toFoundation_neg]
  rfl

theorem ofFoundation_neg (p : ArithmeticSemiformula ξ n) :
    ofFoundation (FFL.FirstOrder.Semiformula.neg p) = (ofFoundation p).neg := by
  apply toFoundation_injective
  rw [toFoundation_ofFoundation, toFoundation_neg, toFoundation_ofFoundation]

theorem ofFoundation_and (p q : ArithmeticSemiformula ξ n) :
    ofFoundation (p ⋏ q) = .and (ofFoundation p) (ofFoundation q) := by
  apply toFoundation_injective
  rw [toFoundation_ofFoundation, toFoundation_and,
    toFoundation_ofFoundation, toFoundation_ofFoundation]

theorem ofFoundation_or (p q : ArithmeticSemiformula ξ n) :
    ofFoundation (p ⋎ q) = .or (ofFoundation p) (ofFoundation q) := by
  apply toFoundation_injective
  rw [toFoundation_ofFoundation, toFoundation_or,
    toFoundation_ofFoundation, toFoundation_ofFoundation]

theorem ofFoundation_all (p : ArithmeticSemiformula ξ (n + 1)) :
    ofFoundation (∀¹ p) = .all (ofFoundation p) := by
  apply toFoundation_injective
  rw [toFoundation_ofFoundation, toFoundation_all, toFoundation_ofFoundation]

theorem ofFoundation_exs (p : ArithmeticSemiformula ξ (n + 1)) :
    ofFoundation (∃¹ p) = .exs (ofFoundation p) := by
  apply toFoundation_injective
  rw [toFoundation_ofFoundation, toFoundation_exs, toFoundation_ofFoundation]

theorem ofFoundation_embed (p : ArithmeticSemiformula Empty n) :
    ofFoundation (Rewriting.emb p : ArithmeticSemiformula ℕ n) =
      (ofFoundation p).embed := by
  apply toFoundation_injective
  rw [toFoundation_ofFoundation, toFoundation_embed, toFoundation_ofFoundation]

theorem ofFoundation_shift (p : ArithmeticSemiformula ℕ n) :
    ofFoundation (Rewriting.shift p) = (ofFoundation p).shiftFree := by
  apply toFoundation_injective
  rw [toFoundation_ofFoundation, toFoundation_shiftFree, toFoundation_ofFoundation]

theorem ofFoundation_free (p : ArithmeticSemiformula ℕ 1) :
    ofFoundation (Rewriting.free p) = (ofFoundation p).free := by
  apply toFoundation_injective
  rw [toFoundation_ofFoundation, toFoundation_free, toFoundation_ofFoundation]

theorem ofFoundation_substOne (p : ArithmeticSemiformula ℕ 1)
    (t : ArithmeticSemiterm ℕ 0) :
    ofFoundation (Rewriting.subst p ![t]) =
      (ofFoundation p).substOne (Term.ofFoundation t) := by
  apply toFoundation_injective
  rw [toFoundation_ofFoundation, toFoundation_substOne,
    toFoundation_ofFoundation, Term.toFoundation_ofFoundation]

@[simp] theorem toFoundation_freeVariables (p : Formula ℕ n) :
    (toFoundation p).freeVariables = p.freeVariables := by
  induction p <;>
    simp [Formula.freeVariables, toFoundation,
      Semiformula.freeVariables, finset_biUnion_two, *]

@[simp] theorem toFoundation_fvSup (p : Formula ℕ n) :
    (toFoundation p).fvSup = p.fvSup := by
  simp [Semiformula.fvSup, Formula.fvSup]

@[simp] theorem toFoundation_allClosure (p : Formula ξ n) :
    toFoundation (allClosure p) = ∀¹* toFoundation p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change toFoundation (allClosure (.all p)) = ∀¹* toFoundation p
      rw [ih]
      rfl

theorem emb_toFoundation_fixFree (p : Proposition) :
    (Rewriting.emb (toFoundation (fixFree p.fvSup p)) :
      ArithmeticSemiformula ℕ p.fvSup) =
      Rew.cast (Nat.zero_add p.fvSup) ▹
        (Rew.fixitr 0 p.fvSup ▹ toFoundation p) := by
  change Rew.emb ▹ toFoundation (fixFree p.fvSup p) = _
  rw [fixFree, toFoundation_rewrite]
  change Rew.emb ▹ (Rew.bind _ _ ▹ toFoundation p) = _
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app]
  apply Semiformula.rew_eq_of_funEqOn₀
  intro x hx
  have hxlt : x < p.fvSup := by
    rw [← toFoundation_fvSup p]
    exact Semiformula.lt_fvSup_of_fvar? hx
  simp [Rew.comp_app, Function.comp_def, Rew.fixitr_fvar, hxlt,
    Term.toFoundation]

@[simp] theorem toFoundation_univClosure (p : Proposition) :
    toFoundation (univClosure p) = (toFoundation p).univCl := by
  refine (Semiformula.coe_inj _ _).mp ?_
  rw [Semiformula.coe_univCl_eq_univCl']
  simp only [univClosure, toFoundation_allClosure,
    Rewriting.emb_allClosure]
  rw [emb_toFoundation_fixFree]
  unfold Semiformula.univCl'
  rw [allClosure_cast, ← toFoundation_fvSup p]

@[simp] theorem toFoundation_succInd (p : Semiproposition 1) :
    toFoundation (Formula.succInd p) =
      FFL.FirstOrder.Arithmetic.succInd (toFoundation p) := by
  unfold Formula.succInd
  rw [toFoundation_imply, toFoundation_substOne, toFoundation_imply,
    toFoundation_all, toFoundation_imply, toFoundation_subst,
    toFoundation_all]
  unfold FFL.FirstOrder.Arithmetic.succInd
  have hid : (toFoundation p)/[(#0 : ArithmeticSemiterm ℕ 1)] =
      toFoundation p := Rewriting.subst1_bvar0_eq _
  rw [hid]
  have hzero : Term.toFoundation (.zero : SyntacticTerm 0) =
      Semiterm.numeral (L := ℒₒᵣ) (ξ := ℕ) (n := 0) 0 := by
    simpa only [Term.numeral] using
      (Term.toFoundation_numeral (ξ := ℕ) (n := 0) 0)
  rw [hzero]
  have hone : Term.toFoundation (.one : SyntacticTerm 1) =
      Semiterm.numeral (L := ℒₒᵣ) (ξ := ℕ) (n := 1) 1 := by
    simpa only [Term.numeral] using
      (Term.toFoundation_numeral (ξ := ℕ) (n := 1) 1)
  have hadd :
      Term.toFoundation
          (.add (.bvar 0) .one : SyntacticTerm 1) =
        Semiterm.Operator.Add.add.operator
          ![(#0 : ArithmeticSemiterm ℕ 1),
            Semiterm.numeral (L := ℒₒᵣ) (ξ := ℕ) (n := 1) 1] := by
    simp only [Term.toFoundation, Fin.isValue, Matrix.fun_eq_vec_two,
      Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.Fin1.eq_one, Matrix.cons_val_fin_one,
      Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
      Rew.func, Function.comp_apply, Rew.emb_bvar, Rew.subst_bvar,
      Semiterm.func.injEq, heq_eq_eq, Matrix.vecCons_inj, and_true,
      true_and]
    exact ⟨rfl, hone⟩
  have hv :
      (Term.toFoundation ∘
          fun _ : Fin 1 ↦ (.add (.bvar 0) .one : SyntacticTerm 1)) =
        ![Semiterm.Operator.Add.add.operator
          ![(#0 : ArithmeticSemiterm ℕ 1),
            Semiterm.numeral (L := ℒₒᵣ) (ξ := ℕ) (n := 1) 1]] := by
    funext i
    refine Fin.cases hadd (fun z ↦ Fin.elim0 z) i
  rw [hv]

@[simp] theorem ofFoundation_univCl (p : ArithmeticProposition) :
    ofFoundation p.univCl = univClosure (ofFoundation p) := by
  apply toFoundation_injective
  rw [toFoundation_ofFoundation, toFoundation_univClosure,
    toFoundation_ofFoundation]

@[simp] theorem ofFoundation_succInd (p : ArithmeticSemiproposition 1) :
    ofFoundation (FFL.FirstOrder.Arithmetic.succInd p) =
      Formula.succInd (ofFoundation p) := by
  apply toFoundation_injective
  rw [toFoundation_ofFoundation, toFoundation_succInd,
    toFoundation_ofFoundation]

end Formula

namespace PeanoCorrespondence

@[simp] theorem equality_refl :
    Formula.toFoundation Equality.refl =
      FFL.FirstOrder.Theory.Eq.refl ℒₒᵣ := by
  rfl

@[simp] theorem equality_symm :
    Formula.toFoundation Equality.symm =
      FFL.FirstOrder.Theory.Eq.symm ℒₒᵣ := by
  rfl

@[simp] theorem equality_trans :
    Formula.toFoundation Equality.trans =
      FFL.FirstOrder.Theory.Eq.trans ℒₒᵣ := by
  rfl

@[simp] theorem equality_zeroExt :
    Formula.toFoundation Equality.zeroExt =
      FFL.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.zero := by
  simp [Equality.zeroExt, FFL.FirstOrder.Theory.Eq.funcExt,
    Formula.toFoundation, Formula.imply, Matrix.conj,
    Semiformula.imp_eq, FFL.FirstOrder.Semiformula.neg,
    Semiformula.Operator.operator, Semiformula.Operator.Eq.sentence_eq,
    Matrix.empty_eq, Matrix.fun_eq_vec_two]
  rfl

@[simp] theorem equality_oneExt :
    Formula.toFoundation Equality.oneExt =
      FFL.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.one := by
  simp [Equality.oneExt, FFL.FirstOrder.Theory.Eq.funcExt,
    Formula.toFoundation, Formula.imply, Matrix.conj,
    Semiformula.imp_eq, FFL.FirstOrder.Semiformula.neg,
    Semiformula.Operator.operator, Semiformula.Operator.Eq.sentence_eq,
    Matrix.empty_eq, Matrix.fun_eq_vec_two]
  rfl

@[simp] theorem equality_addExt :
    Formula.toFoundation Equality.addExt =
      FFL.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.add := by
  simp [Equality.addExt, Equality.binaryCongruenceHyp,
    FFL.FirstOrder.Theory.Eq.funcExt, Formula.toFoundation,
    Formula.imply, Formula.allClosure, Matrix.conj,
    Semiformula.imp_eq, FFL.FirstOrder.Semiformula.neg,
    Semiformula.Operator.operator, Semiformula.Operator.Eq.sentence_eq,
    Matrix.fun_eq_vec_two, Matrix.vecTail]
  rfl

@[simp] theorem equality_mulExt :
    Formula.toFoundation Equality.mulExt =
      FFL.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.mul := by
  simp [Equality.mulExt, Equality.binaryCongruenceHyp,
    FFL.FirstOrder.Theory.Eq.funcExt, Formula.toFoundation,
    Formula.imply, Formula.allClosure, Matrix.conj,
    Semiformula.imp_eq, FFL.FirstOrder.Semiformula.neg,
    Semiformula.Operator.operator, Semiformula.Operator.Eq.sentence_eq,
    Matrix.fun_eq_vec_two, Matrix.vecTail]
  rfl

@[simp] theorem equality_equalExt :
    Formula.toFoundation Equality.equalExt =
      FFL.FirstOrder.Theory.Eq.relExt Language.ORing.Rel.eq := by
  simp [Equality.equalExt, Equality.binaryCongruenceHyp,
    FFL.FirstOrder.Theory.Eq.relExt, Formula.toFoundation,
    Formula.imply, Formula.allClosure, Matrix.conj,
    Semiformula.imp_eq, FFL.FirstOrder.Semiformula.neg,
    Semiformula.Operator.operator, Semiformula.Operator.Eq.sentence_eq,
    Matrix.fun_eq_vec_two, Matrix.vecTail]
  rfl

@[simp] theorem equality_lessExt :
    Formula.toFoundation Equality.lessExt =
      FFL.FirstOrder.Theory.Eq.relExt Language.ORing.Rel.lt := by
  simp [Equality.lessExt, Equality.binaryCongruenceHyp,
    FFL.FirstOrder.Theory.Eq.relExt, Formula.toFoundation,
    Formula.imply, Formula.allClosure, Matrix.conj,
    Semiformula.imp_eq, FFL.FirstOrder.Semiformula.neg,
    Semiformula.Operator.operator, Semiformula.Operator.Eq.sentence_eq,
    Matrix.fun_eq_vec_two, Matrix.vecTail]
  rfl

@[simp] theorem peanoMinus_addZero :
    Formula.toFoundation PeanoMinus.Axiom.addZero =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.addZero := by
  simp only [PeanoMinus.Axiom.addZero,
    FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.addZero,
    Formula.toFoundation_all, Formula.toFoundation_equal,
    Term.toFoundation_add, Term.toFoundation_bvar,
    Term.toFoundation_zero]

@[simp] theorem peanoMinus_addAssoc :
    Formula.toFoundation PeanoMinus.Axiom.addAssoc =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.addAssoc := by
  rfl

@[simp] theorem peanoMinus_addComm :
    Formula.toFoundation PeanoMinus.Axiom.addComm =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.addComm := by
  rfl

@[simp] theorem peanoMinus_addEqOfLt :
    Formula.toFoundation PeanoMinus.Axiom.addEqOfLt =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.addEqOfLt := by
  rfl

@[simp] theorem peanoMinus_zeroLe :
    Formula.toFoundation PeanoMinus.Axiom.zeroLe =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.zeroLe := by
  simp [PeanoMinus.Axiom.zeroLe,
    FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.zeroLe,
    Formula.toFoundation, Term.toFoundation,
    Semiterm.Operator.numeral_zero,
    Semiterm.Operator.operator, Semiterm.Operator.Zero.term_eq,
    Semiformula.Operator.operator, Semiformula.Operator.LE.sentence_eq,
    Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, Rew.func,
    Matrix.empty_eq, Matrix.fun_eq_vec_two]
  rfl

@[simp] theorem peanoMinus_zeroLtOne :
    Formula.toFoundation PeanoMinus.Axiom.zeroLtOne =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.zeroLtOne := by
  simp only [PeanoMinus.Axiom.zeroLtOne, Formula.toFoundation,
    Term.toFoundation, Matrix.fun_eq_vec_two, Nat.succ_eq_add_one,
    Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.Fin1.eq_one, Matrix.cons_val_fin_one,
    FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.zeroLtOne,
    Semiformula.Operator.operator, Semiformula.Operator.LT.sentence_eq,
    Semiformula.rew_rel_eq_comp, Rew.emb_eq_id, Function.comp_apply,
    Rew.id_app, Semiterm.Operator.operator, Rew.subst_zero,
    Semiterm.Operator.numeral_zero, Semiterm.Operator.Zero.term_eq,
    Rew.func, Matrix.empty_eq, Semiterm.Operator.numeral_one,
    Semiterm.Operator.One.term_eq, Rew.subst_bvar,
    Semiformula.rel.injEq, heq_eq_eq, Matrix.vecCons_inj,
    Semiterm.func.injEq, and_true, true_and]
  exact ⟨rfl, rfl, rfl⟩

@[simp] theorem peanoMinus_oneLeOfZeroLt :
    Formula.toFoundation PeanoMinus.Axiom.oneLeOfZeroLt =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.oneLeOfZeroLt := by
  simp [PeanoMinus.Axiom.oneLeOfZeroLt,
    FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.oneLeOfZeroLt,
    Formula.toFoundation, Formula.imply, Term.toFoundation,
    Semiterm.Operator.numeral_zero, Semiterm.Operator.numeral_one,
    Semiformula.imp_eq, FFL.FirstOrder.Semiformula.neg,
    Semiterm.Operator.operator,
    Semiterm.Operator.Zero.term_eq, Semiterm.Operator.One.term_eq,
    Semiformula.Operator.operator, Semiformula.Operator.LE.sentence_eq,
    Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, Rew.func,
    Matrix.empty_eq, Matrix.fun_eq_vec_two]
  rfl

@[simp] theorem peanoMinus_addLtAdd :
    Formula.toFoundation PeanoMinus.Axiom.addLtAdd =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.addLtAdd := by
  rfl

@[simp] theorem peanoMinus_mulZero :
    Formula.toFoundation PeanoMinus.Axiom.mulZero =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.mulZero := by
  simp [PeanoMinus.Axiom.mulZero,
    FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.mulZero,
    Formula.toFoundation, Term.toFoundation,
    Semiterm.Operator.numeral_zero,
    Semiterm.Operator.operator, Semiterm.Operator.Zero.term_eq,
    Semiterm.Operator.Mul.term_eq, Semiformula.Operator.operator,
    Semiformula.Operator.Eq.sentence_eq, Rew.func,
    Matrix.empty_eq, Matrix.fun_eq_vec_two]
  rfl

@[simp] theorem peanoMinus_mulOne :
    Formula.toFoundation PeanoMinus.Axiom.mulOne =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.mulOne := by
  simp [PeanoMinus.Axiom.mulOne,
    FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.mulOne,
    Formula.toFoundation, Term.toFoundation,
    Semiterm.Operator.numeral_one,
    Semiterm.Operator.operator, Semiterm.Operator.One.term_eq,
    Semiterm.Operator.Mul.term_eq, Semiformula.Operator.operator,
    Semiformula.Operator.Eq.sentence_eq, Rew.func,
    Matrix.empty_eq, Matrix.fun_eq_vec_two]
  rfl

@[simp] theorem peanoMinus_mulAssoc :
    Formula.toFoundation PeanoMinus.Axiom.mulAssoc =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.mulAssoc := by
  rfl

@[simp] theorem peanoMinus_mulComm :
    Formula.toFoundation PeanoMinus.Axiom.mulComm =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.mulComm := by
  rfl

@[simp] theorem peanoMinus_mulLtMul :
    Formula.toFoundation PeanoMinus.Axiom.mulLtMul =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.mulLtMul := by
  simp [PeanoMinus.Axiom.mulLtMul,
    FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.mulLtMul,
    Formula.toFoundation, Formula.imply, Formula.allClosure,
    Term.toFoundation, Semiterm.Operator.numeral_zero,
    Semiformula.imp_eq, FFL.FirstOrder.Semiformula.neg,
    Semiterm.Operator.operator,
    Semiterm.Operator.Zero.term_eq, Semiterm.Operator.Mul.term_eq,
    Semiformula.Operator.operator, Semiformula.Operator.LT.sentence_eq,
    Rew.func, Matrix.empty_eq, Matrix.fun_eq_vec_two]
  rfl

@[simp] theorem peanoMinus_distr :
    Formula.toFoundation PeanoMinus.Axiom.distr =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.distr := by
  rfl

@[simp] theorem peanoMinus_ltIrrefl :
    Formula.toFoundation PeanoMinus.Axiom.ltIrrefl =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.ltIrrefl := by
  rfl

@[simp] theorem peanoMinus_ltTrans :
    Formula.toFoundation PeanoMinus.Axiom.ltTrans =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.ltTrans := by
  rfl

@[simp] theorem peanoMinus_ltTri :
    Formula.toFoundation PeanoMinus.Axiom.ltTri =
      FFL.FirstOrder.Arithmetic.PeanoMinus.Axiom.ltTri := by
  rfl

theorem equalityAxiomToFoundation {p : Sentence} :
    EqualityAxiom p →
      FFL.FirstOrder.Theory.eqAxiom ℒₒᵣ (Formula.toFoundation p)
  | .refl => by
      simpa using
        (FFL.FirstOrder.Theory.eqAxiom.refl (L := ℒₒᵣ))
  | .symm => by
      simpa using
        (FFL.FirstOrder.Theory.eqAxiom.symm (L := ℒₒᵣ))
  | .trans => by
      simpa using
        (FFL.FirstOrder.Theory.eqAxiom.trans (L := ℒₒᵣ))
  | .zeroExt => by
      simpa using
        (FFL.FirstOrder.Theory.eqAxiom.funcExt (L := ℒₒᵣ)
          Language.ORing.Func.zero)
  | .oneExt => by
      simpa using
        (FFL.FirstOrder.Theory.eqAxiom.funcExt (L := ℒₒᵣ)
          Language.ORing.Func.one)
  | .addExt => by
      simpa using
        (FFL.FirstOrder.Theory.eqAxiom.funcExt (L := ℒₒᵣ)
          Language.ORing.Func.add)
  | .mulExt => by
      simpa using
        (FFL.FirstOrder.Theory.eqAxiom.funcExt (L := ℒₒᵣ)
          Language.ORing.Func.mul)
  | .equalExt => by
      simpa using
        (FFL.FirstOrder.Theory.eqAxiom.relExt (L := ℒₒᵣ)
          Language.ORing.Rel.eq)
  | .lessExt => by
      simpa using
        (FFL.FirstOrder.Theory.eqAxiom.relExt (L := ℒₒᵣ)
          Language.ORing.Rel.lt)

theorem equalityAxiomOfFoundation {p : ArithmeticSentence} :
    FFL.FirstOrder.Theory.eqAxiom ℒₒᵣ p →
      EqualityAxiom (Formula.ofFoundation p)
  | .refl => by
      simpa only [← equality_refl, Formula.ofFoundation_toFoundation] using
        EqualityAxiom.refl
  | .symm => by
      simpa only [← equality_symm, Formula.ofFoundation_toFoundation] using
        EqualityAxiom.symm
  | .trans => by
      simpa only [← equality_trans, Formula.ofFoundation_toFoundation] using
        EqualityAxiom.trans
  | .funcExt f => by
      cases f with
      | zero =>
          simpa only [← equality_zeroExt,
            Formula.ofFoundation_toFoundation] using EqualityAxiom.zeroExt
      | one =>
          simpa only [← equality_oneExt,
            Formula.ofFoundation_toFoundation] using EqualityAxiom.oneExt
      | add =>
          simpa only [← equality_addExt,
            Formula.ofFoundation_toFoundation] using EqualityAxiom.addExt
      | mul =>
          simpa only [← equality_mulExt,
            Formula.ofFoundation_toFoundation] using EqualityAxiom.mulExt
  | .relExt r => by
      cases r with
      | eq =>
          simpa only [← equality_equalExt,
            Formula.ofFoundation_toFoundation] using EqualityAxiom.equalExt
      | lt =>
          simpa only [← equality_lessExt,
            Formula.ofFoundation_toFoundation] using EqualityAxiom.lessExt

theorem peanoMinusToFoundation {p : Sentence} :
    PeanoMinus p →
      FFL.FirstOrder.Arithmetic.PeanoMinus (Formula.toFoundation p)
  | .equal h =>
      FFL.FirstOrder.Arithmetic.PeanoMinus.equal _
        (equalityAxiomToFoundation h)
  | .addZero => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.addZero
  | .addAssoc => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.addAssoc
  | .addComm => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.addComm
  | .addEqOfLt => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.addEqOfLt
  | .zeroLe => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.zeroLe
  | .zeroLtOne => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.zeroLtOne
  | .oneLeOfZeroLt => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.oneLeOfZeroLt
  | .addLtAdd => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.addLtAdd
  | .mulZero => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.mulZero
  | .mulOne => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.mulOne
  | .mulAssoc => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.mulAssoc
  | .mulComm => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.mulComm
  | .mulLtMul => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.mulLtMul
  | .distr => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.distr
  | .ltIrrefl => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.ltIrrefl
  | .ltTrans => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.ltTrans
  | .ltTri => by
      simpa using FFL.FirstOrder.Arithmetic.PeanoMinus.ltTri

theorem peanoMinusOfFoundation {p : ArithmeticSentence} :
    FFL.FirstOrder.Arithmetic.PeanoMinus p →
      PeanoMinus (Formula.ofFoundation p)
  | .equal _ h => .equal (equalityAxiomOfFoundation h)
  | .addZero => by
      simpa only [← peanoMinus_addZero,
        Formula.ofFoundation_toFoundation] using PeanoMinus.addZero
  | .addAssoc => by
      simpa only [← peanoMinus_addAssoc,
        Formula.ofFoundation_toFoundation] using PeanoMinus.addAssoc
  | .addComm => by
      simpa only [← peanoMinus_addComm,
        Formula.ofFoundation_toFoundation] using PeanoMinus.addComm
  | .addEqOfLt => by
      simpa only [← peanoMinus_addEqOfLt,
        Formula.ofFoundation_toFoundation] using PeanoMinus.addEqOfLt
  | .zeroLe => by
      simpa only [← peanoMinus_zeroLe,
        Formula.ofFoundation_toFoundation] using PeanoMinus.zeroLe
  | .zeroLtOne => by
      simpa only [← peanoMinus_zeroLtOne,
        Formula.ofFoundation_toFoundation] using PeanoMinus.zeroLtOne
  | .oneLeOfZeroLt => by
      simpa only [← peanoMinus_oneLeOfZeroLt,
        Formula.ofFoundation_toFoundation] using PeanoMinus.oneLeOfZeroLt
  | .addLtAdd => by
      simpa only [← peanoMinus_addLtAdd,
        Formula.ofFoundation_toFoundation] using PeanoMinus.addLtAdd
  | .mulZero => by
      simpa only [← peanoMinus_mulZero,
        Formula.ofFoundation_toFoundation] using PeanoMinus.mulZero
  | .mulOne => by
      simpa only [← peanoMinus_mulOne,
        Formula.ofFoundation_toFoundation] using PeanoMinus.mulOne
  | .mulAssoc => by
      simpa only [← peanoMinus_mulAssoc,
        Formula.ofFoundation_toFoundation] using PeanoMinus.mulAssoc
  | .mulComm => by
      simpa only [← peanoMinus_mulComm,
        Formula.ofFoundation_toFoundation] using PeanoMinus.mulComm
  | .mulLtMul => by
      simpa only [← peanoMinus_mulLtMul,
        Formula.ofFoundation_toFoundation] using PeanoMinus.mulLtMul
  | .distr => by
      simpa only [← peanoMinus_distr,
        Formula.ofFoundation_toFoundation] using PeanoMinus.distr
  | .ltIrrefl => by
      simpa only [← peanoMinus_ltIrrefl,
        Formula.ofFoundation_toFoundation] using PeanoMinus.ltIrrefl
  | .ltTrans => by
      simpa only [← peanoMinus_ltTrans,
        Formula.ofFoundation_toFoundation] using PeanoMinus.ltTrans
  | .ltTri => by
      simpa only [← peanoMinus_ltTri,
        Formula.ofFoundation_toFoundation] using PeanoMinus.ltTri

theorem peanoToFoundation {p : Sentence} :
    Peano p →
      FFL.FirstOrder.Arithmetic.Peano (Formula.toFoundation p)
  | .minus h => Or.inl (peanoMinusToFoundation h)
  | .induction p => by
      right
      change ∃ q : ArithmeticSemiformula ℕ 1,
        q ∈ Set.univ ∧
          Formula.toFoundation
              (Formula.univClosure (Formula.succInd p)) =
            (FFL.FirstOrder.Arithmetic.succInd q).univCl
      refine ⟨Formula.toFoundation p, by simp, ?_⟩
      rw [Formula.toFoundation_univClosure,
        Formula.toFoundation_succInd]

theorem peanoOfFoundation {p : ArithmeticSentence} :
    FFL.FirstOrder.Arithmetic.Peano p →
      Peano (Formula.ofFoundation p) := by
  rintro (h | ⟨p, _, rfl⟩)
  · exact .minus (peanoMinusOfFoundation h)
  · simpa only [Formula.ofFoundation_univCl,
      Formula.ofFoundation_succInd] using
      Peano.induction (Formula.ofFoundation p)

end PeanoCorrespondence

namespace Coding

open Encodable

variable {n : ℕ}

@[simp] theorem encode_func_zero :
    Encodable.encode Language.ORing.Func.zero = 0 := rfl

@[simp] theorem encode_func_one :
    Encodable.encode Language.ORing.Func.one = 1 := rfl

@[simp] theorem encode_func_add :
    Encodable.encode Language.ORing.Func.add = 0 := rfl

@[simp] theorem encode_func_mul :
    Encodable.encode Language.ORing.Func.mul = 1 := rfl

@[simp] theorem encode_rel_eq :
    Encodable.encode Language.ORing.Rel.eq = 0 := rfl

@[simp] theorem encode_rel_lt :
    Encodable.encode Language.ORing.Rel.lt = 1 := rfl

@[simp] theorem vecCodeTwo_eq (a b : ℕ) :
    vecCodeTwo a b = Matrix.vecToNat ![a, b] := by
  simp [vecCodeTwo, Matrix.vecToNat]

@[simp] theorem termCode_eq_encode (t : ClosedTerm n) :
    termCode t = Encodable.encode (Term.toFoundation t) := by
  induction t with
  | bvar i => rfl
  | fvar x => exact Empty.elim x
  | zero => rfl
  | one => rfl
  | add s t ihs iht =>
      simp [termCode, Term.toFoundation, Semiterm.encode_eq_toNat,
        Semiterm.toNat, vecCodeTwo_eq, Matrix.vecToNat, Matrix.vecHead,
        Matrix.vecTail, ihs, iht]
  | mul s t ihs iht =>
      simp [termCode, Term.toFoundation, Semiterm.encode_eq_toNat,
        Semiterm.toNat, vecCodeTwo_eq, Matrix.vecToNat, Matrix.vecHead,
        Matrix.vecTail, ihs, iht]

@[simp] theorem formulaCode_eq_encode (p : Formula Empty n) :
    formulaCode p = Encodable.encode (Formula.toFoundation p) := by
  induction p <;>
    simp [formulaCode, Formula.toFoundation, Semiformula.encode_eq_toNat,
      Semiformula.toNat, termCode_eq_encode, vecCodeTwo_eq,
      Matrix.vecToNat, Matrix.fun_eq_vec_two, *]

/-- The numerical code translation is literally the identity because both
interfaces use the same public pairing code. -/
def codeTranslation (n : ℕ) : ℕ := n

theorem codeTranslation_computable : Computable codeTranslation := by
  change Computable (fun n : ℕ ↦ n)
  exact Computable.id

end Coding

namespace Sequent

def toFoundation (Γ : Sequent) : LK.Sequent ℒₒᵣ :=
  Γ.map Formula.toFoundation

def ofFoundation (Γ : LK.Sequent ℒₒᵣ) : Sequent :=
  Γ.map Formula.ofFoundation

@[simp] theorem toFoundation_add (Γ Δ : Sequent) :
    toFoundation (Γ + Δ) = toFoundation Γ + toFoundation Δ := by
  simp [toFoundation]

@[simp] theorem ofFoundation_toFoundation (Γ : Sequent) :
    ofFoundation (toFoundation Γ) = Γ := by
  simp [ofFoundation, toFoundation, Multiset.map_map]

@[simp] theorem toFoundation_ofFoundation (Γ : LK.Sequent ℒₒᵣ) :
    toFoundation (ofFoundation Γ) = Γ := by
  simp [ofFoundation, toFoundation, Multiset.map_map]

theorem toFoundation_injective : Function.Injective toFoundation :=
  Function.LeftInverse.injective ofFoundation_toFoundation

@[simp] theorem ofFoundation_add (Γ Δ : LK.Sequent ℒₒᵣ) :
    ofFoundation (Γ + Δ) = ofFoundation Γ + ofFoundation Δ := by
  simp [ofFoundation]

@[simp] theorem ofFoundation_singleton (p : ArithmeticProposition) :
    ofFoundation ⦃p⦄ = singleton (Formula.ofFoundation p) := by
  rfl

@[simp] theorem ofFoundation_pair (p q : ArithmeticProposition) :
    ofFoundation ⦃p, q⦄ = pair (Formula.ofFoundation p) (Formula.ofFoundation q) := by
  rfl

@[simp] theorem toFoundation_singleton (p : Proposition) :
    toFoundation (singleton p) = ⦃Formula.toFoundation p⦄ := by
  rfl

@[simp] theorem toFoundation_pair (p q : Proposition) :
    toFoundation (pair p q) = ⦃Formula.toFoundation p, Formula.toFoundation q⦄ := by
  rfl

@[simp] theorem toFoundation_shiftFree (Γ : Sequent) :
    toFoundation (shiftFree Γ) = (toFoundation Γ)⁺ := by
  simp [toFoundation, shiftFree, Rewriting.shifts, Multiset.map_map,
    Formula.toFoundation_shiftFree]

@[simp] theorem toFoundation_negateSentences (Γ : Multiset Sentence) :
    toFoundation (negateSentences Γ) =
      ∼LK.Sequent.embed (Γ.map Formula.toFoundation) := by
  simp only [toFoundation, negateSentences, LK.Sequent.embed,
    Multiset.tilde_def, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro p hp
  change Formula.toFoundation ((Formula.embed p).neg) =
    ∼(Rewriting.emb (Formula.toFoundation p) : ArithmeticProposition)
  rw [Formula.toFoundation_neg, Formula.toFoundation_embed]
  rfl

theorem ofFoundation_shift (Γ : LK.Sequent ℒₒᵣ) :
    ofFoundation (Γ⁺) = shiftFree (ofFoundation Γ) := by
  apply toFoundation_injective
  rw [toFoundation_ofFoundation, toFoundation_shiftFree,
    toFoundation_ofFoundation]

theorem ofFoundation_negateSentences (Γ : Multiset ArithmeticSentence) :
    ofFoundation (∼LK.Sequent.embed Γ) =
      negateSentences (Γ.map Formula.ofFoundation) := by
  apply toFoundation_injective
  rw [toFoundation_ofFoundation, toFoundation_negateSentences]
  simp [Multiset.map_map]

end Sequent

namespace Derivation

def cast {Γ Δ : Sequent} (d : Derivation Γ) (h : Γ = Δ) : Derivation Δ :=
  h ▸ d

def toFoundation {Γ : Sequent} :
    Derivation Γ → LK.Derivation Γ.toFoundation
  | .identityEqual s t =>
      (LK.Derivation.identity (L := ℒₒᵣ) Language.ORing.Rel.eq
        ![Term.toFoundation s, Term.toFoundation t]).cast (by rfl)
  | .identityLess s t =>
      (LK.Derivation.identity (L := ℒₒᵣ) Language.ORing.Rel.lt
        ![Term.toFoundation s, Term.toFoundation t]).cast (by rfl)
  | @Derivation.cut Γ Δ p dp dn =>
      (LK.Derivation.cut (L := ℒₒᵣ)
        (Γ := Γ.toFoundation) (Δ := Δ.toFoundation)
        (φ := Formula.toFoundation p)
        (LK.Derivation.cast (toFoundation dp) (by simp only [Sequent.toFoundation_add,
          Sequent.toFoundation_singleton]))
        (LK.Derivation.cast (toFoundation dn) (by simp only [Sequent.toFoundation_add,
          Sequent.toFoundation_singleton, Formula.toFoundation_neg]; rfl))).cast (by
            simp only [Sequent.toFoundation_add])
  | @Derivation.contraction Γ p d =>
      (LK.Derivation.contraction (Γ := Γ.toFoundation)
        (φ := Formula.toFoundation p)
        (LK.Derivation.cast (toFoundation d) (by simp [Sequent.toFoundation_add,
          Sequent.toFoundation_pair]))).cast (by
          simp only [Sequent.toFoundation_add, Sequent.toFoundation_singleton])
  | @Derivation.weakening Γ p d =>
      (LK.Derivation.weakening (φ := Formula.toFoundation p)
        (toFoundation d)).cast (by
        simp only [Sequent.toFoundation_add, Sequent.toFoundation_singleton])
  | .verum => (LK.Derivation.verum (L := ℒₒᵣ)).cast (by rfl)
  | @Derivation.or Γ p q d =>
      (LK.Derivation.or (Γ := Γ.toFoundation)
        (φ := Formula.toFoundation p) (ψ := Formula.toFoundation q)
        (LK.Derivation.cast (toFoundation d) (by simp [Sequent.toFoundation_add,
          Sequent.toFoundation_pair]))).cast (by
          simp only [Sequent.toFoundation_add, Sequent.toFoundation_singleton,
            Formula.toFoundation_or])
  | @Derivation.and Γ p q dp dq =>
      (LK.Derivation.and (Γ := Γ.toFoundation)
        (φ := Formula.toFoundation p) (ψ := Formula.toFoundation q)
        (LK.Derivation.cast (toFoundation dp) (by simp only [Sequent.toFoundation_add,
          Sequent.toFoundation_singleton]))
        (LK.Derivation.cast (toFoundation dq) (by simp only [Sequent.toFoundation_add,
          Sequent.toFoundation_singleton]))).cast (by
          simp only [Sequent.toFoundation_add, Sequent.toFoundation_singleton,
            Formula.toFoundation_and])
  | @Derivation.all Γ p d =>
      (LK.Derivation.all (Γ := Γ.toFoundation)
        (φ := Formula.toFoundation p)
        (LK.Derivation.cast (toFoundation d) (by
          simp only [Sequent.toFoundation_add, Sequent.toFoundation_shiftFree,
            Sequent.toFoundation_singleton, Formula.toFoundation_free]))).cast (by
            simp only [Sequent.toFoundation_add, Sequent.toFoundation_singleton,
              Formula.toFoundation_all])
  | @Derivation.exs Γ p t d =>
      (LK.Derivation.exs (Γ := Γ.toFoundation)
        (φ := Formula.toFoundation p) (t := Term.toFoundation t)
        (LK.Derivation.cast (toFoundation d) (by
          simp only [Sequent.toFoundation_add, Sequent.toFoundation_singleton,
            Formula.toFoundation_substOne]))).cast (by
            simp only [Sequent.toFoundation_add, Sequent.toFoundation_singleton,
              Formula.toFoundation_exs])

def ofFoundation {Γ : LK.Sequent ℒₒᵣ} :
    LK.Derivation Γ → Derivation (Sequent.ofFoundation Γ)
  | .identity Language.ORing.Rel.eq v =>
      cast (.identityEqual (Term.ofFoundation (v 0)) (Term.ofFoundation (v 1))) (by
        rfl)
  | .identity Language.ORing.Rel.lt v =>
      cast (.identityLess (Term.ofFoundation (v 0)) (Term.ofFoundation (v 1))) (by
        rfl)
  | @LK.Derivation.cut _ Γ p Δ dp dn =>
      cast (Derivation.cut (Γ := Sequent.ofFoundation Γ)
        (Δ := Sequent.ofFoundation Δ) (p := Formula.ofFoundation p)
        (cast (ofFoundation dp) (by simp only [Sequent.ofFoundation_add,
          Sequent.ofFoundation_singleton]))
        (cast (ofFoundation dn) (by
          simp only [Sequent.ofFoundation_add, Sequent.ofFoundation_singleton]
          change Sequent.ofFoundation Δ +
            Sequent.singleton (Formula.ofFoundation (FFL.FirstOrder.Semiformula.neg p)) = _
          rw [Formula.ofFoundation_neg]))) (by
            simp only [Sequent.ofFoundation_add])
  | @LK.Derivation.contraction _ Γ p d =>
      cast (Derivation.contraction (Γ := Sequent.ofFoundation Γ)
        (p := Formula.ofFoundation p)
        (cast (ofFoundation d) (by simp [Sequent.ofFoundation_add,
          Sequent.singleton, Sequent.pair]))) (by
            simp only [Sequent.ofFoundation_add, Sequent.ofFoundation_singleton])
  | @LK.Derivation.weakening _ Γ p d =>
      cast (Derivation.weakening (p := Formula.ofFoundation p)
        (ofFoundation d)) (by
          simp only [Sequent.ofFoundation_add, Sequent.ofFoundation_singleton])
  | .verum => cast .verum (by rfl)
  | @LK.Derivation.or _ Γ p q d =>
      cast (Derivation.or (Γ := Sequent.ofFoundation Γ)
        (p := Formula.ofFoundation p)
        (q := Formula.ofFoundation q)
        (cast (ofFoundation d) (by simp [Sequent.ofFoundation_add,
          Sequent.singleton, Sequent.pair]))) (by
            simp only [Sequent.ofFoundation_add, Sequent.ofFoundation_singleton,
              Formula.ofFoundation_or])
  | @LK.Derivation.and _ Γ p q dp dq =>
      cast (Derivation.and (Γ := Sequent.ofFoundation Γ)
        (p := Formula.ofFoundation p)
        (q := Formula.ofFoundation q)
        (cast (ofFoundation dp) (by simp only [Sequent.ofFoundation_add,
          Sequent.ofFoundation_singleton]))
        (cast (ofFoundation dq) (by simp only [Sequent.ofFoundation_add,
          Sequent.ofFoundation_singleton]))) (by
            simp only [Sequent.ofFoundation_add, Sequent.ofFoundation_singleton,
              Formula.ofFoundation_and])
  | @LK.Derivation.all _ Γ p d =>
      cast (Derivation.all (Γ := Sequent.ofFoundation Γ)
        (p := Formula.ofFoundation p)
        (cast (ofFoundation d) (by
          simp only [Sequent.ofFoundation_add, Sequent.ofFoundation_shift,
            Sequent.ofFoundation_singleton, Formula.ofFoundation_free]))) (by
              simp only [Sequent.ofFoundation_add, Sequent.ofFoundation_singleton,
                Formula.ofFoundation_all])
  | @LK.Derivation.exs _ Γ p t d =>
      cast (Derivation.exs (Γ := Sequent.ofFoundation Γ)
        (p := Formula.ofFoundation p)
        (t := Term.ofFoundation t)
        (cast (ofFoundation d) (by
          simp only [Sequent.ofFoundation_add, Sequent.ofFoundation_singleton,
            Formula.ofFoundation_substOne]))) (by
              simp only [Sequent.ofFoundation_add, Sequent.ofFoundation_singleton,
                Formula.ofFoundation_exs])

end Derivation

namespace TheoryCorrespondence

def toFoundation (T : Theory) : ArithmeticTheory :=
  {p | Formula.ofFoundation p ∈ T}

def ofFoundation (T : ArithmeticTheory) : Theory :=
  {p | Formula.toFoundation p ∈ T}

@[simp] theorem mem_toFoundation {T : Theory} {p : ArithmeticSentence} :
    p ∈ toFoundation T ↔ Formula.ofFoundation p ∈ T := by
  rfl

@[simp] theorem mem_ofFoundation {T : ArithmeticTheory} {p : Sentence} :
    p ∈ ofFoundation T ↔ Formula.toFoundation p ∈ T := by
  rfl

@[simp] theorem ofFoundation_toFoundation (T : Theory) :
    ofFoundation (toFoundation T) = T := by
  ext p
  simp [ofFoundation, toFoundation]

@[simp] theorem toFoundation_ofFoundation (T : ArithmeticTheory) :
    toFoundation (ofFoundation T) = T := by
  ext p
  simp [ofFoundation, toFoundation]

theorem peano_toFoundation :
    toFoundation Peano = FFL.FirstOrder.Arithmetic.Peano := by
  ext p
  change Peano (Formula.ofFoundation p) ↔
    FFL.FirstOrder.Arithmetic.Peano p
  constructor
  · intro h
    simpa using PeanoCorrespondence.peanoToFoundation h
  · exact PeanoCorrespondence.peanoOfFoundation

end TheoryCorrespondence

namespace Proof

def toFoundation {T : Theory} {p : Sentence} (b : Proof T p) :
    FFL.FirstOrder.Theory.Proof (TheoryCorrespondence.toFoundation T)
      (Formula.toFoundation p) where
  axioms := b.axioms.map Formula.toFoundation
  axioms_mem := by
    intro q hq
    rcases Multiset.mem_map.mp hq with ⟨r, hr, rfl⟩
    simpa [TheoryCorrespondence.toFoundation] using b.axioms_mem r hr
  derivation := LK.Derivation.cast b.derivation.toFoundation (by
    simp [Sequent.toFoundation_add,
      Sequent.toFoundation_singleton, Sequent.toFoundation_negateSentences,
      LK.Sequent.embed, Multiset.map_tilde_comm, Multiset.map_map])

def ofFoundation {T : ArithmeticTheory} {p : ArithmeticSentence}
    (b : FFL.FirstOrder.Theory.Proof T p) :
    Proof (TheoryCorrespondence.ofFoundation T) (Formula.ofFoundation p) where
  axioms := b.axioms.map Formula.ofFoundation
  axioms_mem := by
    intro q hq
    rcases Multiset.mem_map.mp hq with ⟨r, hr, rfl⟩
    simpa [TheoryCorrespondence.ofFoundation] using b.axioms_mem r hr
  derivation := Derivation.cast (Derivation.ofFoundation b.derivation) (by
    rw [Multiset.map_add, Sequent.ofFoundation_add]
    change Sequent.ofFoundation ⦃Rewriting.emb p⦄ +
      Sequent.ofFoundation ((∼b.axioms).map Rewriting.emb) = _
    rw [Sequent.ofFoundation_singleton, Formula.ofFoundation_embed,
      Multiset.map_tilde_comm]
    change Sequent.singleton (Formula.ofFoundation p).embed +
      Sequent.ofFoundation (∼LK.Sequent.embed b.axioms) = _
    rw [Sequent.ofFoundation_negateSentences])

end Proof

theorem provable_toFoundation_iff (T : Theory) (p : Sentence) :
    Provable T p ↔
      Nonempty (FFL.FirstOrder.Theory.Proof
        (TheoryCorrespondence.toFoundation T) (Formula.toFoundation p)) := by
  constructor
  · rintro ⟨b⟩
    exact ⟨b.toFoundation⟩
  · rintro ⟨b⟩
    have h := Proof.ofFoundation b
    exact ⟨by simpa using h⟩

theorem consistent_toFoundation_iff (T : Theory) :
    Consistent T ↔
      FFL.Entailment.Consistent (TheoryCorrespondence.toFoundation T) := by
  rw [FFL.Entailment.consistent_iff_unprovable_bot]
  change (¬Provable T .falsum) ↔
    ¬Nonempty (FFL.FirstOrder.Theory.Proof
      (TheoryCorrespondence.toFoundation T) (Formula.toFoundation (.falsum : Sentence)))
  exact not_congr (provable_toFoundation_iff T .falsum)

theorem deductivelyExtends_toFoundation_iff (U T : Theory) :
    DeductivelyExtends U T ↔
      FFL.Entailment.WeakerThan (TheoryCorrespondence.toFoundation U)
        (TheoryCorrespondence.toFoundation T) := by
  constructor
  · intro h
    constructor
    intro p hp
    rcases hp with ⟨bp⟩
    have bU := Proof.ofFoundation bp
    have bU' : Proof U (Formula.ofFoundation p) := by simpa using bU
    rcases h ⟨bU'⟩ with ⟨bT⟩
    have bf := bT.toFoundation
    change Nonempty (FFL.FirstOrder.Theory.Proof
      (TheoryCorrespondence.toFoundation T) p)
    simpa using Nonempty.intro bf
  · intro h p hp
    rw [provable_toFoundation_iff] at hp ⊢
    exact h.wk hp

theorem deductivelyExtendsPeano_toFoundation_iff (T : Theory) :
    DeductivelyExtends Peano T ↔
      FFL.Entailment.WeakerThan FFL.FirstOrder.Arithmetic.Peano
        (TheoryCorrespondence.toFoundation T) := by
  rw [deductivelyExtends_toFoundation_iff,
    TheoryCorrespondence.peano_toFoundation]

theorem axiomCodes_toFoundation_iff (T : Theory) (n : ℕ) :
    AxiomCodes T n ↔
      FailureOfComposition.AxiomCodes
        (TheoryCorrespondence.toFoundation T) n := by
  constructor
  · rintro ⟨p, hp, hpT⟩
    refine ⟨Formula.toFoundation p, ?_, ?_⟩
    · rw [Sentence.quote_eq_encode_nat]
      simpa using hp
    · simpa [TheoryCorrespondence.toFoundation] using hpT
  · rintro ⟨p, hp, hpT⟩
    refine ⟨Formula.ofFoundation p, ?_, ?_⟩
    · change Coding.formulaCode (Formula.ofFoundation p) = n
      rw [Coding.formulaCode_eq_encode, Formula.toFoundation_ofFoundation]
      simpa only [Sentence.quote_eq_encode_nat] using hp
    · exact hpT

/-- Local and maintained axiom predicates agree after the explicit computable
code translation.  Here that translation is definitionally the identity. -/
theorem axiomCodes_codeTranslation_iff (T : Theory) (n : ℕ) :
    AxiomCodes T n ↔
      FailureOfComposition.AxiomCodes
        (TheoryCorrespondence.toFoundation T) (Coding.codeTranslation n) := by
  simpa [Coding.codeTranslation] using axiomCodes_toFoundation_iff T n

theorem reAxiomCodes_toFoundation_iff (T : Theory) :
    REPred (AxiomCodes T) ↔
      REPred (FailureOfComposition.AxiomCodes
        (TheoryCorrespondence.toFoundation T)) := by
  have h : AxiomCodes T = FailureOfComposition.AxiomCodes
      (TheoryCorrespondence.toFoundation T) :=
    funext fun n ↦ propext (axiomCodes_toFoundation_iff T n)
  rw [h]

end FailureOfComposition.Palomar.Arithmetic
