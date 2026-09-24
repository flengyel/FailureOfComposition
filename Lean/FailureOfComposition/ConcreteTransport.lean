/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ArithmetizationTransport
import FailureOfComposition.ConcreteGodel

/-!
PA-provable representation transport into the fully constructed history
arithmetization. The source representation retains its explicitly stated laws.
Translations are selected indices, not claimed computable code-table maps.
-/

set_option autoImplicit false



open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.ConcreteTransport
open ProofSearch ProgramIndices
noncomputable section

def toConcrete (A : Arithmetization) : ℕ → ℕ :=
  ArithmetizationTransport.translate A ConcreteEvaluator.arithmetization

theorem toConcrete_uniform (A : Arithmetization) (e : ℕ) :
    Uniform 𝗣𝗔 (ConcreteEvaluator.eventualGraph (toConcrete A e)) (A.graph e) :=
  ArithmetizationTransport.translate_uniform A ConcreteEvaluator.arithmetization e

theorem toConcrete_pointwise_iff (A : Arithmetization)
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (e f : ℕ) :
    ConcreteIndices.PointwiseIndex T (toConcrete A e) (toConcrete A f) ↔
      ProgramIndices.PointwiseIndex A T e f :=
  ArithmetizationTransport.translate_pointwise_iff A ConcreteEvaluator.arithmetization T e f

/-- An equivalence of quotient sets; no quotient composition is assumed. -/
def quotientEquiv (A : Arithmetization) (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    Quotient (ProgramIndices.indexSetoid A T) ≃ Quotient (ConcreteIndices.indexSetoid T) :=
  ArithmetizationTransport.quotientEquiv A ConcreteEvaluator.arithmetization T

theorem toConcrete_composition (A : Arithmetization)
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (e f : ℕ) :
    ConcreteIndices.PointwiseIndex T (toConcrete A (A.compIndex e f))
      (CategoricalRiceShapiro.PartialRecursive.canonicalPartrecCompIndex
        (toConcrete A e) (toConcrete A f)) :=
  ArithmetizationTransport.translate_composition A ConcreteEvaluator.arithmetization T e f

end
end FailureOfComposition.ConcreteTransport
