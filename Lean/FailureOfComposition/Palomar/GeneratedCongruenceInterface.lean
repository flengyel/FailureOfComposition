/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.Palomar.PiOneInterface

/-!
# Independent generated-congruence statement interface

The permanent Σ₁ and generated-relation definitions live with the arithmetic
and evaluator declarations they extend. This focused re-export is used by the
Solution-side correspondence proof; the eligible Challenge inlines the same
readable definitions.
-/
@[expose] public section
