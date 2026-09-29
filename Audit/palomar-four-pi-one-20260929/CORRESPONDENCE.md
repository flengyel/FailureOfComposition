# Cumulative Four correspondence index

The selected independent theorem is
`FailureOfComposition.Palomar.pi_one_characterization`; its proved transport is
`FailureOfComposition.Palomar.Arithmetic.Evaluator.pi_one_characterization`.

| Obligation | Independent declaration | Proved bridge |
| --- | --- | --- |
| Standard term evaluation | `Arithmetic.Term.standardEval` | `Arithmetic.Term.standardEval_toFoundation` |
| Standard formula satisfaction under all environments/binders | `Arithmetic.Formula.standardEval` | `Arithmetic.Formula.standardEval_toFoundation` |
| Closed standard truth | `Arithmetic.StandardTrue` | `Arithmetic.standardTrue_toFoundation_iff` |
| Bounded quantifiers | `Arithmetic.Formula.ball`, `bexs` | `Formula.toFoundation_ball`, `Formula.toFoundation_bexs` |
| Bounded hierarchy, both directions | `Arithmetic.Hierarchy.DeltaZero` | `Hierarchy.deltaZero_toFoundation_iff` |
| Π₁ hierarchy, both directions | `Arithmetic.Hierarchy.PiOne` | `Hierarchy.piOne_toFoundation_iff` |
| True Π₁ completeness, both directions | `Arithmetic.PiOneComplete` | `Arithmetic.piOneComplete_toFoundation_iff` |
| Right compatibility, both directions | `Arithmetic.Evaluator.RightCompatible` | `Evaluator.rightCompatible_toFoundation_iff` |
| Composition congruence, both directions | `Arithmetic.Evaluator.CompositionCongruence` | `Evaluator.compositionCongruence_toFoundation_iff` |
| Actual evaluator equality | `Arithmetic.Evaluator.actualEval` | `Evaluator.actualEval_toFoundation` |
| Extensional agreement, both directions | `Arithmetic.Evaluator.AgreesWithExtensional` | `Evaluator.agreesWithExtensional_toFoundation_iff` |
| Maintained theorem root | n/a | `FailureOfComposition.ConcreteIndices.pi_one_characterization` |

The final bridge discharges deductive PA extension and consistency through
`deductivelyExtendsPeano_toFoundation_iff` and
`consistent_toFoundation_iff`. It introduces no enumerability, soundness,
presentation, realization, or completeness hypothesis.
