# Productive range correspondence

| Independent declaration | Maintained target | Role |
| --- | --- | --- |
| `Arithmetic.Evaluator.rangeOfGraph` | `ConcreteIndices.rangeOfGraph` | Partial identity graph `r = w ∧ ∃ x, G_e(x,r)`. |
| `Arithmetic.Evaluator.RangeRealizes` | `ProofSearch.Uniform PA` | Actual PA derivation of the uniform range-graph equation. |
| `Arithmetic.Evaluator.rangeIndex_realizes` | `ConcreteIndices.rangeIndex_realizes` | Correctness of the fixed independent classical selector. |
| `Arithmetic.Evaluator.rangeIndex_choice_toFoundation` | `ConcreteIndices.rangeIndex_choice_independent` | Pointwise equality of independent and maintained range choices over every PA extension. |
| `Arithmetic.Evaluator.rangeIndices_toFoundation_iff` | maintained pointwise equality of both chosen range indices | Two-direction transport for both operands, including the range of empty. |
| `Arithmetic.Evaluator.range_counterexample_productive` | `ConcreteIndices.range_counterexample_via_productiveness_of_re_axioms` | Transport of the same natural-number witness and exact public hypotheses. |

The two selectors are not asserted to choose the same natural number, and the
independent selector is not claimed computable.  Their PA-uniform realization
laws place them in the same pointwise-provability classes.  The common range
correspondence has a checked dependency closure independent of both range
counterexample proof routes.
