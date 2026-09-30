# Range correspondence

| Independent declaration | Maintained target | Role |
| --- | --- | --- |
| `Arithmetic.Evaluator.rangeOfGraph` | `ConcreteIndices.rangeOfGraph` | The partial identity graph `r = w ∧ ∃ x, G_e(x,r)`. |
| `Arithmetic.Evaluator.rangeGraph` | `ConcreteIndices.rangeGraph` | Range graph of the fixed evaluator program. |
| `Arithmetic.Evaluator.uniformGraphSentence` | `ProofSearch.uniformSentence` | One internally universal binary-graph equation. |
| `Arithmetic.Evaluator.RangeRealizes` | `ProofSearch.Uniform PA` | Actual PA derivability of the range graph equation. |
| `Arithmetic.Evaluator.toFoundation_rangeGraph` | maintained range graph value | Exact formula translation, including binder order and substitution. |
| `Arithmetic.Evaluator.rangeRealizes_toFoundation_iff` | maintained PA-uniform realization | Preservation and reflection of the realization proof. |
| `Arithmetic.Evaluator.exists_rangeRealizes` | `ConcreteIndices.rangeIndex_realizes` | Nonemptiness of the independent selector predicate. |
| `Arithmetic.Evaluator.rangeIndex_realizes` | `Classical.epsilon_spec` | Correctness of the fixed independent selector. |
| `Arithmetic.Evaluator.rangeIndex_choice_toFoundation` | `ConcreteIndices.rangeIndex_choice_independent` | Pointwise equality of the independent and maintained choices. |
| `Arithmetic.Evaluator.rangeIndices_toFoundation_iff` | maintained pointwise equality of both range choices | Two-direction transport, using symmetry/transitivity on both operands. |
| `Arithmetic.Evaluator.range_counterexample_godel` | `ConcreteIndices.range_counterexample_of_re_axioms` | Transport of the same natural-number witness and exact hypotheses. |

The selector definitions are not claimed to choose the same natural number.
The checked bridge proves that they occupy the same pointwise-provability class
over every deductive extension of PA.  The realization and choice bridges do
not depend on the counterexample theorem.
