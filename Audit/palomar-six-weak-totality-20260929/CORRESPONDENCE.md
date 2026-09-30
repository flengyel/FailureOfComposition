# Weak-totality correspondence

The sixth independent statement keeps the maintained external-input
`PointwiseIndex`, concrete outer-first composition, fixed empty and identity
indices, and the exact compiled guard family.

| Independent declaration | Maintained target | Checked bridge |
| --- | --- | --- |
| `Arithmetic.Evaluator.IndexCompiler.compile` | `ArithmeticCodeCompiler.compile` | `IndexCompiler.compile_toFoundation` |
| `Arithmetic.Evaluator.historyCode` | `HistoryWitnesses.historyCode` | `historyCode_toFoundation` |
| `Arithmetic.Evaluator.guardCode` | `HistoryWitnesses.guardCode` | `guardCode_toFoundation` |
| `Arithmetic.Evaluator.guardIndex` | `ConcreteIndices.guardIndex` | `guardIndex_toFoundation` (equality of natural-number indices) |
| `Arithmetic.Evaluator.WeaklyTotalIndex` | `ConcreteIndices.WeaklyTotalIndex` | `weaklyTotalIndex_toFoundation_iff` in both directions |
| Independent PA extension, consistency, and r.e. axiom codes | Maintained instances and `AxiomCodes` predicate | `deductivelyExtendsPeano_toFoundation_iff`, `consistent_toFoundation_iff`, `reAxiomCodes_toFoundation_iff` |
| `Arithmetic.Evaluator.weak_totality_counterexample` | `ConcreteIndices.weak_totality_counterexample_of_re_axioms` | same witness transported through the preceding equalities/equivalences |

The compiler bridge is structural and proves literal equality of the generated
Mathlib program code. Thus the selected statement uses the same natural number
`guardIndex d`; standard-model graph equivalence is not substituted for index
equality. The weak-totality predicate bridge does not depend on the maintained
counterexample theorem. The sixth selected proof reaches the maintained
productive root and the history-divergence/productiveness route, while the
cumulative dependency audit rejects reachability of the listed Gödel-II and
Craig-presentation roots from this proof.
