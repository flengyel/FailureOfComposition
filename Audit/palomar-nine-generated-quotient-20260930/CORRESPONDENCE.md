# Ninth-result correspondence

The ninth public statement uses the independent definitions in
`Palomar/GeneratedQuotientInterface.lean`.  Its selected proof is direct: under
independent Σ₁ soundness, result 5 identifies `GeneratedRel T e d` with
`actualEval e = actualEval d`, so actual evaluation descends to the quotient.
Mathlib code existence gives surjectivity, the classification gives injectivity,
and `Kleene.eval_compIndex` proves preservation of multiplication.

| Independent declaration | Maintained target / role | Checked bridge |
| --- | --- | --- |
| `Evaluator.GeneratedQuotient` | `ConcreteIndices.GeneratedQuotient` | `generatedQuotientToFoundation` |
| `Evaluator.generatedQuotientMk` | `ConcreteIndices.generatedQuotientMk` | `generatedQuotientToFoundation_mk` |
| quotient multiplication by `compIndex` | maintained multiplication by `canonicalPartrecCompIndex` | `generatedQuotientToFoundation_mul` |
| quotient unit represented by `identityIndex` | maintained chosen realization of the identity graph | `generatedQuotientToFoundation_one` |
| `Evaluator.UnaryPartrec` | `FailureOfComposition.UnaryPartrec` | `unaryPartrecMulEquivToFoundation` |
| `Evaluator.UnaryPartrec.ofIndex` | maintained `UnaryPartrec.ofIndex` | `unaryPartrecMulEquivToFoundation_ofIndex` |
| total partial identity | maintained target unit | `unaryPartrecMulEquivToFoundation_one` |
| direct independent multiplicative equivalence | maintained multiplicative equivalence | `generatedQuotientPartialRecursiveEquiv_toFoundation` |
| independent equivalence on the fixed unit | total partial identity | `generatedQuotientPartialRecursiveEquiv_one` |

The quotient maps are induced by identity on natural-number representatives.
The unit proof does not assert equality between the fixed identity index and the
maintained chosen realization index: it proves equality of their quotient
classes through the maintained graph quotient and the PA-uniform identity law.
The direct selected proof and all correspondence support have recursive axiom
closures contained in `propext`, `Classical.choice`, and `Quot.sound`.
