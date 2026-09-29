# Generated-congruence correspondence

The fifth independent statement uses these definitions and proved bridges. All
formula variables range over the complete independent arithmetic syntax, and
all index variables range over `ℕ`.

| Independent declaration | Maintained target | Exact bridge |
| --- | --- | --- |
| `Arithmetic.Hierarchy.SigmaOne p` | `FFL.FirstOrder.Arithmetic.Hierarchy 𝚺 1 p.toFoundation` | `Hierarchy.sigmaOne_toFoundation_iff` (with named forward and reverse proofs) |
| `Arithmetic.StandardTrue p` | standard satisfaction of `p.toFoundation` in `ℕ` | reused `standardTrue_toFoundation_iff` |
| `Arithmetic.Provable T p` | a maintained proof of `p.toFoundation` in `TheoryCorrespondence.toFoundation T` | reused `provable_toFoundation_iff` |
| `Arithmetic.SigmaOneSound T` | `GeneratedCongruence.SigmaOneSound (TheoryCorrespondence.toFoundation T)` | `sigmaOneSound_toFoundation_iff` |
| `Evaluator.PointwiseIndex T e d` | `ConcreteIndices.PointwiseIndex (TheoryCorrespondence.toFoundation T) e d` | reused `pointwiseIndex_toFoundation_iff` |
| `Evaluator.compIndex e d` | `canonicalPartrecCompIndex e d` | reused `compIndex_toFoundation` |
| `Evaluator.GeneratedRel T e d` | `ConcreteIndices.GeneratedRel (TheoryCorrespondence.toFoundation T) e d` | `generatedRel_toFoundation_iff` |
| `Evaluator.actualEval e` | `Kleene.eval e` | reused `actualEval_toFoundation` pointwise, then function extensionality |

`Evaluator.GeneratedRel` is defined independently as the intersection of all
relations satisfying `IsCompositionCongruence` and containing every
`PointwiseIndex` generator. The bridge also proves, without using the
classification theorem:

- `generatedRel_base` (generator containment);
- `generatedRel_equivalence` (reflexivity, symmetry, and transitivity);
- `generatedRel_comp` (two-argument composition compatibility); and
- `generatedRel_least` (leastness among all such congruences).

Finally,
`Arithmetic.Evaluator.generated_congruence_classification T hPA` transports
`ConcreteIndices.generated_congruence_classification` through the soundness,
relation, composition, and evaluator bridges. Its only public hypothesis is the
independent deductive extension `DeductivelyExtends Peano T`; neither branch
assumes consistency or enumerability.
