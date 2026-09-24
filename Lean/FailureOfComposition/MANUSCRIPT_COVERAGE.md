# Manuscript v36: mathematical coverage

This map records the final source review of
[`failure_of_composition_2026-09-21_v36.tex`](../../research/notes/failure_of_composition_2026-09-21_v36.tex),
*Pointwise provable equality and the failure of composition*. The reviewed
manuscript blob is `e0a2bd4b3570235fa4ea89ffe8dcf9d5445499f9`.
The review starts from commit `355316179c294071d087b04bef0d08bb4329dcb0`
and includes the three coverage additions below. The manuscript is unchanged.

**Coverage review and integrated verification passed on 2026-09-23.**
No unproved mathematical claim was identified within the program-index scope
specified here after the additions. The native build, all 72 strict style
checks, theorem and dependency audits, and all 103 kernel replays passed. Runtime evidence is recorded separately in
[`validation.json`](../../Audit/failure-composition-v36/evidence/validation.json).

Names below are relative to `FailureOfComposition`. `PA` denotes `𝗣𝗔`.
The concrete theorems concern the fixed natural-number program numbering and
the constructed PA arithmetization. General numbering theorems expose their
`ProgramIndices.Arithmetization` laws; the concrete development proves all
those laws instead of assuming them.

## Numbered results

| Manuscript statement | Lean declaration and source | Hypotheses and conclusion checked |
| --- | --- | --- |
| Theorem 1, `thm:obstruction`: four witnesses | `ConcreteIndices.obstruction_four_properties_of_re_axioms` in [ManuscriptObstruction](ManuscriptObstruction.lean) | PA extension, consistency, and r.e. axiom codes. The two middle equalities retain **uniform** T-provability. Their stronger PA-uniform forms are also proved. |
| Theorem 1: no quotient composition | `ConcreteIndices.no_index_quotient_of_re_axioms` in [ConcreteIndexObstruction](ConcreteIndexObstruction.lean); `no_index_quotient_via_godel_of_re_axioms` in [ConcreteGodelRE](ConcreteGodelRE.lean) | The same theory hypotheses. Excludes every binary operation on the actual pointwise quotient satisfying the representative composition equation. Productive and Gödel-II routes have separate checked proof dependencies. |
| Corollary 2, `cor:not-category`: proposed composition already fails on endomorphisms of omega | `ConcreteIndices.NoIndexQuotientComposition` and the preceding no-operation theorems; `pa_no_index_quotient_via_godel` in [ConcreteGodel](ConcreteGodel.lean) | Failure of any representative-respecting binary operation on this endomorphism quotient supplies the categorical obstruction, before associativity or units can be imposed. The PA specialization is closed. |
| Theorem 3, `thm:characterization`: right compatibility, congruence, Pi-one completeness, and extensional agreement | `ConcreteIndices.pi_one_characterization` in [ConcretePiOneCharacterization](ConcretePiOneCharacterization.lean) | Exactly PA extension and consistency; no enumerability assumption. Extensional equality means equality of actual partial functions, including their domains. |
| Theorem 4, `thm:generated-congruence`: generated relation is extensional equality in the Sigma-one sound case and universal otherwise | `ConcreteIndices.generated_congruence_classification` in [ConcreteGeneratedCongruence](ConcreteGeneratedCongruence.lean) | Only PA extension; no consistency or enumerability assumption. The generated relation is the intersection of all composition congruences containing pointwise provability. |
| Proposition 5, `prop:weak`: weak totality is not invariant | `ConcreteIndices.weak_totality_counterexample_of_re_axioms` and `no_quotient_weak_totality_of_re_axioms` in [ConcreteWeakTotality](ConcreteWeakTotality.lean) | Every consistent r.e. PA extension. The weak-totality quantifier ranges over all natural-number program indices, and the predicate does not descend to the actual pointwise quotient. |
| Proposition 6, `prop:range`: range assignment is not invariant | `ConcreteIndices.range_counterexample_of_re_axioms` and `no_index_quotient_range_of_re_axioms` in [RangeGodel](RangeGodel.lean) | Every consistent r.e. PA extension. Pointwise equivalent indices have inequivalent range indices. [RangeProductive](RangeProductive.lean) proves the same obstruction by the productive route. |

## Definitions, auxiliary conclusions, and displayed equations

| Manuscript item | Checked declarations | Scope of the match |
| --- | --- | --- |
| Uniform and pointwise equality, `eq:uniform` and `eq:pointwise` | `ProofSearch.Uniform`, `Pointwise`; `ProgramIndices.kleeneEqAt_iff_eqAt`; `ConcreteIndices.uniformIndex_iff_kleene` | External standard input quantification remains outside provability. The uniform definedness/common-value formula is formally equivalent in PA to uniform output-graph equality, by functionality. |
| Quotient composition, `eq:quotient-composition` | `quotient_composition_exists_iff`; `ConcreteIndices.NoIndexQuotientComposition` | The quotient equation quantifies over every operation satisfying the representative law. No presumed quotient composition is used in the contradiction. |
| Program composition and its PA graph law, `eq:composition-graph` | `Kleene.compIndex_primrec`, `eval_compIndex`; `ConcreteEvaluator.eventualGraph_composition` | The outer program runs after the inner one. The arithmetic equation holds for all internal inputs and intermediate values in arbitrary PA models. |
| Kleene normal form | `Kleene.T₁_primrec`, `U_primrec`, `normal_form_equation`; `ConcreteNormalForm.normalFormGraph_realizes`, `computationPredicate_nat`, `outputGraph_nat` | A checked computation-stage/output coding supplies the standard normal form and its separate PA-uniform bridge to the evaluator graph. |
| Functional Sigma-one realization, `eq:graph-realization` | `SigmaOneRealization.realize_graph`; `ConcreteEvaluator.arithmetization` | Every PA-functional Sigma-one graph has a PA-uniformly realizing concrete index. No unproved realization premise remains in the concrete results. |
| R.e. axioms and partial-program enumeration | `theorem_codes_re_of_axiom_codes`, `axiom_codes_re_of_program_enumerator`, `theorem_codes_re_of_program_enumerator` | The enumerator may be partial and presents its range. Arbitrary r.e. theories do not inherit an extra Delta-one-presentation requirement. |
| Guard, search, and uniformly empty composite, `eq:guard-graph`, `eq:search-graph`, `eq:composite-empty` | `ProofSearch.guard_eval`, `search_eval`, `guard_search_empty`; `ConcreteIndices.guard_search_uniformIndex_empty`, `identity_comp_uniformIndex` | The proof-predicate graph construction and the productive history construction both retain internal graph laws. Their selected numerical witnesses need not be identical. |
| Productive complement of diagonal halting | `Productive`, `complement_diagonal_productive`, `productive_escape_re`; `ConcreteEvaluator.exists_true_unprovable_history_divergence_of_theorem_codes` | The productive function is computable. Consistency, together with Sigma-one completeness for genuine computations, suffices; arbitrary T is not assumed sound. |
| Automatic left compatibility | `ConcreteIndices.pointwiseIndex_comp_left` | Fix the outer program and replace the inner one. The opposite compatibility direction is the obstruction. |
| PA plus all true Pi-one sentences | `PiOneCharacterization.truePiOneExtension`, its standard-model and consistency instances, `truePiOneExtension_piOneComplete`, `truePiOneExtension_theorem_codes_not_re`, `truePiOneExtension_axiom_codes_not_re` in [TruePiOneTheory](TruePiOneTheory.lean) | The exact union is defined. Nonenumerability applies to its entire theorem-code set, so an alternative r.e. axiomatization is excluded as well. |
| Generated quotient is a monoid | `ConcreteIndices.GeneratedQuotient`, `generated_quotient_mul_mk`, `generatedQuotientMulEquiv` | The monoid operation is induced by actual program composition; strict associativity of the numerical compiler is not assumed. |
| Sound quotient is the monoid of unary partial recursive functions | `ConcreteIndices.generatedQuotientPartialRecursiveEquiv` in [PartialRecursiveQuotient](PartialRecursiveQuotient.lean) | A bundled monoid isomorphism to `UnaryPartrec = {f : ℕ → Part ℕ // Nat.Partrec f}`, with actual partial composition. Surjectivity uses the code-existence theorem. |
| Unsound quotient is the one-element monoid; PA specialization | `ConcreteIndices.generated_quotient_subsingleton_iff_not_sound`, `pa_generated_iff_extensional` | Both directions of the singleton characterization are proved. The monoid unit supplies an element. |
| Domain partial identity and R-totality | `ConcreteIndices.domainIndex_realizes`, `domainIndex_graph_equation`, `rTotal_of_pointwise_identity`, `exists_rTotal_not_weaklyTotal_of_re_axioms` in [DomainTotality](DomainTotality.lean) | The domain graph law is PA-uniform. The same productive witness is R-total but not weakly total. |
| Convergence-conservativity consequence | `ConcreteIndices.guard_convergenceAt_provable`, `insert_provable_iff_of_provable`, `montagna_condition_two_not_one`, `not_montagna_condition_two_implies_one` in [ConservativityConsequence](ConservativityConsequence.lean) | Uses actual provability in PA with a convergence axiom inserted. Each external numeral instance is PA-provable; no uniform PA totality proof is claimed. |
| Range equation, `eq:range` | `ConcreteIndices.rangeIndex_realizes`, `rangeIndex_graph_equation`, `rangeIndex_eval` in [RangeAssignment](RangeAssignment.lean) | The existential input ranges over arbitrary PA-model elements. Standard partial-function semantics is proved separately. |
| Every PA-correct choice of range indices fails to descend | `ConcreteIndices.no_quotient_range_of_correct_assignment` in [RangeWitness](RangeWitness.lean) | Independence from the chosen realizing indices is proved. Standard-model agreement alone is not substituted for the PA-uniform graph equation. |

## Additions made by this review

The review closed three omissions in the public statement packaging:

1. The four-witness tuple now preserves uniform provability in its middle
   clauses. `uniformKleeneSentence_iff_uniformSentence` also proves the
   equivalence with the manuscript's uniformly quantified partial-program
   equality formula, rather than relying on an informal encoding convention.
2. The true-Pi-one extension is now an actual named arithmetic theory with
   its model, consistency, completeness, and nonenumerability proved.
3. The sound generated quotient now has a bundled isomorphism to actual
   partial recursive functions, in addition to the earlier graph-quotient
   isomorphism and extensional classification.

## Representation and historical scope

The covered statements use the constructed concrete evaluator and the proved
PA arithmetization laws. PA-uniform representation transport is formalized in
`ArithmetizationTransport` and `ConcreteTransport`. This is stronger than
standard extensional agreement and is the comparison required for provability
quotients.

The proof for arbitrary r.e. axioms uses a deductively equivalent Craig
Delta-one presentation where a proof predicate is needed. It proves the
stated existential obstructions without asserting literal identity with the
manuscript's augmented Feferman derivation codes. The concrete realization,
Pi-one necessity, and productive history arguments are checked proofs of the
stated conclusions; they need not reproduce each displayed historical proof.

Montagna's generated objects have ordinary arithmetic codings. Coding
reindexes an external family of proof obligations; it never licenses moving
the quantifier inside provability. The Lean obstruction is already on
endomorphisms of omega. It therefore suffices for the proposed category's
failure, without constructing every object and morphism of that proposal.

Literal historical code-table identities, all cited auxiliary calculi,
bibliographical assertions, and a full reconstruction of the historical
multiobject syntactic categories are outside the formalization claim.
The chosen global realization selectors are not asserted to be computable.
The dependency separation of productive and Gödel proofs was already proved;
the audits preserve that separation and do not assert logical independence of
two unspecified formal sentences.

## Verification and preparation boundary

The maintained mathematical library has 71 modules plus its umbrella.
The strict style gate re-elaborates all 72 sources with
`linter.mathlibStandardSet=true` and `warningAsError=true`, rejects linter
suppressions, and records source hashes. Diagnostic audit scripts and the
31 pinned evaluator modules are outside this style-editing scope; the
verifier still runs the audits and kernel-replays the evaluator modules.
The complete kernel inventory is 103 modules.

The review is a collaborating-agent semantic review, separately documented in
[`coverage-review.md`](../../Audit/failure-composition-v36/evidence/coverage-review.md).
It is not external human acceptance. Palomar preparation and the author's
arXiv version 37 remain subsequent work.
