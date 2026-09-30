# Manuscript v36: mathematical statements and Lean declarations

This document gives the mathematical content and maintained Lean signatures of
the results in [manuscript v36](../../manuscript/failure_of_composition_2026-09-21_v36.tex).
The manuscript has six numbered results: Theorems 1, 3 and 4, Corollary 2, and
Propositions 5 and 6. It has no numbered lemmas. The nine Palomar selections
separate two proof routes and include an unnumbered monoid consequence; they
are not nine successive manuscript theorem numbers.

The maintained proofs of all nine selections are present. The latest reviewed
verification evidence is for the independently defined cumulative **Eight** pair
at `5435b5b528795590f250a82bf8937779b4fc86b4`, including both proof routes for
the Proposition 6 range counterexample. It passed local Comparator verification
through con-ron, NanoDa, and the Lean default kernel. Selection nine still
awaits migration into the cumulative interface. The
[selection table](#the-nine-palomar-selections) distinguishes these statuses.
This document does not claim a new verification run or registry acceptance.

## Notation and formal scope

Fix the concrete natural-number numbering of unary partial recursive programs
used by this development. Write $C_e(x,y)$ for its arithmetic graph formula,
$\varphi_e$ for its actual partial function, $i$ for the fixed identity
index, and $z$ for the fixed empty-program index. Composition applies the
right program first: $e\bullet d=\operatorname{comp}(e,d)$.

Define equality of partial computations by

$$
E_{e,d}(x)\;:=\;
\bigl((\exists y\,C_e(x,y))\leftrightarrow(\exists y\,C_d(x,y))\bigr)
\land
\bigl((\exists y\,C_e(x,y))\to
       \exists y\,(C_e(x,y)\land C_d(x,y))\bigr).
$$

Thus divergence on both sides counts as equality. The two provability relations
have different quantifier orders:

$$
e\approx_T d\iff \forall n\in\mathbb N\;T\vdash E_{e,d}(\bar n),
\qquad
e\equiv_T d\iff T\vdash\forall x\,E_{e,d}(x).
$$

The quantifier in $\approx_T$ is external and ranges over standard natural
inputs. The quantifier in $\equiv_T$ occurs inside one arithmetic sentence.
Let $Q_T=\mathbb N/{\approx_T}$, with quotient map $q_T$.

| Mathematical notation | Maintained Lean definition and meaning |
| --- | --- |
| $T$, a theory of arithmetic | `FFL.FirstOrder.ArithmeticTheory` |
| $T\supseteq\mathrm{PA}$ | `[𝗣𝗔 ⪯ T]`: deductive extension, which also covers literal inclusion of PA axioms |
| Consistency | `[Consistent T]`: no derivation of falsum; no soundness hypothesis is implicit |
| R.e. axioms | `REPred (FailureOfComposition.AxiomCodes T)`, the codes of the actual axioms of this presentation |
| $\varphi_e$ | `FailureOfComposition.Kleene.eval e : ℕ → Part ℕ`; equality includes equality of domains |
| $C_e$ | `FailureOfComposition.ConcreteEvaluator.eventualGraph e` |
| $e\bullet d$ | `CategoricalRiceShapiro.PartialRecursive.canonicalPartrecCompIndex e d` |
| $i,z$ | `FailureOfComposition.Kleene.identityIndex`, `FailureOfComposition.ConcreteEmptyGraph.concreteEmptyIndex` |
| $e\approx_T d$ | `FailureOfComposition.ConcreteIndices.PointwiseIndex T e d` |
| $e\equiv_T d$ | `FailureOfComposition.ConcreteIndices.UniformIndex T e d`; internally universal graph equality, proved equivalent over PA to the displayed Kleene-equality sentence |
| $Q_T$, $q_T(e)$ | `Quotient (FailureOfComposition.ConcreteIndices.indexSetoid T)`, `Quotient.mk (indexSetoid T) e` |
| True-$\Pi^0_1$ completeness | `FailureOfComposition.PiOneCharacterization.PiOneComplete T`: every true arithmetic $\Pi^0_1$ sentence is provable in $T$ |
| $\Sigma^0_1$ soundness | `FailureOfComposition.GeneratedCongruence.SigmaOneSound T`: every $\Sigma^0_1$ sentence proved in $T$ is true in $\mathbb N$ |
| $e\sim_T d$ | `FailureOfComposition.ConcreteIndices.GeneratedRel T e d`, the intersection of all equivalence relations containing $\approx_T$ and compatible with composition in both arguments |
| $W_T(e)$ | `FailureOfComposition.ConcreteIndices.WeaklyTotalIndex T e`: $\forall d\,[e\bullet d\approx_T z\to d\approx_T z]$ |
| $\rho_e$ | `FailureOfComposition.ConcreteIndices.rangeIndex e`, a selected index with the PA-uniform graph equation $C_{\rho_e}(r,w)\leftrightarrow(r=w\land\exists x\,C_e(x,r))$ |

The equality definitions and their bridges are in
[ProgramIndices](ProgramIndices.lean),
[ConcreteIndexObstruction](ConcreteIndexObstruction.lean), and
[ManuscriptObstruction](ManuscriptObstruction.lean). The concrete evaluator
proves its functionality, composition and realization laws; callers of the
concrete theorems do not supply an arithmetization or realization hypothesis.

The signatures below omit proof bodies. The declaration names are fully
qualified; their other names and notation use this common context:

```lean
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalRiceShapiro.PartialRecursive
open FailureOfComposition
open FailureOfComposition.ConcreteIndices
open FailureOfComposition.ConcreteEmptyGraph
```

## Theorem 1: four witness properties and failure of quotient composition

For every consistent theory $T$ extending PA whose axiom codes are recursively
enumerable, there exist program indices $f,g$ such that

$$
f\approx_T i,\qquad
f\bullet g\equiv_T z,\qquad
i\bullet g\equiv_T g,\qquad
g\not\approx_T z.
$$

Consequently, there is no binary operation $C:Q_T\times Q_T\to Q_T$ satisfying

$$
\forall e,d\in\mathbb N,\qquad
C(q_T(e),q_T(d))=q_T(e\bullet d).
$$

The two middle witness clauses are **uniform**, not merely pointwise. The
maintained witness construction proves them already in PA before weakening
to $T$. The productive proof establishes the existential statement using
the alternative argument in the manuscript; it need not choose the numerical
programs from the manuscript's proof-of-contradiction construction.

[Four-property signature: ManuscriptObstruction](ManuscriptObstruction.lean)

```lean
theorem FailureOfComposition.ConcreteIndices.obstruction_four_properties_of_re_axioms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ∃ f g : ℕ, PointwiseIndex T f Kleene.identityIndex ∧
      UniformIndex T (canonicalPartrecCompIndex f g) concreteEmptyIndex ∧
      UniformIndex T (canonicalPartrecCompIndex Kleene.identityIndex g) g ∧
      ¬PointwiseIndex T g concreteEmptyIndex
```

The no-operation conclusion is named `NoIndexQuotientComposition T`. Its
definition is exactly the negated existence statement above:

```lean
def FailureOfComposition.ConcreteIndices.NoIndexQuotientComposition
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] : Prop :=
  ¬∃ C : Quotient (indexSetoid T) → Quotient (indexSetoid T) →
      Quotient (indexSetoid T),
    ∀ e f, C (Quotient.mk (indexSetoid T) e) (Quotient.mk (indexSetoid T) f) =
      Quotient.mk (indexSetoid T) (canonicalPartrecCompIndex e f)
```

The two routes have the same hypotheses and conclusion:

```lean
theorem FailureOfComposition.ConcreteIndices.no_index_quotient_of_re_axioms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (FailureOfComposition.AxiomCodes T)) :
    NoIndexQuotientComposition T

theorem FailureOfComposition.ConcreteIndices.no_index_quotient_via_godel_of_re_axioms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (FailureOfComposition.AxiomCodes T)) :
    NoIndexQuotientComposition T
```

Sources: [productive route](ConcreteIndexObstruction.lean) and
[Gödel-II route](ConcreteGodelRE.lean). The Gödel-II route obtains a deductively
equivalent Craig presentation internally; the displayed theorem does not assume
that the original axiom predicate is decidable or has a supplied Δ₁ presentation.

## Corollary 2: the categorical obstruction

For every consistent recursively enumerable extension $T$ of PA, the proposed
composition for $S'_T$ fails to define a category: it already fails to be an
operation on the proposed endomorphism classes of $\omega$. In particular,
the failure occurs for the proposed $S'$ at $T=\mathrm{PA}$.

The formal content is the no-operation assertion of Theorem 1, together with
its closed PA specialization:

```lean
theorem FailureOfComposition.ConcreteIndices.pa_no_index_quotient_via_godel :
    NoIndexQuotientComposition 𝗣𝗔
```

Source: [ConcreteGodel](ConcreteGodel.lean). Any category with the proposed
endomorphism set and representative composition equation would supply the
excluded binary operation, before associativity or identity laws are considered.
The formalization does not separately construct all the historical objects and
morphism classes of $S'_T$.

## Theorem 3: the four-way characterization

For every consistent extension $T$ of PA, the following conditions are
equivalent. No enumerability hypothesis is required.

1. For all $f,h,g$, if $f\approx_T h$, then
   $f\bullet g\approx_T h\bullet g$.
2. For all $f,f',g,g'$, if $f\approx_T f'$ and $g\approx_T g'$, then
   $f\bullet g\approx_T f'\bullet g'$.
3. Every true arithmetic $\Pi^0_1$ sentence is provable in $T$.
4. For all $e,d$, $e\approx_T d$ if and only if
   $\varphi_e=\varphi_d$ as partial functions.

The first condition fixes the inner program and replaces the outer one; this
is the manuscript's convention for right compatibility. The formal conjunction
of three adjacent biconditionals expresses all four conditions' equivalence.

```lean
theorem FailureOfComposition.ConcreteIndices.pi_one_characterization
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T] :
    (RightCompatible T ↔ CompositionCongruence T) ∧
    (CompositionCongruence T ↔ PiOneCharacterization.PiOneComplete T) ∧
    (PiOneCharacterization.PiOneComplete T ↔ AgreesWithExtensional T)
```

Source and definitions:
[ConcretePiOneCharacterization](ConcretePiOneCharacterization.lean).

## Theorem 4: the generated composition congruence

For every extension $T$ of PA, let $\sim_T$ be the least equivalence relation
containing $\approx_T$ and compatible with $\bullet$ in both arguments. Then

$$
\sim_T=
\begin{cases}
\{(e,d):\varphi_e=\varphi_d\},&T\text{ is }\Sigma^0_1\text{-sound},\\
\mathbb N\times\mathbb N,&T\text{ is not }\Sigma^0_1\text{-sound}.
\end{cases}
$$

Neither consistency nor recursive enumerability is assumed here. Failure of
Σ₁ soundness includes consistent unsound theories as well as inconsistent ones.

```lean
theorem FailureOfComposition.ConcreteIndices.generated_congruence_classification
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    (GeneratedCongruence.SigmaOneSound T →
      ∀ e d : ℕ, GeneratedRel T e d ↔ Kleene.eval e = Kleene.eval d) ∧
    (¬GeneratedCongruence.SigmaOneSound T → ∀ e d : ℕ, GeneratedRel T e d)
```

Source: [ConcreteGeneratedCongruence](ConcreteGeneratedCongruence.lean).

## Proposition 5: weak totality depends on the representative

For every consistent recursively enumerable extension $T$ of PA, the predicate

$$
W_T(e)\iff\forall d\in\mathbb N\;
       (e\bullet d\approx_T z\to d\approx_T z)
$$

is not invariant under $\approx_T$. More specifically, some member of the
fixed guard family is pointwise provably equal to identity but is not weakly
total, whereas identity is weakly total:

```lean
theorem FailureOfComposition.ConcreteIndices.weak_totality_counterexample_of_re_axioms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ∃ d, PointwiseIndex T (guardIndex d) Kleene.identityIndex ∧
      ¬WeaklyTotalIndex T (guardIndex d) ∧ WeaklyTotalIndex T Kleene.identityIndex
```

The consequent failure of any representing predicate on the quotient is also
proved:

```lean
theorem FailureOfComposition.ConcreteIndices.no_quotient_weak_totality_of_re_axioms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ¬∃ P : Quotient (indexSetoid T) → Prop,
      ∀ e, P (Quotient.mk (indexSetoid T) e) ↔ WeaklyTotalIndex T e
```

Source: [ConcreteWeakTotality](ConcreteWeakTotality.lean). Weak totality is this
cancellation predicate over all program indices; it is not ordinary totality of
the computed partial function.

## Proposition 6: range assignment depends on the representative

For each program $e$, choose a range partial identity $\rho_e$ satisfying
the following graph equation **uniformly in PA**:

$$
\mathrm{PA}\vdash\forall r\,\forall w\;
\bigl(C_{\rho_e}(r,w)\leftrightarrow
       (r=w\land\exists x\,C_e(x,r))\bigr).
$$

For every consistent recursively enumerable extension $T$ of PA, there is an
index $u$ such that

$$
u\approx_T z\quad\text{and}\quad\rho_u\not\approx_T\rho_z.
$$

Consequently, there is no function $R:Q_T\to Q_T$ with
$R(q_T(e))=q_T(\rho_e)$ for every program index $e$.

The Gödel-II and productive proofs have identical theorem signatures:

```lean
theorem FailureOfComposition.ConcreteIndices.range_counterexample_of_re_axioms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ∃ u : ℕ, PointwiseIndex T u concreteEmptyIndex ∧
      ¬PointwiseIndex T (rangeIndex u) (rangeIndex concreteEmptyIndex)

theorem FailureOfComposition.ConcreteIndices.range_counterexample_via_productiveness_of_re_axioms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ∃ u : ℕ, PointwiseIndex T u concreteEmptyIndex ∧
      ¬PointwiseIndex T (rangeIndex u) (rangeIndex concreteEmptyIndex)

theorem FailureOfComposition.ConcreteIndices.no_index_quotient_range_of_re_axioms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) : NoIndexQuotientRange T
```

Sources: [RangeGodel](RangeGodel.lean), [RangeProductive](RangeProductive.lean),
and the definition of `NoIndexQuotientRange` in [RangeWitness](RangeWitness.lean).

The maintained `rangeIndex` is selected by classical choice from a proved
realization theorem. [RangeAssignment](RangeAssignment.lean) proves
`rangeIndex_realizes`, the graph equation in every PA model, and
`rangeIndex_choice_independent`. Replacing it with another PA-uniformly correct
range index preserves its pointwise class, not necessarily its numerical index.
`no_quotient_range_of_correct_assignment` in [RangeWitness](RangeWitness.lean)
extends non-descent to every such assignment. Agreement only in the standard
model is insufficient, and these global selectors are not claimed computable.

## Unnumbered consequence: the generated quotient monoid

The paragraph after Theorem 4 states that $\mathbb N/{\sim_T}$ is the monoid of
unary partial recursive functions when $T$ is Σ₁ sound, and the one-element
monoid otherwise. Multiplication is induced by $\bullet$; the identity class
is the unit. Numerical program composition need not be strictly associative:
the required equalities hold in the quotient.

The target of the sound-case isomorphism is the actual subtype

```lean
def FailureOfComposition.UnaryPartrec :=
  { f : ℕ → Part ℕ // Nat.Partrec f }
```

Its multiplication is partial-function composition:
`(f * g).val x = (g.val x).bind f.val`. Its unit sends `x` to `Part.some x`.
This is not another syntactic graph quotient. The maintained isomorphism and
its representative equation have the following signatures:

```lean
noncomputable def FailureOfComposition.ConcreteIndices.generatedQuotientPartialRecursiveEquiv
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hT : GeneratedCongruence.SigmaOneSound T) :
    GeneratedQuotient T ≃* UnaryPartrec

theorem FailureOfComposition.ConcreteIndices.generatedQuotientPartialRecursiveEquiv_mk
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hT : GeneratedCongruence.SigmaOneSound T) (e : ℕ) :
    generatedQuotientPartialRecursiveEquiv T hT (generatedQuotientMk T e) =
      UnaryPartrec.ofIndex e
```

Here `(UnaryPartrec.ofIndex e).val = Kleene.eval e`. The source proves
surjectivity onto all unary partial recursive functions using Mathlib's
code-existence theorem. No enumerability assumption on $T$ is present.

The ninth Palomar selection packages both facts into one statement:

```lean
theorem FailureOfComposition.Palomar.generated_quotient_partial_recursive
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hT : GeneratedCongruence.SigmaOneSound T) :
    ∃ E : GeneratedQuotient T ≃* UnaryPartrec,
      ∀ e : ℕ, E (generatedQuotientMk T e) = UnaryPartrec.ofIndex e
```

Sources: [PartialRecursiveQuotient](PartialRecursiveQuotient.lean) and the
[legacy nine-result Solution](Palomar/Solution.lean). This ninth selection still
awaits migration into the cumulative interface. The complementary result is:

```lean
theorem FailureOfComposition.ConcreteIndices.generated_quotient_subsingleton_iff_not_sound
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    Subsingleton (GeneratedQuotient T) ↔ ¬GeneratedCongruence.SigmaOneSound T

theorem FailureOfComposition.ConcreteIndices.pa_generated_iff_extensional
    (e d : ℕ) : GeneratedRel 𝗣𝗔 e d ↔ Kleene.eval e = Kleene.eval d
```

Source: [ConcreteGeneratedCongruence](ConcreteGeneratedCongruence.lean). The
monoid unit supplies an inhabitant, so `Subsingleton` here gives a one-element
monoid rather than a possibly empty type.

## Further mathematical assertions in the manuscript

These are auxiliary results, not additional numbered theorems or additional
Palomar selections. Declaration names in this table are prefixed by
`FailureOfComposition.`.

| Mathematical assertion | Maintained declarations and scope |
| --- | --- |
| Kleene normal form and its connection to the concrete arithmetic graph | `Kleene.normal_form_equation` in [KleeneNormalForm](KleeneNormalForm.lean); `ConcreteNormalForm.normalFormGraph_realizes` in [ConcreteNormalForm](ConcreteNormalForm.lean). The PA-uniform graph comparison is separate from standard semantic adequacy. |
| PA-provable composition and realization of every PA-functional Σ₁ graph | `ConcreteEvaluator.eventualGraph_composition` in [ConcreteEvaluatorGraph](ConcreteEvaluatorGraph.lean); `SigmaOneRealization.realize_graph` in [SigmaOneRealization](SigmaOneRealization.lean). |
| R.e. axioms suffice for r.e. theorem codes | `theorem_codes_re_of_axiom_codes` in [TheoryEnumerability](TheoryEnumerability.lean), with explicit partial-program-enumerator variants in [AxiomEnumeration](AxiomEnumeration.lean). |
| Productiveness supplies true divergence unprovable in a consistent r.e. PA extension | `complement_diagonal_productive` and `productive_escape_re` in [Productiveness](Productiveness.lean), followed by the concrete history construction. The productive function is computable; soundness of the ambient theory is not an extra hypothesis. |
| Fixing the outer program preserves pointwise equality of inner programs | `ConcreteIndices.pointwiseIndex_comp_left` in [ConcretePiOneCharacterization](ConcretePiOneCharacterization.lean); requires PA extension only. |
| PA plus all true Π₁ sentences is consistent, Π₁ complete and not r.e. | `PiOneCharacterization.truePiOneExtension`, its standard-model and consistency instances, `PiOneCharacterization.truePiOneExtension_piOneComplete`, `PiOneCharacterization.truePiOneExtension_theorem_codes_not_re`, and `PiOneCharacterization.truePiOneExtension_axiom_codes_not_re` in [TruePiOneTheory](TruePiOneTheory.lean). Nonenumerability of all theorem codes also excludes an alternative r.e. axiomatization with the same consequences. |
| Equality with identity implies the domain-based R-totality condition | `ConcreteIndices.rTotal_of_pointwise_identity` in [DomainTotality](DomainTotality.lean); requires PA extension only. |
| Every consistent r.e. PA extension has an R-total index that is not weakly total | `ConcreteIndices.exists_rTotal_not_weaklyTotal_of_re_axioms` in [DomainTotality](DomainTotality.lean); domain assignment retains its PA-uniform graph equation. |
| Pointwise convergence-conservativity does not imply index weak totality over PA | `ConcreteIndices.montagna_condition_two_not_one` and `ConcreteIndices.not_montagna_condition_two_implies_one` in [ConservativityConsequence](ConservativityConsequence.lean). The convergence axiom at each external standard input is already PA-provable; no single uniform totality proof is asserted. |

## The nine Palomar selections

All selected names below have prefix `FailureOfComposition.Palomar.`. Corresponding maintained
names have prefix `FailureOfComposition.ConcreteIndices.`. The legacy
[Challenge](Palomar/Challenge.lean)/[Solution](Palomar/Solution.lean) pair contains
all nine. The independently defined cumulative
[SolutionEight at the tested commit](https://github.com/flengyel/FailureOfComposition/blob/5435b5b528795590f250a82bf8937779b4fc86b4/Lean/FailureOfComposition/Palomar/SolutionEight.lean)
contains the first eight, with explicit independent arithmetic theory, extension,
consistency and r.e.-axiom predicates. These separate environments reuse the
selected declaration names; the legacy and independent signatures are connected
by proved correspondence, not asserted to be the same raw representation.

The locally verified source at `5435b5b528795590f250a82bf8937779b4fc86b4` includes
[ChallengeEight](https://github.com/flengyel/FailureOfComposition/blob/5435b5b528795590f250a82bf8937779b4fc86b4/Lean/FailureOfComposition/Palomar/ChallengeEight.lean),
[SolutionEight](https://github.com/flengyel/FailureOfComposition/blob/5435b5b528795590f250a82bf8937779b4fc86b4/Lean/FailureOfComposition/Palomar/SolutionEight.lean),
[RangeBridge](https://github.com/flengyel/FailureOfComposition/blob/5435b5b528795590f250a82bf8937779b4fc86b4/Lean/FailureOfComposition/Palomar/RangeBridge.lean),
and [RangeProductiveBridge](https://github.com/flengyel/FailureOfComposition/blob/5435b5b528795590f250a82bf8937779b4fc86b4/Lean/FailureOfComposition/Palomar/RangeProductiveBridge.lean).
The evidence below records the cumulative Eight acceptance and the separate
correspondence and dependency routes for both Proposition 6 selections.

| Selection | Mathematical statement | Corresponding maintained declaration | Independent cumulative status |
| --- | --- | --- | --- |
| `obstruction_four_properties` | Theorem 1, four witness properties including two uniform clauses | `obstruction_four_properties_of_re_axioms` | Locally verified in Eight |
| `no_quotient_composition_productive` | Theorem 1 consequence / Corollary 2, productive route | `no_index_quotient_of_re_axioms` | Locally verified in Eight |
| `no_quotient_composition_godel` | Same no-operation statement, Gödel-II route | `no_index_quotient_via_godel_of_re_axioms` | Locally verified in Eight |
| `pi_one_characterization` | Theorem 3 | `pi_one_characterization` | Locally verified in Eight |
| `generated_congruence_classification` | Theorem 4 | `generated_congruence_classification` | Locally verified in Eight |
| `weak_totality_counterexample` | Proposition 5, explicit guard witness | `weak_totality_counterexample_of_re_axioms` | Locally verified in Eight |
| `range_counterexample_godel` | Proposition 6, Gödel-II route | `range_counterexample_of_re_axioms` | Locally verified in Eight |
| `range_counterexample_productive` | Proposition 6, productive route | `range_counterexample_via_productiveness_of_re_axioms` | Locally verified in Eight |
| `generated_quotient_partial_recursive` | Unnumbered sound generated-quotient monoid consequence | `generatedQuotientPartialRecursiveEquiv` and its `_mk` theorem | Maintained proof; migration pending |

For the latest reviewed verification checkpoint, Eight, see the
[verification record](../../Audit/palomar-eight-productive-range-20260930/RESULT.json)
and [correspondence record](../../Audit/palomar-eight-productive-range-20260930/CORRESPONDENCE.md).
Those records concern local checks, including Comparator, at the recorded pins.
They are not a verification of a nine-result eligible pair or a Palomar
publication/acceptance record. Productive and Gödel-II routes are distinguished
by declaration dependencies, not by a claim of logical independence.

## Representation and historical limits

The concrete statements fix Mathlib's program numbering and the constructed
PA arithmetization. There are also genuine parameterized results. For example,
`FailureOfComposition.ProgramIndices.no_index_quotient_of_re_axioms` in
[ConcreteIndexObstruction](ConcreteIndexObstruction.lean) takes an explicit
`ProgramIndices.Arithmetization`. That structure supplies standard adequacy,
PA-provable functionality and composition, and PA-uniform realization of every
PA-functional Σ₁ graph. [ArithmetizationTransport](ArithmetizationTransport.lean)
proves quotient-set equivalence and preservation of representative composition
for structures with these laws; [ConcreteTransport](ConcreteTransport.lean)
specializes the comparison to the concrete evaluator. The selected translations
are not asserted computable.

These results do not identify arbitrary representations from standard
extensional agreement alone. They do not assert literal equality with historical
program code tables, augmented Feferman derivation codes, or chosen binumerations
of proof predicates. Nor do they reconstruct every object and morphism of the
historical multiobject syntactic categories. The categorical conclusion uses the
documented identification of the proposed endomorphisms of $\omega$ with the
pointwise program quotient. Bibliographical claims and assertions about what
earlier authors stated remain mathematical and historical exposition, rather
than Lean theorem declarations.
