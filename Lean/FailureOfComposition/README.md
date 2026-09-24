# FailureOfComposition: quotient obstructions and the generated congruence

**For every extension of PA, the least composition congruence containing
pointwise provable equality is extensional equality when the theory is
Sigma-one sound, and the universal relation otherwise.** Neither consistency
nor recursive enumerability is assumed.
For consistent extensions, pointwise provable equality itself is a composition
congruence exactly when the theory proves every true Pi-one sentence; in that
case it is extensional equality of the computed partial functions.
For recursively enumerable axiom codes, the concrete obstruction is also proved
by two independent routes. The quotient uses
natural-number Mathlib program indices, the production history evaluator's
arithmetical graphs, and Montagna's external pointwise provability relation.
The theorem has no `Arithmetization` or graph-realization hypothesis.
The concrete weak-totality and range-assignment obstructions are also proved.

The development now constructs the complete arithmetization, including
realization of every PA-functional Sigma-one graph. PA-provable translations
compare its representation with any other arithmetization satisfying the
manuscript's stated laws. The [coverage map](MANUSCRIPT_COVERAGE.md) records
all numbered results and the covered program-index consequences. Literal historical code-table
identities and a reconstruction of every historical syntactic category
remain outside that formalization claim. The maintained library lives in
`Lean/FailureOfComposition/`, uses the namespace `FailureOfComposition`, and
is included in the main Lean project. Import its umbrella with
`import FailureOfComposition`. Library theorem and module names below
are abbreviated relative to this namespace.

From the repository root, build the library and run its checks with:

```sh
./scripts/syncfailcomp.sh --check-environment
./scripts/syncfailcomp.sh
```

Review and verification records remain under
`Audit/failure-composition-v36/evidence/`. The native Lake build, theorem and
dependency audits, all 72 strict style checks, and all 103 kernel replays
passed. The final [manuscript coverage review](MANUSCRIPT_COVERAGE.md)
is complete for the stated program-index scope.

The [Palomar preparation draft](Palomar/README.md) packages nine selected claims
and their proved counterparts with provenance metadata and a local comparison
check. Its deliberate Challenge holes are outside the production umbrella and
the 72-source style gate. The Solution is checked separately without holes.
Palomar eligibility remains blocked by the newer required toolchain and the
Challenge's Foundation/project import closure; see the draft for the exact
remaining steps. The author's successful full WSL mirror run is recorded as
user-reported evidence, separately from checks performed here.

## Main result

The productiveness theorem is

```lean
FailureOfComposition.ConcreteIndices.no_index_quotient_of_re_axioms
  (T : ArithmeticTheory) [PA ⪯ T] [Consistent T]
  (hT : REPred (FailureOfComposition.AxiomCodes T)) :
  FailureOfComposition.ConcreteIndices.NoIndexQuotientComposition T
```

The independent second-incompleteness theorem has exactly the same hypotheses:

```lean
FailureOfComposition.ConcreteIndices.no_index_quotient_via_godel_of_re_axioms
  (T : ArithmeticTheory) [PA ⪯ T] [Consistent T]
  (hT : REPred (FailureOfComposition.AxiomCodes T)) :
  FailureOfComposition.ConcreteIndices.NoIndexQuotientComposition T
```

Neither theorem requires a Delta-one presentation of `T`, soundness of `T`,
or a supplied realization law. The proof-dependency audit excludes Gödel II
from the productive route and excludes productiveness from the Gödel-II route.

Here `PA` denotes Lean's `𝗣𝗔`, and

\[
G_e(x,y)\equiv\exists s\,C(s,\bar e,x,y),
\qquad C=\texttt{evalnCertificateFormula}.
\]

`PointwiseIndex T e f` means that, for every **external** natural number `n`,
`T` proves the manuscript's definedness/common-value equality of `G_e` and
`G_f` at the numeral `n`. PA-provable functionality makes this equivalent to
provable equality of their output graphs. It does not mean that `T` proves a
single universally quantified equality.

`NoIndexQuotientComposition T` excludes every binary operation on this quotient
whose value on classes of `e,f` is the class of the actual
`canonicalPartrecCompIndex e f`. Thus it rules out induced program composition,
not merely a particular implementation of quotient lifting.

There are also variants assuming r.e. theorem codes, a Foundation Delta-one
axiom presentation, or an explicit partial-recursive axiom enumerator.
`ProgramIndices.no_index_quotient_of_re_axioms` supplies the corresponding
general-numbering conclusion under the manuscript's explicit
`Arithmetization` assumptions. The interface retains those assumptions when
the arithmetization is arbitrary; `ConcreteEvaluator.arithmetization`
discharges them for the concrete proofs.

## Generated composition congruence

`CompositionClosure.Generated` is the intersection of all equivalence
relations preserved by the given binary operation and containing the given
generating relation. Its closure laws and leastness are proved without
arithmetic assumptions. For concrete program indices,
`ConcreteIndices.GeneratedRel T` uses the actual
`canonicalPartrecCompIndex` and `PointwiseIndex T` as its generators.

The main theorem is

```lean
FailureOfComposition.ConcreteIndices.generated_congruence_classification
  (T : ArithmeticTheory) [PA ⪯ T] :
  (GeneratedCongruence.SigmaOneSound T →
    ∀ e d, GeneratedRel T e d ↔ Kleene.eval e = Kleene.eval d) ∧
  (¬GeneratedCongruence.SigmaOneSound T →
    ∀ e d, GeneratedRel T e d)
```

`SigmaOneSound T` means that every Sigma-one sentence proved by `T` is true
in the natural numbers. It is connected explicitly to Foundation's
`SoundOnHierarchy 𝚺 1` class. The concrete theorem requires no arithmetization,
realization, consistency, or presentation hypothesis beyond the displayed
extension of PA. `pa_generated_iff_extensional` specializes the result to PA.

The central inclusion, `extensional_implies_generated`, is unconditional for
PA extensions. The proof uses the manuscript's least-computation construction,
implemented with the least successful stage of the checked history evaluator:

- `HGraph e` returns the pair of that stage and its input.
- `BGraph e` reads the indicated computation.
- `AGraph e G` reads the same computation and requires the output to satisfy
  `G` at the decoded input.

The minimum graph is Sigma-one because unsuccessful stages are expressed by
the positive Sigma-one assertion that the total history evaluator returns
zero. PA proves its equivalence to absence of a successful computation at
that stage. No bounded negation of an arbitrary Sigma-one formula is treated
as Sigma-one. Least-stage existence and all functionality and composition
equations hold in arbitrary PA models.

When `eventualGraph e` and `G` agree on the natural numbers, the outer witness
graphs are pointwise PA-provably equal. At each standard pair of stage and
input, a true ground equation fixes the evaluator's output in every PA model.
In the successful case, a true ground instance of `G` is PA-provable by
Sigma-one completeness. Thus all internal output candidates are accounted
for. Composing with `HGraph e` identifies `eventualGraph e` with its
intersection with `G`. Repeating the construction in the other direction,
using symmetry of conjunction and PA-provable realization, proves the
unconditional inclusion for all functional Sigma-one graphs.

Under Sigma-one soundness, pointwise provability implies standard graph
equality. Standard graph equality is a congruence, so leastness gives the
reverse inclusion. In the unsound case, choose a false proved Sigma-one
sentence `σ`. The graph `σ ∧ y = x` is provably equal to identity in `T`
and extensionally empty. The unconditional inclusion therefore identifies
identity with the empty graph; composing gives the universal relation.
The final theorem supplies the proved inclusion internally, with no such
premise left to the caller.

The index–graph transfer respects composition through its PA-uniform graph
equations. No strict equality of the selected indices is assumed. Quotients
by the generated congruence carry induced monoid operations. Their index and
functional-graph presentations are connected by the constructed monoid
isomorphism `generatedQuotientMulEquiv`. Multiplication of concrete index
classes is definitionally the class of `canonicalPartrecCompIndex`.
The quotient is a singleton exactly when Sigma-one soundness fails. The development keeps
this quotient construction distinct from any separately packaged isomorphism
to a subtype of partial-recursive functions.

## Pi-one completeness characterization

`PiOneCharacterization.PiOneComplete T` means that every arithmetic sentence
in `Hierarchy 𝚷 1` which is true in the natural numbers is provable in `T`.
The concrete theorem is

```lean
FailureOfComposition.ConcreteIndices.pi_one_characterization
  (T : ArithmeticTheory) [PA ⪯ T] [Consistent T] :
  (RightCompatible T ↔ CompositionCongruence T) ∧
  (CompositionCongruence T ↔ PiOneCharacterization.PiOneComplete T) ∧
  (PiOneCharacterization.PiOneComplete T ↔ AgreesWithExtensional T)
```

Here right compatibility replaces the outer program while fixing the inner
one. `CompositionCongruence` preserves the equivalence in both arguments of
the actual `canonicalPartrecCompIndex`. `AgreesWithExtensional T` is the
statement `∀ e d, PointwiseIndex T e d ↔ Kleene.eval e = Kleene.eval d`.
The equality on the right is equality of partial functions on the natural
numbers. The external input quantifier in `PointwiseIndex` is unchanged.

The eight characterization modules prove the following steps.

- `PiOneNecessity` applies the PA proof-search obstruction to `¬θ`, where `θ`
  is a true Pi-one sentence omitted by `T`. PA has no proof of `¬θ` by its
  standard soundness. Internal Sigma-one completeness supplies the theorem
  `¬θ → Prov_PA(¬θ)`. Thus a `T`-proof of `¬Prov_PA(¬θ)` would prove `θ`.
  The existing guard and search graphs therefore contradict right
  compatibility. This implication requires only `PA ⪯ T`.
- `PiOneExtensionality` first derives Sigma-one soundness from consistency and
  Pi-one completeness. It then proves the two directions of agreement with
  extensional equality. Common values use PA proofs of ground computations
  and PA functionality; joint divergence uses true Pi-one sentences. The
  internal output quantifier ranges over arbitrary PA-model elements.
- `PiOneCongruence` proves automatic left compatibility and the equivalence
  between right compatibility and full congruence. `PiOneCharacterization`
  assembles the graph theorem, and `PiOneIndexCharacterization` transports it
  using PA-provable realization and composition. The concrete wrapper supplies
  the fully constructed arithmetization, so its callers supply no realization
  or numbering law.
- `QuotientComposition` proves that an operation satisfying the representative
  composition law exists exactly when the equivalence is a congruence. Hence
  `ConcreteIndices.no_index_quotient_iff_not_piOneComplete` characterizes
  failure of induced quotient composition exactly by failure of Pi-one
  completeness.

The public characterization assumes neither recursive enumerability, a
Delta-one presentation, nor soundness of `T`. Its dependency audit excludes
both the productive-set theorem and Gödel II. The proof of internal Sigma-one
completeness is used directly; no converse reflection implication is assumed.

## Concrete witnesses and proof

All constructor graph equations are proved in arbitrary PA models, including
nonstandard stages, inputs, outputs, and minimization candidates. An explicit
structural compiler translates every Foundation `Nat.ArithPart₁.Code n` into
Mathlib `Nat.Partrec.Code`. `computes_compile` proves graph preservation for
all finite arities; `unaryCompile_realizes` gives a PA proof of uniform
realization on ordinary unary inputs. No compiler-correctness field is assumed.

For a standard index `d`, let `h_d(s)` be the history evaluator applied to
`(s,d,d)`. Its output is zero when no successful computation is recorded at
that stage, and `y+1` when the recorded output is `y`. The arithmetic programs
`guardCode d` and `searchCode d` have PA-provable graphs

\[
F_d(x,y)\leftrightarrow h_d(x)=0\land y=x,
\]
\[
S_d(x,y)\leftrightarrow
 h_d(y)>0\land\forall r<y\,h_d(r)=0.
\]

Their indices are explicitly `encode (unaryCompile (guardCode d))` and
`encode (unaryCompile (searchCode d))`. These are new compiler-produced
witnesses, not identifications with the older indices selected by classical
choice. The identity index is 48; the previous explicit empty witness has
index 11.

Productiveness supplies a genuinely divergent diagonal program `d` for which
`T` does not prove the negation of the **actual history formula**
`∃ s y, C(s,d,d,y)`. Consistency suffices: Sigma-one completeness prevents `T`
from proving any false divergence sentence. No soundness of `T` is assumed.

For each standard input `n`, Sigma-one completeness proves `h_d(n)=0`, so
`F_d` is pointwise provably equal to identity. PA proves `F_d ∘ S_d` empty and
`identity ∘ S_d` equal to `S_d`. If these composites were pointwise provably
equal, the input-zero instance, together with PA's least-number principle,
would prove the excluded divergence sentence. The compiler's PA graph
identities transfer this contradiction to concrete natural-number indices.

The theorem-code premise is discharged separately in `TheoryEnumerability`.
It enumerates finite lists of axioms together with pure-logic proofs of their
finite implications. The theorem
`theorem_codes_re_of_axiom_codes` requires only r.e. axiom codes, not a
Delta-one presentation, consistency, or soundness. `AxiomEnumeration` connects
this premise to the partial-recursive range presentation used in v36.

## Full Sigma-one realization

`SigmaOneRealization.semidecision_exists` proves, for every Sigma-one formula
with any finite number of inputs, the existence of a concrete program that
returns zero exactly when the formula holds. The selected standard program
works for every input vector in every PA model. The proof covers all ten
cases of Foundation's Sigma-one induction principle:

- Arithmetic terms and atomic formulas have exact arithmetic-code evaluations.
- Pairing semideciders realizes conjunction.
- Disjunction and existential quantification use bounded-history dovetailing.
  They do not search sequentially through possibly divergent candidates.
- Bounded universal quantification uses actual primitive recursion. A formula
  induction in PA proves correctness even at nonstandard bounds.

For a binary formula, fair search returns a successful output candidate.
PA-provable functionality ensures that every successful candidate is the
required output. Completeness then gives the uniform PA graph equation:

```lean
SigmaOneRealization.realize_graph
  (F : ProofSearch.Graph) (hF : ProofSearch.Functional F) :
  ∃ e, ProofSearch.Uniform PA (ConcreteEvaluator.eventualGraph e) F
```

`ConcreteEvaluator.arithmetization` fills every field of the earlier
`ProgramIndices.Arithmetization` interface with proved concrete results.
It has no parameters. The formula proof is a structural existence theorem
using explicit program combinators; no packaged computable global
formula-to-program function is claimed.

## Independent Gödel-II route and r.e. presentations

`ConcreteIndices.no_index_quotient_via_godel` first handles a theory with a
Foundation Delta-one presentation. It realizes the earlier proof-search graph
witnesses using the newly proved formula realization theorem, and invokes
second incompleteness. The dependency audit verifies that this route does not
use the productive-set proof.

`CraigPresentation.exists_craig_presentation` removes the presentation
restriction. For an arbitrary theory with r.e. axiom codes, it constructs a
deductively equivalent theory with an axiom predicate provably Delta-one over
**IΣ1**, as required by Foundation's proof predicate.

The construction represents the original axiom set by a fixed Sigma-one
formula `A(n)`. An original axiom is padded with a logical tautology containing
a PA-proof code for `A` applied to that axiom's code. Sigma-one completeness
and the standard-model soundness of **PA** provide exactly these certificates;
no soundness of the original theory is used. The existing PA-proof checker,
syntax operations, and bounded padding checks give the IΣ1-provable Delta-one
presentation. Removing or adjoining the tautology proves equivalence of the
two deductive closures.

The Gödel-II noncongruence witnesses for this presentation transport to the
original theory because the pointwise relation depends only on its theorems.
`ConcreteGodelRE` thus establishes the same r.e.-axiom theorem and explicit
axiom-enumerator specialization as the productive route.

## Representation transport

`ArithmetizationTransport` selects PA-uniform graph translations between any
two arithmetizations satisfying the stated realization laws. It proves:

- exact preservation and reflection of external pointwise provability;
- an equivalence of the quotient **sets**;
- preservation of composition on representative classes.

No quotient composition is assumed in these statements, so this is not a
claim of equivalence between categories whose construction is obstructed.
`ConcreteTransport` specializes the target to the fully constructed history
arithmetization. These are selected translations by classical choice; no
computable map between arbitrary historical numerical code tables is asserted.
The PA-uniform graph equations, rather than agreement only over standard
naturals, justify the transport.

## Evaluator and normal-form correspondence

`ConcreteEvaluator.stageComputation_iff_evaln` (in module
`ConcreteAdequacy`) proves exact standard-stage agreement
between the raw history certificate and Mathlib's `Code.evaln`. Stage induction
and program-constructor induction cover all constructors. Consequently

\[
G_e(x,y)\iff y\in\operatorname{eval}(e,x)
\iff\exists w\,(T_1(e,x,w)\land U(w)=y)
\]

on the standard naturals, for the concrete `T₁,U` already defined in
`KleeneNormalForm`.

`ConcreteNormalForm` supplies an explicit arithmetic computation predicate by
pairing a stage with its output and an arithmetic graph for the output
projection. It proves their standard correspondence with that `T₁,U` and a
**PA-provable** equivalence of the resulting normal-form graph with `G_e`.
Thus the concrete construction has both standard adequacy and its own
internal normal-form correspondence.

The manuscript fixes an acceptable numbering and assumes PA functionality,
composition, and functional Sigma-one graph realization. The general theorem
is proved under those stated properties; the concrete arithmetization now
proves every one of them, including general graph realization. Standard
agreement alone does not
prove PA equivalence to a different arithmetic representation. No translation
to unspecified literal formula syntax in Montagna, Di Paola--Montagna, or
Odifreddi is claimed, and no manuscript convention has been silently changed.

## Concrete weak totality and R totality

[`ConcreteWeakTotality`](ConcreteWeakTotality.lean) uses the concrete identity and empty indices and the
compiler's composition operation to define

\[
W_T(e)\;\Longleftrightarrow\;
\forall d\in\mathbb N,\quad
\operatorname{comp}(e,d)\approx_T z\;\Longrightarrow\;d\approx_T z.
\]

For every consistent extension of PA with recursively enumerable axiom codes,
`ConcreteIndices.weak_totality_counterexample_of_re_axioms` constructs a guard
index pointwise provably equal to identity but not weakly total. Identity is
weakly total. The associated search is an explicit witness: composing the
guard with it is pointwise provably empty, while the search itself is not.
`no_quotient_weak_totality_of_re_axioms` rules out any predicate on the
pointwise quotient that represents this index predicate. The theorem is also
provided for an explicit program enumerating the axioms and for Delta-one
axiom presentations. Its existence proof uses productiveness, without Godel II.

[`DomainTotality`](DomainTotality.lean) realizes a concrete domain index with the PA-uniform equation

\[
C_{d_e}(x,y)\;\Longleftrightarrow\;
x=y\land\exists v\,C_e(x,v).
\]

`RTotal T e` is the index condition `PointwiseIndex T (domainIndex e)
Kleene.identityIndex`. Pointwise provable equality with identity implies this
condition. The same guard is therefore R total but not weakly total, both for
the general consistent r.e. extension and in a closed PA specialization. The
domain index is selected by classical choice from the proved graph-realization
theorem; no computability claim about this selector is needed here.

[`ConservativityConsequence`](ConservativityConsequence.lean) defines conservativity using the actual theory
`insert σ PA`: every Pi-one sentence provable in that theory must be provable
in PA. Each standard-input convergence sentence of the guard is already
PA-provable. Adjoining any one of those sentences preserves **all** theorems,
so in particular it is Pi-one conservative. Nevertheless the guard fails
weak totality. `montagna_condition_two_not_one` and
`not_montagna_condition_two_implies_one` formalize this counterexample to the
program-index reading of Montagna's Theorem 2.3. The input quantifier remains
external: this does not assert a single PA proof of uniform convergence.

These results use the manuscript's history-predicate variant of the guard.
They do not assert literal identity with Montagna's chosen proof binumeration.

## The range-assignment obstruction

[`RangeAssignment`](RangeAssignment.lean) realizes a range index `rangeIndex e`
with the PA-uniform graph equation

\[
C_{\rho_e}(r,w)\;\Longleftrightarrow\;
r=w\land\exists x\,C_e(x,r).
\]

The existential input ranges over arbitrary elements of every PA model.
`rangeIndex_eval` separately identifies the standard partial function as the
partial identity on the set-theoretic range of `Kleene.eval e`. The selected
index comes from the proved Sigma-one realization theorem; callers supply no
arithmetization or realization hypothesis. Any two indices satisfying this
PA-uniform equation are PA-uniformly equivalent, hence have the same
pointwise quotient class. No computability claim about the classical selector
is needed.

[`RangeWitness`](RangeWitness.lean) proves the common argument. Its probe has
graph `P(p) ∧ y = 0`. Separate PA refutations of every standard instance
`P(n)` make the probe pointwise equal to the concrete empty index. Its range
at input/output zero expresses the internally quantified sentence `∃ p, P(p)`.
Thus equality of the two range programs at the single standard input zero
would prove `∀ p, ¬P(p)` in T. The proof preserves the distinction between
`∀ n, T ⊢ ...` and `T ⊢ ∀ p, ...` throughout.

[`RangeGodel`](RangeGodel.lean) instantiates P with the proof-of-contradiction
predicate. Consistency provides the numeralwise PA refutations; Gödel's second
incompleteness theorem excludes uniform absence. The principal theorem is

```lean
FailureOfComposition.ConcreteIndices.range_counterexample_of_re_axioms
  (T : ArithmeticTheory) [PA ⪯ T] [Consistent T]
  (hT : REPred (AxiomCodes T)) :
  ∃ u : ℕ, PointwiseIndex T u ConcreteEmptyGraph.concreteEmptyIndex ∧
    ¬PointwiseIndex T (rangeIndex u)
      (rangeIndex ConcreteEmptyGraph.concreteEmptyIndex)
```

Craig's deductively equivalent Delta-one presentation removes the presentation
restriction on T. The same program and range indices transport between the
two theories. This matches the manuscript's existential counterexample; it
does not identify the selected presentation's proof codes literally with the
manuscript's augmented derivation codes. Explicit axiom-enumerator and closed
PA specializations are also provided.

[`RangeProductive`](RangeProductive.lean) gives an independent proof from a
true unprovable diagonal-history divergence. The probe tests positive history
at the supplied stage. Each standard stage has a PA-certified zero history
result, while uniform absence would prove the excluded divergence sentence.
This route uses the existing productive-set theorem and does not use Gödel II.
The established dependency separation for the earlier composition proofs is
extended to these two range proofs.

`NoIndexQuotientRange T` rules out every unary operation on the actual pointwise
quotient whose value on `[e]` is `[rangeIndex e]`.
`no_quotient_range_of_correct_assignment` extends the conclusion to every
assignment `ρ : ℕ → ℕ` satisfying the PA-uniform range equation. Consequently,
non-descent is independent of the chosen realizing indices.

## Final manuscript coverage

The [coverage map](MANUSCRIPT_COVERAGE.md) compares the six numbered results,
their definitions, and their program-index consequences with the checked
declarations and hypotheses. The review closed three statement-packaging gaps:

- [ManuscriptObstruction](ManuscriptObstruction.lean) retains uniform
  T-provability in Theorem 1's middle clauses. It also proves the PA equivalence
  between uniform output-graph equality and the manuscript's uniformly
  quantified definedness/common-value formula.
- [TruePiOneTheory](TruePiOneTheory.lean) defines PA plus all true Pi-one
  sentences, proves its consistency and Pi-one completeness, and proves that
  neither its theorem codes nor its axiom codes are recursively enumerable.
- [PartialRecursiveQuotient](PartialRecursiveQuotient.lean) constructs the
  monoid of actual unary partial recursive maps and the bundled monoid
  isomorphism from the generated quotient of every Sigma-one sound PA extension.

The historical coding and multiobject boundaries remain explicit in the map.
The exact mathematical hypotheses are audited. All 230 declaration types
from the preceding milestone's type audit are unchanged after style cleanup.

## Montagna's objects and quantification

Montagna (1989), pp. 105–107, generates objects from `ω` by binary products and
disjoint unions and codes their elements by natural numbers. On p. 106 the
input quantifier is outside PA provability; on p. 107 he explicitly restricts
the discussion to arrows `ω → ω`. Di Paola--Montagna (1991), p. 646, uses the
corresponding external conjunction for `T`.

Failure in the proposed `End(ω)` already prevents the proposed category
construction. Coding reindexes the external family; it does not replace
`∀ n, T ⊢ E(n̄)` with `T ⊢ ∀ x, E(x)`. There is no remaining obligation to
transport the obstruction separately across every generated object.

## Remaining scope

- The required representation comparison is proved under the manuscript's
  explicit arithmetization laws. Literal identity with a separately specified
  historical formula or numerical code table is not claimed.
- The manuscript coverage and strict style gates have passed. The next
  milestone is preparation of the Lean code for Palomar; the author will
  then prepare version 37 for arXiv with the formalization description.
- External human acceptance remains separate from the checked development.

Full PA graph realization, both concrete obstruction proofs, their
arbitrary-r.e.-axiom bridges, the Pi-one characterization, and the generated
congruence classification, concrete weak-totality obstruction, R-totality
contrast, conservativity consequence, and range-assignment obstruction are
discharged. The completed [coverage review](MANUSCRIPT_COVERAGE.md)
records the exact statements, proof variants, and representation boundaries.

## Native verification and historical provenance

For a source checkout on `/mnt/c`, use `./scripts/syncfailcomp.sh` from the
repository root. It synchronizes the required sources into the persistent Linux
mirror `${FAILCOMP_DST:-$HOME/src/FailureOfComposition}` and keeps build output,
logs, and temporary package metadata there. It shares the existing PCats
checkouts, without copying dependencies. The default Lake worker pool and
number of simultaneous style processes are both one; this reduces scheduling
concurrency but does not impose an aggregate memory limit.

For a Git checkout already on the Linux filesystem, the direct verifier is
also available. From the repository's `Lean/` directory, run:

```sh
./FailureOfComposition/verify.sh --check-environment
./FailureOfComposition/verify.sh
```

From the repository root, the equivalent entry point is
`./scripts/verify-failure-composition.sh`. Both use the existing pinned
dependency checkouts under `${PCATS_DST:-$HOME/src/PCats}/.lake/packages`, or
the directories in a validated `CRS_LAKE_PACKAGES` mapping. The environment
check uses bare `lean --version` and invokes no Lake command. Full verification
passes a canonical path override to every Lake invocation and revalidates the
checkouts afterward. It never clones or updates dependencies.

The external PCats configuration does not need additional library entries.
`syncpcats.sh` continues to mirror its four original libraries; this verifier
builds the maintained sources in the repository's `Lean/` root. See the
[WSL workflow](../../scripts/README.md#failure-of-composition-verification-in-wsl)
for details. Do not substitute bare `lake env` for the environment check:
Lake may resolve and clone dependencies before running its requested command.

Native verification passed on 2026-09-24 using existing external dependency
checkouts, with no repository-local `.lake/packages` directory before or after
the run. This was tested in the Linux verification runtime. The author has
reported a successful WSL environment check; full WSL verification remains
pending after a reported system crash. The native library build, theorem
types, axiom/dependency audits, and all 103 kernel replays passed with no
warnings in the maintained mathematical library. Its inventory consists of
71 `FailureOfComposition` mathematical modules, the umbrella, and 31 pinned
`CategoricalRiceShapiro` evaluator modules.

The repeatable strict style gate, `python3 FailureOfComposition/check_style.py`,
re-elaborates all 72 maintained mathematical sources with Mathlib's standard
linters explicitly enabled and all warnings treated as errors. It rejects
linter suppressions and records the source hash for each check. Audit helper
commands and pinned evaluator/dependency sources are outside this style-editing
scope; the helper commands and evaluator kernel checks still run separately.
The gate passed with zero diagnostics and no suppressions. Unnecessary global
heartbeat overrides were removed; the one required override is documented
and scoped to `CraigPresentation.axiom_proof_iff`.

The verifier checks the toolchain and dependency pins, builds the maintained
library, inspects theorem types and axiom dependencies, checks proof dependency
closures, and kernel-replays `FailureOfComposition` and the imported
`CategoricalRiceShapiro` modules. The productive theorem is checked for absence
of `Arithmetization`, Gödel-II, and `sorryAx` dependencies. The Gödel-II roots
must depend on `consistent_unprovable` and must not depend on productiveness.
General realization and the Craig bridge are audited separately. The
characterization roots are checked for absence of productive-set, Gödel-II,
and `sorryAx` dependencies; the generated-congruence roots are additionally
checked for absence of a Pi-one-completeness dependency. The 13 weak-totality,
domain-realization, and conservativity audit roots have no arithmetization
parameter, Godel-II, or `sorryAx` dependency.
The range audits extend the same checks: the generic range construction and
probe argument use neither obstruction proof, the productive range route
excludes Gödel II, and the Gödel range route must use `consistent_unprovable`
while excluding productiveness. Their axiom envelope is checked separately.
All 27 range dependency-audit roots passed. The productive roots explicitly
depend on `productive_escape_re` and `diagonal_escape`.

The native run used these pins:

- Lean 4.32.2, compiler `f3b06c705e6c85f5314019d5d3baab0fec5b580c`.
- Foundation `a3dd617f88bda178eb6c206dd5db91f88b6a2a42`.
- Mathlib `905b95818eb32af7874a58b427f50c1711a5e96c`.
- Evaluator source-pin commit `97484e4988a3e632e2c255c641edbe5292a86ea3`.
- Manuscript blob `e0a2bd4b3570235fa4ea89ffe8dcf9d5445499f9`.

The 17 additional coverage dependency roots check the uniform obstruction,
the true-Pi-one theory, and the partial-recursive quotient isomorphism.
The isomorphism uses neither productiveness, Gödel II, nor Pi-one completeness.

The native audits found only `propext`, `Classical.choice`, and `Quot.sound`
among the audited roots' axioms. The full log uses the maintained
`FailureOfComposition` namespace. Earlier agent-review logs used the former
`ExternalProbe` namespace; the review report preserves that provenance.
The source-provenance audit traversed 2,578 modules across 16 pinned, clean
dependency packages, with no unresolved imports or untracked dependency sources.

Evidence is retained in `Audit/failure-composition-v36/evidence/`:

- [Persistent mirror verification](../../Audit/failure-composition-v36/evidence/syncfailcomp-validation.json)
  records initialization of an existing empty directory, the successful build
  from an empty project cache, 40 script regressions, and a repeat sync that
  preserved all 836 cache files. All 72 style checks, 103 kernel replays, and
  260 previously audited theorem types passed unchanged.
- [Dependency-reuse verification](../../Audit/failure-composition-v36/evidence/wsl-dependency-reuse.json)
  records the external-checkout run, all 260 preserved audited types, and
  the 22 runner regressions. `syncpcats.sh` and all Lean proof sources are unchanged.
- [Final coverage map](MANUSCRIPT_COVERAGE.md) and
  [independent coverage review](../../Audit/failure-composition-v36/evidence/coverage-review.md)
  record the semantic comparison and remaining representation boundaries.
- [Strict style report](../../Audit/failure-composition-v36/evidence/style-lint.json)
  records all 72 source checks, their hashes, and the enforced options.
- [Native build record](../../Audit/failure-composition-v36/evidence/native-build.json)
  records the exact command and successful exit status.
- [Verification log](../../Audit/failure-composition-v36/evidence/verification.log)
  and [validation record](../../Audit/failure-composition-v36/evidence/validation.json)
  record the run outcome, module inventory, hashes, and exact scope.
- [Evaluator source pins](../../Audit/failure-composition-v36/evidence/evaluator-source-pins.json)
  and [source provenance](../../Audit/failure-composition-v36/evidence/source-provenance.json)
  record the imported dependency sources.
- [Weak-totality review](../../Audit/failure-composition-v36/evidence/weak-totality-review.md)
  records independent source review of the three new modules and their exact
  manuscript scope.
- [Range review](../../Audit/failure-composition-v36/evidence/range-review.md)
  records the four-module independent source review, internal quantifiers,
  realizing-index choice independence, and the scope of both proof routes.
- [Generated-congruence milestone review](../../Audit/failure-composition-v36/evidence/milestone-review.md)
  distinguishes collaborating-agent reviews from authors' checks. It does not
  claim external human acceptance.
