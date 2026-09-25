# Palomar preparation: draft statement interface

**DRAFT NOT SUBMISSION READY.** This directory makes nine intended declarations
and their proved counterparts reviewable. It is not an eligible Palomar
submission, a Comparator success report, or a registry entry.

The maintained repository is [flengyel/FailureOfComposition](https://github.com/flengyel/FailureOfComposition).
Its accepted checkpoint is `073e95e54907eb26b6af9070302f5afdde04d963`, using
Lean 4.35.0-rc2, Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`, and
Foundation `e72cfe981aa65166f37fa4e2584f4806bc48d72f`. The independent port
rerun and subsequent evaluator cleanup passed their WSL checks. The cleanup's
103-source style gate, build, audits, kernel replays, and nine paired draft
checks are recorded in [STYLE_CLEANUP_VALIDATION.json](../Porting/STYLE_CLEANUP_VALIDATION.json).
The uploaded evidence was checked against the published source hashes.

[The Codex task](../../../docs/CODEX_PALOMAR_TASK.md) specifies the remaining
arithmetic interface, correspondence proofs, and real Comparator checks.
The earlier 4.32.2 development and initial export remain documented as provenance;
the manuscript is unchanged.

## The nine selected declarations

The names below have prefix `FailureOfComposition.Palomar`. Both
[`Challenge.lean`](Challenge.lean) and [`Solution.lean`](Solution.lean) declare
them. [`comparator.json`](comparator.json) selects them in this order and permits
only `propext`, `Quot.sound`, and `Classical.choice`. It selects no unspecified
definitions.

| Declaration | Mathematical claim and exact assumptions | Maintained proof root in `FailureOfComposition.ConcreteIndices` |
| --- | --- | --- |
| `obstruction_four_properties` | Theorem 1: every consistent PA extension with r.e. axiom codes has guard/search indices satisfying all four witness properties. The two composition clauses are uniformly provable in T. | `obstruction_four_properties_of_re_axioms` |
| `no_quotient_composition_productive` | Theorem 1/Corollary 2: for such T, no binary operation on the actual pointwise quotient satisfies the representative composition equation. Productive route. | `no_index_quotient_of_re_axioms` |
| `no_quotient_composition_godel` | The identical quotient statement and hypotheses, by the separate Gödel-II route. | `no_index_quotient_via_godel_of_re_axioms` |
| `pi_one_characterization` | Theorem 3: for every consistent PA extension, right compatibility, composition congruence, true-Pi-one completeness, and agreement with actual partial-function equality are equivalent. No r.e. hypothesis. | `pi_one_characterization` |
| `generated_congruence_classification` | Theorem 4: for every PA extension, the least generated congruence is extensional equality if T is Sigma-one sound, and universal otherwise. Neither consistency nor r.e. axiomatizability is required. | `generated_congruence_classification` |
| `weak_totality_counterexample` | Proposition 5: every consistent r.e. PA extension has a guard pointwise equivalent to identity that fails weak totality, while identity is weakly total. | `weak_totality_counterexample_of_re_axioms` |
| `range_counterexample_godel` | Proposition 6: under the same consistent-r.e.-extension assumptions, an index is pointwise equivalent to empty while its PA-correct range index is inequivalent to the empty program's range index. Gödel-II route. | `range_counterexample_of_re_axioms` |
| `range_counterexample_productive` | The identical range statement and hypotheses, by the productive route. | `range_counterexample_via_productiveness_of_re_axioms` |
| `generated_quotient_partial_recursive` | For every Sigma-one sound PA extension, the generated quotient is monoid-isomorphic to actual unary partial recursive functions. Its representative equation sends each index class to that index's evaluation. | `generatedQuotientPartialRecursiveEquiv`, `generatedQuotientPartialRecursiveEquiv_mk` |

Here pointwise provability means a separate T-proof for every external
standard natural-number input. Uniform provability means one proof of the
internally universally quantified graph equation. All program-index
quantifiers range over the natural numbers. The main r.e. statements leave no
arithmetization, realization, Delta-one-presentation, or soundness premise
for the caller to supply.

The ninth declaration's target is the subtype of actual partial maps
`{ f : ℕ → Part ℕ // Nat.Partrec f }`, with partial composition. It is not
merely another syntactic graph quotient. The generated congruence is defined
by intersection of all composition-compatible equivalence relations
containing pointwise provability.

## Verified toolchain and remaining blockers

The requirements were checked on September 25, 2026 against
the [submitter policy at `792c7c0`](https://github.com/PalomarRegistry/PalomarPolicy/blob/792c7c0b9e798bd02719e795ef11fa2b5929e067/CONTRIBUTING.md)
and [PalomarSubmission at `a59f25b`](https://github.com/PalomarRegistry/PalomarSubmission/tree/a59f25bd8a66bf6faf3a4f4260d412989c0185ea).

1. **Toolchain compatibility is resolved.** Its
   [`toolchains.json`](https://github.com/PalomarRegistry/PalomarSubmission/blob/a59f25bd8a66bf6faf3a4f4260d412989c0185ea/toolchains.json)
   requires at least `v4.35.0-rc2`. The accepted port uses that release with
   matching Mathlib and Foundation pins and has passed the project checks.
2. **Challenge dependency boundary.** The draft Challenge imports local
   modules whose closure includes Foundation and proved project results.
   The [dependency policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/792c7c0b9e798bd02719e795ef11fa2b5929e067/CONTRIBUTING.md#24-dependencies)
   permits only core, canonical Mathlib and its pinned dependencies, and
   specifically approved Tau Ceti and CSLib libraries in that closure.
   These imports therefore fail the current policy. A legitimate readable
   statement interface with permitted dependencies is still required.
   Solution-only Foundation dependencies are a different matter and are
   permitted when their source and pins satisfy the dependency rules.
3. **Snapshot licensing scope.** This repository now has the exported
   Apache-2.0 code license at its root as `LICENSE`. The historical missing-root
   issue is resolved. The manuscript has been added under `manuscript/` with
   its existing licensing preserved; the code license is not a new grant for
   the paper. Its scope must be settled for any final submitted snapshot under
   the [repository-license policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/792c7c0b9e798bd02719e795ef11fa2b5929e067/CONTRIBUTING.md#25-repository-licence).
4. **Comparator has not run.** Local elaboration, matching declaration types,
   axiom audits, and ordinary kernel replay do not establish Palomar's
   protected Challenge/Solution comparison. Its current
   [verifier](https://github.com/PalomarRegistry/PalomarSubmission/blob/a59f25bd8a66bf6faf3a4f4260d412989c0185ea/scripts/verify_submission.py)
   uses Lean-bundled `lake comparator` and exported-proof checking, including
   the toolchain's bundled NanoDa and con-ron kernels. No successful Comparator
   or Palomar mechanical/editorial result is asserted here.

Solving the dependency boundary must preserve the statements. Adding the
desired result as a hypothesis, hiding it inside an unconstrained definition,
weakening its quantifiers, or substituting unrelated notions of PA or
provability would not solve this preparation task. No extra axiom is proposed.

The Foundation port, namespace migration, and evaluator style cleanup are
complete. The permitted arithmetic statement interface still needs a proved
correspondence with the existing notions. Comparator follows the bodies of
ordinary definitions in the statement's dependency graph; replacing definitions
by Foundation aliases does not establish this correspondence or make different
definitions compare identically.

## Files and eventual selection paths

The repository contains the substantive formalization, so
[`formalization.yaml`](formalization.yaml) omits the thin-wrapper `repository`
block. The separate wrapper declarations in this directory do not turn the
whole repository into a thin-wrapper repository.

If these blockers are resolved and a later exact commit is ready, the intended
selection is:

| Setting | Repository-relative value |
| --- | --- |
| Repository | `flengyel/FailureOfComposition` |
| Selected project | `Lean` |
| Comparator configuration | `Lean/FailureOfComposition/Palomar/comparator.json` |
| Metadata | `Lean/FailureOfComposition/Palomar/formalization.yaml` |
| Challenge module | `FailureOfComposition.Palomar.Challenge` |
| Solution module | `FailureOfComposition.Palomar.Solution` |

The submission revision must be the full SHA of that later checked commit.
These paths are preparation data, not an instruction to submit the present
baseline. One configuration containing all nine declarations would be one
registry entry; each selected declaration would be reviewed.

The separate repository has been created and published. It preserves the
nested `Lean` project layout and contains the maintained code and manuscript.
The old repository remains linked only for historical provenance and evidence.
`ROOTPROVENANCE.json` is the frozen initial export record, not an assertion that
this repository is still unpublished or that later files match the export hashes.
The retained `export_repository.py` helper reproduces the original code-export
workflow; it is not a complete backup tool for this repository's added manuscript.

`Challenge.lean` contains nine deliberate theorem holes to expose the intended
types. It stays outside the maintained proof umbrella. `Solution.lean` does
not import Challenge and supplies its proofs from the maintained library.
Do not import both same-name interfaces into one Lean environment. The holes
are excluded explicitly from metadata proof counts; this is not a claim that
every unrelated probe or fixture in the repository is hole-free.

## Run the local paired check in WSL

The existing Linux port checkout already has the accepted toolchain and
dependency installations. When a changed draft needs checking, use it directly:

```bash
cd /home/flengyel/src/FailureOfComposition-port
export LEAN_NUM_THREADS=1 FAILCOMP_STYLE_JOBS=1
mkdir -p .codex-work/tmp
export TMPDIR="$PWD/.codex-work/tmp"
python3 Lean/FailureOfComposition/Palomar/check_draft.py
```

The checker reuses the validated pinned dependency checkouts, incrementally
builds the maintained proof library, elaborates Challenge and Solution
separately, and runs `CheckInterface.lean` to compare the nine types and their
axiom envelopes. The deliberate Challenge-hole warnings are expected. The
Solution is checked with strict Mathlib style linting and warnings as errors.
The local checker passed all nine declarations during the September 25 WSL
acceptance run. It is not Comparator or Palomar mechanical verification. The
next task adds those checks without repeating the completed toolchain port.

## Scope, provenance, and review

The mathematical source is Florian Lengyel's
[version 36 manuscript](../../../manuscript/failure_of_composition_2026-09-21_v36.tex).
Metadata therefore records `relationship: formalizes`, rather than treating
the Lean development as the result's first presentation. The manuscript's
classifications are retained. Montagna (1989) and Di Paola–Montagna (1991)
are historical background sources. Novelty is not independently established
by this preparation.

The evaluator uses Mathlib's program numbering with a constructed PA
arithmetization. The generated-congruence proof uses least successful history
stages; the r.e. Gödel route uses a Craig presentation. These are proved
representation choices, not claims of literal identity with historical code
tables. The weak-totality witness is the productive history guard. The
categorical consequence is formalized through the failure of the induced
operation on endomorphisms of omega; no reconstruction of every historical
multiobject syntactic category is claimed.

Range programs satisfy the PA-uniform graph equation, not only the standard
set-theoretic description. The maintained library also proves that the
obstruction persists for every PA-correct choice of range indices. The nine
selected declarations include the witness statements; auxiliary choice,
domain-totality, conservativity, and other coverage results remain documented
in the [manuscript coverage map](../MANUSCRIPT_COVERAGE.md).

The productive and Gödel proofs were checked for separate dependency routes.
This is not a claim of logical independence between two formal sentences.
Review and automation metadata credit AI assistance honestly and distinguish
agent source reviews from human peer review. Any local checks of this draft
are separate from Palomar's checks and do not remove the blockers above.

## Deferred manuscript work

The author plans version 37 to mention the Lean formalization. The proposed
Appendix B revision would replace the primed constructions with a citation to
the obstruction results. That manuscript revision remains separate from this
preparation. Any reassurance about the unprimed constructions `S` and `S_T`
requires checking their actual source definitions and identifying which later
theorems use each construction. That affected-theorem inventory is pending;
this draft makes no blanket claim about all later results in either paper.
