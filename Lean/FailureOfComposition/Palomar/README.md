# Palomar preparation: mechanically verified Nine interface

**COMPLETE LOCAL MECHANICAL PASS; NOT SUBMITTED OR REGISTERED.** This directory
makes nine intended declarations and their proved counterparts reviewable. The
cumulative eligible `ChallengeNine`/`SolutionNine` pair contains all nine
declarations. The exact separate-environment interface and proof-route checks
pass, and stock con-ron, NanoDa, and Lean's default kernel accepted the local
Comparator candidate at project commit
`381de9db4d2214b8fd8d05bf74b56bc9597f01c5`.

That pass uses a narrowly factored proof for Foundation's `TermSubst`
bound-variable field.  The repair preserves the computational blueprint and
record fields, excludes the former expensive proof body from the replacement
path, and is published as immutable Foundation commit
`01f617fbe240a84aaf1c45b31b9d65e0a2e21c1d`. The cumulative Nine run took
181.897 seconds under aggregate containment (178.69 seconds for Comparator)
and peaked at 989,483,008 bytes without pressure or limit events.

The pinned official Palomar verifier subsequently fetched public immutable
commit `48e6eeccc420e8068f1bc6d810ddbe10cfdf39eb` and completed with
`status: pass`, `stage: complete`, and all three kernel acceptances under the
approved `palomar-standard-v1` profile. The complete invocation took 3,034.009
seconds, including a clean 2,560.077-second Solution build and a
143.344-second Comparator phase. This is complete local mechanical verification
of the snapshot, not a Palomar service submission, editorial decision,
registration, or registry entry.

The module-based candidate at public immutable commit
`6adc1084e57ca3e9011dbd3765e99b803842ee17` has now also completed the current
verifier at PalomarSubmission `65f0154` under `palomar-standard-v1`. The final
report is `pass` / `complete` / `verification`; con-ron accepted 20,931
declarations in verified mode, NanoDa and Lean accepted, and Comparator printed
`Your solution is okay!`. This newer pass covers the current 124-source module
tree and source policy. It remains a local mechanical verification, not a
service submission or registry decision.

The current findings are recorded in [`STATUS.md`](STATUS.md), with the
nine-result migration state in [`RESULT_INVENTORY.json`](RESULT_INVENTORY.json).
The focused submitted-source inventory is
[`SUBMISSION_SOURCE_INVENTORY.json`](SUBMISSION_SOURCE_INVENTORY.json); historical
inventories remain available at their immutable commits and evidence archives.

The maintained repository is [flengyel/FailureOfComposition](https://github.com/flengyel/FailureOfComposition).
Its accepted port checkpoint is `073e95e54907eb26b6af9070302f5afdde04d963`,
using Lean 4.35.0-rc2, Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`, and Foundation
`e72cfe981aa65166f37fa4e2584f4806bc48d72f`.  The current eligibility branch
pins the two-proof Foundation repair
`01f617fbe240a84aaf1c45b31b9d65e0a2e21c1d`; its downstream compilation,
focused Nine validation, and cumulative three-kernel Comparator replay pass.
The independent port rerun and subsequent
evaluator cleanup passed their WSL checks. The cleanup's
103-source style gate, build, audits, kernel replays, and nine paired draft
checks are recorded in [STYLE_CLEANUP_VALIDATION.json](../Porting/STYLE_CLEANUP_VALIDATION.json).
The uploaded evidence was checked against the published source hashes.

[The Codex task](../../../docs/CODEX_PALOMAR_TASK.md) records the completed
eligible interface, correspondence proofs, Comparator checks, and local pinned
official-verifier procedure.
The earlier 4.32.2 development and initial export remain documented as provenance;
the manuscript is unchanged.

## The nine selected declarations

The [statement correspondence](../MANUSCRIPT_STATEMENTS.md) gives each
manuscript result in mathematical notation alongside its Lean signature.
The counts One through Nine refer to selected declarations, including alternate
proof routes, rather than manuscript theorem numbers.

The names below have prefix `FailureOfComposition.Palomar`. Both
[`ChallengeNine.lean`](ChallengeNine.lean) and [`SolutionNine.lean`](SolutionNine.lean) declare
them. [`comparator-nine.json`](comparator-nine.json) selects them in this order and permits
only `propext`, `Quot.sound`, and `Classical.choice`. It selects no unspecified
definitions.

| Declaration | Checkpoint status | Mathematical claim and exact assumptions | Maintained proof root in `FailureOfComposition.ConcreteIndices` |
| --- | --- | --- | --- |
| `obstruction_four_properties` | Migrated; locally verified in the cumulative Nine pair | Theorem 1: every consistent PA extension with r.e. axiom codes has guard/search indices satisfying all four witness properties. The two composition clauses are uniformly provable in T. | `obstruction_four_properties_of_re_axioms` |
| `no_quotient_composition_productive` | Migrated; locally verified in the cumulative Nine pair | Theorem 1/Corollary 2: for such T, no binary operation on the actual pointwise quotient satisfies the representative composition equation. Productive route. | `no_index_quotient_of_re_axioms` |
| `no_quotient_composition_godel` | Migrated and locally verified in the cumulative Nine pair on the repaired public Foundation pin | Theorem 1/Corollary 2: the identical quotient statement and hypotheses, by the separate Gödel-II route. | `no_index_quotient_via_godel_of_re_axioms` |
| `pi_one_characterization` | Migrated and locally verified in the cumulative Nine pair | Theorem 3: for every consistent PA extension, right compatibility, composition congruence, true-Pi-one completeness, and agreement with actual partial-function equality are equivalent. No r.e. hypothesis. | `pi_one_characterization` |
| `generated_congruence_classification` | Migrated and locally verified in the cumulative Nine pair | Theorem 4: for every PA extension, the least generated congruence is extensional equality if T is Sigma-one sound, and universal otherwise. Neither consistency nor r.e. axiomatizability is required. | `generated_congruence_classification` |
| `weak_totality_counterexample` | Migrated and locally verified in the cumulative Nine pair | Proposition 5: every consistent r.e. PA extension has a guard pointwise equivalent to identity that fails weak totality, while identity is weakly total. | `weak_totality_counterexample_of_re_axioms` |
| `range_counterexample_godel` | Migrated and locally verified in the cumulative Nine pair | Proposition 6: under the same consistent-r.e.-extension assumptions, an index is pointwise equivalent to empty while its PA-correct range index is inequivalent to the empty program's range index. Gödel-II route. | `range_counterexample_of_re_axioms` |
| `range_counterexample_productive` | Migrated and locally verified in the cumulative Nine pair | The identical Proposition 6 statement and hypotheses, by the separate productive route. | `range_counterexample_via_productiveness_of_re_axioms` |
| `generated_quotient_partial_recursive` | Migrated and locally verified in the cumulative Nine pair | For every Sigma-one sound PA extension, the generated quotient is monoid-isomorphic to actual unary partial recursive functions. Its representative equation sends each index class to that index's evaluation. | `generatedQuotientPartialRecursiveEquiv`, `generatedQuotientPartialRecursiveEquiv_mk` |

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

## Current toolchain and submission preparation

The module-based candidate is checked against the
[policy at `96b034c`](https://github.com/PalomarRegistry/PalomarPolicy/blob/96b034cc31a72a63d4f4041911dce337a85c9a04/CONTRIBUTING.md)
and [PalomarSubmission at `65f0154`](https://github.com/PalomarRegistry/PalomarSubmission/tree/65f0154ed776cd26c224254aa57b379137f28b0d).
The complete earlier pass under `a59f25b` remains historical evidence for its
immutable snapshot; it does not by itself satisfy the newer module-source rule.

1. **Toolchain compatibility is resolved.** Its
   [`toolchains.json`](https://github.com/PalomarRegistry/PalomarSubmission/blob/65f0154ed776cd26c224254aa57b379137f28b0d/toolchains.json)
   requires at least `v4.35.0-rc2`. The accepted port uses that release with
   matching Mathlib and Foundation pins and has passed the project checks.
2. **Challenge dependency boundary is resolved.** The readable cumulative
   `ChallengeNine` interface imports only permitted Mathlib sources and passes
   the current source audit.
   Solution-only Foundation dependencies are a different matter and are
   permitted when their source and pins satisfy the dependency rules.
3. **Submitted-source scope and modules.** The focused tree contains 124 Lean
   modules and no Lean source under `Audit/`. The current static scan reports
   no source-policy issue. ChallengeNine is 44,261 bytes and 999 lines. See
   [`PALOMAR_SUBMISSION_SCOPE.md`](../../../docs/PALOMAR_SUBMISSION_SCOPE.md).
4. **Licensing notices are explicit.** Apache-2.0 covers the formalization and
   supporting code. The manuscript README records the author's retained
   copyright and arXiv's perpetual, non-exclusive distribution license; that
   grant is not a general public reuse license. No demonstrated mechanical
   licensing failure is pending.
5. **Comparator and official-verifier evidence remains local.** The cumulative eligible
   `ChallengeNine`/`SolutionNine` pair at tested project commit
   `381de9db4d2214b8fd8d05bf74b56bc9597f01c5` passed con-ron, NanoDa, and Lean's
   default kernel.  The exact selected declarations are
   `obstruction_four_properties`, `no_quotient_composition_productive`,
   `no_quotient_composition_godel`, `pi_one_characterization`,
   `generated_congruence_classification`, `weak_totality_counterexample`,
   `range_counterexample_godel`, `range_counterexample_productive`, and
   `generated_quotient_partial_recursive`;
   no definition holes are selected. The run
   consumed authenticated stable Challenge/Solution exports and completed in
   181.897 seconds under aggregate containment at 989,483,008 bytes peak with
   no pressure, limit, deadline,
   swap, or OOM event.  Earlier timeouts and pressure stops remain valid
   historical resource results for their recorded dependency revisions, not
   theorem rejections. The older pinned
   [verifier](https://github.com/PalomarRegistry/PalomarSubmission/blob/a59f25bd8a66bf6faf3a4f4260d412989c0185ea/scripts/verify_submission.py)
   then fetched public commit `48e6eeccc420e8068f1bc6d810ddbe10cfdf39eb`,
   performed its protected source-provenance, clean build, export, comparison,
   and kernel checks, and reported a complete pass under
   `palomar-standard-v1`. Con-ron accepted 20,847 declarations; NanoDa and Lean
   also accepted. The execution took 3,034.009 seconds and had no deadline,
   OOM, pressure-stop, or host-reserve event. This is a complete local run of
   the pinned official verifier, not a Palomar service or editorial result.
6. **The current immutable candidate has a complete local mechanical pass.**
   PalomarSubmission `65f0154` fetched public commit
   `6adc1084e57ca3e9011dbd3765e99b803842ee17`. After preserving one earlier
   host-monitor abort, a narrowly repaired external monitor guarded the one
   newly authorized execution. The report is `pass` / `complete` /
   `verification`; all three kernels and Comparator accepted. The guarded run
   took 3,720.403 seconds, recorded no deadline/OOM/pressure/host-reserve stop,
   and cleaned its owned cgroup.
7. **Service submission remains separate.** No event was uploaded, no service
   submission was made, and no registration or editorial review occurred. The
   default 16-CPU profile was unavailable on this four-CPU host; the approved
   standard profile qualified and was selected explicitly. Technical
   preparation is complete for this immutable snapshot; upload, service review,
   registration, and editorial acceptance remain separate decisions.

Solving the dependency boundary must preserve the statements. Adding the
desired result as a hypothesis, hiding it inside an unconstrained definition,
weakening its quantifiers, or substituting unrelated notions of PA or
provability would not solve this preparation task. No extra axiom is proposed.

The Foundation port, namespace migration, and evaluator style cleanup are
complete.  The permitted arithmetic statement interface and proved
correspondence now support all nine selections. Comparator follows the bodies of ordinary
definitions in the statement's dependency graph; replacing definitions by
Foundation aliases does not establish this correspondence or make different
definitions compare identically.

## Files and eventual selection paths

The repository contains the substantive formalization, so
[`formalization.yaml`](formalization.yaml) omits the thin-wrapper `repository`
block. The separate wrapper declarations in this directory do not turn the
whole repository into a thin-wrapper repository.

The all-nine handoff paths are:

| Setting | Repository-relative value |
| --- | --- |
| Repository | `flengyel/FailureOfComposition` |
| Selected project | `Lean` |
| Comparator configuration | `Lean/FailureOfComposition/Palomar/comparator-nine.json` |
| Metadata | `Lean/FailureOfComposition/Palomar/formalization.yaml` |
| Challenge module | `FailureOfComposition.Palomar.ChallengeNine` |
| Solution module | `FailureOfComposition.Palomar.SolutionNine` |
| Local Comparator-tested revision | `381de9db4d2214b8fd8d05bf74b56bc9597f01c5` |
| Earlier official-verifier source revision | `48e6eeccc420e8068f1bc6d810ddbe10cfdf39eb` |
| Current official-verifier source revision | `6adc1084e57ca3e9011dbd3765e99b803842ee17` |
| Current verifier revision | `65f0154ed776cd26c224254aa57b379137f28b0d` |
| Official-verifier profile | `palomar-standard-v1` |

Any later submission revision must be an immutable full SHA. A changed snapshot,
including changed submission metadata, is not covered by the pass above unless
prepared and verified again. These paths are preparation data, not an instruction
to submit. One configuration containing all nine declarations would be one
registry entry; each selected declaration would still be reviewed.

The separate repository has been created and published. It preserves the
nested `Lean` project layout and contains the maintained code and manuscript.
The old repository remains linked only for historical provenance and evidence.
`ROOTPROVENANCE.json` is the frozen initial export record, not an assertion that
this repository is still unpublished or that later files match the export hashes.
The focused submission omits the superseded export helper and cumulative
One-through-Eight interfaces; their exact sources remain in immutable history.

`ChallengeNine.lean` contains exactly nine deliberate theorem holes to expose
the intended types. It stays outside the maintained proof umbrella.
`SolutionNine.lean` does
not import Challenge and supplies its proofs from the maintained library.
Do not import both same-name interfaces into one Lean environment. The holes
are excluded explicitly from metadata proof counts; this is not a claim that
every unrelated probe or fixture in the repository is hole-free.

## Run the focused local gates in WSL

The existing Linux port checkout already has the accepted toolchain and
dependency installations. When a changed draft needs checking, use it directly:

```bash
cd /home/flengyel/src/FailureOfComposition-port
export LEAN_NUM_THREADS=1 FAILCOMP_STYLE_JOBS=1
mkdir -p .codex-work/tmp
export TMPDIR="$PWD/.codex-work/tmp"
PALOMAR_SUBMISSION_CHECKOUT=/path/to/PalomarSubmission-at-65f0154 \
  PALOMAR_PYTHON=/path/to/its-python \
  bash scripts/run-palomar-nine-focused.sh .codex-work/palomar/nine-focused
```

The maintained suite builds the selected modules, compiles the bridges strictly,
checks Challenge and Solution in separate environments, walks full proof bodies
for axioms and route separation, applies the current Challenge source policy,
and runs the retained negative fixtures. The nine deliberate Challenge-hole
warnings are expected. These focused gates remain distinct from Comparator and
the complete official verifier.

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
