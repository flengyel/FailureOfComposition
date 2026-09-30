# Palomar eligibility status

The entries below are dated verification records. Counts such as Eight refer to
selected declarations, including alternate proof routes, not manuscript theorem
numbers. The [statement correspondence](../MANUSCRIPT_STATEMENTS.md) gives the
mathematical statements, Lean signatures, and source numbering. Later
documentation and doccomment corrections do not constitute another build or
Comparator run; recorded hashes and resource measurements refer to their
original tested commits.

## 2026-09-30 current-verifier module candidate

PalomarSubmission `65f0154ed776cd26c224254aa57b379137f28b0d` and
PalomarPolicy `96b034cc31a72a63d4f4041911dce337a85c9a04` require every submitted
Lean source to use the module system and limit each file to 10,000 physical
lines. The earlier complete pass below remains valid for its pinned verifier,
but it does not establish this newer eligibility condition.
Their upstream heads still match those revisions. PalomarTemplate has advanced
from the verifier-pinned `128a6c5ce5f48622e69927ccd639cbff401022e8` to
`2891de4c48955af824969a263d31b25e7a9a1406`; the inspected change applies the
same module/source-size rule to the starter template and does not change this
submission's selected paths or nine-result contract.

The focused candidate retains 124 Lean modules from the 197-source baseline.
It moves the active Nine dependency audit and four negative fixtures from
`Audit/` into maintained `Checks/` and `Tests/` modules, moves the evaluator pin
record into `Provenance/`, and omits 73 superseded or out-of-scope Lean sources.
No file remains under `Audit/` in the candidate. Omitted sources and reports
remain at immutable commit `5586bae3730e49f866da1d4e2f0ebb1dadacc2ca` and in
the previously verified evidence archives. See
[`PALOMAR_SUBMISSION_SCOPE.md`](../../../docs/PALOMAR_SUBMISSION_SCOPE.md).

The current official static scan checks all 124 files with no issue; the pinned
Lean parser accepts `--deps-json` for all 124. ChallengeNine is 44,261 bytes and
999 lines. Strict selected builds, the exact nine-result interface check, the
full-environment dependency/axiom audit, current Challenge source policy, and
the maintained negative regressions pass. The selected ChallengeNine and
SolutionNine source is unchanged from the accepted snapshot after normalizing
only module/public-visibility commands and blank lines. A fresh immutable public
candidate and one current official-verifier execution remain before current
submission readiness is claimed.

The manuscript notice now records the existing arXiv perpetual, non-exclusive
distribution license while preserving the author's copyright and the separate
Apache-2.0 code license. This is a clarification, not a new license grant.

Historical sections below refer to paths and artifacts as they existed at their
recorded commits. Their removal from the focused candidate does not alter those
results.

## 2026-09-30 pinned official verifier pass for cumulative Nine

Pinned PalomarSubmission revision
`a59f25bd8a66bf6faf3a4f4260d412989c0185ea` fetched the public immutable
snapshot `48e6eeccc420e8068f1bc6d810ddbe10cfdf39eb` and selected project `Lean`,
`comparator-nine.json`, `formalization.yaml`, `ChallengeNine`, and
`SolutionNine`. Preparation reported `status: pending`, `stage: prepared` with
the matching source SHA and paths. The snapshot is a packaging-only descendant
of local Comparator-tested code/configuration commit
`381de9db4d2214b8fd8d05bf74b56bc9597f01c5`; the Challenge, Solution, and
portable configuration hashes are unchanged.

The default `palomar-namespace-16x32-v1` capacity check failed because the host
had four rather than sixteen effective CPUs. The approved
`palomar-standard-v1` profile passed with 16,772,218,880 bytes effective RAM,
15,933,607,936-byte `memory.high`, 16,436,774,502-byte `memory.max`, and more
than 875 GB workspace free. Pinned bubblewrap v0.12.0, nested namespaces, and
delegated cgroup supervision passed harmless preflights.

The one official `execute` payload returned zero after 3,034.009 seconds. The
final report says `status: pass`, `stage: complete`, `phase: verification`, and
has no errors. A clean Solution build took 2,560.077 seconds, Solution export
took 18.681 seconds, and Comparator took 143.344 seconds. Con-ron accepted
20,847 declarations in verified mode; NanoDa and Lean's default kernel also
accepted, and Comparator printed `Your solution is okay!`. The largest recorded
phase cgroup peak was 9,151,164,416 bytes during trusted-cache work; Comparator
peaked at 786,345,984 bytes. No deadline, OOM, OOM-kill, external pressure, or
host-reserve stop occurred. Cleanup took 0.002 seconds and left no owned cgroup.

The verifier detected the root Apache-2.0 license and emitted only the existing
preferred Challenge review-surface warning. This is a complete local mechanical
pass under the named pinned official-verifier profile. It is not a Palomar
service submission, editorial decision, registration, or registry acceptance.
The manuscript retains its own notice, so its licensing scope remains a
maintainer/editorial decision before service submission. Detailed evidence is
in `Audit/palomar-official-nine-20260930/`.

## 2026-09-30 generated quotient and cumulative Nine pass

The eligible interface now includes the unnumbered sound generated-quotient
consequence after Theorem 4. The independent proof descends actual evaluation
through the migrated generated-congruence classification, obtains all unary
partial recursive functions from Mathlib's code-existence theorem, and proves
multiplication using the concrete evaluator composition law. Checked bridges
identify representatives, multiplication, the actual-function target, and the
maintained equivalence. The quotient unit is matched to the maintained chosen
identity realization by equality of quotient classes, without asserting that
the underlying chosen indices are literally equal.

`ChallengeNine`/`SolutionNine` own exactly all nine selected declarations. The
exact separate-environment checker compared 5,149 recursively reachable
statement constants and found exactly nine Challenge theorem holes, no
definition holes, and only `propext`, `Classical.choice`, and `Quot.sound` in
the Solution proof closures. The pinned source audit passes. ChallengeNine is
44,209 bytes and 998 lines: within the 100 KiB/1,000-line hard limits and above
the preferred 32 KiB/300-line review surface. The ninth root has 16,160
constants; the complete selected proof union has 21,850, 39 marginal over
Eight. The earlier productive/Gödel route separations remain checked.

The proof/interface parent is
`6bcb9f691053bfa9ea16939be1950fa25e4e8753`. The exact tested
code/configuration/harness commit is
`381de9db4d2214b8fd8d05bf74b56bc9597f01c5`; it adds a one-line correction to
the launcher's evidence-directory guard. The first stable-export parent failed
before payload start on that stale path, and its setup classification is
preserved. Stable Challenge and Solution exports are respectively 18,976,072
bytes, `cbc5f32f3da1b7c40612c3bf07f5d1da9f663ed0100225c1f2701d726c8fff03`,
and 158,336,512 bytes,
`5ddfa3701144f56f12ac354f3eabc5e0a8414c4cac923630cc06769a33f5259e`.

The sole cumulative Nine Comparator payload accepted the exact pair through
con-ron, NanoDa, and Lean's default kernel and printed `Your solution is okay!`.
Con-ron accepted 20,847 declarations. Contained elapsed time was 181.897
seconds (178.69 seconds for Comparator); aggregate peak memory was 989,483,008
bytes, with zero pressure, high/max, deadline, swap, or OOM events. Separate
timestamped before/after records and an exit-zero comparison confirm that both
exports and both configurations were unchanged. Cleanup left no owned workload.

All nine selected declarations are migrated and locally kernel verified.
Complete official Palomar verification, final submission-snapshot/licensing
review, submission, and registration remain. This local pass is not an official
submission or registry acceptance. Detailed evidence is indexed in
`Audit/palomar-nine-generated-quotient-20260930/`.

## 2026-09-30 productive range counterexample and cumulative Eight pass

The eligible interface now includes the productive proof route for the same
Proposition 6 range counterexample already selected through Gödel II. The new
bridge reuses the checked PA-uniform range selector and transports the maintained
`range_counterexample_via_productiveness_of_re_axioms` theorem with the same
natural-number witness. Its closure reaches the maintained history-divergence
and productive-escape route and excludes the public and maintained Gödel-II/Craig
range roots. The seventh root retains the converse exclusion, and the common
range correspondence reaches neither counterexample route.

`ChallengeEight`/`SolutionEight` own exactly the eight selected declarations.
The exact separate-environment checker compared 4,482 recursively reachable
statement constants and found exactly eight Challenge theorem holes, no
definition holes, and only `propext`, `Classical.choice`, and `Quot.sound` in
the Solution proof closures. The pinned source audit passes. ChallengeEight is
42,885 bytes and 979 lines: within the 100 KiB/1,000-line hard limits and above
the preferred 32 KiB/300-line review surface. The complete selected proof union
is 21,811 constants, 13 marginal over Seven; the two range proof routes remain
separated.

The tested code/configuration/harness commit is
`5435b5b528795590f250a82bf8937779b4fc86b4`. Stable Challenge and Solution
exports are respectively 15,693,866 bytes,
`a4b1ea1dea71d2252fe847cb4f8a9f342657258a09194dc4a0408902d2489032`,
and 158,212,339 bytes,
`bf599e27742336ee02f751be4e46b20cdc25606e610a4c2b4549a411b1baca13`.
The sole cumulative Eight Comparator payload accepted the exact pair through
con-ron, NanoDa, and Lean's default kernel and printed `Your solution is okay!`.
Contained elapsed time was 190.419 seconds (188.46 seconds for Comparator);
aggregate peak memory was 794,050,560 bytes, with zero pressure, high/max,
deadline, swap, or OOM events. Timestamped before/after records and an exit-zero
comparison confirm that both exports and both configurations were unchanged.
Cleanup left no owned workload.

Eight declarations are migrated and locally kernel verified. Declaration 9 and
complete official Palomar verification remain. This local pass is not an
official submission or registry acceptance. Detailed evidence is indexed in
`Audit/palomar-eight-productive-range-20260930/`.

## 2026-09-30 Gödel-II range counterexample and cumulative Seven pass

The independent interface now includes the exact PA-uniform range graph and a
fixed classical selector for a realizing index. The checked bridge proves
uniform realization and choice independence against the maintained range
index, then transports pointwise equality for both range operands and the
maintained counterexample with the same natural-number witness. The seventh
proof reaches the maintained Gödel-II/Craig root and excludes the productive
range route.

`ChallengeSeven`/`SolutionSeven` own exactly the seven selected declarations.
The exact separate-environment checker compared 4,481 recursively reachable
statement constants and found exactly seven Challenge theorem holes, no
definition holes, and only `propext`, `Classical.choice`, and `Quot.sound` in
the Solution proof closures. The pinned source audit passes. ChallengeSeven is
42,249 bytes and 966 lines: within the 100 KiB/1,000-line hard limits and above
the preferred 32 KiB/300-line review surface. The complete selected proof
union is 21,798 constants, 82 marginal over Six; the productive and Gödel/Craig
routes remain separated.

The tested code/configuration/harness commit is
`16e73188e12244f651c7ce57207095bd0d223a44`. Stable Challenge and Solution
exports are respectively 15,691,644 bytes,
`20e1cac661f1947ed9fd0bc7b5d39d7ac9a2f27a12705ecd5b0f95c44c5db5db`,
and 158,127,081 bytes,
`784ca63776a83356b0d63ed4ad9b6a3c1bd14e7ac936f9ed5b19850a3e4463f4`.
The sole cumulative Seven Comparator payload accepted the exact pair through
con-ron, NanoDa, and Lean's default kernel and printed `Your solution is okay!`.
Contained elapsed time was 199.537 seconds (197.88 seconds for Comparator);
aggregate peak memory was 787,070,976 bytes, with zero pressure, high/max,
deadline, swap, or OOM events. Timestamped before/after records and an
exit-zero comparison confirm that both exports and both configurations were
unchanged. Cleanup left no owned workload.

Seven declarations are migrated and locally kernel verified. Declarations 8–9
and complete official Palomar verification remain. This local pass is not an
official submission or registry acceptance. Detailed evidence is indexed in
`Audit/palomar-seven-godel-range-20260930/`.

## 2026-09-29 weak-totality counterexample and cumulative Six pass

The independent interface now includes the exact productive-history guard
family and weak-totality cancellation predicate.  The checked bridge proves
literal equality of the independently compiled guard index with the maintained
natural-number index, proves weak-totality correspondence in both directions,
and transports the maintained counterexample with the same witness.  The sixth
proof reaches the maintained productive root and does not reach the audited
Gödel-II/Craig roots.

`ChallengeSix`/`SolutionSix` own exactly the six selected declarations.  The
exact separate-environment checker compared 4,470 recursively reachable
statement constants and found exactly six Challenge theorem holes, no
definition holes, and only `propext`, `Classical.choice`, and `Quot.sound` in
the Solution proof closures.  The pinned source audit passes. ChallengeSix is
45,265 bytes and 999 lines: within the 100 KiB/1,000-line hard limits and above
the preferred 32 KiB/300-line review surface.  The complete selected proof
union is 21,716 constants, 160 marginal over Five; the productive and
Gödel/Craig routes remain separated.

The tested code/configuration/harness commit is
`b923699c670857f174ab445483d1508a453eaab0`. Stable Challenge and Solution
exports are respectively 15,675,974 bytes,
`fde6894a5cb94f001c54509fdbe4077e6db3e97b96240e2c90c9b121d9854280`,
and 157,753,313 bytes,
`b2941e09078256c52b1b6d76c87d5c2027b79ee31e8ad3a6837ca42c76d32c4a`.
The one cumulative Six Comparator payload accepted the exact pair through
con-ron, NanoDa, and Lean's default kernel and printed `Your solution is okay!`.
Contained elapsed time was 199.351 seconds (197.78 seconds for Comparator);
aggregate peak memory was 803,315,712 bytes, with zero pressure, high/max,
deadline, swap, or OOM events.  Separate before/after records confirm that both
exports and both configurations were unchanged.

The first parent invocation failed before payload start because its script path
was relative to the `Lean/` workload directory.  The preserved exit-127 record
contains no Comparator artifacts.  The permitted corrected parent invocation
launched the checkpoint's sole payload; its child evidence was written to the
script's fixed `comparator-six-01` artifact directory while its containment
telemetry is in `comparator-six-02`.

Six declarations are migrated and locally kernel verified.  Declarations 7–9
and complete official Palomar verification remain.  This local pass is not an
official submission or registry acceptance. Detailed evidence is indexed in
`Audit/palomar-six-weak-totality-20260929/`.

## 2026-09-29 generated-congruence classification and cumulative Five pass

The independent interface now includes the full generated-congruence
classification for every deductive extension of PA. The checked bridge proves
two-way Σ₁ hierarchy membership for every formula and binder environment,
standard Σ₁-soundness correspondence, and an independent intersection
definition of the least two-sided composition congruence. Generator
containment, equivalence, composition closure, and leastness are named Lean
theorems. The relation correspondence is audited as independent of the
classification theorem. Neither consistency nor enumerability was added.

`ChallengeFive`/`SolutionFive` own exactly the five selected declarations. The
exact separate-environment checker compared 4,440 recursively reachable
statement constants and found exactly five Challenge theorem holes, no
definition holes, and only `propext`, `Classical.choice`, and `Quot.sound` in
the Solution proof closures. The pinned source audit passes. ChallengeFive is
42,977 bytes and 948 lines: within the 100 KiB/1,000-line hard limits and above
the preferred 32 KiB/300-line review surface. The complete selected proof
union is 21,556 constants, 160 marginal over Four; the productive and
Gödel/Craig routes remain separated.

The tested code/configuration/harness commit is
`e9ff8aaf06f38322197e81042723418aab6a8987`. Stable Challenge and Solution
exports are respectively 15,637,707 bytes,
`b43649cc83c40522d546e324582b391410ea56eaf2e0b24c4a29ecd9893d8a9c`,
and 156,465,976 bytes,
`46565a171f8585298f47bfa7a9176110cf0736e561e90c49fbd5f6eeecbbd82f`.
The one cumulative Five Comparator payload accepted the exact pair through
con-ron, NanoDa, and Lean's default kernel and printed `Your solution is okay!`.
Contained elapsed time was 175.855 seconds; aggregate peak memory was
806,871,040 bytes, with zero pressure, high/max, deadline, swap, or OOM events.

Five declarations are migrated and locally kernel verified. Four migrations
and complete official Palomar verification remain. This local pass is not an
official submission or registry acceptance. Detailed evidence is indexed in
`Audit/palomar-five-generated-congruence-20260929/`.

## 2026-09-29 Π₁ characterization and cumulative Four pass

The independent interface now includes the full Π₁ characterization for
every consistent deductive extension of PA, with no enumerability or soundness
hypothesis.  The checked bridge proves standard term/formula evaluation under
all environments and binders, two-way bounded and Π₁ hierarchy
correspondence, true-Π₁-completeness correspondence, and both directions of
the right-compatibility, composition-congruence, and extensional-agreement
translations.  It transports the maintained
`ConcreteIndices.pi_one_characterization` theorem without changing its
signature.

`ChallengeFour`/`SolutionFour` own exactly the four selected declarations.  The
exact separate-environment checker compared 4,429 recursively reachable
statement constants and found exactly four Challenge theorem holes, no
definition holes, and only `propext`, `Classical.choice`, and `Quot.sound` in
the Solution proof closures.  The pinned source audit passes.  ChallengeFour is
40,928 bytes and 915 lines: within the 100 KiB/1,000-line hard limits and above
the preferred 32 KiB/300-line review surface.  The complete selected proof
union is 21,396 constants, 136 marginal over the accepted Three union; the
productive and Gödel/Craig routes remain separated.

The tested code/configuration/harness commit is
`9701db331411efb2af66ce25440e696373b1df79` (proof/interface commit
`97f2b1fd80d64d31b9609fe2e4954a44cc4545e9`).  Stable Challenge and Solution
exports are respectively 15,610,269 bytes,
`a26f6ea34d668a5892c4cfcba13969b945b915ab612d23e029c418fbe9c4789f`,
and 155,636,209 bytes,
`0159636259a723892090969b9f4d06909c4ce09c2d6526d4b71d248221b6e766`.
The one cumulative Four Comparator payload accepted the exact pair through
con-ron, NanoDa, and Lean's default kernel and printed `Your solution is okay!`.
Contained elapsed time was 142.732 seconds; aggregate peak memory was
771,825,664 bytes, with zero pressure, high/max, deadline, swap, or OOM events.

Four declarations are migrated and locally kernel verified.  Five migrations
and complete official Palomar verification remain.  This local pass is not an
official submission or registry acceptance.  Detailed evidence is indexed in
`Audit/palomar-four-pi-one-20260929/`.

## 2026-09-29 integrated TermSubst repair and cumulative Three pass

The exact TermSubst bound-variable replacement was integrated in the actual
Foundation `Functions.lean` context.  The strictly compiled source preserves
the blueprint, all three computational fields, and the unchanged fvar/func
proof fields.  `constructionBvarDefinedExact` is inferred from the new field
theorem's projection: its raw type is not expression-identical to the unfolded
field obligation, while an ordinary Lean theorem checks their kernel
convertibility.  The new proof path excludes the former expensive proof body
and uses only `propext`, `Classical.choice`, and `Quot.sound`.

The integrated construction export is 43,708,676 bytes, with 774,125
expression records and 7,984 declaration records, SHA-256
`e1e79e14a42c5cf31b3c12c0ecc0a146399a8f62ed9550df7d3c843e56e5ba6d`.
Stock verified con-ron accepted its 7,980 declarations and completed 7,602
checks in 24.250 seconds (24.481 seconds contained elapsed), peaking at
253,480,960 bytes with no pressure, limit, deadline, swap, or OOM event.

The scoped Foundation repair is public at
`https://github.com/flengyel/foundation.git`, branch
`palomar-termsubst-bvar-repair-20260929`, exact commit
`01f617fbe240a84aaf1c45b31b9d65e0a2e21c1d`, parent
`46715b758b3069351825f276f1d98de1e60f1e4f`.  Project commit
`9dc0a581dcc023fa0918cdf05e38c7c5288907de` pins that immutable revision;
Mathlib, Lean, and the verifier remain unchanged.  The active Functions target
and `SolutionThree` rebuilt successfully, and all focused strict, exact
interface/ownership/shared-body, Challenge source-policy, recursive
axiom/dependency, route-separation, configuration, and negative-regression
gates passed.  The selected closure is 21,260 constants (4,153 marginal over
the first-two union).

The cumulative Three Comparator used stable authenticated exports.  Challenge
is 14,380,640 bytes, SHA-256
`d4082d08628fff75f298333d2aa71944a22a73ab25d163439679f9908fc513ae`;
Solution is 154,914,915 bytes, SHA-256
`f67bbf4bb981e813f60061cc54b5bd6d097ceb8ca92104ef838e71aee507d7e6`.
Comparator accepted the exact three selected declarations through con-ron,
NanoDa, and Lean's default kernel and printed `Your solution is okay!`.
Contained elapsed time was 161.947 seconds, peak aggregate memory was
779,714,560 bytes, and no pressure, high/max, deadline, swap, or OOM event
occurred.  This is a complete local Comparator pass for the cumulative Three
pair, not official Palomar verification or verification of the six remaining
declarations.

Three declarations are now migrated and locally kernel verified.  Six
declaration migrations and complete official verification remain.  Detailed
evidence is indexed in `Audit/palomar-termsubst-integration-20260929/`.

## 2026-09-29 TermSubst bound-variable proof experiment

The exact standalone replacement for
`FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_2`
strictly compiles, has the same universe-renamed/alpha-normalized type, excludes
the original helper from its 1,719-declaration recursive closure, and uses only
`propext`, `Classical.choice`, and `Quot.sound`.  Its 43,394,988-byte export has
SHA-256
`1234ba6a1a2533a797a0c3a8f1482b849e3b2d24cc3acae85deab90aaf0351ce`.
Stock verified con-ron accepted 7,953 declarations and completed all 7,576
checks in 29.239 seconds; the contained workload elapsed 29.495 seconds and
peaked at 247,910,400 bytes with no pressure, limit, deadline, swap, or OOM
event.

The actual one-field Foundation patch also strictly compiled.  Body-sensitive
snapshots preserve the blueprint, the three computational fields, and the
unchanged fvar/func proof fields (modulo generated-name renumbering), while the
construction's 8,551-declaration closure reaches the new field proof under only
the permitted axioms.  Its final exact-contract gate failed, however: an
explicitly stated named theorem is definitionally equivalent to the field
obligation but differs as a raw expression (`OfNat.ofNat` versus `HAdd.hAdd` at
the first normalized difference).  Both authorized actual-context compile
payloads were already consumed, so no third source revision was compiled.  The
single checker allowance was therefore used on the expressly permitted
standalone fallback, not an integrated construction.

No local Foundation repair commit was created, nothing was published, and the
project/Foundation pins remain unchanged.  An audit-overlay symlink-copy error
temporarily overwrote four active compiled companion files, but no source,
manifest, pin, public `.olean`, or `.ilean`.  Exact setup-based reconstruction
reproduced the retained public artifacts byte for byte and restored all
companions; the active Foundation checkout is clean at
`46715b758b3069351825f276f1d98de1e60f1e4f`.  Detailed evidence is indexed in
`Audit/palomar-termsubst-repair-20260929/`.

The next bounded step is to infer the integrated exact theorem's type directly
from the named field projection, then recompile and audit that source before an
integrated replay.  Publication/pinning, downstream validation, cumulative
Three verification, six migrations, and complete official verification remain.

## 2026-09-28 cumulative Three con-ron declaration localization

The tested mathematical candidate and configuration remain
`8094240bb8bfedc34fb875140111f95aabdf79b8`; Challenge/Solution sources,
dependency pins, and the portable Comparator configuration were unchanged.  The
checked diagnostic commit is `d734d8aa53ffc79d639848281ce76db19f57e551`.
The surviving 154,905,023-byte cumulative Solution export was copied to stable
local evidence before replay and now has SHA-256
`64877ccc19f40fc23b59545e0f7afd26f0a6e9dd7ff00c2921620476be5dfe62`.
Because the earlier archive omitted this hash, it authenticates the diagnostic
input but cannot retroactively prove byte identity with the previous Comparator
input.  Source, pin, compiled-module, root, axiom, and command provenance all
match the recorded candidate.

Stock con-ron was run with `--verified --jobs=1 --progress=1` under the unchanged
8 GiB high/10 GiB max, zero-swap, one-CPU containment.  The full export
completed 16,967 of 19,728 checks, last completing
`TermSubst.construction._proof_7` at 61.079 seconds.  The next installed and
exported declaration was `TermSubst.construction._proof_2`.  The PSI guard
stopped the run at 215.675 seconds (139.527 aggregate CPU), 8,955,527,168 bytes
peak, 8,207 high events, full PSI `avg10=98.32`, and zero max/OOM events.  No
verdict was issued.

The pending `_proof_2` theorem has an 8,516-constant closure with exactly the
permitted axioms.  Its 43,376,011-byte dependency-closed export has SHA-256
`58120b32d32e3bab1b355e1fc77e52c2707b6e28e2bdd9641a7afbe29f79de7b`.
Alpha-normalized structural hashes show that its exact type and body match the
full export.  In the isolated replay, con-ron completed 7,562 of 7,568 checks,
last completing `nth.congr_simp`; `_proof_2` was again the next installed and
exported declaration.  This run pressure-stopped at 170.616 seconds (90.799
aggregate CPU), 8,973,803,520 bytes peak, 6,484 high events, full PSI
`avg10=98.36`, and zero max/OOM events.  `_proof_7` is absent from this closure,
and the full replay had already passed `nth.congr_simp`, so the two runs
reproduce the common `_proof_2` check boundary rather than merely naming the
last completed predecessor.

The generated theorem is reached by the `bvar_defined` field proof
`by simp [blueprint]` at Foundation
`Bootstrapping/Syntax/Term/Functions.lean:25`.  This localizes a stock con-ron
performance boundary; it does not identify the checker's internal reduction or
allocation mechanism and is not a theorem rejection.  No proof rewrite or full
Comparator run was made.  The smallest proposed follow-up is an exact-type,
one-field factoring through an explicit evaluation/substitution identity and
the existing `nth_defined.iff`, followed by unchanged stock-kernel validation.

Exactly two checker payloads used 386.291 seconds of the 540-second budget.
Both owned cgroups were empty after cleanup.  Cumulative Three still has no
con-ron, NanoDa, or Lean verdict on the repaired pin.  The first two results
retain their historical complete local pass; six migrations and complete
official verification remain.  Detailed evidence is indexed in
`Audit/palomar-three-conron-localization-20260928/`.

## 2026-09-28 downstream build recovery and cumulative Three checkpoint

The unchanged public Foundation repair remains pinned at
`46715b758b3069351825f276f1d98de1e60f1e4f`.  The unchanged
`Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions` target
first demonstrated a contained hard-cap resource failure under the authorized
build-only 10 GiB profile: 223.424 seconds, exactly 10,737,418,240 bytes peak,
142,817 `memory.max` events, one OOM event, and three OOM kills.  This was a
compiler resource result, not a Lean theorem rejection, and qualified the
single 12 GiB fallback.

The same target then built successfully under the admitted build-only 12 GiB
profile in 208.406 seconds at 12,884,889,600 bytes peak.  Its live host reserve
guard never crossed the 2 GiB floor.  The downstream `SolutionThree` target
subsequently built in 959.000 seconds at 2,057,461,760 bytes peak.  One Lean
compiler at a time was observed.  These build-only limits are local development
settings and are not the Comparator or official-verifier profile.

The new-pin strict checks, exact Three ownership/type/shared-body comparison,
pinned Challenge source policy, permitted-axiom audit, per-root dependency and
proof-route audit, negative regressions, and portable-configuration check all
passed.  The cumulative closure is 21,256 constants: 17,085 for the first root,
17,107 for the productive root, and 20,331 for the Gödel root, adding 4,149 over
the first-two union.  The only three additional constants relative to the old
Foundation pin are the named factored proof helpers.  Productive and
Gödel/Craig reachability remain separated, and the recursive axioms remain
exactly `propext`, `Classical.choice`, and `Quot.sound`.

The exact tested project/configuration commit is
`8094240bb8bfedc34fb875140111f95aabdf79b8`.  The cumulative Comparator used
the unchanged checker containment: 8 GiB high, 10 GiB max, zero swap, one CPU
and Lean thread, 4 GiB available reserve, and the 1,200-second deadline.  Its
first parent invocation failed before any payload because `/usr/bin/time` was
absent; telemetry contains no Lake, Lean, exporter, Comparator, or checker
process.  After the specifically allowed GNU-time correction, the second
parent was the only actual Comparator payload.

That payload built and exported the exact ChallengeThree and SolutionThree,
then started stock con-ron.  The pressure guard stopped the owned workload at
275.973 seconds after full-memory PSI stayed at least 80% for 60 seconds.
Aggregate CPU was 195.022 seconds, peak memory 8,959,299,584 bytes, and there
were 8,666 `memory.high` events, zero hard-max events, and zero OOM events.
Con-ron issued no verdict; NanoDa and Lean replay did not start.  The deadline
did not fire, cleanup left the owned cgroup empty, and no retry was made.  This
is an inconclusive resource result, not a rejection or a local three-result
pass.

The first two declarations retain their historical complete local
three-kernel pass for the recorded Two checkpoint.  The third declaration is
migrated and exactly checked on the repaired pin but still lacks cumulative
external verification.  Six migrations and complete official verification
remain.  Detailed evidence is indexed in
`Audit/palomar-foundation-build-recovery-20260928/`.

## 2026-09-28 containment continuation and public repair pin checkpoint

The ordinary WSL workload context reports an operational systemd 257.13 user
manager (`running`, no failed units) and a writable delegated cgroup v2 with
`cpu`, `memory`, and `pids`. The Codex filesystem sandbox instead receives
`Operation not permitted` from the same manager query. The earlier launcher's
generic error discarded this distinction, so its archived message alone did
not identify the old manager state. The launcher now classifies operational,
degraded, transitional, unreachable, permission-denied, and missing/read-only
delegation states separately. Its 21 regressions pass, including reachable
degraded, unreachable, and missing-controller fixtures.

Two harmless exact-path smoke launches were recorded. The first exposed only
a diagnostic mistake caused by bubblewrap's private cgroup namespace. After
passing the authenticated host leaf to the diagnostic payload, the second
verified the actual pressure supervisor, cgroup placement and cleanup, one CPU,
`memory.high=8G`, `memory.max=10G`, zero swap, bubblewrap read-only input, and a
parent/child/grandchild process tree. No resource event occurred.

The continuation then made one actual stock con-ron launch against the retained
integrated-construction export, SHA-256
`8d1ae06a757442846b5f3ad7190433adb7b462d97147f9132e2ed7011038ac63`.
Con-ron explicitly accepted 8,090 declarations in verified mode and completed
all 7,707 checks in 22.052 seconds, at 247,754,752 bytes aggregate peak memory,
with no pressure, high/max, deadline, swap, OOM, OOM-kill, or pids event. The
previous checkpoint remains one parent invocation, zero checker launches, and
a setup failure; it has not been reclassified as a pass.

The exact Foundation repair
`46715b758b3069351825f276f1d98de1e60f1e4f` was published without altering its
parentage at `https://github.com/flengyel/foundation.git`, branch
`palomar-helper-repair-20260928`, and confirmed publicly fetchable. Project
checkpoint `53afd6ae8a056eb0dbd5618e49b6025066bb2199` pins that full commit. Lake
resolved the active dependency from the public URL; all unrelated manifest
entries stayed unchanged, and the repaired source hash matches the tested
isolated build. The active repaired `Basic` module rebuilt successfully in
47.681 seconds at 992,169,984 bytes peak without a resource event.

The affected downstream build then stopped at
`Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions`. The
mandated pressure guard terminated it after 205.856 seconds when full-memory
PSI had remained at least 80% for 60 seconds. Peak memory was 8,974,295,040
bytes, with 6,898 `memory.high` events and last full PSI `avg10=97.38`; hard-max,
swap, OOM, OOM-kill, and pids events were zero. This is an inconclusive build
resource result, not a Lean theorem rejection. Under the task's stop rule, the
strict/interface/source-policy/dependency gates were not rerun on the new pin
and no cumulative Three Comparator parent or payload was launched.

Thus the repair is publicly pinned and its actual construction export is
stock-con-ron accepted, but the Three candidate is not fully rebuilt or locally
cumulative-kernel verified on the new pin. ChallengeThree, SolutionThree, the
Gödel bridge, and the portable configuration are byte-unchanged from
`b557d255f1d0b42920440cb2d4762b1ca54b2728`. The first two declarations retain
their historical Two-pair pass for its recorded pin. Third-result external
verification, six migrations, and complete official verification remain.
Detailed evidence is indexed in
`Audit/palomar-foundation-continuation-20260928/`.

## 2026-09-28 local Foundation integration checkpoint

The factored proof was integrated into an isolated checkout of Foundation at
parent `e72cfe981aa65166f37fa4e2584f4806bc48d72f` and committed locally as
`46715b758b3069351825f276f1d98de1e60f1e4f`.  The ordinary contextual patch
applies cleanly to that parent and changes only
`Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Basic.lean`.
It preserves the blueprint and computational record fields and replaces the
`construction.func_defined` proof with the named factored proof.

The real modified Foundation target and all 1,071 dependencies were rebuilt in
an isolated Lake build.  The target build passed in 1,079.365 seconds at
5,301,583,872 bytes peak, and an explicit
`-DwarningAsError=true` recompilation of the modified module passed in 52.086
seconds at 540,504,064 bytes peak.  Neither run recorded pressure, limit,
deadline, swap, or OOM events.  Separate baseline/repaired environments give
exact normalized matches for the public `blueprint` type and body,
`construction` type, and the `func_defined` obligation.  The rebuilt
construction directly reaches the named factored proof; its recursive axioms
are exactly `propext`, `Classical.choice`, and `Quot.sound`.  The factored
proof's 8,660-constant closure does not reach the former expensive generated
proof.  The generated name `construction._proof_4` is reused for the unrelated
`bvar_defined` field and is not evidence of a stale proof.

The actual record-context export is 44,064,407 bytes with 779,210 expression
records and 8,094 declaration records, SHA-256
`8d1ae06a757442846b5f3ad7190433adb7b462d97147f9132e2ed7011038ac63`.
The single authorized stock con-ron parent invocation then failed at the
containment systemd-manager preflight, before a run directory or con-ron
process was created.  The task expressly counts setup failures, so no retry was
made.  Consequently the standalone acceptance gate did not pass, the local
Foundation commit was not published, the project remains pinned to `e72cfe9`,
and no cumulative Three Comparator attempt was authorized.  This is a checked
local integration and a recorded gate/setup failure, not a public pinned
repair or third-result kernel pass.

## 2026-09-27 exact Foundation helper replacement diagnostic

The Palomar candidate remains at tested proof/configuration commit
`b557d255f1d0b42920440cb2d4762b1ca54b2728`; no Challenge, Solution,
comparator configuration, or dependency pin changed.  Diagnostic commit
`996f70e1630602a7543a43c7ed87adec02ac841a` proves a project-local
replacement for
`FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.construction._proof_4`.
Its universe-renamed elaborated type exactly matches the generated helper, its
8,661-constant recursive closure excludes the original helper, and its only
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The unchanged 44,002,216-byte helper export timed out without a verdict under
both Lean's export checker (120.379 seconds, 8,895,926,272 bytes peak) and
NanoDa (120.957 seconds, 5,317,881,856 bytes peak).  Thus the original input's
bounded failure is not shown to be con-ron-specific.  Neither run emitted a
progress marker establishing that it reached the suspect helper, and their
resource profiles differ.  The timed attribution source was the unretained
`PieceBlueprint.lean`; the retained `BlueprintConversionControl.lean` was not
compiled and has no timing attached to it.  The factored proof avoids broad
unfolding, but the original stall mechanism remains unknown.

The direct Lean-checker command omitted Comparator's `--silent` option, while
still producing no progress; its separate help capture failed on an
incompatible cached Lean-4.34.1 `Leanc.olean` and is not interface evidence.
The diagnostic NanoDa configuration set `num_threads` to 1.  End-to-end
supervisor elapsed time exceeded the two 120-second deadlines by 0.379 and
0.957 seconds respectively.

The replacement uses targeted projection reduction, the existing
`val_mkSigma` and substitution identities, and `listMax_defined.iff`.  Its
44,022,108-byte dependency-closed export was explicitly accepted by the
unchanged bundled stock con-ron in verified mode: 65.935 seconds and
239,558,656 bytes peak, with no pressure, limit, deadline, or OOM events.  The
replacement body has 134 distinct expression nodes versus 583 in the original;
the export itself is slightly larger, so file-size reduction does not explain
the result.

This establishes a checked exact-type local replacement candidate, not an
integrated Foundation repair at that historical checkpoint.  Its compile
omitted `-DwarningAsError=true`, although no warnings were printed.  The pinned
Foundation checkout and candidate manifest remained unchanged, and no
cumulative Three Comparator was run.  The later local integration outcome is
recorded above.  The third declaration therefore remains migrated and exactly
checked but not locally cumulative-kernel verified; six declarations and
official verification remain outstanding.  Full diagnostic evidence is in
`Audit/palomar-foundation-helper-replacement-20260928/`.

## 2026-09-27 Gödel-II con-ron bottleneck diagnosis

The Three mathematical checkpoint remains unchanged at tested proof commit
`b557d255f1d0b42920440cb2d4762b1ca54b2728`.  Memoized expression-DAG
profiling and dependency-closed stock con-ron probes localize the earlier
resource timeout to the pinned Foundation declaration
`FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.construction._proof_4`.
This auto-generated `simp [blueprint]` proof has only 583 pointer-distinct and
583 structurally distinct body nodes, but con-ron does not complete its check
under the checkpoint limits.

The 44,002,216-byte helper-only export contains 778,146 expression records and
8,077 declaration records.  Con-ron completes the immediately preceding
`listMax.congr_simp` check, then reaches the 120.359-second diagnostic deadline
without another heartbeat.  It peaks at 8,710,561,792 bytes, records 47,191
`memory.high` events, and reaches full-memory PSI `avg10=86.6`; max, OOM,
OOM-kill, swap, and pids events remain zero.  The larger axiom-code bridge
reproduces the same boundary.  Its exact dependency path begins at
`reAxiomCodes_toFoundation_iff`, enters the maintained
`FailureOfComposition.AxiomCodes` quotation machinery, and reaches the
Foundation construction proof through `termBVVec`.

The four permitted diagnostic probe slots used 390.927 seconds of active
checker wall time.  The first slot failed in bubblewrap before con-ron started
and is still counted; the corrected bridge probes and helper-only probe all
completed parsing and installation but returned no check verdict.  The early
pressure guard was validated with a synthetic fixture.  Full profiler,
overlap, export, and probe details are retained in
`Audit/palomar-godel-bottleneck-20260927/` and the checkpoint archive.

No narrow candidate-side repair is supported by these measurements.  The
offending proof belongs to the pinned Foundation revision and is already
forced by the maintained axiom-code type; changing a local wrapper would not
remove it.  Dependencies and mathematical proofs were left unchanged.  The
gate for a new cumulative Three Comparator attempt was therefore not met, and
no full attempt was launched.  Three declarations remain migrated and exactly
checked, only the first two remain locally three-kernel verified, six
declarations remain unmigrated, and official verification remains outstanding.

## 2026-09-27 cumulative Gödel-II quotient checkpoint

Tested code commit `b557d255f1d0b42920440cb2d4762b1ca54b2728`
adds the third eligible result,
`FailureOfComposition.Palomar.no_quotient_composition_godel`, through the
maintained Gödel-II and Craig-presentation route.  The public theorem has the
same independent assumptions and pointwise-quotient conclusion as the
productive result.  `GodelQuotientBridge.lean` transports deductive PA
extension, consistency, and r.e. axiom codes to the maintained theory, applies
`ConcreteIndices.no_index_quotient_via_godel_of_re_axioms`, and transports the
conclusion back through the checked identity-on-representatives quotient
correspondence.  The Delta-one Craig presentation remains internal to the
maintained proof.

`ChallengeThree.lean` is 36,005 bytes and 963 lines, imports only the same two
permitted Mathlib modules as ChallengeTwo, and has exactly the three selected
theorem holes and no definition holes.  `SolutionThree.lean` owns all three
selected declarations.  Its productive theorem still calls its owned
first-result wrapper; its Gödel theorem instead calls the separate new bridge.
Solution imports no Challenge module.  The exact separate-environment checker
compares 4,065 recursively reachable statement declarations, including shared
bodies and metadata, and rejects changed shared definitions, a Two-only
selection, and legacy, One-only, or Two-only module overrides.  Strict source
checks, permitted-axiom checks, and the pinned Challenge source-policy audit
all pass.

The complete proof closures contain 17,085 constants for the first root,
17,107 for the productive quotient root, and 20,328 for the Gödel quotient
root.  The three-root union contains 21,253 constants, adding 4,146 over the
17,107-constant two-result baseline.  The retained complete name sets show
that the Gödel root reaches the maintained r.e.-axiom Gödel obstruction,
Craig presentation, equivalent-presentation bridge, concrete Gödel
noncongruence, and graph Gödel theorem.  It reaches none of the audited
productive escape, first-result, or productive quotient proof roots.  The
productive root continues to reach its owned first-result theorem and reaches
none of those Gödel/Craig declarations.  This is proof-route reachability, not
a claim of logical independence.  Every root's recursive axiom closure is
exactly `propext`, `Classical.choice`, and `Quot.sound`.

Portable `comparator-three.json` has SHA-256
`72d9a84010d5ac2e8fb2e0144a58adf06b623e7d266a816b468b3e2cd6da5265`
and contains no machine-specific kernel commands.  Its protected local copy
differs only by the authenticated con-ron and NanoDa commands and has SHA-256
`28077cc3bc32e0b503297303fedb18b477109b0015d2f790f1d4fb8bad4b139f`.
The run resolved the toolchain from the `Lean/` project and queried the exact
prefix executable: Lean 4.35.0-rc2 at
`11acb17ec6b07a8f9e9173e6845197929540936b`.

After the focused gates passed and the tested commit was published, the one
permitted cumulative three-result Comparator attempt built and exported the
exact ChallengeThree/SolutionThree pair and started con-ron.  It reached the
1,200-second hard deadline before con-ron returned a verdict; NanoDa and Lean's
default kernel did not start.  Supervisor elapsed time was 1,200.657 seconds,
exit status was 124, and `deadline_fired=true`.  Peak aggregate cgroup memory
was 9,364,590,592 bytes.  The 8 GiB soft threshold recorded 39,846 high events
and sustained pressure, but the 10 GiB hard maximum recorded zero events;
swap, OOM, OOM-kill, and pids-limit events were all zero.  No verification
process remained afterward.  This timeout is an inconclusive resource result,
not a kernel rejection, and no retry was launched.

Accordingly, three declarations are now migrated and exactly checked, but only
the first two retain a completed local three-kernel Comparator pass.  The third
is not recorded as locally kernel-verified.  Six declarations remain
unmigrated, and official verification remains outstanding.  No submission,
registration, merge to `main`, Palomar contact, manuscript edit, or later-result
migration was performed.

## 2026-09-27 cumulative productive-quotient checkpoint

Tested code commit `4dba750bec8c81a30e0bfe8ab4126e35cbadddb8`
adds the second eligible result,
`FailureOfComposition.Palomar.no_quotient_composition_productive`, as a
corollary of the checked four-witness theorem.  `ChallengeTwo.lean` is 35,259
bytes and 947 lines, imports only `Mathlib.Computability.RE` and
`Mathlib.Data.Fin.VecNotation`, and has exactly the two selected theorem holes.
`SolutionTwo.lean` owns proved wrappers for both selected declarations and
does not import either Challenge module.

The independent statement uses
`IndexQuotient T := Quot (PointwiseIndex T)` and the explicit representative
`indexQuotientMk`.  The Solution proves that `PointwiseIndex T` is an
equivalence relation for deductive PA extensions, constructs the identity-on-
representatives equivalence with the maintained quotient, proves its
representative equation and
`indexQuotientMk T e = indexQuotientMk T d ↔ PointwiseIndex T e d`, and proves
equivalence of the independent and maintained no-composition assertions.  A
separate pure-LK lemma obtains every external pointwise instance from one
internally universal `UniformIndex` proof.  The selected corollary uses the
owned first-result wrapper and the direct representative chain; it does not
invoke the old complete quotient obstruction or the Gödel-II route.

`CheckTwoInterface.lean` checks the two modules in separate environments,
requires both declarations to be owned by the intended modules, compares the
universe-renamed types and the entire recursively reachable shared statement
graph, excludes only the two selected Challenge proof bodies, and audits each
Solution proof closure.  The shared graph has 4,064 constants.  The first and
second Solution closures have 17,085 and 17,107 constants respectively; their
union has 17,107, adding 22 constants over the first-result baseline.  The
second closure reaches the owned first-result theorem and reaches none of the
audited old complete quotient, Gödel-II, semantic-completeness, or theorem-code
routes.  Its recursive axioms are exactly `propext`, `Classical.choice`, and
`Quot.sound`.  Changed shared definitions, one-result selection, legacy-module
selection, and One-only module selection are all rejected by retained negative
tests.  The pinned source-policy audit reports no untrusted Challenge source.

The portable `comparator-two.json` contains no machine-specific kernel paths;
its SHA-256 is
`f9bc72802f3d52589a125b22ec1c4e0da6b68b3c02e320c6687c68e895a744c3`.
The protected local copy differs only by the authenticated con-ron and NanoDa
commands and has SHA-256
`7307033e3a3c37b9db85c5da3b83cf664fd104eefc4b50e1967be6d84bf1a13f`.
The run resolved the pinned prefix from the `Lean/` project and obtained Lean
version and commit from that prefix's exact executable: Lean 4.35.0-rc2 at
`11acb17ec6b07a8f9e9173e6845197929540936b`.

After all focused gates passed and the tested commit was published, the single
permitted cumulative two-result Comparator attempt passed in 131.755 seconds.
ChallengeTwo and SolutionTwo built and exported; con-ron accepted 16,218
declarations, NanoDa accepted, Lean's default kernel accepted, and Comparator
reported `Your solution is okay!`.  The run used one CPU and one Lean thread,
`memory.high=8G`, `memory.max=10G`, zero swap, a 1,200-second hard deadline,
and 30-second termination grace.  Peak aggregate cgroup memory was 740,855,808
bytes.  There were no pressure, high/max, deadline, swap, OOM, or OOM-kill
events, and no verification process remained afterward.

This is a local Comparator pass for exactly two results, not complete official
verification.  The seven other declarations remain unmigrated and unchecked
by this eligible cumulative pair.  No submission, registration, merge to
`main`, Palomar contact, manuscript edit, or subsequent-result migration was
performed.

## 2026-09-27 exact first-result validation and cost checkpoint

The exact `ChallengeOne`/`SolutionOne` pair is now checked independently of the
legacy nine-result pair.  `CheckOneInterface.lean` loads the two One modules in
separate environments, requires each selected declaration to be owned by the
intended module, and selects only
`FailureOfComposition.Palomar.obstruction_four_properties`.  It compares the
universe-renamed theorem type and recursively compares every reachable
statement-side declaration type and shared body.  It also checks that Solution
does not import Challenge, that the Challenge's only declaration using its
deliberate hole is the selected theorem, that definition-hole selection is
empty, and that the Solution proof closure uses only `propext`,
`Classical.choice`, and `Quot.sound`.

That exact shared declaration graph has 4,061 constants.  The corresponding
full Challenge proof/axiom closure has 4,062 because it additionally includes
the selected theorem's `sorryAx`; this accounts for the earlier reported 4,062
count.  The Solution proof closure has 17,085 constants.  A disposable negative
test with the same outer theorem type and a changed shared definition body is
rejected, and the first-result command rejects attempts to select the legacy
`Challenge`/`Solution` modules.  The pinned Palomar source-policy audit passes
for the three resolved ChallengeOne dependency sources.  The existing
`CheckInterface.lean` and `comparator.json` remain explicitly the legacy
nine-result check and configuration.

The large syntactic implication was profiled without normalization or
reduction.  Across the complete selected Solution closure, raw recursive tree
counting gives 2,339,825 type nodes and 146,843,997 body nodes (149,183,822
total).  Deduplicating by actual `Expr` pointer identity separately within each
declaration gives 3,927,585 nodes; deduplicating pointer identity globally
across the closure gives 2,456,546.  Structural `Expr.eqv` deduplication gives
3,918,882 per declaration and 1,958,995 globally.  These latter structural
sets measure alpha-equivalent expression structure, not physical sharing or
checking complexity.

For `uniformSentence_imp_uniformKleeneSentence`, the 5,284,884 raw body nodes
collapse to 3,518 physical pointer-distinct nodes and 3,437 structurally
distinct nodes.  Its `simpa [source, target, p, q, Semiformula.free]` identity
has 313,269 raw nodes but 792 pointer-distinct nodes.  The final
`LK.Derivation.cast` has 4,957,443 raw nodes but 2,787 pointer-distinct nodes;
its equality proof accounts for 4,956,721 raw and 2,781 pointer-distinct nodes.
`uniform_one`, measured separately, has 1,067,954 raw and 4,282
pointer-distinct body nodes.  Thus the raw recursion repeatedly recounts a
small shared DAG.  No proof refactor was made: moving or splitting the shared
term would not demonstrate an aggregate representation saving.

The pinned exporter uses one global visited-expression map for an export, so
its expression records are structurally deduplicated across declarations.  An
exact Comparator-style SolutionOne export is 111,171,395 bytes, SHA-256
`73167f386626484bfda122998a2fc5b51a70ae1ef5800efb168fe72aaa1bc6a7`,
with 1,976,236 expression records and 16,200 declaration records.  An isolated
export rooted at the profiled implication is 21,628,085 bytes, SHA-256
`00fa4693703c0683cd136eb0dc5aac059bf0b421fb2b26d1342bb55279d241b8`,
with 371,912 expression records and 4,795 declaration records.  Full export
dumps remain local and are not evidence-bundle payloads.  A strict direct check
of `ManuscriptObstruction.lean` passed in 21.848 seconds of supervised elapsed
time with 340,574,208 bytes peak aggregate cgroup memory.

Tested code commit `2304008d712c020bcc528412ed17c43dc46717d4`
adds the exact checker and protected One-pair configuration; the proof sources
are unchanged from the integrated refactor commit
`c016ecf20e06fcb0b4b8c391fe1a2705e80d78c4`.  After the focused strict,
interface, negative, source-policy, recursive-axiom, and profile gates passed,
the single permitted local first-result Comparator attempt completed in
139.167 seconds.  ChallengeOne and SolutionOne built and exported; con-ron
accepted 16,196 declarations, NanoDa accepted, Lean's default kernel accepted,
and Comparator reported `Your solution is okay!`.  The run used one CPU and
one Lean thread with `memory.high=8G`, `memory.max=10G`, zero swap, a
1,200-second deadline, and 30-second termination grace.  Peak aggregate cgroup
memory was 2,815,442,944 bytes; there were no high/max/OOM events, no deadline,
and no recorded memory-pressure stall time.

This is a local pass for the exact first-result pair, not a complete official
verifier pass.  The other eight declarations remain outside this checkpoint.
The complete Solution is not claimed to be Foundation-free: the targeted
refactors remove specific dependency routes while retaining maintained
evaluator and witness results.  No submission, registration, merge to `main`,
Palomar contact, or manuscript edit occurred.

## 2026-09-27 targeted modularity checkpoint

The earlier inference that a complete independent reconstruction was already
necessary is superseded by measured, checked refactors at two narrower
boundaries.  The exported first-result proof now uses both replacements:

- `uniformSentence_imp_uniformKleeneSentence` is an explicit syntactic LK
  implication from the maintained uniform graph sentence to the Kleene
  sentence.  The final transport uses its one-way corollary and no longer
  depends on `uniformIndex_toFoundation_iff` for either middle clause.  The
  existing biconditional remains available for other callers.
- `DirectDerivationEnumeration.lean` implements an external effective checker
  for every rule of the independent arithmetic calculus, finite r.e.-axiom
  evidence, sound reconstruction of an actual `Proof`, and serialization of
  every actual `Derivation`.  The first integrated candidate used its
  maintained theorem-code transfer.  The final candidate instead enumerates
  independent `Provable T` directly and composes that predicate with the
  primitive-recursive independent history-divergence sentence in
  `DirectDivergenceBridge.lean`.  Productiveness and the existing concrete
  four-witness laws then meet at that smaller boundary.  The final proof no
  longer calls
  `reAxiomCodes_toFoundation_iff`, `theorem_codes_re_of_axiom_codes`, or
  `obstruction_four_properties_of_re_axioms`.

The first integrated candidate decreased the complete selected Solution
closure from 19,259 to 18,970 constants.  The final direct-divergence candidate
decreases it to 17,085, with its unchanged type closure still 4,060 constants;
the evaluator obstruction body closes over 17,084.  A source-local
reconstruction of the old proof measures 2,720 removed and 546 introduced
closure names.  Excluding the two comparison-root identities on each side,
the substantive counts are 2,718 removed and 544 introduced, a net reduction
of 2,174.  The direct theorem-code enumerator closes over 7,189 constants, the
generic independent-provability enumerator over 7,192, the direct divergence
primitive-recursiveness proof over 7,294, and the retained but unused
Foundation theorem-code transfer over 15,474.

Expression-node counts are raw `Lean.Expr` tree nodes without normalization,
not runtime or memory measurements.  The syntactic uniform implication has a
large 5,284,884-node proof value despite its 5,217-constant closure; the direct
enumerator theorem has 27,376 proof-value nodes.  Thus the constant closure is
strictly smaller.  The next Comparator candidate is the exact checked
`Palomar.SolutionOne` first-result proof from this checkpoint; the large
explicit LK proof term remains a documented performance risk, not an
unproved obligation.  No Comparator was launched in this checkpoint.

Focused builds and strict warning-as-error checks pass for the new enumerator,
the direct divergence bridge, `ManuscriptObstruction`, `ObstructionBridge`,
and `SolutionOne`.  The local nine-declaration Challenge/Solution comparison
passes with exact types.  The selected proof and new helpers use only
`propext`, `Classical.choice`, and `Quot.sound`; they introduce no `sorry`,
`admit`, or `native_decide`.  The Challenge type and its 4,062-constant closure
are unchanged.  The complete official verifier was not launched, and the
other eight selected declarations remain subsequent work.

## 2026-09-26 first-result interface checkpoint

Commit `76f8139b5f33cc7e7dfbaf81c0141df81c11ff75` advances the recovered
`279001c43fd324fe48ec443858fb1bd7e47e6859` checkout through the first faithful
target.  It adds an independent arithmetic/evaluator statement interface, the
concrete Foundation correspondence, and a one-theorem Challenge/Solution pair
for `obstruction_four_properties`.  The theorem retains the consistent r.e.
deductive-PA-extension hypotheses, the external pointwise clauses, and both
single-sentence internal uniform clauses.

The correspondence is now split deliberately:

- `ArithmeticInterface.lean` and `EvaluatorInterface.lean` contain the
  independent definitions used identically by the Challenge and Solution.
- `ArithmeticBridge.lean` and `EvaluatorBridge.lean` contain syntax,
  derivation, evaluator, and pointwise correspondence.  The evaluator bridge
  no longer imports the manuscript obstruction.
- `ObstructionBridge.lean` is the only layer importing
  `ManuscriptObstruction`; it contains uniform-index conversion and the final
  first-result transport.
- `ChallengeOne.lean` is 34,291 bytes and 974 lines, imports only
  `Mathlib.Computability.RE` and `Mathlib.Data.Fin.VecNotation`, and has exactly
  its one deliberate theorem hole.  `SolutionOne.lean` does not import it.

Checked commands ran one contained workload at a time with one CPU,
`memory.high=8G`, `memory.max=10G`, and zero swap.  The relevant retained run
directories below `.codex-work/palomar/continuation/20260926T120622Z/` are:

- `evaluator-bridge-simp-only-strict-59`: strict direct evaluator-bridge check,
  exit 0.
- `evaluator-bridge-simp-only-build-60`: Lake build with no warnings, exit 0.
- `modular-solution-one-final-build-61`: modular Solution build with no
  warnings, exit 0.
- `modular-solution-one-final-strict-62`: strict direct Solution check, exit 0.
- `challenge-one-final-64`: normal Challenge check allowing its deliberate
  hole, exit 0.  The preceding strict diagnostic rejected only `uses sorry`.
- `check-one-final-modular-17`: exact Challenge/Solution dependency comparison,
  exit 0 and 4,062 exactly matching statement-side constants.

The real one-result Comparator built and exported the pair, then reached
`Running con-ron kernel on solution`.  Run `comparator-one-run-3` ended at its
7,200-second guard (supervisor elapsed 7,201.855 seconds, exit 137), with
`deadline_fired=true`, peak memory 8,710,762,496 bytes, and zero `memory.max`,
OOM, or OOM-kill events.  The 8 GiB soft ceiling caused about 90% full memory
pressure.  A bounded retry with a 9 GiB soft ceiling was stopped deliberately
after the proof-architecture concern was raised; `comparator-one-run-4` exit
143 is therefore not a checker failure.

The dependency audit locates the cost precisely.  The shared Challenge
statement closure is 4,062 constants; the current Solution proof closure is
19,259.  The maintained
`ConcreteIndices.obstruction_four_properties_of_re_axioms` alone closes over
18,613 constants (13,810 from its type closure), so the independent transport
adds only 646 constants.  Further file splitting will not reduce external
kernel work.  A material reduction requires a direct obstruction proof over
the independent calculus, avoiding the maintained Foundation theorem; that is
the next proof-engineering track before another long Comparator retry.

Remaining work includes that direct local obstruction route, migration from
the one-result checkpoint to the final nine-result Challenge/Solution, the
other eight target declarations and their exact scopes, and eligible
Comparator verification.  The complete official verifier remains unsafe on
this host and was not launched.  No submission, registration, merge to
`main`, or manuscript edit has occurred.

Status recorded 2026-09-25 on `codex/palomar-eligibility`. This is a truthful
checkpoint, not a submission or a Comparator pass for an eligible Challenge.

## Outcome

The verification launcher was repaired first. The tested code commit is
`8ffd9325e3abf93f1b6b2b586fffe0b2b6b34314`; validation was recorded in the
later documentation-only commit `1c287855569f8d754baa57ae6961f3221929b9ac`.
Both commits are published on `origin/codex/palomar-eligibility`. The focused
suite has 13 passing tests, and the exact tested launcher passed one real
reduced-resource containment diagnostic and both snapshot-only capacity gates.
No four-hour Comparator rerun was made. The earlier successful local Comparator
run remains attached to its original source and launcher hashes.

The mathematical Challenge remains ineligible. No theorem type, maintained
proof, or manuscript file was changed. In particular, the current draft was
not replaced by an unproved abstraction, a semantic consequence relation, or
an interface with extra realization assumptions merely to make its imports
look acceptable.

## Source-policy result

At commit `1c287855569f8d754baa57ae6961f3221929b9ac`, the pinned Lean source walk

```text
cd Lean
lake env lean --src-deps FailureOfComposition/Palomar/Challenge.lean
```

resolves the four written imports to these candidate-local files:

| Import | Resolved source | Palomar classification |
| --- | --- | --- |
| `FailureOfComposition.ManuscriptObstruction` | `Lean/FailureOfComposition/ManuscriptObstruction.lean` | untrusted |
| `FailureOfComposition.ConcretePiOneCharacterization` | `Lean/FailureOfComposition/ConcretePiOneCharacterization.lean` | untrusted |
| `FailureOfComposition.PartialRecursiveQuotient` | `Lean/FailureOfComposition/PartialRecursiveQuotient.lean` | untrusted |
| `FailureOfComposition.RangeAssignment` | `Lean/FailureOfComposition/RangeAssignment.lean` | untrusted |

This follows the actual `lean_source_dependencies` and
`audit_challenge_sources` logic at PalomarSubmission
`a59f25bd8a66bf6faf3a4f4260d412989c0185ea`. Candidate-local helper imports are
rejected before moving Foundation behind another local module could matter.
The full paths, Git blobs, SHA-256 values, and policy hashes are in
[`ELIGIBILITY_INVENTORY.json`](ELIGIBILITY_INVENTORY.json).

The permitted roots do not supply the missing interface. Pinned Mathlib has
`Nat.Partrec.Code`, `REPred`, and semantic first-order syntax, but not the PA
derivation, proof coding, arithmetic hierarchy, or evaluator arithmetization
used here. The accepted TauCeti revision
`221bb56a017bb794421eac4fa543d7a5e85add75` contains no corresponding logic.
The observed CSLib head `a91aaaf96a72419b399c41c974a171749bf5b929`
has generic inference systems and propositional logics, but no first-order PA
or matching evaluator graph.

## Correspondence checkpoint

The first selected result cannot yet be transported faithfully. The smallest
unproved prerequisite is an independent derivability correspondence:

> For a permitted, explicit arithmetic syntax and calculus, construct
> computable inverse translations to the maintained Foundation syntax and
> prove, uniformly for every theory, preservation and reflection of actual
> derivations.

This single bridge is needed simultaneously to transport deductive PA
extension, consistency, and r.e. axiom codes without narrowing the quantified
theories. A set-theoretic formula bijection is insufficient because it does not
preserve `REPred`. The next dependent obligation is a PA-uniform equivalence
between an explicit permitted evaluator graph and
`ConcreteEvaluator.eventualGraph` for every standard program index. Only after
those two results exist can `obstruction_four_properties` be obtained from the
maintained theorem with the required external pointwise and internal uniform
provability clauses.

The remaining concepts and their exact dependencies are inventoried
machine-readably in `ELIGIBILITY_INVENTORY.json`. Quotient transport is not the
first blocker: it depends on the preceding provability and hierarchy bridges.
The range assignment also cannot be replaced by an arbitrary classical
selector; a different concrete selector first needs its PA-uniform graph
correctness, after which the maintained choice-independence theorem applies.

## Verification boundary and machine blocker

No new eligible Comparator or complete Palomar verifier run was started,
because there is no eligible candidate to verify. The historical local
Comparator success in run `20260925T162212Z-45800` remains evidence only for the
Foundation-dependent draft.

This WSL instance also cannot safely host the pinned complete verifier profile:

- The default `palomar-namespace-16x32-v1` needs 16 effective CPUs and
  28 GiB RAM; the observed machine has 4 effective CPUs and 16,772,214,784
  bytes of effective RAM.
- The explicit alternate `palomar-standard-v1` passes its 14 GiB numerical
  minimum, but on this host its fixed 95%/98% calculation produces
  `memory.high=15,933,604,044` and `memory.max=16,436,770,488`. The latter
  leaves only 335,444,296 bytes of physical headroom, versus the launcher's
  established 4 GiB safe system reserve.
- The profile does not set `memory.swap.max`. Wrapping it in the launcher's
  safe 11 GiB aggregate cap would make the official profile capacity check
  fail, so that is not an honest workaround.

Consequently the complete verifier was not launched. This is an exact
environment blocker, not a claimed verifier failure and not permission to
weaken the profile. Detailed launcher evidence and the eligibility audit remain
under `.codex-work/palomar/`; review bundles export only focused evidence.

No merge to `main`, submission, registration, or Palomar contact has occurred.
Manuscript edits remain deferred.
