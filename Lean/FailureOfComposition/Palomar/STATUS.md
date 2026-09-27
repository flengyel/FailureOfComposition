# Palomar eligibility status

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
