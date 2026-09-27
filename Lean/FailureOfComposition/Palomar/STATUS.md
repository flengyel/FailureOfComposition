# Palomar eligibility status

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
