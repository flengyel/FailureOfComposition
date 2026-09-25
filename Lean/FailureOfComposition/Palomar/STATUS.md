# Palomar eligibility status

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
