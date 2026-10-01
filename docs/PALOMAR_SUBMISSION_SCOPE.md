# Focused Palomar Nine submission scope

The submission branch deliberately contains the sources needed to build,
compare, and audit the cumulative Nine result. It is not a museum of every
intermediate experiment used to reach that result.

## Selection method

The starting snapshot is commit
`5586bae3730e49f866da1d4e2f0ebb1dadacc2ca`. It contained 197 tracked Lean
sources, including 40 below `Audit/`. Lean 4.35.0-rc2 `--deps-json` output was
used as the authoritative local import graph. The roots were:

- `FailureOfComposition.Palomar.ChallengeNine`;
- `FailureOfComposition.Palomar.SolutionNine`;
- the exact Nine interface checker;
- the Nine dependency audit; and
- the current changed-body and wrong-route negative fixtures.

The resulting transitive graph contains 123 Lean modules. The focused
`FailureOfComposition` default root adds one module, for 124 submitted Lean
sources. `SUBMISSION_SOURCE_INVENTORY.json` records every retained path and
hash. The complete old-path/new-path or omission table, including blob IDs,
SHA-256 values, callers, and immutable links, is packaged with the module-port
evidence.

## Audit disposition

`Audit/` contained frozen reports, stage-specific launchers, profiling probes,
failed repair experiments, and the source files for earlier cumulative checks.
Those records remain available at the immutable baseline commit and in the
previously verified timestamped evidence archives. They are not maintained
submission inputs.

Six files were promoted rather than retired:

| Old path | Maintained path | Purpose |
| --- | --- | --- |
| `Audit/failure-composition-v36/evidence/evaluator-source-pins.json` | `Lean/FailureOfComposition/Provenance/evaluator-source-pins.json` | Original evaluator-source provenance used by `build_evaluator.py`; bytes unchanged. |
| `Audit/palomar-nine-generated-quotient-20260930/NineDependencyAudit.lean` | `Lean/FailureOfComposition/Palomar/Checks/NineDependencyAudit.lean` | Current recursive dependency/axiom and route audit. |
| `Audit/palomar-nine-generated-quotient-20260930/negative/NineResultNegativeChallenge.lean` | `Lean/FailureOfComposition/Palomar/Tests/NineResultNegativeChallenge.lean` | Changed-shared-body negative fixture. |
| `Audit/palomar-nine-generated-quotient-20260930/negative/NineResultNegativeSolution.lean` | `Lean/FailureOfComposition/Palomar/Tests/NineResultNegativeSolution.lean` | Changed-shared-body negative fixture. |
| `Audit/palomar-nine-generated-quotient-20260930/negative/NineWrongRouteSolution.lean` | `Lean/FailureOfComposition/Palomar/Tests/NineWrongRouteSolution.lean` | Wrong productive-range-route fixture. |
| `Audit/palomar-nine-generated-quotient-20260930/negative/NineWrongRouteAudit.lean` | `Lean/FailureOfComposition/Palomar/Tests/NineWrongRouteAudit.lean` | Confirms that the wrong-route fixture is rejected for the intended dependency reason. |

The remaining 35 Audit Lean files and 156 non-Lean Audit records are omitted
from the submitted snapshot. The former are historical diagnostics or
superseded stage checkers/fixtures; the latter are immutable evidence or
stage-specific launchers. Nothing in the selected proof or current checks
imports `Audit/`.

## Other retirements

The branch also omits the One-through-Eight cumulative pairs, their exact
interface checkers and configurations, the legacy Challenge/Solution pair,
three superseded whole-project Lean checks, seven proof sources outside the
exact Nine closure, and obsolete port/synchronization launchers. Their current
callers were themselves retired stage tools or the former broad root module.
The first eight public contracts are instead compared with the accepted
baseline in a separate immutable checkout, so retaining `ChallengeEight` and
`SolutionEight` in the submitted tree is unnecessary.

Historical sources can be inspected without reconstruction at:

```text
https://github.com/flengyel/FailureOfComposition/tree/5586bae3730e49f866da1d4e2f0ebb1dadacc2ca
```

The earlier complete local official-verifier pass remains recorded at candidate
`48e6eeccc420e8068f1bc6d810ddbe10cfdf39eb`. Removing historical files does not
retroactively alter that result; the module-based snapshot receives its own
current-verifier result.

## Module visibility

All 124 retained Lean sources use Lean 4.35's module header. Imports are public
where downstream statement or proof bodies use imported declarations, and the
retained files use `@[expose] public section` to preserve their pre-module
unfoldability. Compiler diagnostics required a small set of formerly `private`
implementation helpers to become public because public declarations contain
them in their types or bodies. Those changes affect visibility only; the helper
definitions themselves are unchanged. The generated-quotient bridge's helper
was renamed to `generatedFoundationWeakerThan` solely to avoid the now-public
name already used by the quotient bridge.

The complete ChallengeNine and SolutionNine sources, after removing only the
module command, public-import marker, public-section marker, and blank lines,
are byte-identical to their accepted forms at `5586bae3730e49f866da1d4e2f0ebb1dadacc2ca`.
The Lean interface checker separately compares all nine theorem types and 5,149
recursively reachable shared statement constants in distinct environments.

The current Palomar source scan at PalomarSubmission
`65f0154ed776cd26c224254aa57b379137f28b0d` checks 124 Lean files and reports no
module-header, symlink, UTF-8, or 10,000-line violation. ChallengeNine remains
subject to its separate limits and is 44,261 bytes and 999 physical lines.

## Current-verifier outcome

The focused public candidate is
`6adc1084e57ca3e9011dbd3765e99b803842ee17`. The current verifier fetched that
commit, accepted its preparation metadata and source requirements, and passed
the `palomar-standard-v1` capacity check. Its first full execution reached
`solution-build` before the separately maintained host guard encountered a
transient `ProcessLookupError` while reading the live process tree. The guard's
fail-closed behavior terminated only the owned cgroup after 654.137 seconds;
cleanup found no remaining owned workload. No kernel ran in that preserved
infrastructure-abort record.

The guard was narrowly repaired to skip a PID that disappears during individual
process inspection while retaining fail-closed handling of unavailable host
telemetry. Three deterministic fixtures passed. A newly authorized execution of
the unchanged candidate then completed in 3,720.403 seconds with official report
`status: pass`, `stage: complete`, `phase: verification`. Con-ron accepted
20,931 declarations in verified mode, NanoDa and Lean's default kernel accepted,
and Comparator printed `Your solution is okay!`. No resource or monitor stop
occurred, and cleanup found no remaining owned cgroup. The snapshot is therefore
technically ready for the separate service-submission decision.
