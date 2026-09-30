# Cumulative Nine: pinned official verifier result

## Outcome

The pinned Palomar verifier completed successfully on the public immutable
snapshot `48e6eeccc420e8068f1bc6d810ddbe10cfdf39eb`. Its final report says
`status: pass`, `stage: complete`, and `phase: verification`, with no errors.
The selected pair is exactly:

- project `Lean`;
- configuration `Lean/FailureOfComposition/Palomar/comparator-nine.json`;
- metadata `Lean/FailureOfComposition/Palomar/formalization.yaml`;
- Challenge `FailureOfComposition.Palomar.ChallengeNine`;
- Solution `FailureOfComposition.Palomar.SolutionNine`;
- the nine ordered theorem names in the submitted configuration;
- no selected definitions;
- permitted axioms `propext`, `Quot.sound`, and `Classical.choice`.

The immutable candidate is a packaging-only descendant of the earlier local
Comparator-tested code/configuration commit
`381de9db4d2214b8fd8d05bf74b56bc9597f01c5`. The Challenge, Solution, and
portable configuration bytes are unchanged between those revisions.

## Preparation and capacity

Preparation fetched the public Git snapshot and produced a pending/prepared
report with matching source SHA and selected paths. The root repository license
was declared and detected as Apache-2.0. The manuscript retains its own notice;
whether that notice is sufficient for a service submission remains a separate
maintainer/editorial scope decision rather than a failure reported by this
mechanical run.

The default `palomar-namespace-16x32-v1` profile was ineligible on this host
because only four effective CPUs were available. The explicitly selected and
approved `palomar-standard-v1` profile passed capacity checking:

- 4 effective CPUs;
- 16,772,218,880 bytes effective RAM;
- `memory.high` 15,933,607,936 bytes;
- `memory.max` 16,436,774,502 bytes;
- at least 875,995,172,864 bytes workspace free;
- 32,768 task limit and zero workload swap.

Pinned bubblewrap v0.12.0 was built from the verifier-authenticated source and
had SHA-256
`636192e7fa50bfc6a19820aed6538f0b85194fcb1f92be405f1ec70d188d91ba`.
Basic and nested namespace tests and the official delegated-cgroup supervisor
smoke passed. Setup retained two non-payload corrections: the host Python 3.13
could not satisfy the pinned Python environment, so the exact Actions Python
3.11.10 artifact was installed and locally relocated; the first bubblewrap
source-build parent failed before compilation because `xz` was unavailable,
then succeeded after the missing unpacker was provisioned. Ruby 3.3.8,
Bundler 2.7.2, and Licensee 10.0.0 were installed in the isolated tool area.
None of these setup attempts launched the verifier payload.

An initial diagnostic guard fixture used the already elapsed task
clock and correctly exercised the job-budget stop; the corrected harmless
fixture passed. No checker payload was involved in either fixture.

## Execution

Exactly one official `execute` payload was launched. The external guard retained
the truthful task-start epoch and supplied an explicit 19,800-second verifier
budget. It constrained all descendants to CPU 0 and monitored host availability
and full-memory pressure without changing the official profile limits.

- parent elapsed: 3,034.009 seconds;
- cleanup: 0.002 seconds;
- stop reason: none;
- remaining owned cgroups: none;
- minimum observed host `MemAvailable`: 11,049,693,184 bytes;
- peak host full-memory PSI `avg10`: 10.97 (stop threshold 80 for 60 seconds);
- maximum recorded phase cgroup peak: 9,151,164,416 bytes, during trusted-cache
  work;
- solution build: 2,560.077 seconds, 4,888,596,480-byte cgroup peak;
- solution export: 18.681 seconds, 731,492,352-byte cgroup peak;
- Comparator: 143.344 seconds, 786,345,984-byte cgroup peak;
- no deadline, OOM, OOM-kill, host-reserve, or external pressure stop.

The protected Challenge was renamed by the verifier to
`PalomarCanonical0a7f7368b550bced339ef22e.Challenge`; the protected
configuration is therefore intentionally not byte-identical to the submitted
JSON. The report authenticates the canonical Challenge object and protected
configuration.

Comparator reported:

```text
con-ron: accepted 20847 declarations (--verified)
con-ron kernel accepts the solution
nanoda kernel accepts the solution
Lean default kernel accepts the solution
Your solution is okay!
```

The final process exit was zero and the report contains no contradictory error
or resource-abort state. The one warning is the already known preferred review
surface warning: ChallengeNine is 44,209 bytes and 998 lines, below the pinned
100 KiB/1,000-line hard limits but above 32 KiB/300 lines.

## Scope and remaining decisions

This establishes a complete local mechanical pass using the pinned official
Palomar verifier under `palomar-standard-v1`. All nine selected declarations
are migrated, compared, exported, and accepted by con-ron, NanoDa, and Lean's
default kernel for the exact public snapshot above.

It does not constitute a Palomar service upload, submission, editorial review,
registration, or registry acceptance. No CI receipt was fabricated. Before a
service submission, the maintainer should resolve the manuscript-license scope
and decide whether to submit this exact verified snapshot or prepare and verify
a later metadata-only descendant.
