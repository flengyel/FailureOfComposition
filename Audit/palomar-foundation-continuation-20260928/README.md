# Foundation containment continuation checkpoint

This checkpoint repairs the local containment preflight, validates the exact
checker launch path, replays the already-built integrated Foundation export,
publishes and pins the tested one-proof Foundation repair, and records the
first downstream rebuild boundary. It does not claim a cumulative Three
Comparator pass.

## Containment diagnosis

The earlier launcher discarded the output and status distinction from
`systemctl --user is-system-running`. In the ordinary WSL user context used
for workloads, the installed systemd 257.13 manager reported `running`, with
`NFailedUnits=0`, `NJobs=0`, and control group
`/user.slice/user-1000.slice/user@1000.service`. The cgroup v2 mount was
writable and the delegated user group exposed the `cpu`, `memory`, and `pids`
controllers. The same manager query from the Codex filesystem sandbox failed
with `Operation not permitted`; that restricted context cannot establish the
manager's host state. The generic archived error therefore did not identify
whether the earlier manager was unavailable or merely inaccessible.

`scripts/verify-palomar.sh` now distinguishes running, degraded, transitional,
unavailable, permission-denied, and missing/read-only-delegation cases. A
degraded manager is accepted only when manager properties and the failed-unit
query succeed; all controller and writable-cgroup checks still apply. The
launcher regression suite has 21 passing tests, including reachable degraded,
unreachable/permission-denied, and missing-controller cases.

Two harmless smoke launches were used. The first proved the cgroup placement
and limits but its diagnostic payload incorrectly tried to discover the host
cgroup path through the sandbox's deliberately private cgroup namespace. The
second passed after the wrapper supplied the already-authenticated host leaf
and limits paths to the diagnostic payload. It exercised the same supervisor,
cgroup, CPU affinity, bubblewrap boundary, and pressure guard as the checker;
read back `memory.high=8G`, `memory.max=10G`, zero swap, and CPU 0; verified a
parent/child/grandchild tree, read-only input, writable private `/tmp`, and
successful cleanup; and recorded no resource event.

## Integrated stock con-ron gate

The retained 44,064,407-byte export rooted at the rebuilt
`FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.construction` and
`constructionFuncDefined` was reused byte-for-byte. Its SHA-256 is
`8d1ae06a757442846b5f3ad7190433adb7b462d97147f9132e2ed7011038ac63`.
The unchanged bundled stock con-ron, SHA-256
`4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef`,
accepted 8,090 declarations in verified mode and completed all 7,707 checks.
Supervisor elapsed time was 22.052 seconds, aggregate CPU was 21.887753
seconds, and aggregate peak memory was 247,754,752 bytes. There were no
pressure, deadline, high/max, swap, OOM, OOM-kill, or pids-limit events. This
was one actual checker launch, not a retry of the earlier setup failure.

## Publication, pin, and downstream build boundary

The exact tested Foundation commit
`46715b758b3069351825f276f1d98de1e60f1e4f`, parent
`e72cfe981aa65166f37fa4e2584f4806bc48d72f`, is publicly fetchable from
`https://github.com/flengyel/foundation.git` on branch
`palomar-helper-repair-20260928`. Only
`Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Basic.lean` changes.
The project now pins the full commit and Lake resolved the active package from
that public URL. Every unrelated manifest entry remained byte-for-byte
unchanged; the repaired source blob retained SHA-256
`6a95b78fe707869e908b1b4a06f33826c4a670ddb2e9b8f7892764d3589b05dc`.

The active public-pin build of the modified `Basic` module passed in 47.681
seconds at 992,169,984 bytes peak with no resource event. The subsequent
`FailureOfComposition.Palomar.SolutionThree` build then reached the first
affected downstream Foundation module,
`Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions`, and was
terminated by the mandated early-pressure guard. It ran for 205.856 seconds,
used 125.259607 CPU seconds, peaked at 8,974,295,040 bytes, recorded 6,898
`memory.high` events, and sustained full-memory PSI above 80% for 60 seconds
(last sample 97.38%). It recorded zero `memory.max`, swap, OOM, OOM-kill, and
pids-limit events. Exit 137 reflects supervisor termination, not a Lean
theorem rejection.

This is a genuine downstream build/resource blocker under the fixed limits.
The strict Three build, exact interface, source-policy, dependency/axiom and
route audits were consequently not rerun on the new pin, and no cumulative
Three Comparator parent or payload was launched. The ChallengeThree,
SolutionThree, Gödel bridge, and portable configuration bytes remain unchanged
from proof/configuration baseline
`b557d255f1d0b42920440cb2d4762b1ca54b2728`.

The project pin/launcher checkpoint is
`53afd6ae8a056eb0dbd5618e49b6025066bb2199`. The first two declarations retain
their historical Two-pair pass for their recorded dependency version. The
third declaration remains migrated and exactly compared only at its earlier
checkpoint; it has not received cumulative external-kernel verification on the
new Foundation pin. Six declaration migrations and complete official
verification remain outstanding.
