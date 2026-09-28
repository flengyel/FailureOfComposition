# Foundation downstream build recovery

This checkpoint separates local compiler containment from the unchanged
Comparator/checker containment.  It changes no theorem, Challenge, Solution,
portable Comparator configuration, toolchain, or dependency revision.  The
build-only profiles documented here are development settings, not an official
Palomar verification profile.

The unchanged Foundation
`FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions` target first ran
with `memory.high=memory.max=10 GiB`, zero swap, one CPU, and one Lean thread.
It ended in a contained hard-cap OOM after 223.424 seconds: peak memory was
exactly 10,737,418,240 bytes, with 142,817 `memory.max` events, one OOM event,
three OOM kills, and no output artifact.  This qualified the single authorized
fallback.

The unchanged target then passed under the build-only 12 GiB profile in
208.406 seconds.  Peak memory was 12,884,889,600 bytes, with 232 harmless max
events, zero OOM events, and peak full-memory PSI `avg10` of 3.12%.  The live
one-second host guard never crossed its 2 GiB floor; the minimum observed
`MemAvailable` was 3,485,306,880 bytes.  Lake produced the ordinary olean,
ilean, C, setup, and trace artifacts from the public Foundation pin.

The downstream `FailureOfComposition.Palomar.SolutionThree` target then built
successfully under the same admitted profile in 959.000 seconds, at
2,057,461,760 bytes peak, with no pressure, limit, deadline, or OOM event.
Supervisor telemetry observed one Lean compiler at a time.  The subsequent
strict source checks, exact interface/body/ownership comparison, pinned source
policy, recursive axiom and route audit, changed-definition and incomplete-set
negative regressions, and portable configuration check all passed in a
sequential 102.490-second contained run.

On the repaired Foundation pin the complete selected closure is 21,256
constants.  The first result remains 17,085, the productive result 17,107, and
the Gödel result 20,331; the cumulative marginal over the first two is 4,149.
The three additional constants relative to the former pin are the named
factored Foundation proof helpers.  The only recursively reached axioms remain
`propext`, `Classical.choice`, and `Quot.sound`.  The productive root does not
reach the maintained Gödel/Craig roots, and the Gödel root does not reach the
productive or first-result proof roots.

Two harmless infrastructure smokes exhausted the task allowance.  The first
showed that an immediate synthetic low-memory sample stopped the payload before
it could write its in-cgroup readback.  After the concrete correction—sampling
at the configured one-second interval—the second read back 12 GiB high/max,
zero swap, CPU 0 and `nproc=1` in both parent and child, then stopped the owned
tree at 1.032 seconds and emptied it in 0.051 seconds.  Every timed run retained
an exact source snapshot.

This record is the pre-Comparator identity.  A cumulative Three Comparator
attempt, if made, uses the separate unchanged checker profile:
`memory.high=8 GiB`, `memory.max=10 GiB`, zero swap, one CPU/Lean thread,
4 GiB available-memory reserve, the established PSI stop, and a 1,200-second
deadline.
