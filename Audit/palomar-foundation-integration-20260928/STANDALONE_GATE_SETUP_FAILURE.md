# Standalone integrated-construction gate: setup failure

This is the complete retained record of the checkpoint's one authorized parent
invocation.  The containment runner exited before it created a run directory,
so there is no cgroup status or workload log for this invocation.

Invoked from `/home/flengyel/src/FailureOfComposition-port`:

```text
sha256sum /home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/con-ron && /usr/bin/bash .codex-work/palomar/foundation-integration/20260928T040804Z/run-contained.sh replay-integrated-construction-conron-01 240 /home/flengyel/src/FailureOfComposition-port/Lean /home/flengyel/src/FailureOfComposition-port/.codex-work/palomar/helper-kernel-replacement/20260928T002059Z/kernel-sandbox.sh conron /home/flengyel/src/FailureOfComposition-port/.codex-work/palomar/foundation-integration/20260928T040804Z/exports/integrated-construction.ndjson
```

Complete output:

```text
4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef  /home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/con-ron
error: the ordinary WSL user systemd manager is unavailable
```

Observed state immediately afterward:

- no `runs/replay-integrated-construction-conron-01` directory existed;
- no con-ron, NanoDa, leanchecker, Comparator, or verification workload was
  running;
- stock con-ron therefore had no internal launch and returned no verdict.

The prompt states that setup failures consume the corresponding launch
attempt.  The parent invocation is consequently counted as the one standalone
attempt and was not retried.  No cumulative Three Comparator attempt was made.
