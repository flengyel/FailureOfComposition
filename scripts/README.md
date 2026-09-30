# Verification entry points

This focused submission keeps only the active Palomar Nine workflow.

```sh
python3 scripts/check-palomar-submission-tree.py
PALOMAR_UPSTREAM_ROOT=/path/to/pinned/current-upstreams \
  PALOMAR_GNU_TIME=/path/to/gnu-time \
  bash scripts/verify-palomar.sh --check-environment
PALOMAR_SUBMISSION_CHECKOUT=/path/to/PalomarSubmission-at-65f0154 \
  PALOMAR_PYTHON=/path/to/verifier-python \
  bash scripts/run-palomar-nine-focused.sh .codex-work/palomar/nine-focused
```

`verify-palomar.sh` validates the fixed Lean, Mathlib, Foundation, current
PalomarSubmission, PalomarPolicy, and PalomarTemplate identities. The focused
script runs the strict Nine build, exact interface/dependency checks, current
Challenge source policy, and maintained negative regressions. The launcher's
full-verifier mode operates on a public immutable Git commit; it does not
submit, register, or upload anything.

The evaluator sources retain their original source-pin input at
`Lean/FailureOfComposition/Provenance/evaluator-source-pins.json`. The historical
native-port, synchronization, One-through-Eight, and profiling launchers remain
available at immutable pre-submission commits and in their evidence archives;
they are not active inputs to this snapshot. See
[`docs/PALOMAR_SUBMISSION_SCOPE.md`](../docs/PALOMAR_SUBMISSION_SCOPE.md).
