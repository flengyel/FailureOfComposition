# Verification entry points

This standalone export contains only the FailureOfComposition workflow.
The original repository's unrelated mirror and production runners are absent.

From a Linux checkout, run:

```sh
bash scripts/verify-failure-composition.sh --check-environment
bash scripts/verify-failure-composition.sh
```

From a checkout on `/mnt/c`, use a persistent Linux mirror:

```sh
FAILCOMP_DST="$HOME/src/FailureOfCompositionStandalone" bash scripts/syncfailcomp.sh --check-environment
FAILCOMP_DST="$HOME/src/FailureOfCompositionStandalone" bash scripts/syncfailcomp.sh
```

The selected mirror must be absent or an empty dedicated directory, or already
owned by this exact source checkout. Existing mirrors owned by the original
repository are refused. `--sync-only` copies sources without a native build.
The mirror retains its build tree, logs, reports, and temporary package mappings.
Synchronization refuses local edits to managed files and preserves its lock
through verification; interrupted source updates are journaled for recovery.

Both entry points reuse the exact 16 pinned checkouts supplied by
`${PCATS_DST:-$HOME/src/PCats}/.lake/packages` or `CRS_LAKE_PACKAGES`. They do not
clone, fetch, pull, or update dependencies. Each Lake command receives a validated
path override. Use the provided environment check instead of bare `lake env`.
Defaults `LEAN_NUM_THREADS=1` and `FAILCOMP_STYLE_JOBS=1` reduce concurrency;
they are not an aggregate memory limit. Failures propagate nonzero exit codes.

## Codex port checkout

`bash scripts/setup-codex-wsl.sh` creates a fresh, independent Git checkout under
`~/src/FailureOfComposition-port` on the migration branch. This helper clones
only the repository: it does not run Lean, fetch proof dependencies, or alter
existing mirrors. Keep that checkout outside the synchronization workflow.
See [Codex WSL setup](../docs/CODEX_WSL_SETUP.md) for installation, launch, and
verification instructions, and [the first task](../docs/CODEX_PORT_TASK.md) for
the exact port scope and candidate dependency revisions.
