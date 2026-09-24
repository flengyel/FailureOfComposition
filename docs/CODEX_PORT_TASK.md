# First Codex task: port the verified development

Work in the dedicated Linux checkout on `codex/lean-4.35.0-rc2`, following
`AGENTS.md`. Complete the toolchain port and its verification. Do not stop after
writing a plan or listing likely incompatibilities. If a concrete external or
mathematical blocker prevents completion, retain the work and document it.

## Starting point and target

The accepted pre-setup commit is
`93fc6536f17f84933edf6d223eb41c8e3a9f866c`. The setup documentation commit adds no
Lean proof changes. Record the actual starting HEAD before editing.

| Component | Accepted baseline | Candidate for this task |
| --- | --- | --- |
| Lean | `leanprover/lean4:v4.32.2` | `leanprover/lean4:v4.35.0-rc2` |
| Mathlib | `905b95818eb32af7874a58b427f50c1711a5e96c` | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Foundation | `a3dd617f88bda178eb6c206dd5db91f88b6a2a42` | `e72cfe981aa65166f37fa4e2584f4806bc48d72f` |

The candidate Foundation and Mathlib commits both declare the target Lean
toolchain. This was checked on 2026-09-24; successful compilation of this project
with those revisions has not yet been established. Pin full commits and retain
the complete resolved transitive dependency manifest. Do not silently select a
moving branch, latest release, or different Foundation revision.

## 1. Establish the local starting state

The maintainer's source checkout is
`/mnt/c/Users/fleng/Zettelkasten/Projects/FailureOfComposition`, and the existing
execution environment is
`/home/flengyel/src/FailureOfComposition`. Preserve both. This task executes in
the new `/home/flengyel/src/FailureOfComposition-port` Git checkout created by
the setup helper, or the explicitly selected fresh alternative.

Read the root README, coverage map, Palomar README, verifier, package preparation
helper, evaluator pin checker, and this task. Inspect `git status --short --branch`,
the origin URL, HEAD, free disk space, and available memory. Do not
overwrite pre-existing work. Confirm this is a real Git checkout and not a
syncfailcomp mirror, and that the branch is the migration branch.

Use persistent working directories and sequential builds:

```bash
mkdir -p .codex-work/logs .codex-work/tmp
export TMPDIR="$PWD/.codex-work/tmp"
export LEAN_NUM_THREADS=1
export FAILCOMP_STYLE_JOBS=1
set -o pipefail
bash scripts/verify-failure-composition.sh --check-environment \
  2>&1 | tee .codex-work/logs/baseline-environment.log
```

Record `PCATS_DST` and `CRS_LAKE_PACKAGES` if set. The check must validate the
accepted toolchain, 31 evaluator source pins, and baseline package revisions.
It runs no Lake command and does not require another full baseline replay. If
it fails, diagnose the installation or mapping; do not modify the shared package
checkouts or call a download-producing Lake command there. The author's earlier
full WSL run is reported evidence, not a run performed by this Codex session.

## 2. Provision the isolated target environment

Install `leanprover/lean4:v4.35.0-rc2` with elan if absent; retain 4.32.2 and do
not change elan's global default. Update only this branch's `Lean/lean-toolchain`
and Lake configuration to the exact candidate pins. Regenerate the committed
manifest in this isolated checkout with the target toolchain. Dependency
downloads and Mathlib cache retrieval are part of this task, but must resolve
inside this checkout's `Lean/.lake/packages`; never update PCats dependencies.

Clear baseline package overrides from the target-build environment after
recording them. Do not symlink or copy the old Foundation/Mathlib build trees
into the port. Inspect the resolved manifest: every dependency revision must be
explicit, and the project and Mathlib toolchain files must match exactly.
Keep downloads and builds sequential; investigate resource exhaustion before
retrying rather than launching more workers.

The baseline validation helpers cannot yet run against this environment:
`prepare_packages.py` and `verify.sh` hard-code 4.32.2, and package preparation
defaults to the shared PCats tree. Make the target verifier use this checkout's
resolved packages, retaining exact revision/origin/cleanliness checks. A mapping
must contain every resolved package, not an assumed count of 16. Use the updated
`prepare_packages.py` to produce the canonical Lake `--packages` override rather
than treating an input mapping as a ready-made Lake file.

## 3. Port sources and validation together

Repair imports and API changes with focused builds, beginning at the first
failing module in dependency order. Known inspection findings are guides, not
counts of broken proofs:

- Foundation renamed `LO` to `FFL` and moved first-order syntax, arithmetic,
  and bootstrapping modules. Check actual definitions before replacing names.
- Four current sources import `InductionSchemeDelta1`; the candidate supplies
  related definability instances elsewhere. Establish the replacement instances
  with the same hypotheses rather than adding new assumptions.
- Lean 4.33 changed transparency in type matching. Diagnose failed applications
  and prefer explicit local repairs; do not globally disable checking or linting.
- Lean 4.34 deprecated names including `if_pos` and `if_neg`. The current proof
  scope has 11 uses, suitable for targeted renaming.
- Verification metaprograms inspect Lean environments. Compile and port them
  as needed; preserve what each audit checks. In particular, update renamed
  dependency roots without making the productive/Goedel separation checks
  vacuous.

Preserve all 72 FailureOfComposition mathematical modules and the 31 evaluator
modules, plus the three verification sources and nine Palomar pairs. Any
necessary inventory change must be explained and covered by the verifier.
The current style checker excludes the 31 evaluator sources because they are
pinned imports. Explicitly review and account for changes to those sources;
do not report their style as checked unless the port actually checks it.

The original evaluator pin file is
`Audit/failure-composition-v36/evidence/evaluator-source-pins.json`. Preserve it
and `ROOTPROVENANCE.json` as origin records. Add port provenance under
`Lean/FailureOfComposition/Porting/` that identifies the starting commit,
original source hashes, changed files, and current source hashes. Adapt
`build_evaluator.py` and consumers to check the new source hashes and dependency
closure. Do not claim edited files still equal blobs at the old pin commit.
Any broader changes to verifier behavior require focused regression checks.

Keep theorem meanings, assumptions, proof-route separation, and axiom envelopes
unchanged. Never replace a proof by `sorry`, an axiom, or a hypothesis asserting
the needed conclusion. Keep Challenge outside the proof umbrella; its deliberate
holes remain confined there. Elaborate Challenge and Solution separately since
they intentionally declare the same names.

## 4. Acceptance checks

Once focused compilation succeeds, run the updated environment check and full
verifier with the isolated target package mapping. Capture logs with real exit
codes. Full verification must still include:

1. Exact toolchain/dependency and source-provenance validation.
2. Native `lake build FailureOfComposition` and the complete module inventory.
3. Strict style checks with warnings treated as errors.
4. `Verification/CheckTypes.lean`, `CheckAxioms.lean`, and
   `CheckDependencies.lean`, including the productive/Goedel dependency checks.
5. Kernel replays for both `FailureOfComposition` and `CategoricalRiceShapiro`.
6. The updated `Palomar/check_draft.py` check of all nine statement/proof pairs.

Run the full checks once repairs settle; repeat only checks affected by a later
change. Compare public theorem signatures and the manuscript coverage map with
the starting commit, accounting for namespace/API changes. A build alone cannot
establish that the statements retained their intended meaning.

The existing local paired checker is not Palomar Comparator. Do not record a
Comparator pass or submission readiness based on it. Challenge redesign and
Palomar submission are outside this first task.

## 5. Commit and handoff

Write `Lean/FailureOfComposition/Porting/STATUS.md` with starting and final pins,
changes, commands, exit codes, completed checks, remaining errors, and log paths.
Distinguish observed results from planned checks. Keep bulky generated output
under ignored `.codex-work/`; commit the concise report and provenance records.

Make focused local commits on the migration branch after reviewing the diff and
running `git diff --check`. Do not push or merge the port as part of this task.
If a blocker remains, label the checkpoint incomplete and include the exact
failure and smallest reproducing command. End with the branch, commit(s), changed
files, validation outcome, and next unresolved obligation. Do not edit v36 or
present a partial port as verified.
