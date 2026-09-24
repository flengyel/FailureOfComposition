# Working on FailureOfComposition

## Project and mathematical scope

This repository maintains the Lean formalization and manuscript of *Pointwise
provable equality and the failure of composition*. Read `README.md`,
`Lean/FailureOfComposition/MANUSCRIPT_COVERAGE.md`, and the task-specific guide
before editing. The Lake project is `Lean/`; its package name is still
`CategoricalRiceShapiro` for compatibility.

The accepted development uses Lean 4.32.2, Mathlib
`905b95818eb32af7874a58b427f50c1711a5e96c`, and Foundation
`a3dd617f88bda178eb6c206dd5db91f88b6a2a42`. The pre-setup repository checkpoint is
`93fc6536f17f84933edf6d223eb41c8e3a9f866c`. A newer toolchain is a migration until
its build and audits pass; see `docs/CODEX_PORT_TASK.md`.

Preserve theorem types, quantifiers, and mathematical hypotheses. In particular:

- Pointwise provability quantifies over external standard natural inputs;
  uniform provability is a single universally quantified statement in T.
- Retain consistency versus Sigma-one soundness and r.e. versus arbitrary
  theories exactly where the existing results require them.
- Keep productive and Goedel-II proof routes separate in the dependency audits.
  This is dependency separation, not a claim of logical independence.
- Retain PA-uniform graph specifications, including the range construction.
- Preserve the documented program-index scope; do not claim that every
  historical multiobject category has been reconstructed in Lean.

Do not add axioms, weaken statements, assume an obligation, or introduce proof
holes into the maintained proofs. The nine deliberate holes in the separate
Palomar Challenge are the existing exception. Solution must not import Challenge
or depend on its holes. The permitted proof axioms are `propext`,
`Classical.choice`, and `Quot.sound`; do not introduce `native_decide` dependencies.

## Files and workspaces

- Permanent Lean code belongs under `Lean/`, including any porting support.
  `Audit/` is for generated reports and temporary probes, not maintained proofs.
- Preserve `ROOTPROVENANCE.json` as the initial export record. Preserve the
  original evaluator-source pin record as provenance; migrated sources require
  a separate, explicit record and corresponding validation.
- The author is preparing manuscript v37. A toolchain port does not authorize
  edits to `manuscript/failure_of_composition_2026-09-21_v36.tex`.
- Work in the dedicated Linux Git checkout and migration branch described in
  `docs/CODEX_WSL_SETUP.md`. Never develop in a syncfailcomp-managed mirror.
- The maintainer's source path is
  `/mnt/c/Users/fleng/Zettelkasten/Projects/FailureOfComposition`; the existing
  execution path is `/home/flengyel/src/FailureOfComposition`. Keep the isolated
  port checkout distinct from both.
- Keep the existing PCats, Categorical_Rice_Shapiro, and ParametricBoundedLob
  checkouts and their dependencies untouched. Use a separate dependency tree for
  the port; do not reuse old compiled objects with a newer Lean version.
- Do not run destructive cleanup or discard user changes. Respect the current
  task's commit/push authorization. The first porting task specifies local
  branch commits and leaves merging to main for review.

## Builds and evidence

Start with `git status --short --branch`, then inspect the pins and scripts.
Use `bash scripts/verify-failure-composition.sh --check-environment` for the
accepted baseline; it validates installed dependencies without invoking Lake.
Bare Lake commands may fetch packages and are not a baseline preflight.

The baseline verifier checks hard-coded toolchain revisions and evaluator Git
blob hashes. Port these checks deliberately along with the source. Do not bypass
them or regenerate provenance silently to obtain a passing report.

Default to `LEAN_NUM_THREADS=1` and `FAILCOMP_STYLE_JOBS=1`, and run one build or
kernel replay at a time. These settings reduce concurrency; they do not bound
total memory. Keep logs and temporary package mappings under `.codex-work/` in
the Linux checkout, and preserve command exit codes when piping through `tee`.
Do not copy the proof tree or dependency builds into `/tmp`.

Use focused compilation during repairs. Once the port is ready, run the full
native build, strict style check, theorem/type and axiom checks, dependency
audits, and kernel replays for both libraries, followed by the nine paired draft
checks. A passing paired draft check is not Palomar Comparator verification.
Record actual commands, revisions, exit codes, and remaining failures.

## Palomar

Read `Lean/FailureOfComposition/Palomar/README.md`. Foundation is permitted in
Solution, but the current Challenge's transitive imports are ineligible. A port
alone does not fix that boundary. Preserve faithful arithmetic statements;
replacing their content with assumptions or unconstrained definitions is not a
solution. Do not submit, register, or contact Palomar unless explicitly asked.
