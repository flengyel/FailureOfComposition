# Evaluator style cleanup

The independent WSL rerun passed at
`d2100df1b583368c56c00c3a4babf0bb72b0cfb2` on 2026-09-25. Its results are
recorded in `INDEPENDENT_REVIEW.json`. The source changes described below are
subsequent work; the earlier pass does not validate them.

## Changes

The fresh build reported 96 distinct style diagnostics in 13 evaluator files:
92 uses of `letI`, three uses of `haveI`, and one line exceeding 100 characters.
Each proof-instance diagnostic explicitly recommends `let` or `have` because
the goal is a proposition. The cleanup applies exactly those recommendations
and wraps the long line. Theorem statements, hypotheses, definitions, imports,
and linter settings are unchanged. No general replacement outside the reported
locations was performed.

The evaluator source commit is
`defc4bd198260adbc8729c9b25e293223d746770`. `EVALUATOR_PROVENANCE.json` records
its source hashes and retains the earlier port source checkpoint and the
independently checked baseline. The original export and evaluator pin records
are unchanged.

## Gate coverage

The strict style checker now re-elaborates all 72 FailureOfComposition sources
and all 31 pinned evaluator sources with Mathlib's standard linters enabled
and warnings treated as errors. The previous gate excluded the evaluator
sources, so their warnings did not invalidate the successful port run.

The 72 FailureOfComposition sources still permit no linter suppressions.
The evaluator has three pre-existing declaration-local `linter.flexible`
exceptions, retained and reported explicitly:

- `ArithmeticCode.FoundationCompat.evalAux_unique`
- `ArithmeticCode.FoundationCompat.eval_unique`
- `ArithmeticCode.Evaluation.eval_codeLift_iff`

Only those exact declaration-scoped exceptions are accepted in their existing
files. No additional exception is permitted. Removing these earlier exceptions
would require a separate proof cleanup; this change adds none.

The nine deliberate `sorry` warnings in the separate Palomar Challenge are
unaffected. The Solution and its checked dependency closure remain required
to be free of `sorryAx`.

## Validation and WSL handoff

Source checks performed during preparation:

- All 96 warning locations match the uploaded fresh-build log.
- Ignoring whitespace and the 95 indicated keyword substitutions, all edited
  Lean source tokens match the accepted port.
- Current evaluator hashes and the complete 31-module dependency closure pass
  `build_evaluator.py --check-only`.
- Three gate regression tests pass: evaluator inventory coverage, scoped
  exception boundaries, and rejection of warnings even with compiler exit 0.
- `git diff --check` passes.

**Lean compilation and the expanded 103-source strict gate passed for this cleanup.**
The full WSL suite also passed its theorem/type, axiom, dependency, kernel-replay,
and nine paired draft checks. [STYLE_CLEANUP_VALIDATION.json](STYLE_CLEANUP_VALIDATION.json)
records the exact checked source commit and whether the completed run was reused.
The preparation environment has no Lean installation and an 8 GiB memory
limit. Use the existing Linux port checkout and its compatible dependency
caches; another independent checkout or dependency download is unnecessary.
Keep one build active at a time.

From a clean `/home/flengyel/src/FailureOfComposition-port`, fetch the cleanup
branch and switch to it, then run:

```bash
mkdir -p .codex-work/logs .codex-work/tmp
export TMPDIR="$PWD/.codex-work/tmp"
export LEAN_NUM_THREADS=1 FAILCOMP_STYLE_JOBS=1
set -o pipefail
python3 Lean/FailureOfComposition/Verification/test_style_gate.py
bash scripts/verify-failure-composition.sh --check-environment
bash scripts/verify-failure-composition.sh 2>&1 \
  | tee .codex-work/logs/evaluator-style-cleanup.log
```

Acceptance requires the native build, all 103 style checks, type/axiom and
dependency audits, both project kernel replays, and nine paired draft checks
to pass. Retain `evaluator-style-cleanup.log` and the generated
`.codex-work/logs/port-verification/style-lint.json`. The latter must list 103
passing sources, zero diagnostics, and only the three recorded pre-existing
scoped exceptions. This run remains separate from Palomar Comparator.
