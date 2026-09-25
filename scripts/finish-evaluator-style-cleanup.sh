#!/usr/bin/env bash
# Finish the already-authorized cleanup: verify, record, fast-forward, and publish.
# May be invoked as: git show FETCH_HEAD:scripts/finish-evaluator-style-cleanup.sh | bash
set -euo pipefail
if [[ ${1-} == --help ]]; then
  echo 'Run from the clean FailureOfComposition port checkout. Verifies cleanup and pushes main without force.'
  exit 0
fi
[[ $# == 0 ]] || { echo 'No arguments are supported except --help.' >&2; exit 2; }
fail() { echo "ERROR: $*" >&2; exit 1; }
for command in git python3 ps awk tee tar date grep; do
  command -v "$command" >/dev/null || fail "Missing command: $command"
done
root=$(git rev-parse --show-toplevel) || fail 'Run inside the existing port checkout.'
[[ $(pwd -P) == "$(cd "$root" && pwd -P)" ]] || fail 'Run from the Git repository root.'
[[ -z $(git status --porcelain) ]] || fail 'Working tree has changes; preserve them before running.'
fetch_urls=$(git remote get-url --all origin)
push_urls=$(git remote get-url --push --all origin)
while IFS= read -r url; do
  case "$url" in
    git@github.com:flengyel/FailureOfComposition.git|https://github.com/flengyel/FailureOfComposition.git) ;;
    *) fail 'Origin must identify flengyel/FailureOfComposition using SSH or HTTPS.' ;;
  esac
done <<< "$fetch_urls"$'\n'"$push_urls"
[[ -n $(git config user.name) && -n $(git config user.email) ]] || fail 'Configure Git user.name and user.email first.'
git var GIT_AUTHOR_IDENT >/dev/null || fail 'Configure the existing Git author identity first.'
git var GIT_COMMITTER_IDENT >/dev/null || fail 'Configure the existing Git committer identity first.'
active=$(ps -eo comm=,args= | awk '$1 == "lean" || $1 == "lake" || $1 == "leanchecker"')
[[ -z $active ]] || fail "Another Lean/Lake process is active. Wait for completion, then rerun: $active"
known=7506b26a5bb92c036fc13bdae7262f26b21368e0
stamp=$(date -u +%Y%m%dT%H%M%SZ)-$$
run_dir="$root/.codex-work/logs/evaluator-style-cleanup-$stamp"
mkdir -p "$run_dir" "$root/.codex-work/tmp"
export TMPDIR="$root/.codex-work/tmp" LEAN_NUM_THREADS=1 FAILCOMP_STYLE_JOBS=1
validator="$TMPDIR/validate-style-cleanup-$stamp.py"
cat > "$validator" <<'PY'
import hashlib, json, sys
from pathlib import Path

root, log = Path(sys.argv[1]), Path(sys.argv[2])
final = ('PASS native build, module inventory, strict style gate, theorem/type and axiom audits, '
         'dependency audit, both kernel replays, and nine paired draft checks')
lines = [line for line in log.read_text().splitlines() if line.strip()]
assert lines and lines[-1] == final, 'Full verifier final PASS must be the last nonempty line'
evidence = root / '.codex-work/logs/port-verification'
style = json.loads((evidence / 'style-lint.json').read_text())
native = json.loads((evidence / 'native-build.json').read_text())
assert native['status'] == 'passed' and native['returncode'] == 0, 'Native build failed'
assert native['lean_toolchain'] == 'leanprover/lean4:v4.35.0-rc2'
assert native['foundation_revision'] == 'e72cfe981aa65166f37fa4e2584f4806bc48d72f'
assert native['mathlib_revision'] == '065356127b1dc0016f66b7283ce0ce2c4055aa55'
assert native['mathematical_module_counts'] == {
    'FailureOfComposition': 72, 'CategoricalRiceShapiro': 31, 'total': 103}
assert style['status'] == 'passed' and style['returncode'] == 0
assert style['source_count'] == 103 and style['warning_or_error_count'] == 0
assert style['warnings_are_errors'] and not style['new_linter_suppressions_allowed']
lean = root / 'Lean'
pins = json.loads((lean / 'FailureOfComposition/Porting/EVALUATOR_PROVENANCE.json').read_text())
expected = {'FailureOfComposition.lean'} | {
    str(p.relative_to(lean)) for p in (lean / 'FailureOfComposition').glob('*.lean')
} | {p['path'] for p in pins['files']}
rows = style['results']
assert len(expected) == len(rows) == 103 and {r['source'] for r in rows} == expected
exceptions = {
    'CategoricalRiceShapiro/ArithmeticCode/FoundationCompat.lean': {'evalAux_unique', 'eval_unique'},
    'CategoricalRiceShapiro/ArithmeticCode/Evaluation.lean': {'eval_codeLift_iff'},
}
assert {p: set(names) for p, names in style['existing_scoped_exceptions'].items()} == exceptions
for row in rows:
    assert row['status'] == 'passed' and row['returncode'] == 0
    assert row['warning_or_error_count'] == row['linter_suppression_count'] == 0
    assert row['source_unchanged_during_check']
    allowed = exceptions.get(row['source'], set())
    assert set(row['existing_scoped_exceptions']) == allowed
    assert row['existing_scoped_exception_count'] == len(allowed)
    assert row['sha256'] == hashlib.sha256((lean / row['source']).read_bytes()).hexdigest()
assert sum(r['existing_scoped_exception_count'] for r in rows) == 3
PY
work() {
  local mapping='+refs/heads/*:refs/remotes/origin/*' target checked acceptance_mode
  if ! git config --get-all remote.origin.fetch | grep -Fqx -- "$mapping"; then
    git config --add remote.origin.fetch "$mapping"
  fi
  git fetch origin </dev/null
  target=$(git rev-parse 'refs/remotes/origin/codex/evaluator-style-cleanup^{commit}')
  git merge-base --is-ancestor "$known" "$target" || fail 'Cleanup branch no longer contains the reviewed cleanup.'
  git merge-base --is-ancestor main "$target" || fail 'Local main has independent changes; no branch was moved.'
  git merge-base --is-ancestor refs/remotes/origin/main "$target" || fail 'Remote main has independent changes; no branch was moved.'
  git switch --detach "$target"
  printf '%s\n' "$target" > "$run_dir/verified-source-commit.txt"
  python3 Lean/FailureOfComposition/Verification/test_style_gate.py </dev/null 2>&1 | tee "$run_dir/gate-tests.log"
  bash scripts/verify-failure-composition.sh --check-environment </dev/null 2>&1 | tee "$run_dir/environment-check.log"
  acceptance_mode=fresh_verification
  if git diff --quiet "$known" "$target" -- Lean scripts/verify-failure-composition.sh &&
     python3 -I "$validator" "$root" "$root/.codex-work/logs/evaluator-style-cleanup.log" \
       > "$run_dir/reuse-check.log" 2>&1; then
    cp "$root/.codex-work/logs/evaluator-style-cleanup.log" "$run_dir/verification.log"
    acceptance_mode=reused_completed_7506_run
    echo 'Reusing the completed cleanup run: matching source hashes and every required gate passed.'
  else
    bash scripts/verify-failure-composition.sh </dev/null 2>&1 | tee "$run_dir/verification.log"
  fi
  python3 -I "$validator" "$root" "$run_dir/verification.log"
  [[ -z $(git status --porcelain) ]] || fail 'The source checkout changed during verification.'
  python3 - "$root" "$run_dir" "$target" "$acceptance_mode" <<'PY'
from datetime import datetime, timezone
import hashlib, json, shutil, sys
from pathlib import Path

root, run, source, mode = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3], sys.argv[4]
porting = 'Lean/FailureOfComposition/Porting/'
replacements = {
    'README.md': (
        'extends warnings-as-errors checks to all 31 evaluator sources; its changed\n'
        'proofs require a subsequent WSL verification before acceptance.',
        'extends warnings-as-errors checks to all 31 evaluator sources. The cleanup\n'
        'passed its full WSL verification; see the\n'
        '[validation record](Lean/FailureOfComposition/Porting/STYLE_CLEANUP_VALIDATION.json).'),
    'Lean/FailureOfComposition/README.md': (
        'and no suppressions; the expanded gate and evaluator cleanup await their WSL\n'
        'run. See [the cleanup record](Porting/STYLE_CLEANUP.md).',
        'and no suppressions. The expanded 103-source gate and evaluator cleanup\n'
        'passed the full WSL suite; see the [validation record](Porting/STYLE_CLEANUP_VALIDATION.json)\n'
        'and [cleanup record](Porting/STYLE_CLEANUP.md).'),
    porting + 'STATUS.md': (
        '[evaluator style cleanup](STYLE_CLEANUP.md) has separate pending validation.',
        '[evaluator style cleanup](STYLE_CLEANUP.md) passed its separate full WSL\n'
        'verification; see [STYLE_CLEANUP_VALIDATION.json](STYLE_CLEANUP_VALIDATION.json).'),
    porting + 'STYLE_CLEANUP.md': (
        '**Lean compilation and the expanded strict gate are pending for this cleanup.**',
        '**Lean compilation and the expanded 103-source strict gate passed for this cleanup.**\n'
        'The full WSL suite also passed its theorem/type, axiom, dependency, kernel-replay,\n'
        'and nine paired draft checks. [STYLE_CLEANUP_VALIDATION.json](STYLE_CLEANUP_VALIDATION.json)\n'
        'records the exact checked source commit and whether the completed run was reused.'),
}
updated = {}
for relative, (old, new) in replacements.items():
    text = (root / relative).read_text()
    if text.count(old) != 1:
        raise SystemExit(f'Documentation changed; expected exactly one pending marker in {relative}')
    updated[relative] = text.replace(old, new)
evidence = root / '.codex-work/logs/port-verification'
for name in ('style-lint.json', 'native-build.json'):
    shutil.copy2(evidence / name, run / name)
files = ('verification.log', 'gate-tests.log', 'style-lint.json', 'native-build.json')
report = {
    'status': 'passed', 'recorded_at': datetime.now(timezone.utc).isoformat(),
    'verified_source_commit': source, 'acceptance_mode': mode,
    'regression_tests_exit_code': 0, 'full_verification_exit_code': 0,
    'style_sources': 103, 'warning_or_error_count': 0,
    'unexpected_linter_suppression_count': 0, 'existing_scoped_exceptions': 3,
    'palomar_comparator_run': False,
    'evidence_directory': str(run.relative_to(root)),
    'sha256': {name: hashlib.sha256((run / name).read_bytes()).hexdigest() for name in files},
}
for relative, text in updated.items():
    (root / relative).write_text(text)
(root / porting / 'STYLE_CLEANUP_VALIDATION.json').write_text(json.dumps(report, indent=2) + '\n')
shutil.copy2(root / porting / 'STYLE_CLEANUP_VALIDATION.json', run / 'STYLE_CLEANUP_VALIDATION.json')
PY
  git diff --check
  git add -- README.md Lean/FailureOfComposition/README.md \
    Lean/FailureOfComposition/Porting/STYLE_CLEANUP.md \
    Lean/FailureOfComposition/Porting/STATUS.md \
    Lean/FailureOfComposition/Porting/STYLE_CLEANUP_VALIDATION.json
  git commit -m 'Record verified evaluator style cleanup' </dev/null
  checked=$(git rev-parse HEAD)
  printf '%s\n' "$checked" > "$run_dir/validation-commit.txt"
  git fetch origin </dev/null
  git merge-base --is-ancestor main "$checked" || fail 'Local main changed; verified commit retained.'
  git merge-base --is-ancestor refs/remotes/origin/main "$checked" || fail 'Remote main changed; verified commit retained.'
  git switch main
  git merge --ff-only "$checked"
  git push origin refs/heads/main:refs/heads/main </dev/null
  printf 'PASS: main published at %s\n' "$checked"
}
set +e
(set -e; work) 2>&1 | tee "$run_dir/workflow.log"
exit_codes=("${PIPESTATUS[@]}")
set -e
result=${exit_codes[0]}
if [[ $result == 0 && ${exit_codes[1]} != 0 ]]; then result=${exit_codes[1]}; fi
python3 - "$run_dir" "$result" <<'PY'
from datetime import datetime, timezone
import json, sys
from pathlib import Path
run = Path(sys.argv[1])
(run / 'workflow-status.json').write_text(json.dumps({
    'exit_code': int(sys.argv[2]), 'finished_at': datetime.now(timezone.utc).isoformat()
}, indent=2) + '\n')
PY
bundle="$run_dir.tar.gz"
tar -czf "$bundle" -C "$(dirname "$run_dir")" "$(basename "$run_dir")"
printf 'Evidence bundle: %s\n' "$bundle"
if [[ $result != 0 ]]; then
  echo 'Workflow stopped. Logs and all source changes were retained; no reset, deletion, or force push was used.' >&2
fi
exit "$result"
