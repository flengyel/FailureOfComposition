#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import pathlib
import shutil
import subprocess
import sys
from datetime import datetime, timezone

REPOSITORY = pathlib.Path("/home/flengyel/src/FailureOfComposition-port")
LEAN_ROOT = REPOSITORY / "Lean"
EVIDENCE = REPOSITORY / ".codex-work/palomar/five-generated-congruence/20260929T224214Z"
INPUTS = EVIDENCE / "inputs/comparator"
PREFIX = pathlib.Path("/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2")
GNU_TIME = REPOSITORY / ".codex-work/tmp/gnu-time/usr/bin/time"
EXPECTED_FOUNDATION = "01f617fbe240a84aaf1c45b31b9d65e0a2e21c1d"
EXPECTED_MATHLIB = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
EXPECTED_SUBMISSION = "a59f25bd8a66bf6faf3a4f4260d412989c0185ea"
EXPECTED_THEOREMS = [
    "FailureOfComposition.Palomar.obstruction_four_properties",
    "FailureOfComposition.Palomar.no_quotient_composition_productive",
    "FailureOfComposition.Palomar.no_quotient_composition_godel",
    "FailureOfComposition.Palomar.pi_one_characterization",
    "FailureOfComposition.Palomar.generated_congruence_classification",
]


def run(*args: str, cwd: pathlib.Path = REPOSITORY) -> str:
    return subprocess.run(args, cwd=cwd, check=True, text=True, stdout=subprocess.PIPE).stdout.strip()


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: prepare_comparator.py EXPECTED_HEAD")
    expected_head = sys.argv[1]
    if INPUTS.exists():
        raise SystemExit(f"Comparator inputs already exist: {INPUTS}")
    head = run("git", "rev-parse", "HEAD")
    if head != expected_head or run("git", "rev-parse", "origin/codex/palomar-eligibility") != head:
        raise SystemExit("HEAD is not the exact published replay candidate")
    if run("git", "branch", "--show-current") != "codex/palomar-eligibility":
        raise SystemExit("wrong project branch")
    if run("git", "status", "--porcelain", "--untracked-files=normal"):
        raise SystemExit("project worktree is not clean")
    pins = {
        "foundation": run("git", "-C", str(LEAN_ROOT / ".lake/packages/Foundation"), "rev-parse", "HEAD"),
        "mathlib": run("git", "-C", str(LEAN_ROOT / ".lake/packages/mathlib"), "rev-parse", "HEAD"),
        "palomar_submission": run("git", "-C", str(REPOSITORY / ".codex-work/palomar/upstream/PalomarSubmission"), "rev-parse", "HEAD"),
    }
    if pins != {"foundation": EXPECTED_FOUNDATION, "mathlib": EXPECTED_MATHLIB, "palomar_submission": EXPECTED_SUBMISSION}:
        raise SystemExit(f"unexpected dependency identity: {pins}")
    lean_version = run(str(PREFIX / "bin/lean"), "--version", cwd=LEAN_ROOT)
    if "version 4.35.0-rc2" not in lean_version or "11acb17" not in lean_version:
        raise SystemExit(f"unexpected Lean identity: {lean_version}")
    source = LEAN_ROOT / "FailureOfComposition/Palomar/comparator-five.json"
    portable_value = json.loads(source.read_text(encoding="utf-8"))
    if portable_value.get("theorem_names") != EXPECTED_THEOREMS or portable_value.get("definition_names") != []:
        raise SystemExit("portable theorem/definition selection changed")
    if "external_kernels" in portable_value:
        raise SystemExit("portable config contains machine-local kernels")
    if set(portable_value.get("permitted_axioms", [])) != {"propext", "Classical.choice", "Quot.sound"}:
        raise SystemExit("portable permitted axioms changed")

    INPUTS.mkdir(parents=True)
    portable = INPUTS / "portable-comparator-five.json"
    protected = INPUTS / "protected-comparator-five.json"
    shutil.copyfile(source, portable)
    protected_value = dict(portable_value)
    protected_value["external_kernels"] = {
        "con-ron": [str(PREFIX / "bin/con-ron")],
        "nanoda": [str(PREFIX / "bin/nanoda_bin")],
    }
    protected.write_text(json.dumps(protected_value, indent=2) + "\n", encoding="utf-8")
    portable.chmod(0o444)
    protected.chmod(0o444)
    without_kernels = dict(protected_value)
    del without_kernels["external_kernels"]
    if without_kernels != portable_value:
        raise SystemExit("protected transformation changed more than external kernels")

    export_paths = {
        "challenge": EVIDENCE / "exports/comparator-five-challenge.ndjson",
        "solution": EVIDENCE / "exports/comparator-five-solution.ndjson",
    }
    sources = [
        LEAN_ROOT / "FailureOfComposition/Palomar/ChallengeFive.lean",
        LEAN_ROOT / "FailureOfComposition/Palomar/SolutionFive.lean",
        LEAN_ROOT / "FailureOfComposition/Palomar/PiOneBridge.lean",
        LEAN_ROOT / "FailureOfComposition/Palomar/GeneratedCongruenceBridge.lean",
        LEAN_ROOT / "FailureOfComposition/Palomar/GeneratedCongruenceInterface.lean",
        LEAN_ROOT / "FailureOfComposition/Palomar/ArithmeticInterface.lean",
        LEAN_ROOT / "FailureOfComposition/Palomar/EvaluatorInterface.lean",
        LEAN_ROOT / "FailureOfComposition/Palomar/CheckFiveInterface.lean",
    ]
    tools = ["lake", "lean", "leanexport", "leanchecker", "nanoda_bin", "con-ron"]
    identity = {
        "generated_at": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "scope": "one local cumulative Five Comparator attempt",
        "official_verification": False,
        "project_commit": head,
        "project_tree": run("git", "rev-parse", "HEAD^{tree}"),
        "branch": "codex/palomar-eligibility",
        "origin_branch": head,
        "lean_version": lean_version,
        "lean_prefix": str(PREFIX),
        **pins,
        "selected_theorems": EXPECTED_THEOREMS,
        "source_files": {
            str(path.relative_to(REPOSITORY)): {"bytes": path.stat().st_size, "sha256": sha256(path), "git_blob": run("git", "hash-object", str(path))}
            for path in sources
        },
        "tools": {name: {"path": str(PREFIX / "bin" / name), "sha256": sha256(PREFIX / "bin" / name)} for name in tools}
        | {"gnu_time": {"path": str(GNU_TIME), "sha256": sha256(GNU_TIME)}},
        "configs": {
            "source": {"path": str(source), "sha256": sha256(source)},
            "portable": {"path": str(portable), "sha256": sha256(portable)},
            "protected": {"path": str(protected), "sha256": sha256(protected)},
            "transformation": "add only authenticated absolute con-ron and nanoda commands",
        },
        "exports": {name: {"path": str(path), "bytes": path.stat().st_size, "sha256": sha256(path)} for name, path in export_paths.items()},
        "checker_profile": {
            "memory_high_bytes": 8 * 1024**3, "memory_max_bytes": 10 * 1024**3,
            "memory_swap_max_bytes": 0, "physical_headroom_bytes": 2 * 1024**3,
            "available_reserve_bytes": 4 * 1024**3, "cpu_list": "0",
            "lean_num_threads": 1, "deadline_seconds": 1200,
            "termination_grace_seconds": 30, "pressure_full_avg10_threshold": 80,
            "pressure_consecutive_seconds": 60,
        },
        "attempt_accounting_before_launch": {"checkpoint_parent_attempts": 0, "checkpoint_payload_launches": 0},
    }
    (INPUTS / "identity.json").write_text(json.dumps(identity, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("PASS prepared authenticated cumulative Five Comparator inputs")
    print(f"portable_sha256={sha256(portable)}")
    print(f"protected_sha256={sha256(protected)}")


if __name__ == "__main__":
    main()
