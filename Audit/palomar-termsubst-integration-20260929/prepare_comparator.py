#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import pathlib
import shutil
import subprocess
from datetime import datetime, timezone


REPOSITORY = pathlib.Path("/home/flengyel/src/FailureOfComposition-port")
LEAN_ROOT = REPOSITORY / "Lean"
EVIDENCE = REPOSITORY / ".codex-work/palomar/termsubst-integration/20260929T062653Z"
ANALYSIS = EVIDENCE / "analysis"
INPUTS = ANALYSIS / "comparator-inputs"
PREFIX = pathlib.Path(
    "/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2"
)
GNU_TIME = REPOSITORY / ".codex-work/tmp/gnu-time/usr/bin/time"
EXPECTED_HEAD = "9dc0a581dcc023fa0918cdf05e38c7c5288907de"
EXPECTED_FOUNDATION = "01f617fbe240a84aaf1c45b31b9d65e0a2e21c1d"
EXPECTED_MATHLIB = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
EXPECTED_SUBMISSION = "a59f25bd8a66bf6faf3a4f4260d412989c0185ea"
EXPECTED_THEOREMS = [
    "FailureOfComposition.Palomar.obstruction_four_properties",
    "FailureOfComposition.Palomar.no_quotient_composition_productive",
    "FailureOfComposition.Palomar.no_quotient_composition_godel",
]


def run(*args: str, cwd: pathlib.Path = REPOSITORY) -> str:
    return subprocess.run(
        args, cwd=cwd, check=True, text=True, stdout=subprocess.PIPE
    ).stdout.strip()


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def checked_head(path: pathlib.Path, expected: str) -> str:
    value = run("git", "-C", str(path), "rev-parse", "HEAD")
    if value != expected:
        raise SystemExit(f"unexpected revision at {path}: {value}")
    return value


def main() -> None:
    if INPUTS.exists():
        raise SystemExit(f"Comparator inputs already exist: {INPUTS}")
    if run("git", "rev-parse", "HEAD") != EXPECTED_HEAD:
        raise SystemExit("HEAD is not the tested pre-Comparator commit")
    if run("git", "rev-parse", "origin/codex/palomar-eligibility") != EXPECTED_HEAD:
        raise SystemExit("tested commit is not the published branch head")
    if run("git", "branch", "--show-current") != "codex/palomar-eligibility":
        raise SystemExit("wrong project branch")
    status = run("git", "status", "--porcelain", "--untracked-files=normal")
    if status:
        raise SystemExit(f"project worktree is not clean:\n{status}")

    foundation = checked_head(LEAN_ROOT / ".lake/packages/Foundation", EXPECTED_FOUNDATION)
    mathlib = checked_head(LEAN_ROOT / ".lake/packages/mathlib", EXPECTED_MATHLIB)
    submission = checked_head(
        REPOSITORY / ".codex-work/palomar/upstream/PalomarSubmission",
        EXPECTED_SUBMISSION,
    )
    lean_version = run(str(PREFIX / "bin/lean"), "--version", cwd=LEAN_ROOT)
    if "version 4.35.0-rc2" not in lean_version or "11acb17" not in lean_version:
        raise SystemExit(f"unexpected Lean identity: {lean_version}")

    gate_rows = []
    for line in (ANALYSIS / "focused-gates.tsv").read_text(encoding="utf-8").splitlines()[1:]:
        label, exit_status, elapsed = line.split("\t")
        gate_rows.append({"gate": label, "exit_status": int(exit_status), "elapsed_seconds": int(elapsed)})
    if not gate_rows or any(row["exit_status"] != 0 for row in gate_rows):
        raise SystemExit("one or more focused gates did not pass")
    focused_status = json.loads(
        (EVIDENCE / "runs/focused-three-gates-01/cgroup-status.json").read_text()
    )
    if focused_status.get("state") != "finished" or focused_status.get("exit_status") != 0:
        raise SystemExit("focused gate supervisor record is not a pass")

    ps = run("ps", "-eo", "comm=,args=")
    checker_names = {"lean", "lake", "leanexport", "leanchecker", "nanoda_bin", "con-ron"}
    active = [line for line in ps.splitlines() if line.split(None, 1)[0] in checker_names]
    if active:
        raise SystemExit("overlapping Lean/checker process:\n" + "\n".join(active))

    source = LEAN_ROOT / "FailureOfComposition/Palomar/comparator-three.json"
    portable_value = json.loads(source.read_text(encoding="utf-8"))
    if portable_value.get("theorem_names") != EXPECTED_THEOREMS:
        raise SystemExit("portable theorem selection changed")
    if portable_value.get("definition_names") != [] or "external_kernels" in portable_value:
        raise SystemExit("portable config is not portable or has definition holes")
    if set(portable_value.get("permitted_axioms", [])) != {
        "propext", "Classical.choice", "Quot.sound"
    }:
        raise SystemExit("portable permitted axioms changed")

    INPUTS.mkdir(parents=True)
    portable = INPUTS / "portable-comparator-three.json"
    protected = INPUTS / "protected-comparator-three.json"
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

    sources = [
        LEAN_ROOT / "FailureOfComposition/Palomar/ChallengeThree.lean",
        LEAN_ROOT / "FailureOfComposition/Palomar/SolutionThree.lean",
        LEAN_ROOT / "FailureOfComposition/Palomar/GodelQuotientBridge.lean",
        LEAN_ROOT / "FailureOfComposition/Palomar/ArithmeticBridge.lean",
        LEAN_ROOT / "FailureOfComposition/Palomar/QuotientBridge.lean",
        LEAN_ROOT / "FailureOfComposition/Palomar/CheckThreeInterface.lean",
        LEAN_ROOT / "FailureOfComposition/ConcreteGodelRE.lean",
        LEAN_ROOT / "FailureOfComposition/ConcreteGodel.lean",
        LEAN_ROOT / "FailureOfComposition/CraigPresentation.lean",
        LEAN_ROOT / ".lake/packages/Foundation/Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Basic.lean",
        LEAN_ROOT / ".lake/packages/Foundation/Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Functions.lean",
    ]
    tools = ["lake", "lean", "leanexport", "leanchecker", "nanoda_bin", "con-ron"]
    identity = {
        "generated_at": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "scope": "one local cumulative Three Comparator attempt on repaired Foundation pin",
        "official_verification": False,
        "project_commit": EXPECTED_HEAD,
        "project_tree": run("git", "rev-parse", "HEAD^{tree}"),
        "branch": "codex/palomar-eligibility",
        "origin_branch": EXPECTED_HEAD,
        "lean_version": lean_version,
        "lean_prefix": str(PREFIX),
        "mathlib": mathlib,
        "foundation": foundation,
        "palomar_submission": submission,
        "selected_theorems": EXPECTED_THEOREMS,
        "source_files": {
            str(path.relative_to(REPOSITORY)): {
                "bytes": path.stat().st_size,
                "sha256": sha256(path),
                "git_blob": run("git", "hash-object", str(path)),
            }
            for path in sources
        },
        "tools": {
            name: {
                "path": str(PREFIX / "bin" / name),
                "sha256": sha256(PREFIX / "bin" / name),
            }
            for name in tools
        } | {
            "gnu_time": {"path": str(GNU_TIME), "sha256": sha256(GNU_TIME)}
        },
        "configs": {
            "source": {"path": str(source), "sha256": sha256(source)},
            "portable": {"path": str(portable), "sha256": sha256(portable)},
            "protected": {"path": str(protected), "sha256": sha256(protected)},
            "transformation": "add only authenticated absolute con-ron and nanoda commands",
        },
        "exports": {
            name: {
                "path": str(path),
                "bytes": path.stat().st_size,
                "sha256": sha256(path),
            }
            for name, path in {
                "challenge": EVIDENCE / "exports/comparator-three-challenge.ndjson",
                "solution": EVIDENCE / "exports/comparator-three-solution.ndjson",
            }.items()
        },
        "focused_gates": gate_rows,
        "checker_profile": {
            "memory_high_bytes": 8 * 1024**3,
            "memory_max_bytes": 10 * 1024**3,
            "memory_swap_max_bytes": 0,
            "physical_headroom_bytes": 2 * 1024**3,
            "available_reserve_bytes": 4 * 1024**3,
            "cpu_list": "0",
            "lean_num_threads": 1,
            "nanoda_generated_config_num_threads": 4,
            "con_ron_configured_arguments": [],
            "note": "Lake appends the export path to con-ron and a generated JSON config to NanoDa; CPU affinity remains one for the entire process tree.",
            "deadline_seconds": 1200,
            "termination_grace_seconds": 30,
            "pressure_full_avg10_threshold": 80,
            "pressure_consecutive_seconds": 60,
        },
        "attempt_accounting_before_launch": {
            "checkpoint_parent_attempts": 0,
            "checkpoint_payload_launches": 0,
            "prior_cumulative_three_attempts": 2,
            "prior_results": [
                "timeout_inconclusive_on_original_Foundation_pin",
                "pressure_stop_inconclusive_on_first_repaired_Foundation_pin",
            ],
        },
    }
    (INPUTS / "identity.json").write_text(
        json.dumps(identity, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (INPUTS / "command.txt").write_text(
        f"cd {LEAN_ROOT} && {GNU_TIME} -v -o "
        f"{EVIDENCE}/runs/comparator-three-termsubst-01/time.log "
        f"{PREFIX}/bin/lake comparator --config {protected} "
        f"--challenge-from-export {EVIDENCE}/exports/comparator-three-challenge.ndjson "
        f"--solution-from-export {EVIDENCE}/exports/comparator-three-solution.ndjson\n",
        encoding="utf-8",
    )
    print("PASS prepared authenticated cumulative Three Comparator inputs")
    print(f"portable_sha256={sha256(portable)}")
    print(f"protected_sha256={sha256(protected)}")


if __name__ == "__main__":
    main()
