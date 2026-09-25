#!/usr/bin/env python3
"""Evidence and input checks for ``scripts/verify-palomar.sh``.

This module is deliberately standard-library-only.  It does not launch Lean,
Comparator, or a checker; the shell launcher owns those actions.  Keeping the
pure decisions here makes malformed supervisor records, capacity snapshots,
and stale precheck inputs regression-testable without mock checkers.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from typing import Any, Iterable


GIB = 1024**3
MIN_DISK_BYTES = 20 * GIB
CHECKER_NAMES = {
    "lean",
    "lake",
    "leanexport",
    "leanchecker",
    "nanoda_bin",
    "con-ron",
}
REQUIRED_LIMITS = {
    "memory.oom.group",
    "memory.swap.max",
    "memory.high",
    "memory.max",
    "pids.max",
}
SOURCE_SUFFIXES = {".json", ".lean", ".py", ".sh", ".toml", ".yaml", ".yml"}


class EvidenceError(RuntimeError):
    """A required evidence record is absent, malformed, or inconsistent."""


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def atomic_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f"{path.name}.{os.getpid()}.tmp")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    os.replace(temporary, path)


def atomic_text(path: Path, value: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f"{path.name}.{os.getpid()}.tmp")
    temporary.write_text(value, encoding="utf-8")
    os.replace(temporary, path)


def read_json_object(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except OSError as error:
        raise EvidenceError(f"cannot read {path.name}: {error}") from error
    except json.JSONDecodeError as error:
        raise EvidenceError(f"malformed {path.name}: {error}") from error
    if not isinstance(value, dict):
        raise EvidenceError(f"{path.name} must contain a JSON object")
    return value


def read_meminfo(path: Path = Path("/proc/meminfo")) -> dict[str, int]:
    values: dict[str, int] = {}
    for line in path.read_text(encoding="ascii").splitlines():
        key, separator, remainder = line.partition(":")
        if not separator:
            continue
        fields = remainder.split()
        if fields and fields[0].isdigit():
            multiplier = 1024 if fields[1:] == ["kB"] else 1
            values[key] = int(fields[0]) * multiplier
    required = {"MemTotal", "MemAvailable", "SwapTotal", "SwapFree"}
    missing = sorted(required - values.keys())
    if missing:
        raise EvidenceError(f"missing /proc/meminfo fields: {', '.join(missing)}")
    return values


def read_cgroup_number(path: Path) -> int | None:
    try:
        raw = path.read_text(encoding="ascii").strip()
    except OSError as error:
        raise EvidenceError(f"cannot read cgroup value {path}: {error}") from error
    if raw == "max":
        return None
    if not raw.isdigit():
        raise EvidenceError(f"malformed cgroup value in {path}: {raw!r}")
    return int(raw)


def cgroup_ancestors(target: Path) -> list[Path]:
    root = Path("/sys/fs/cgroup")
    resolved = target.resolve(strict=True)
    if not resolved.is_relative_to(root):
        raise EvidenceError(f"cgroup path escapes {root}: {resolved}")
    ancestors = []
    current = resolved
    while True:
        ancestors.append(current)
        if current == root:
            return ancestors
        current = current.parent


def collect_ancestor_capacity(target: Path) -> dict[str, Any]:
    records: list[dict[str, Any]] = []
    memory_remaining: int | None = None
    swap_remaining: int | None = None
    for position, directory in enumerate(cgroup_ancestors(target)):
        memory_paths = [
            directory / "memory.max",
            directory / "memory.high",
            directory / "memory.current",
        ]
        swap_paths = [directory / "memory.swap.max", directory / "memory.swap.current"]
        memory_present = [path.is_file() for path in memory_paths]
        swap_present = [path.is_file() for path in swap_paths]
        if position == 0 and (not all(memory_present) or not all(swap_present)):
            raise EvidenceError(f"delegated cgroup lacks memory controller files: {directory}")
        if any(memory_present) and not all(memory_present):
            raise EvidenceError(f"ancestor has incomplete memory controller files: {directory}")
        if any(swap_present) and not all(swap_present):
            raise EvidenceError(f"ancestor has incomplete swap controller files: {directory}")
        memory_max = read_cgroup_number(memory_paths[0]) if all(memory_present) else None
        memory_high = read_cgroup_number(memory_paths[1]) if all(memory_present) else None
        memory_current = (
            read_cgroup_number(memory_paths[2]) or 0 if all(memory_present) else None
        )
        swap_max = read_cgroup_number(swap_paths[0]) if all(swap_present) else None
        swap_current = (
            read_cgroup_number(swap_paths[1]) or 0 if all(swap_present) else None
        )
        available_memory = (
            max(0, memory_max - memory_current)
            if memory_max is not None and memory_current is not None
            else None
        )
        available_swap = (
            max(0, swap_max - swap_current)
            if swap_max is not None and swap_current is not None
            else None
        )
        if available_memory is not None:
            memory_remaining = (
                available_memory
                if memory_remaining is None
                else min(memory_remaining, available_memory)
            )
        if available_swap is not None:
            swap_remaining = (
                available_swap
                if swap_remaining is None
                else min(swap_remaining, available_swap)
            )
        records.append(
            {
                "path": str(directory),
                "memory_controller_files_present": all(memory_present),
                "memory_current": memory_current,
                "memory_high": memory_high,
                "memory_max": memory_max,
                "memory_remaining": available_memory,
                "swap_controller_files_present": all(swap_present),
                "swap_current": swap_current,
                "swap_max": swap_max,
                "swap_remaining": available_swap,
            }
        )
    return {
        "effective_memory_remaining": memory_remaining,
        "effective_swap_remaining": swap_remaining,
        "records": records,
    }


def active_checker_processes() -> list[str]:
    result = subprocess.run(
        ["ps", "-eo", "pid=,ppid=,comm=,args="],
        check=True,
        capture_output=True,
        text=True,
    )
    active = []
    for line in result.stdout.splitlines():
        fields = line.split(None, 3)
        if len(fields) >= 3 and fields[2] in CHECKER_NAMES:
            active.append(line.strip())
    return active


def evaluate_capacity(
    snapshot: dict[str, Any], requirements: dict[str, int]
) -> list[str]:
    errors = []
    memory_max = requirements["memory_max"]
    swap_max = requirements["swap_max"]
    memory_headroom = requirements["memory_headroom"]
    memory_available_reserve = requirements["memory_available_reserve"]
    swap_headroom = requirements["swap_headroom"]
    required_available_memory = memory_max + memory_available_reserve
    required_swap = swap_max + swap_headroom

    if snapshot["mem_total"] - memory_max < memory_headroom:
        errors.append("memory.max would leave less than the required physical headroom")
    if snapshot["mem_available"] < required_available_memory:
        errors.append("current MemAvailable cannot cover the phase plus free-memory reserve")
    if snapshot["swap_total"] < required_swap:
        errors.append("SwapTotal cannot cover the phase allowance plus swap reserve")
    if snapshot["swap_free"] < required_swap:
        errors.append("current SwapFree cannot cover the phase allowance plus swap reserve")
    if snapshot["disk_available"] < requirements.get("disk_min", MIN_DISK_BYTES):
        errors.append("workspace has less than the required free disk")

    ancestor_memory = snapshot.get("ancestor_memory_remaining")
    if ancestor_memory is not None and ancestor_memory < required_available_memory:
        errors.append("an ancestor cgroup cannot cover the phase plus free-memory reserve")
    ancestor_swap = snapshot.get("ancestor_swap_remaining")
    if ancestor_swap is not None and ancestor_swap < required_swap:
        errors.append("an ancestor cgroup cannot cover the phase plus swap reserve")
    if snapshot.get("active_workloads"):
        errors.append("an overlapping Lean or Comparator workload is active")
    return errors


def capacity_command(args: argparse.Namespace) -> int:
    meminfo = read_meminfo(Path(args.meminfo))
    ancestor = collect_ancestor_capacity(Path(args.cgroup))
    disk_available = shutil.disk_usage(args.repository).free
    snapshot = {
        "mem_total": meminfo["MemTotal"],
        "mem_available": meminfo["MemAvailable"],
        "swap_total": meminfo["SwapTotal"],
        "swap_free": meminfo["SwapFree"],
        "disk_available": disk_available,
        "ancestor_memory_remaining": ancestor["effective_memory_remaining"],
        "ancestor_swap_remaining": ancestor["effective_swap_remaining"],
        "active_workloads": active_checker_processes(),
    }
    requirements = {
        "memory_max": args.memory_max,
        "swap_max": args.swap_max,
        "memory_headroom": args.memory_headroom,
        "memory_available_reserve": args.memory_available_reserve,
        "swap_headroom": args.swap_headroom,
        "disk_min": args.disk_min,
    }
    errors = evaluate_capacity(snapshot, requirements)
    record = {
        "classification": "capacity_preflight_snapshot",
        "phase": args.phase,
        "snapshot_only": True,
        "reservation": False,
        "note": (
            "This preflight observes current capacity; it cannot reserve resources "
            "against unrelated workloads started later."
        ),
        "requirements": requirements,
        "snapshot": snapshot,
        "ancestor_cgroups": ancestor["records"],
        "result": "pass" if not errors else "fail",
        "errors": errors,
    }
    atomic_json(Path(args.output), record)
    print(
        "CAPACITY"
        f" phase={args.phase} mem_total={snapshot['mem_total']}"
        f" mem_available={snapshot['mem_available']} memory_max={args.memory_max}"
        f" physical_headroom={args.memory_headroom}"
        f" available_reserve={args.memory_available_reserve}"
    )
    print(
        "CAPACITY"
        f" phase={args.phase} swap_total={snapshot['swap_total']}"
        f" swap_free={snapshot['swap_free']} swap_max={args.swap_max}"
        f" swap_reserve={args.swap_headroom} disk_available={disk_available}"
    )
    print("CAPACITY snapshot_only=true reservation=false")
    for error in errors:
        print(f"error: {error}", file=sys.stderr)
    return 0 if not errors else 1


def parse_env(path: Path) -> dict[str, str]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        raise EvidenceError(f"cannot read {path.name}: {error}") from error
    result: dict[str, str] = {}
    for line in lines:
        key, separator, value = line.partition("=")
        if not separator or not key or key in result:
            raise EvidenceError(f"malformed or duplicate entry in {path.name}: {line!r}")
        result[key] = value
    return result


def require_bool(status: dict[str, Any], key: str, expected: bool) -> str | None:
    value = status.get(key)
    if type(value) is not bool:  # bool is deliberately stricter than truthiness
        return f"{key} is missing or not boolean"
    if value is not expected:
        return f"{key} is {value}, expected {expected}"
    return None


def require_nonnegative_int(mapping: dict[str, Any], key: str) -> str | None:
    value = mapping.get(key)
    if type(value) is not int or value < 0:
        return f"{key} is missing or not a nonnegative integer"
    return None


def assess_supervised_run(
    run: Path,
    expected: dict[str, str],
    markers: dict[str, str],
) -> dict[str, Any]:
    status = read_json_object(run / "cgroup-status.json")
    errors: list[str] = []
    computational_errors: list[str] = []
    if status.get("state") != "finished":
        errors.append("state is not finished")
    if type(status.get("exit_status")) is not int:
        errors.append("exit_status is missing or not an integer")
    elif status["exit_status"] != 0:
        computational_errors.append(f"payload exit_status is {status['exit_status']}")
    if "term_signal" not in status:
        errors.append("term_signal is missing")
    elif status.get("term_signal") is not None:
        computational_errors.append(f"payload term_signal is {status['term_signal']}")
    for key, wanted in (
        ("deadline_fired", False),
        ("liveness_lost", False),
        ("placement_ok", True),
        ("populated_after_kill", False),
    ):
        problem = require_bool(status, key, wanted)
        if problem:
            errors.append(problem)
    for key in ("placement_error", "launch_error"):
        if key not in status or status.get(key) is not None:
            errors.append(f"{key} is missing or non-null")
    if not isinstance(status.get("cgroup"), str) or not status["cgroup"].startswith(
        "/sys/fs/cgroup/"
    ):
        errors.append("cgroup is missing or not an absolute cgroup-v2 path")
    if type(status.get("supervisor_pid")) is not int or status["supervisor_pid"] <= 0:
        errors.append("supervisor_pid is missing or invalid")
    if type(status.get("cpu_delegated")) is not bool:
        errors.append("cpu_delegated is missing or not boolean")
    if "sandbox_started" not in status or status.get("sandbox_started") is not None:
        errors.append("sandbox_started is missing or non-null for the unsandboxed supervisor")
    if not isinstance(status.get("elapsed"), (int, float)) or isinstance(
        status.get("elapsed"), bool
    ) or status["elapsed"] < 0:
        errors.append("elapsed is missing or invalid")
    problem = require_nonnegative_int(status, "memory_peak")
    if problem:
        errors.append(problem)

    limits = status.get("limits_applied")
    if not isinstance(limits, dict):
        errors.append("limits_applied is missing or not an object")
    else:
        for key in sorted(REQUIRED_LIMITS):
            if limits.get(key) is not True:
                errors.append(f"required limit {key} was not applied")

    events = status.get("memory_events")
    if not isinstance(events, dict):
        errors.append("memory_events is missing or not an object")
        events = {}
    for key in ("high", "max", "oom", "oom_kill", "oom_group_kill"):
        problem = require_nonnegative_int(events, key)
        if problem:
            errors.append(f"memory_events.{problem}")
    for key in ("oom", "oom_kill", "oom_group_kill"):
        if type(events.get(key)) is int and events[key] != 0:
            errors.append(f"memory_events.{key} is {events[key]}")

    pids_events = status.get("pids_events")
    if not isinstance(pids_events, dict):
        errors.append("pids_events is missing or not an object")
    else:
        problem = require_nonnegative_int(pids_events, "max")
        if problem:
            errors.append(f"pids_events.{problem}")
        elif pids_events["max"] != 0:
            errors.append(f"pids_events.max is {pids_events['max']}")

    try:
        raw_systemd = (run / "systemd-run.exit").read_text(encoding="ascii").strip()
        if not raw_systemd or not raw_systemd.isdigit():
            raise ValueError
        systemd_exit = int(raw_systemd)
        if systemd_exit != 0:
            errors.append(f"systemd-run exit status is {systemd_exit}")
    except (OSError, ValueError):
        systemd_exit = None
        errors.append("systemd-run.exit is missing or malformed")

    try:
        containment = parse_env(run / "containment.env")
        containment_expected = {
            "classification": "aggregate_process_tree_containment",
            "memory_high": expected["memory_high"],
            "memory_max": expected["memory_max"],
            "memory_swap_max": expected["memory_swap_max"],
            "memory_oom_group": "1",
            "cpu_request": expected["cpu_list"],
            "nproc": "1",
            "cpus_allowed_list": expected["cpu_list"],
        }
        for key, wanted in containment_expected.items():
            if containment.get(key) != wanted:
                errors.append(
                    f"containment {key}={containment.get(key)!r}, expected {wanted!r}"
                )
        if containment.get("cgroup_limits") != status.get("cgroup"):
            errors.append("containment cgroup_limits does not match supervisor cgroup")
        if containment.get("cgroup_leaf") != f"{status.get('cgroup')}/leaf":
            errors.append("containment cgroup_leaf does not match supervisor cgroup")
    except EvidenceError as error:
        containment = {}
        errors.append(str(error))

    output_path = run / expected["output_name"]
    try:
        output = output_path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        output = ""
        errors.append(f"{output_path.name} is missing")
    marker_values = {name: needle in output for name, needle in markers.items()}
    for name, present in marker_values.items():
        if not present:
            computational_errors.append(f"success marker {name} is absent")
    computational_success = not computational_errors and status.get("exit_status") == 0
    infrastructure_clean = not errors
    return {
        "status": status,
        "events": events,
        "systemd_exit_status": systemd_exit,
        "marker_values": marker_values,
        "computational_success": computational_success,
        "computational_errors": computational_errors,
        "infrastructure_clean": infrastructure_clean,
        "errors": errors,
        "passed": infrastructure_clean and computational_success,
    }


def shell_value(value: Any) -> str:
    text = "" if value is None else str(value)
    return text.replace("\n", " ").replace("\r", " ")


def finalize_command(args: argparse.Namespace) -> int:
    run = Path(args.run)
    destination = run / args.destination
    expected = {
        "memory_high": str(args.memory_high),
        "memory_max": str(args.memory_max),
        "memory_swap_max": str(args.memory_swap_max),
        "cpu_list": args.cpu_list,
        "output_name": args.output_name,
    }
    if args.kind == "comparator":
        markers = {
            "con_ron_accepts": "con-ron kernel accepts the solution",
            "nanoda_accepts": "nanoda kernel accepts the solution",
            "lean_accepts": "Lean default kernel accepts the solution",
            "comparator_accepts": "Your solution is okay!",
        }
    else:
        markers = {"paired_check_accepts": "PASS local paired draft check"}
    try:
        assessment = assess_supervised_run(run, expected, markers)
    except EvidenceError as error:
        assessment = {
            "status": {},
            "events": {},
            "systemd_exit_status": None,
            "marker_values": {name: False for name in markers},
            "computational_success": False,
            "computational_errors": ["required supervisor evidence is unavailable"],
            "infrastructure_clean": False,
            "errors": [str(error)],
            "passed": False,
        }
    status = assessment["status"]
    events = assessment["events"]
    lines = [
        f"verification_kind={args.verification_kind}",
        "official_palomar_verification=false",
        f"resume_of={shell_value(args.resume_of)}",
        f"result={'pass' if assessment['passed'] else 'fail'}",
        f"infrastructure_clean={str(assessment['infrastructure_clean']).lower()}",
        f"computational_success={str(assessment['computational_success']).lower()}",
        f"payload_exit_status={shell_value(status.get('exit_status'))}",
        f"term_signal={shell_value(status.get('term_signal'))}",
        f"systemd_exit_status={shell_value(assessment['systemd_exit_status'])}",
        f"elapsed_seconds={shell_value(status.get('elapsed'))}",
        f"memory_peak_bytes={shell_value(status.get('memory_peak'))}",
        f"memory_high_events={shell_value(events.get('high'))}",
        f"memory_max_events={shell_value(events.get('max'))}",
        f"memory_oom_events={shell_value(events.get('oom'))}",
        f"memory_oom_kill_events={shell_value(events.get('oom_kill'))}",
        f"deadline_fired={str(status.get('deadline_fired')).lower()}",
        f"liveness_lost={str(status.get('liveness_lost')).lower()}",
        f"placement_ok={str(status.get('placement_ok')).lower()}",
        f"populated_after_kill={str(status.get('populated_after_kill')).lower()}",
        *[
            f"{name}={str(value).lower()}"
            for name, value in assessment["marker_values"].items()
        ],
        "infrastructure_errors=" + shell_value("; ".join(assessment["errors"])),
        "computational_errors="
        + shell_value("; ".join(assessment["computational_errors"])),
    ]
    atomic_text(destination, "\n".join(lines) + "\n")
    return 0 if assessment["passed"] else 1


def git_output(directory: Path, *arguments: str) -> str:
    result = subprocess.run(
        ["git", "--no-optional-locks", "-C", str(directory), *arguments],
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode:
        raise EvidenceError(
            f"git {' '.join(arguments)} failed in {directory}: {result.stderr.strip()}"
        )
    return result.stdout.strip()


def source_paths(repository: Path) -> list[Path]:
    lean = repository / "Lean"
    candidates = {
        repository / "scripts" / "verify-palomar.sh",
        repository / "scripts" / "palomar_launcher_checks.py",
        lean / "lean-toolchain",
        lean / "lake-manifest.json",
        lean / "lakefile.toml",
    }
    for name in ("CategoricalRiceShapiro.lean", "FailureOfComposition.lean"):
        candidates.add(lean / name)
    for root in (lean / "CategoricalRiceShapiro", lean / "FailureOfComposition"):
        for path in root.rglob("*"):
            if (
                path.is_file()
                and "__pycache__" not in path.parts
                and path.suffix in SOURCE_SUFFIXES
            ):
                candidates.add(path)
    missing = [path for path in candidates if not path.is_file()]
    if missing:
        raise EvidenceError(f"missing precheck input: {missing[0]}")
    return sorted(candidates)


def content_entries(repository: Path, paths: Iterable[Path]) -> list[dict[str, Any]]:
    entries = []
    for path in sorted(Path(item).resolve(strict=True) for item in paths):
        if not path.is_relative_to(repository):
            raise EvidenceError(f"input escapes repository: {path}")
        entries.append(
            {
                "path": path.relative_to(repository).as_posix(),
                "bytes": path.stat().st_size,
                "sha256": sha256_file(path),
            }
        )
    return entries


def dependency_records(repository: Path) -> list[dict[str, Any]]:
    lean = repository / "Lean"
    manifest = read_json_object(lean / "lake-manifest.json")
    packages = manifest.get("packages")
    if not isinstance(packages, list) or not packages:
        raise EvidenceError("lake-manifest.json has no packages array")
    package_root = (lean / manifest.get("packagesDir", ".lake/packages")).resolve()
    records = []
    for package in packages:
        if not isinstance(package, dict) or not isinstance(package.get("name"), str):
            raise EvidenceError("malformed package entry in lake-manifest.json")
        name = package["name"]
        revision = package.get("rev")
        if not isinstance(revision, str) or len(revision) != 40:
            raise EvidenceError(f"{name}: package revision is not a full Git SHA")
        directory = (package_root / name.strip("«»")).resolve(strict=True)
        head = git_output(directory, "rev-parse", "HEAD")
        status = git_output(directory, "status", "--porcelain", "--untracked-files=all")
        if head != revision:
            raise EvidenceError(f"{name}: resolved HEAD {head} != pin {revision}")
        if status:
            raise EvidenceError(f"{name}: resolved dependency checkout is dirty")
        config_name = package.get("configFile", "lakefile.toml")
        manifest_name = package.get("manifestFile", "lake-manifest.json")
        config = directory / config_name
        package_manifest = directory / manifest_name
        records.append(
            {
                "name": name,
                "url": package.get("url"),
                "pin": revision,
                "resolved_path": str(directory),
                "resolved_head": head,
                "worktree_clean": True,
                "config_file": config_name,
                "config_sha256": sha256_file(config),
                "manifest_file": manifest_name,
                "manifest_sha256": sha256_file(package_manifest),
            }
        )
    return records


def build_precheck_manifest(repository: Path, lean_prefix: Path) -> dict[str, Any]:
    repository = repository.resolve(strict=True)
    lean_prefix = lean_prefix.resolve(strict=True)
    selected_paths = source_paths(repository)
    relative_selected = [str(path.relative_to(repository)) for path in selected_paths]
    worktree_status = git_output(
        repository,
        "status",
        "--porcelain=v1",
        "--untracked-files=all",
        "--",
        *relative_selected,
    ).splitlines()
    tools = []
    for name in ("lean", "lake"):
        path = lean_prefix / "bin" / name
        if not path.is_file() or not os.access(path, os.X_OK):
            raise EvidenceError(f"missing selected-toolchain executable: {path}")
        tools.append({"name": name, "path": str(path), "sha256": sha256_file(path)})
    return {
        "schema": "failure-of-composition-precheck-inputs-v1",
        "repository": str(repository),
        "git_head": git_output(repository, "rev-parse", "HEAD"),
        "worktree_status_for_inputs": worktree_status,
        "command": "python3 Lean/FailureOfComposition/Palomar/check_draft.py",
        "files": content_entries(repository, selected_paths),
        "selected_toolchain": tools,
        "dependencies": dependency_records(repository),
    }


def manifest_command(args: argparse.Namespace) -> int:
    value = build_precheck_manifest(Path(args.repository), Path(args.lean_prefix))
    atomic_json(Path(args.output), value)
    print(f"PRECHECK_INPUT_MANIFEST {args.output} sha256={sha256_file(Path(args.output))}")
    return 0


def compare_manifests(expected: Path, actual: Path) -> tuple[bool, list[str]]:
    left = read_json_object(expected)
    right = read_json_object(actual)
    if left == right:
        return True, []
    differences = []
    for key in sorted(left.keys() | right.keys()):
        if left.get(key) != right.get(key):
            differences.append(key)
    return False, differences


def compare_command(args: argparse.Namespace) -> int:
    try:
        equal, differences = compare_manifests(Path(args.expected), Path(args.actual))
        report = {
            "classification": "precheck_input_manifest_comparison",
            "expected": str(Path(args.expected).resolve()),
            "actual": str(Path(args.actual).resolve()),
            "result": "match" if equal else "stale",
            "differing_sections": differences,
        }
    except EvidenceError as error:
        equal = False
        report = {
            "classification": "precheck_input_manifest_comparison",
            "expected": str(Path(args.expected).resolve()),
            "actual": str(Path(args.actual).resolve()),
            "result": "stale",
            "differing_sections": ["missing_or_malformed_manifest"],
            "error": str(error),
        }
    if args.report:
        atomic_json(Path(args.report), report)
    if equal:
        print("PASS precheck input manifest matches")
        return 0
    print(
        "STALE precheck input evidence: "
        + ", ".join(report["differing_sections"]),
        file=sys.stderr,
    )
    return 1


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    subparsers = result.add_subparsers(dest="command", required=True)

    capacity = subparsers.add_parser("capacity")
    capacity.add_argument("--repository", required=True)
    capacity.add_argument("--cgroup", required=True)
    capacity.add_argument("--phase", required=True)
    capacity.add_argument("--memory-max", type=int, required=True)
    capacity.add_argument("--swap-max", type=int, required=True)
    capacity.add_argument("--memory-headroom", type=int, required=True)
    capacity.add_argument("--memory-available-reserve", type=int, required=True)
    capacity.add_argument("--swap-headroom", type=int, required=True)
    capacity.add_argument("--disk-min", type=int, default=MIN_DISK_BYTES)
    capacity.add_argument("--meminfo", default="/proc/meminfo")
    capacity.add_argument("--output", required=True)
    capacity.set_defaults(function=capacity_command)

    finalize = subparsers.add_parser("finalize")
    finalize.add_argument("--kind", choices=("comparator", "precheck"), required=True)
    finalize.add_argument("--run", required=True)
    finalize.add_argument("--destination", required=True)
    finalize.add_argument("--verification-kind", required=True)
    finalize.add_argument("--resume-of", default="")
    finalize.add_argument("--memory-high", type=int, required=True)
    finalize.add_argument("--memory-max", type=int, required=True)
    finalize.add_argument("--memory-swap-max", type=int, required=True)
    finalize.add_argument("--cpu-list", required=True)
    finalize.add_argument("--output-name", required=True)
    finalize.set_defaults(function=finalize_command)

    manifest = subparsers.add_parser("precheck-manifest")
    manifest.add_argument("--repository", required=True)
    manifest.add_argument("--lean-prefix", required=True)
    manifest.add_argument("--output", required=True)
    manifest.set_defaults(function=manifest_command)

    compare = subparsers.add_parser("compare-manifests")
    compare.add_argument("--expected", required=True)
    compare.add_argument("--actual", required=True)
    compare.add_argument("--report")
    compare.set_defaults(function=compare_command)
    return result


def main(argv: list[str]) -> int:
    args = parser().parse_args(argv)
    try:
        return args.function(args)
    except (EvidenceError, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
