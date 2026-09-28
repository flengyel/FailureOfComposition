#!/usr/bin/env python3
"""Summarize bounded kernel probes without inferring verdicts from progress."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

ROOT = Path("/home/flengyel/src/FailureOfComposition-port")
EVIDENCE = ROOT / ".codex-work/palomar/godel-bottleneck/20260927T222925Z"
RUNS = EVIDENCE / "runs"
LABELS = [
    "probe-01-re-bridge",
    "probe-02-re-bridge",
    "probe-03-re-bridge-stride1",
    "probe-04-hotspot",
]

ACCEPTED = "accepted"
REJECTED = "rejected"
DECLINED = "declined"
LAUNCH_FAILURE = "launch_failure"
TIMEOUT = "timeout"
PRESSURE_STOP = "pressure_stop"
INTERNAL_ERROR = "internal_error"


def _exit_status(status: dict) -> int | None:
    value = status.get("exit_status")
    return value if isinstance(value, int) else None


def _stopped_classification(status: dict) -> str | None:
    if status.get("deadline_fired"):
        return TIMEOUT
    if status.get("pressure_fired"):
        return PRESSURE_STOP
    return None


def classify_conron(output: str, status: dict, *, launched: bool) -> str:
    """Classify stock con-ron; a timing summary is never an acceptance marker."""
    stopped = _stopped_classification(status)
    if stopped is not None:
        return stopped
    if not launched or status.get("launch_error"):
        return LAUNCH_FAILURE
    exit_status = _exit_status(status)
    if exit_status == 1:
        return REJECTED
    if exit_status == 2:
        return DECLINED
    if exit_status != 0:
        return INTERNAL_ERROR

    verified_acceptance = re.search(
        r"(?m)^con-ron: accepted \d+ declarations \(--verified\)$", output
    ) is not None
    progress_enabled = any(
        line.startswith(("con-ron: parse ", "con-ron: install ", "con-ron: check "))
        for line in output.splitlines()
    )
    checking_complete = (
        "con-ron: check done:" in output if progress_enabled else verified_acceptance
    )
    contradictory = any(
        marker in output
        for marker in (
            "con-ron: install failed at",
            "con-ron: check failed at",
            "con-ron: rejected",
            "con-ron: declined",
        )
    )
    if verified_acceptance and checking_complete and not contradictory:
        return ACCEPTED
    return INTERNAL_ERROR


def classify_leanchecker(output: str, status: dict, *, launched: bool) -> str:
    """Classify `leanchecker --from-export` by its explicit stock verdict."""
    stopped = _stopped_classification(status)
    if stopped is not None:
        return stopped
    if not launched or status.get("launch_error"):
        return LAUNCH_FAILURE
    exit_status = _exit_status(status)
    accepts = "Lean default kernel accepts the solution" in output
    rejects = (
        "Lean default kernel rejects the solution" in output
        or "Quotient post-check rejects the solution" in output
    )
    if exit_status == 0 and accepts and not rejects:
        return ACCEPTED
    if exit_status == 1 and rejects:
        return REJECTED
    return INTERNAL_ERROR


def classify_nanoda(output: str, status: dict, *, launched: bool) -> str:
    """Classify NanoDa with `print_success_message: true`."""
    stopped = _stopped_classification(status)
    if stopped is not None:
        return stopped
    if not launched or status.get("launch_error"):
        return LAUNCH_FAILURE
    exit_status = _exit_status(status)
    accepts = re.search(
        r"(?m)^Checked \d+ declarations with no errors(?:, skipping exported but "
        r"unpermitted axioms .*)?$",
        output,
    ) is not None
    if exit_status == 0 and accepts:
        return ACCEPTED
    if exit_status != 0 and any(
        marker in output
        for marker in (
            "typechecker errors",
            "export file declares unpermitted axiom",
            "Skipped exported but unpermitted axioms",
        )
    ):
        return REJECTED
    return INTERNAL_ERROR


def maximum_assignment(text: str, key: str) -> int | None:
    values = [int(raw) for raw in re.findall(rf"(?m)^{re.escape(key)}=(\d+)$", text)]
    return max(values) if values else None


def max_rss_bytes(text: str) -> int | None:
    values = []
    for line in text.splitlines():
        if " con-ron " not in line:
            continue
        fields = line.split(None, 8)
        if len(fields) >= 6 and all(field.isdigit() for field in fields[:6]):
            values.append(int(fields[4]) * 1024)
    return max(values) if values else None


def summarize(label: str, runs: Path = RUNS) -> dict:
    run = runs / label
    status = json.loads((run / "cgroup-status.json").read_text(encoding="utf-8"))
    workload = (run / "workload.log").read_text(encoding="utf-8")
    processes = (run / "processes.log").read_text(encoding="utf-8")
    progress = [line for line in workload.splitlines() if line.startswith("con-ron:")]
    checks = [line for line in progress if line.startswith("con-ron: check ")]
    checker_started = bool(progress)
    result = {
        "label": label,
        "counts_as_probe_slot": True,
        "checker_started": checker_started,
        "elapsed_seconds": status.get("elapsed"),
        "active_checker_wall_seconds": status.get("elapsed") if checker_started else 0.0,
        "exit_status": status.get("exit_status"),
        "deadline_fired": status.get("deadline_fired"),
        "pressure_fired": status.get("pressure_fired"),
        "pressure_peak_full_avg10": status.get("pressure_peak_full_avg10"),
        "memory_peak_bytes": status.get("memory_peak"),
        "memory_high_events": status.get("memory_events", {}).get("high"),
        "memory_max_events": status.get("memory_events", {}).get("max"),
        "oom_events": status.get("memory_events", {}).get("oom"),
        "oom_kill_events": status.get("memory_events", {}).get("oom_kill"),
        "cpu_usage_seconds": status.get("cpu_stat", {}).get("usage_usec", 0) / 1_000_000,
        "cpu_user_seconds": status.get("cpu_stat", {}).get("user_usec", 0) / 1_000_000,
        "cpu_system_seconds": status.get("cpu_stat", {}).get("system_usec", 0) / 1_000_000,
        "max_sampled_anon_bytes": maximum_assignment(processes, "memory.stat.anon"),
        "max_sampled_file_bytes": maximum_assignment(processes, "memory.stat.file"),
        "max_sampled_conron_rss_bytes": max_rss_bytes(processes),
        "parse_done": any("parse done:" in line for line in progress),
        "install_done": any("install done:" in line for line in progress),
        "check_done": any("check done:" in line for line in progress),
        "last_progress": progress[-1] if progress else None,
        "last_completed_check": checks[-1] if checks else None,
        "classification": classify_conron(workload, status, launched=checker_started),
    }
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--runs", type=Path, default=RUNS)
    parser.add_argument("--output", type=Path, default=EVIDENCE / "analysis/probe-summary.json")
    parser.add_argument("labels", nargs="*", default=LABELS)
    args = parser.parse_args()
    probes = [summarize(label, args.runs) for label in args.labels]
    output = {
        "probe_slots_used": len(probes),
        "probe_slot_limit": 4,
        "active_checker_wall_seconds": round(
            sum(item["active_checker_wall_seconds"] for item in probes), 3
        ),
        "active_checker_wall_limit_seconds": 600,
        "probes": probes,
    }
    destination = args.output
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
