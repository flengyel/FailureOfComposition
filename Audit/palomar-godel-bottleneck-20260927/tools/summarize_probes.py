#!/usr/bin/env python3
"""Summarize the bounded con-ron diagnostic probes and telemetry."""

from __future__ import annotations

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


def summarize(label: str) -> dict:
    run = RUNS / label
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
        "classification": (
            "sandbox-launch-failed-before-checker"
            if not checker_started
            else "accepted"
            if any("con-ron: done:" in line for line in progress)
            else "deadline-inconclusive"
            if status.get("deadline_fired")
            else "pressure-aborted-inconclusive"
            if status.get("pressure_fired")
            else "other-inconclusive"
        ),
    }
    return result


def main() -> None:
    probes = [summarize(label) for label in LABELS]
    output = {
        "probe_slots_used": len(probes),
        "probe_slot_limit": 4,
        "active_checker_wall_seconds": round(
            sum(item["active_checker_wall_seconds"] for item in probes), 3
        ),
        "active_checker_wall_limit_seconds": 600,
        "probes": probes,
    }
    destination = EVIDENCE / "analysis/probe-summary.json"
    destination.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
