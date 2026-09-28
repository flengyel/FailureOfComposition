#!/usr/bin/env python3
"""Classify this checkpoint's bounded replays with kernel-specific verdicts."""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
from pathlib import Path


REPOSITORY = Path(__file__).resolve().parents[3]
CLASSIFIERS = (
    REPOSITORY
    / "Audit/palomar-godel-bottleneck-20260927/tools/summarize_probes.py"
)


def load_classifiers():
    spec = importlib.util.spec_from_file_location("kernel_classifiers", CLASSIFIERS)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load classifiers from {CLASSIFIERS}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def maximum_assignment(text: str, key: str) -> int | None:
    values = [int(raw) for raw in re.findall(rf"(?m)^{re.escape(key)}=(\d+)$", text)]
    return max(values) if values else None


def maximum_process_rss(text: str, command: str) -> int | None:
    values = []
    for line in text.splitlines():
        fields = line.split(None, 8)
        if len(fields) == 9 and fields[7] == command and fields[4].isdigit():
            values.append(int(fields[4]) * 1024)
    return max(values) if values else None


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("runs", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    classifiers = load_classifiers()
    selections = (
        ("replay-01-lean-helper", "leanchecker", "leanchecker"),
        ("replay-02-nanoda-helper", "nanoda", "nanoda_bin"),
        ("replay-03-conron-alternative", "conron", "con-ron"),
    )
    results = []
    for label, kernel, process_command in selections:
        run = args.runs / label
        status = json.loads(
            (run / "cgroup-status.json").read_text(encoding="utf-8")
        )
        output = (run / "workload.log").read_text(encoding="utf-8")
        processes = (run / "processes.log").read_text(encoding="utf-8")
        launched = status.get("launch_error") is None and status.get("placement_ok") is True
        classify = getattr(classifiers, f"classify_{kernel}")
        results.append(
            {
                "label": label,
                "kernel": kernel,
                "classification": classify(output, status, launched=launched),
                "elapsed_seconds": status.get("elapsed"),
                "cpu_usage_seconds": (
                    status.get("cpu_stat", {}).get("usage_usec", 0) / 1_000_000
                ),
                "memory_peak_bytes": status.get("memory_peak"),
                "max_sampled_anon_bytes": maximum_assignment(
                    processes, "memory.stat.anon"
                ),
                "max_sampled_file_bytes": maximum_assignment(
                    processes, "memory.stat.file"
                ),
                "max_sampled_process_rss_bytes": maximum_process_rss(
                    processes, process_command
                ),
                "memory_events": status.get("memory_events"),
                "deadline_fired": status.get("deadline_fired"),
                "pressure_fired": status.get("pressure_fired"),
                "pressure_peak_full_avg10": status.get("pressure_peak_full_avg10"),
                "exit_status": status.get("exit_status"),
            }
        )
    summary = {
        "attempts_used": len(results),
        "attempt_limit": 5,
        "active_checker_wall_seconds": sum(
            result["elapsed_seconds"] for result in results
        ),
        "active_checker_wall_limit_seconds": 600,
        "results": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
