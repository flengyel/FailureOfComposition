#!/usr/bin/env python3
"""Summarize the one bounded cumulative three-result Comparator attempt."""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

EXPECTED_THEOREMS = [
    "FailureOfComposition.Palomar.obstruction_four_properties",
    "FailureOfComposition.Palomar.no_quotient_composition_productive",
    "FailureOfComposition.Palomar.no_quotient_composition_godel",
]


def sha256(path: Path) -> str | None:
    if not path.is_file():
        return None
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def time_fields(text: str) -> dict[str, object]:
    fields: dict[str, object] = {}
    patterns = {
        "user_seconds": r"User time \(seconds\):\s*([0-9.]+)",
        "system_seconds": r"System time \(seconds\):\s*([0-9.]+)",
        "gnu_time_max_rss_kib": r"Maximum resident set size \(kbytes\):\s*(\d+)",
        "gnu_time_exit_status": r"Exit status:\s*(\d+)",
        "wall_clock_text": r"Elapsed \(wall clock\) time[^\n]*\):\s*([^\n]+)",
    }
    for key, pattern in patterns.items():
        match = re.search(pattern, text)
        if not match:
            continue
        value: object = match.group(1).strip()
        if key in {"user_seconds", "system_seconds"}:
            value = float(value)
        elif key in {"gnu_time_max_rss_kib", "gnu_time_exit_status"}:
            value = int(value)
        fields[key] = value
    return fields


def pressure_samples(text: str) -> dict[str, object]:
    samples: list[dict[str, object]] = []
    for match in re.finditer(
        r"memory\.pressure=some avg10=([0-9.]+) avg60=([0-9.]+) "
        r"avg300=([0-9.]+) total=(\d+)\n"
        r"full avg10=([0-9.]+) avg60=([0-9.]+) avg300=([0-9.]+) total=(\d+)",
        text,
    ):
        samples.append(
            {
                "some": {
                    "avg10": float(match.group(1)),
                    "avg60": float(match.group(2)),
                    "avg300": float(match.group(3)),
                    "total_usec": int(match.group(4)),
                },
                "full": {
                    "avg10": float(match.group(5)),
                    "avg60": float(match.group(6)),
                    "avg300": float(match.group(7)),
                    "total_usec": int(match.group(8)),
                },
            }
        )
    return {
        "sample_count": len(samples),
        "first": samples[0] if samples else None,
        "last": samples[-1] if samples else None,
    }


def main() -> None:
    run = Path(sys.argv[1]).resolve()
    status = json.loads((run / "cgroup-status.json").read_text(encoding="utf-8"))
    comparator = (run / "comparator.log").read_text(
        encoding="utf-8", errors="replace"
    )
    time_text = (
        (run / "time.log").read_text(encoding="utf-8", errors="replace")
        if (run / "time.log").is_file()
        else ""
    )
    processes = (run / "processes.log").read_text(
        encoding="utf-8", errors="replace"
    )
    systemd_exit = int((run / "systemd-run.exit").read_text(encoding="ascii").strip())
    protected = json.loads(
        (run / "protected-comparator-three.json").read_text(encoding="utf-8")
    )
    identity = json.loads((run / "identity.json").read_text(encoding="utf-8"))

    def authenticated_export(kind: str) -> bool:
        record = identity.get("exports", {}).get(kind, {})
        path_text = record.get("path")
        if not isinstance(path_text, str):
            return False
        path = Path(path_text)
        return (
            path.is_file()
            and path.stat().st_size == record.get("bytes")
            and sha256(path) == record.get("sha256")
        )

    stages = {
        "challenge_input_authenticated": authenticated_export("challenge"),
        "solution_input_authenticated": authenticated_export("solution"),
        "con_ron_started": "Running con-ron kernel on solution" in comparator,
        "con_ron_accepted": "con-ron kernel accepts the solution" in comparator,
        "nanoda_started": "Running nanoda kernel on solution" in comparator,
        "nanoda_accepted": "nanoda kernel accepts the solution" in comparator,
        "lean_kernel_started": "Running Lean default kernel on solution" in comparator,
        "lean_kernel_accepted": (
            "Lean default kernel accepts the solution" in comparator
        ),
        "comparator_accepted": "Your solution is okay!" in comparator,
    }
    required_stages = [
        "challenge_input_authenticated",
        "solution_input_authenticated",
        "con_ron_started",
        "con_ron_accepted",
        "nanoda_started",
        "nanoda_accepted",
        "lean_kernel_started",
        "lean_kernel_accepted",
        "comparator_accepted",
    ]
    exact_selection = (
        protected.get("challenge_module")
        == "FailureOfComposition.Palomar.ChallengeThree"
        and protected.get("solution_module")
        == "FailureOfComposition.Palomar.SolutionThree"
        and protected.get("theorem_names") == EXPECTED_THEOREMS
        and protected.get("definition_names") == []
    )
    contradictory_stop = (
        status.get("deadline_fired")
        or status.get("pressure_fired")
        or status.get("host_reserve_fired")
        or status.get("host_monitor_failed")
        or status.get("memory_events", {}).get("oom_kill", 0)
        or status.get("memory_events", {}).get("oom_group_kill", 0)
    )
    if (
        exact_selection
        and all(stages[key] for key in required_stages)
        and status.get("exit_status") == 0
        and systemd_exit == 0
        and not contradictory_stop
    ):
        result = "pass"
    elif status.get("deadline_fired"):
        result = "timeout_inconclusive"
    elif status.get("pressure_fired"):
        result = "pressure_stop_inconclusive"
    elif status.get("host_reserve_fired"):
        result = "host_reserve_stop_inconclusive"
    elif status.get("host_monitor_failed"):
        result = "host_monitor_failure"
    elif status.get("memory_events", {}).get("oom_kill", 0) or status.get(
        "memory_events", {}
    ).get("oom_group_kill", 0):
        result = "oom_inconclusive"
    else:
        result = "nonzero_or_interrupted"
    accepted_match = re.search(r"con-ron: accepted (\d+) declarations", comparator)
    record = {
        "attempt_scope": "local cumulative three-result Comparator only",
        "attempt_ordinal_for_checkpoint": 1,
        "cumulative_three_attempt_ordinal_overall": 3,
        "official_palomar_verification": False,
        "other_six_declarations_verified": False,
        "exact_selection": exact_selection,
        "selected_modules": {
            "challenge": protected.get("challenge_module"),
            "solution": protected.get("solution_module"),
        },
        "selected_theorems": protected.get("theorem_names"),
        "result": result,
        "systemd_exit_status": systemd_exit,
        "supervisor": status,
        "kernel_stages": stages,
        "con_ron_accepted_declarations": (
            int(accepted_match.group(1)) if accepted_match else None
        ),
        "time": time_fields(time_text),
        "memory_pressure": pressure_samples(processes),
        "artifacts": {
            name: {"bytes": path.stat().st_size, "sha256": sha256(path)}
            for name, path in {
                "comparator.log": run / "comparator.log",
                "time.log": run / "time.log",
                "processes.log": run / "processes.log",
                "capacity.json": run / "capacity.json",
                "portable-comparator-three.json": run
                / "portable-comparator-three.json",
                "protected-comparator-three.json": run
                / "protected-comparator-three.json",
                "identity.json": run / "identity.json",
            }.items()
            if path.is_file()
        },
    }
    (run / "result.json").write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(record, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
