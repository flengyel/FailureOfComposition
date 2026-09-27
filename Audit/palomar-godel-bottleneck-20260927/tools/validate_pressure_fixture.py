#!/usr/bin/env python3
"""Validate the synthetic early-pressure termination fixture."""

from __future__ import annotations

import json
import sys
from pathlib import Path


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: validate_pressure_fixture.py STATUS JSONL")
    status = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
    samples = [
        json.loads(line)
        for line in Path(sys.argv[2]).read_text(encoding="utf-8").splitlines()
        if line
    ]
    assert status["state"] == "finished", status
    assert status["placement_ok"] is True, status
    assert status["pressure_fired"] is True, status
    assert status["deadline_fired"] is False, status
    assert status["pressure_full_avg10_threshold"] == 80.0, status
    assert status["pressure_consecutive_seconds"] == 0.4, status
    assert status["pressure_peak_full_avg10"] == 80.0, status
    assert status["memory_events"].get("oom", 0) == 0, status
    assert status["memory_events"].get("oom_kill", 0) == 0, status
    assert len(samples) >= 3, samples
    assert all(sample["above_threshold"] for sample in samples), samples
    assert samples[-1]["consecutive_seconds"] >= 0.4, samples
    assert status["elapsed"] < 10.0, status
    print("PASS pressure fixture: threshold, duration, and owned-workload termination")


if __name__ == "__main__":
    main()
