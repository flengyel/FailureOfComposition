#!/usr/bin/env python3
"""Validate the decisive fields in the retained official mechanical report."""

from __future__ import annotations

import json
from pathlib import Path
import sys


EXPECTED_THEOREMS = [
    "FailureOfComposition.Palomar.obstruction_four_properties",
    "FailureOfComposition.Palomar.no_quotient_composition_productive",
    "FailureOfComposition.Palomar.no_quotient_composition_godel",
    "FailureOfComposition.Palomar.pi_one_characterization",
    "FailureOfComposition.Palomar.generated_congruence_classification",
    "FailureOfComposition.Palomar.weak_totality_counterexample",
    "FailureOfComposition.Palomar.range_counterexample_godel",
    "FailureOfComposition.Palomar.range_counterexample_productive",
    "FailureOfComposition.Palomar.generated_quotient_partial_recursive",
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)
    print(f"PASS {message}")


def main() -> int:
    if len(sys.argv) != 2:
        print(f"usage: {Path(sys.argv[0]).name} MECHANICAL_REPORT", file=sys.stderr)
        return 2
    report = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
    require(report["status"] == "pass", "status is pass")
    require(report["stage"] == "complete", "stage is complete")
    require(report["phase"] == "verification", "phase is verification")
    require(not report["errors"], "error list is empty")
    require(
        report["source"]["commit"]
        == "48e6eeccc420e8068f1bc6d810ddbe10cfdf39eb",
        "immutable source SHA matches",
    )
    requested = report["submission"]["requested_paths"]
    require(requested["project_path"] == "Lean", "project path matches")
    require(
        requested["comparator_config_path"]
        == "Lean/FailureOfComposition/Palomar/comparator-nine.json",
        "Comparator path matches",
    )
    require(
        requested["formalization_metadata_path"]
        == "Lean/FailureOfComposition/Palomar/formalization.yaml",
        "metadata path matches",
    )
    comparator = report["comparator"]
    require(
        comparator["challenge_module"]
        == "FailureOfComposition.Palomar.ChallengeNine",
        "submitted Challenge module matches",
    )
    require(
        comparator["solution_module"]
        == "FailureOfComposition.Palomar.SolutionNine",
        "Solution module matches",
    )
    require(comparator["theorem_names"] == EXPECTED_THEOREMS, "ordered Nine roots match")
    require(comparator["definition_names"] == [], "definition selection is empty")
    require(
        comparator["permitted_axioms"]
        == ["propext", "Quot.sound", "Classical.choice"],
        "permitted axioms match",
    )
    protected = json.loads(report["protected_config"])
    require(
        protected["challenge_module"].startswith("PalomarCanonical")
        and protected["challenge_module"].endswith(".Challenge"),
        "protected Challenge was canonically renamed",
    )
    require(protected["theorem_names"] == EXPECTED_THEOREMS, "protected roots match")
    require(
        report["verification_profile"]["id"] == "palomar-standard-v1",
        "execution profile matches",
    )
    require(
        report["toolchain_commit"]
        == "11acb17ec6b07a8f9e9173e6845197929540936b",
        "Lean toolchain commit matches",
    )
    require(report["license"]["detected_identifier"] == "Apache-2.0", "root license passed")
    log = report["comparator_log_tail"]
    require("con-ron kernel accepts the solution" in log, "con-ron accepted")
    require("nanoda kernel accepts the solution" in log, "NanoDa accepted")
    require("Lean default kernel accepts the solution" in log, "Lean accepted")
    require("Your solution is okay!" in log, "Comparator final acceptance is present")
    resources = report["resource_usage"]
    require(not any(row.get("deadline_fired", False) for row in resources), "no phase deadline fired")
    require(
        not any((row.get("memory_events") or {}).get("oom", 0) for row in resources),
        "no OOM event",
    )
    require(
        not any((row.get("memory_events") or {}).get("oom_kill", 0) for row in resources),
        "no OOM kill",
    )
    print("validated complete local mechanical pass")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, KeyError, ValueError) as exc:
        print(f"FAIL {exc}", file=sys.stderr)
        raise SystemExit(1)
