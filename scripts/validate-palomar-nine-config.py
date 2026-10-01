#!/usr/bin/env python3
"""Validate the portable cumulative-Nine Comparator selection."""

from __future__ import annotations

import json
import sys
from pathlib import Path

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
EXPECTED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def main() -> int:
    if len(sys.argv) != 2:
        raise SystemExit("usage: validate-palomar-nine-config.py CONFIG")
    value = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
    if value.get("challenge_module") != "FailureOfComposition.Palomar.ChallengeNine":
        raise SystemExit("wrong Challenge module")
    if value.get("solution_module") != "FailureOfComposition.Palomar.SolutionNine":
        raise SystemExit("wrong Solution module")
    if value.get("theorem_names") != EXPECTED_THEOREMS:
        raise SystemExit("nine-result theorem selection or order is wrong")
    if value.get("definition_names") != []:
        raise SystemExit("definition_names must be empty")
    if set(value.get("permitted_axioms", [])) != EXPECTED_AXIOMS:
        raise SystemExit("permitted-axiom set is wrong")
    if "external_kernels" in value:
        raise SystemExit("portable config must not contain external_kernels")
    print("PASS portable cumulative-Nine configuration")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
