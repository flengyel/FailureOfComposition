#!/usr/bin/env python3
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


def validate_common(value: dict[str, object]) -> None:
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


def main() -> None:
    if len(sys.argv) not in (2, 4):
        raise SystemExit("usage: validate_nine_config.py PORTABLE [PROTECTED LEAN_PREFIX]")
    portable = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
    validate_common(portable)
    if "external_kernels" in portable:
        raise SystemExit("portable config must not contain external_kernels")
    print("PASS portable cumulative Nine configuration")
    if len(sys.argv) == 4:
        protected = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
        prefix = Path(sys.argv[3]).resolve()
        validate_common(protected)
        expected = {
            "con-ron": [str(prefix / "bin/con-ron")],
            "nanoda": [str(prefix / "bin/nanoda_bin")],
        }
        if protected.get("external_kernels") != expected:
            raise SystemExit("protected config has wrong external kernels")
        removed = {key: value for key, value in protected.items() if key != "external_kernels"}
        if removed != portable:
            raise SystemExit("protected transformation changed more than external_kernels")
        print("PASS protected config differs only by authenticated kernel commands")


if __name__ == "__main__":
    main()
