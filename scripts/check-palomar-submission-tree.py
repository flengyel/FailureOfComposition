#!/usr/bin/env python3
"""Check the deliberately scoped, module-based Palomar Nine submission tree."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re


REPOSITORY = Path(__file__).resolve().parent.parent
INVENTORY = (
    REPOSITORY / "Lean/FailureOfComposition/Palomar/SUBMISSION_SOURCE_INVENTORY.json"
)
CHALLENGE = REPOSITORY / "Lean/FailureOfComposition/Palomar/ChallengeNine.lean"
CONFIGURATION = REPOSITORY / "Lean/FailureOfComposition/Palomar/comparator-nine.json"
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
COMMENT_MARKER = re.compile(r"/-|-/")
ID_LETTER_LIKE = (
    r"\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
    r"\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
    r"\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f"
)
ID_FIRST = rf"A-Za-z_{ID_LETTER_LIKE}"
ID_REST = rf"{ID_FIRST}0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
IDENTIFIER_CONTINUATION = re.compile(rf"[{ID_REST}]|\.[{ID_FIRST}«]")


def lean_sources() -> list[Path]:
    result: list[Path] = []
    for directory, subdirectories, names in os.walk(REPOSITORY, followlinks=False):
        subdirectories[:] = sorted(
            name for name in subdirectories
            if name not in {".git", ".lake"}
            and not (Path(directory) / name).is_symlink()
        )
        for name in sorted(names):
            path = Path(directory) / name
            if name.endswith(".lean") and path.is_file() and not path.is_symlink():
                result.append(path)
    return result


def has_module_header(text: str) -> bool:
    index = 0
    while index < len(text):
        if text[index] in " \r\n":
            index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index + 2)
            index = len(text) if end < 0 else end + 1
        elif text.startswith("/-", index) and not text.startswith(("/--", "/-!"), index):
            index += 3
            depth = 1
            while depth:
                marker = COMMENT_MARKER.search(text, index)
                if marker is None:
                    break
                depth += 1 if marker.group() == "/-" else -1
                index = marker.end()
            if depth:
                return False
        else:
            return text.startswith("module", index) and (
                IDENTIFIER_CONTINUATION.match(text, index + 6) is None
            )
    return False


def main() -> None:
    inventory = json.loads(INVENTORY.read_text(encoding="utf-8"))
    expected = {entry["path"]: entry for entry in inventory["lean_sources"]}
    actual_paths = {
        path.relative_to(REPOSITORY).as_posix(): path for path in lean_sources()
    }
    if set(actual_paths) != set(expected):
        raise SystemExit(
            "Lean source inventory differs: "
            f"missing={sorted(set(expected) - set(actual_paths))} "
            f"extra={sorted(set(actual_paths) - set(expected))}"
        )
    audit = REPOSITORY / "Audit"
    if audit.exists() and any(path.is_file() or path.is_symlink() for path in audit.rglob("*")):
        raise SystemExit("focused submission must not contain Audit files")

    for relative, path in sorted(actual_paths.items()):
        data = path.read_bytes()
        text = data.decode("utf-8")
        if path.is_symlink():
            raise SystemExit(f"Lean source is a symlink: {relative}")
        if not has_module_header(text):
            raise SystemExit(f"Lean source lacks a module header: {relative}")
        if len(text.splitlines()) > 10_000:
            raise SystemExit(f"Lean source exceeds 10,000 lines: {relative}")
        if hashlib.sha256(data).hexdigest() != expected[relative]["sha256"]:
            raise SystemExit(f"Lean source hash differs from inventory: {relative}")
        if re.search(r"^(?:public\s+)?import(?:\s+all)?\s+Audit(?:\.|\s|$)", text, re.M):
            raise SystemExit(f"maintained source imports Audit: {relative}")

    challenge_bytes = CHALLENGE.stat().st_size
    challenge_lines = len(CHALLENGE.read_bytes().splitlines())
    if challenge_bytes > 102_400 or challenge_lines > 1_000:
        raise SystemExit(
            f"ChallengeNine exceeds policy: {challenge_bytes} bytes, {challenge_lines} lines"
        )
    config = json.loads(CONFIGURATION.read_text(encoding="utf-8"))
    if config.get("theorem_names") != EXPECTED_THEOREMS:
        raise SystemExit("Comparator theorem selection differs")
    if config.get("definition_names", []) != []:
        raise SystemExit("Comparator configuration selects definitions")
    if set(config.get("permitted_axioms", [])) != {
        "propext", "Quot.sound", "Classical.choice",
    }:
        raise SystemExit("Comparator axiom policy differs")
    if "external_kernels" in config:
        raise SystemExit("portable configuration contains machine-local kernels")
    print(
        f"PASS focused submission layout: {len(actual_paths)} Lean modules; "
        f"ChallengeNine {challenge_bytes} bytes/{challenge_lines} lines"
    )


if __name__ == "__main__":
    main()
