#!/usr/bin/env python3
"""Regression tests for the kernel-verdict classifiers."""

from __future__ import annotations

import importlib.util
import json
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPT = HERE.parent / "tools/summarize_probes.py"
SPEC = importlib.util.spec_from_file_location("summarize_probes", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class KernelClassificationTests(unittest.TestCase):
    def test_conron_fixtures(self) -> None:
        for path in sorted((HERE / "fixtures").glob("conron-*.json")):
            with self.subTest(path=path.name):
                fixture = json.loads(path.read_text(encoding="utf-8"))
                actual = MODULE.classify_conron(
                    fixture["output"], fixture["status"], launched=fixture["launched"]
                )
                self.assertEqual(actual, fixture["expected"])

    def test_conron_verified_line_cannot_override_timeout(self) -> None:
        output = (
            "con-ron: check done: 1/1 t=0.1s\n"
            "con-ron: accepted 1 declarations (--verified)\n"
        )
        status = {"exit_status": 0, "deadline_fired": True, "pressure_fired": False}
        self.assertEqual(
            MODULE.classify_conron(output, status, launched=True), MODULE.TIMEOUT
        )

    def test_leanchecker_requires_explicit_verdict(self) -> None:
        status = {"exit_status": 0, "deadline_fired": False, "pressure_fired": False}
        self.assertEqual(
            MODULE.classify_leanchecker(
                "Lean default kernel accepts the solution\n", status, launched=True
            ),
            MODULE.ACCEPTED,
        )
        self.assertEqual(
            MODULE.classify_leanchecker("", status, launched=True), MODULE.INTERNAL_ERROR
        )

    def test_nanoda_requires_explicit_success_message(self) -> None:
        status = {"exit_status": 0, "deadline_fired": False, "pressure_fired": False}
        self.assertEqual(
            MODULE.classify_nanoda(
                "Checked 8077 declarations with no errors\n", status, launched=True
            ),
            MODULE.ACCEPTED,
        )
        self.assertEqual(
            MODULE.classify_nanoda("", status, launched=True), MODULE.INTERNAL_ERROR
        )


if __name__ == "__main__":
    unittest.main()
