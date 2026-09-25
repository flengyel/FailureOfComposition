"""Regression checks for evaluator coverage and the warning-as-error gate.

Run with python3; no Lean installation is needed for these gate tests.
"""

from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

LIBRARY = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LIBRARY))
import check_style


class StyleGateTests(unittest.TestCase):
    def test_inventory_includes_every_pinned_evaluator(self):
        project = LIBRARY.parent
        sources = {str(p.relative_to(project)) for p in check_style.style_sources(project)}
        pins = json.loads((LIBRARY / "Porting/EVALUATOR_PROVENANCE.json").read_text())
        self.assertEqual(len(sources), 103)
        self.assertTrue({p["path"] for p in pins["files"]}.issubset(sources))

    def test_only_existing_declaration_scoped_exceptions_are_allowed(self):
        relative = "CategoricalRiceShapiro/ArithmeticCode/FoundationCompat.lean"
        existing = "set_option linter.flexible false in\ntheorem eval_unique : True := by trivial\n"
        self.assertEqual(check_style.suppression_inventory(relative, existing), (["eval_unique"], []))
        for source, content in (
            ("FailureOfComposition/Example.lean", existing),
            (relative, existing.replace("eval_unique", "new_theorem")),
            (relative, existing.replace("false in", "false")),
            (relative, existing.replace("linter.flexible", "linter.style.haveILetI")),
        ):
            with self.subTest(source=source, content=content):
                self.assertTrue(check_style.suppression_inventory(source, content)[1])

    def test_evaluator_warning_rejects_even_zero_exit_code(self):
        with tempfile.TemporaryDirectory() as temporary:
            project = Path(temporary) / "Lean"
            source = project / "CategoricalRiceShapiro/Evaluator/Example.lean"
            source.parent.mkdir(parents=True)
            source.write_text("example : True := by trivial\n")
            warning = json.dumps({"severity": "warning", "data": "proof-instance style warning"})
            result = subprocess.CompletedProcess([], 0, warning + "\n", "")
            with (patch.object(check_style, "style_sources", return_value=[source]),
                  patch.object(check_style, "bounded_lake_command", return_value=["unused"]),
                  patch.object(check_style.subprocess, "run", return_value=result),
                  redirect_stdout(io.StringIO())):
                with self.assertRaises(SystemExit) as failure:
                    check_style.check_style(project, project / "packages.json")
            self.assertEqual(failure.exception.code, 1)
            report = json.loads((project.parent / ".codex-work/logs/port-verification/style-lint.json").read_text())
            self.assertEqual(report["status"], "failed")
            self.assertEqual(report["warning_or_error_count"], 1)


if __name__ == "__main__":
    unittest.main()
