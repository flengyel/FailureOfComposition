#!/usr/bin/env python3
"""Focused regressions for the Palomar verification launcher."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest


REPOSITORY = Path(__file__).resolve().parents[2]
HELPER_PATH = REPOSITORY / "scripts" / "palomar_launcher_checks.py"
LAUNCHER = REPOSITORY / "scripts" / "verify-palomar.sh"
SPEC = importlib.util.spec_from_file_location("palomar_launcher_checks", HELPER_PATH)
assert SPEC is not None and SPEC.loader is not None
CHECKS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKS)


class CapacityTests(unittest.TestCase):
    def requirements(self):
        return {
            "memory_max": 11 * CHECKS.GIB,
            "swap_max": 20 * CHECKS.GIB,
            "memory_headroom": 4 * CHECKS.GIB,
            "memory_available_reserve": CHECKS.GIB,
            "swap_headroom": 2 * CHECKS.GIB,
            "disk_min": 20 * CHECKS.GIB,
        }

    def snapshot(self):
        return {
            "mem_total": 32 * CHECKS.GIB,
            "mem_available": 30 * CHECKS.GIB,
            "swap_total": 24 * CHECKS.GIB,
            "swap_free": 24 * CHECKS.GIB,
            "disk_available": 100 * CHECKS.GIB,
            "ancestor_memory_remaining": None,
            "ancestor_swap_remaining": None,
            "active_workloads": [],
        }

    def test_free_swap_not_total_swap_controls_admission(self):
        snapshot = self.snapshot()
        snapshot["swap_free"] = CHECKS.GIB
        errors = CHECKS.evaluate_capacity(snapshot, self.requirements())
        self.assertTrue(any("SwapFree" in error for error in errors))

    def test_clean_capacity_snapshot_passes(self):
        self.assertEqual(
            CHECKS.evaluate_capacity(self.snapshot(), self.requirements()), []
        )

    def test_ancestor_limit_and_existing_workload_fail(self):
        snapshot = self.snapshot()
        snapshot["ancestor_memory_remaining"] = 11 * CHECKS.GIB
        snapshot["active_workloads"] = ["123 1 con-ron con-ron --verified"]
        errors = CHECKS.evaluate_capacity(snapshot, self.requirements())
        self.assertTrue(any("ancestor cgroup" in error for error in errors))
        self.assertTrue(any("overlapping" in error for error in errors))


class SupervisorEvidenceTests(unittest.TestCase):
    expected = {
        "memory_high": str(10 * CHECKS.GIB),
        "memory_max": str(11 * CHECKS.GIB),
        "memory_swap_max": str(20 * CHECKS.GIB),
        "cpu_list": "0",
        "output_name": "comparator.log",
    }

    markers = {
        "con_ron_accepts": "con-ron kernel accepts the solution",
        "nanoda_accepts": "nanoda kernel accepts the solution",
        "lean_accepts": "Lean default kernel accepts the solution",
        "comparator_accepts": "Your solution is okay!",
    }

    def clean_status(self):
        return {
            "state": "finished",
            "cgroup": "/sys/fs/cgroup/user.slice/example/palomar-test",
            "supervisor_pid": 100,
            "exit_status": 0,
            "term_signal": None,
            "deadline_fired": False,
            "liveness_lost": False,
            "elapsed": 2.5,
            "placement_ok": True,
            "placement_error": None,
            "launch_error": None,
            "sandbox_started": None,
            "cpu_delegated": True,
            "limits_applied": {key: True for key in CHECKS.REQUIRED_LIMITS},
            "rlimits_applied": {},
            "memory_events": {
                "low": 0,
                "high": 17,
                "max": 3,
                "oom": 0,
                "oom_kill": 0,
                "oom_group_kill": 0,
            },
            "memory_peak": 1024,
            "pids_events": {"max": 0},
            "cpu_stat": {},
            "populated_after_kill": False,
        }

    def write_run(self, root: Path, status=None, systemd="0\n"):
        if status is not None:
            (root / "cgroup-status.json").write_text(
                json.dumps(status), encoding="utf-8"
            )
        (root / "systemd-run.exit").write_text(systemd, encoding="ascii")
        (root / "containment.env").write_text(
            "classification=aggregate_process_tree_containment\n"
            "cgroup_limits=/sys/fs/cgroup/user.slice/example/palomar-test\n"
            "cgroup_leaf=/sys/fs/cgroup/user.slice/example/palomar-test/leaf\n"
            f"memory_high={self.expected['memory_high']}\n"
            f"memory_max={self.expected['memory_max']}\n"
            f"memory_swap_max={self.expected['memory_swap_max']}\n"
            "memory_oom_group=1\n"
            "cpu_request=0\n"
            "nproc=1\n"
            "cpus_allowed_list=0\n",
            encoding="utf-8",
        )
        (root / "comparator.log").write_text(
            "\n".join(self.markers.values()) + "\n", encoding="utf-8"
        )

    def assess(self, status=None, systemd="0\n"):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.write_run(root, self.clean_status() if status is None else status, systemd)
            return CHECKS.assess_supervised_run(root, self.expected, self.markers)

    def test_clean_record_passes_and_memory_pressure_is_not_oom(self):
        result = self.assess()
        self.assertTrue(result["passed"])
        self.assertEqual(result["events"]["high"], 17)
        self.assertEqual(result["events"]["max"], 3)

    def test_success_strings_cannot_hide_false_placement(self):
        status = self.clean_status()
        status["placement_ok"] = False
        status["placement_error"] = "not placed"
        result = self.assess(status)
        self.assertTrue(result["computational_success"])
        self.assertFalse(result["infrastructure_clean"])
        self.assertFalse(result["passed"])

    def test_success_strings_cannot_hide_infrastructure_failures(self):
        mutations = {
            "unapplied_limit": lambda value: value["limits_applied"].__setitem__(
                "memory.max", False
            ),
            "deadline": lambda value: value.__setitem__("deadline_fired", True),
            "liveness": lambda value: value.__setitem__("liveness_lost", True),
            "survivor": lambda value: value.__setitem__("populated_after_kill", True),
        }
        for name, mutate in mutations.items():
            with self.subTest(name=name):
                status = self.clean_status()
                mutate(status)
                self.assertFalse(self.assess(status)["passed"])

    def test_failed_systemd_completion_fails(self):
        result = self.assess(systemd="1\n")
        self.assertFalse(result["infrastructure_clean"])
        self.assertIn("systemd-run exit status", " ".join(result["errors"]))

    def test_missing_and_malformed_status_write_failure_record(self):
        for payload in (None, "{not-json"):
            with self.subTest(payload=payload):
                with tempfile.TemporaryDirectory() as temporary:
                    run = Path(temporary)
                    if payload is not None:
                        (run / "cgroup-status.json").write_text(
                            payload, encoding="utf-8"
                        )
                    arguments = [
                        "finalize",
                        "--kind",
                        "comparator",
                        "--run",
                        str(run),
                        "--destination",
                        "status.env",
                        "--verification-kind",
                        "local_comparator",
                        "--memory-high",
                        self.expected["memory_high"],
                        "--memory-max",
                        self.expected["memory_max"],
                        "--memory-swap-max",
                        self.expected["memory_swap_max"],
                        "--cpu-list",
                        "0",
                        "--output-name",
                        "comparator.log",
                    ]
                    self.assertEqual(CHECKS.main(arguments), 1)
                    record = (run / "status.env").read_text(encoding="utf-8")
                    self.assertIn("result=fail", record)
                    self.assertIn("infrastructure_clean=false", record)


class PrecheckBindingTests(unittest.TestCase):
    def test_changed_input_fixture_changes_manifest(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            source = root / "Challenge.lean"
            source.write_text("def witness := 1\n", encoding="utf-8")
            first = {"files": CHECKS.content_entries(root, [source])}
            source.write_text("def witness := 2\n", encoding="utf-8")
            second = {"files": CHECKS.content_entries(root, [source])}
            expected = root / "expected.json"
            actual = root / "actual.json"
            expected.write_text(json.dumps(first), encoding="utf-8")
            actual.write_text(json.dumps(second), encoding="utf-8")
            equal, differences = CHECKS.compare_manifests(expected, actual)
            self.assertFalse(equal)
            self.assertEqual(differences, ["files"])

    def test_changed_configuration_fixture_changes_manifest(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            configuration = root / "comparator.json"
            configuration.write_text('{"theorem_names":["first"]}\n', encoding="utf-8")
            first = {"files": CHECKS.content_entries(root, [configuration])}
            configuration.write_text('{"theorem_names":["second"]}\n', encoding="utf-8")
            second = {"files": CHECKS.content_entries(root, [configuration])}
            expected = root / "expected.json"
            actual = root / "actual.json"
            expected.write_text(json.dumps(first), encoding="utf-8")
            actual.write_text(json.dumps(second), encoding="utf-8")
            equal, differences = CHECKS.compare_manifests(expected, actual)
            self.assertFalse(equal)
            self.assertEqual(differences, ["files"])

    def test_absent_historical_manifest_is_stale(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            actual = root / "actual.json"
            actual.write_text("{}\n", encoding="utf-8")
            result = CHECKS.main(
                [
                    "compare-manifests",
                    "--expected",
                    str(root / "missing.json"),
                    "--actual",
                    str(actual),
                    "--report",
                    str(root / "report.json"),
                ]
            )
            self.assertEqual(result, 1)
            report = json.loads((root / "report.json").read_text(encoding="utf-8"))
            self.assertEqual(report["result"], "stale")

    def test_fake_preparatory_command_is_routed_through_supervision(self):
        with tempfile.TemporaryDirectory() as temporary:
            trace = Path(temporary) / "trace.txt"
            evidence = Path(temporary) / "evidence"
            shell = f"""
source {LAUNCHER!s}
run_supervised() {{
  local observed_run=$1 observed_output=$2 observed_unit_log=$3
  local observed_high=$4 observed_max=$5 observed_swap=$6 observed_deadline=$7
  local observed_cwd=$8
  shift 8
  printf '%s|%s|%s|%s|%s|%s|%s\\n' \\
    "$observed_run" "$observed_high" "$observed_max" "$observed_swap" \\
    "$observed_deadline" "$observed_cwd" "$1" > {trace!s}
  "$@"
}}
run_precheck_phase {evidence!s} /usr/bin/true
"""
            subprocess.run(["bash", "-c", shell], cwd=REPOSITORY, check=True)
            fields = trace.read_text(encoding="utf-8").strip().split("|")
            self.assertEqual(fields[0], str(evidence))
            self.assertEqual(fields[1:4], ["12G", "12800M", "12G"])
            self.assertEqual(fields[4], "14400")
            self.assertEqual(fields[5], str(REPOSITORY))
            self.assertEqual(fields[6], "/usr/bin/true")


class SyntaxTests(unittest.TestCase):
    def test_launcher_syntax(self):
        subprocess.run(["bash", "-n", str(LAUNCHER)], cwd=REPOSITORY, check=True)


if __name__ == "__main__":
    unittest.main()
