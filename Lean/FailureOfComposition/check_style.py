#!/usr/bin/env python3
"""Re-elaborate the maintained library with Mathlib's standard linters as errors."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

sys.dont_write_bytecode = True
from prepare_packages import clean_environment, positive_setting, validated_packages


def check_style(project, packages):
    workers = positive_setting("FAILCOMP_STYLE_JOBS")
    library = project / "FailureOfComposition"
    evidence = project.parent / "Audit/failure-composition-v36/evidence"
    sources = [project / "FailureOfComposition.lean", *sorted(library.glob("*.lean"))]
    command = [
        "lake", "--packages=" + str(packages), "env", "lean", "--json",
        "-Dlinter.mathlibStandardSet=true", "-DwarningAsError=true",
    ]
    report = {
        "status": "running",
        "started_at": datetime.now(timezone.utc).isoformat(),
        "scope": "All maintained FailureOfComposition mathematical sources and their umbrella",
        "excluded": {
            "Verification/*.lean": "Diagnostic audit commands, run separately by verify.sh",
            "CategoricalRiceShapiro and external dependencies": "Pinned imported sources",
        },
        "command_template": [*command, "{source}"],
        "source_count": len(sources),
        "worker_processes": workers,
        "warnings_are_errors": True,
        "linter_suppressions_allowed": False,
        "results": [],
    }
    evidence.mkdir(parents=True, exist_ok=True)
    report_path = evidence / "style-lint.json"

    def save_report():
        temporary = report_path.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(report, indent=2) + "\n")
        temporary.replace(report_path)

    def check(source):
        relative = str(source.relative_to(project))
        before = source.read_bytes()
        # Suppression would turn a clean result into a misleading gate.
        suppressions = re.findall(
            r"^\s*set_option\s+(?:weak\.)?linter\.\S+\s+(?:false|0)\b",
            before.decode(), re.M,
        )
        result = subprocess.run(
            [*command, relative], cwd=project, env=clean_environment(),
            capture_output=True, text=True, check=False,
        )
        messages = []
        unparsed = []
        for line in result.stdout.splitlines():
            if not line.strip():
                continue
            try:
                messages.append(json.loads(line))
            except json.JSONDecodeError:
                unparsed.append(line)
        diagnostics = [
            message for message in messages
            if message.get("severity") in {"error", "warning"}
            or ("linter." in message.get("data", "")
                and re.search(r"\berror:", message.get("data", "")))
        ]
        unchanged = source.read_bytes() == before
        passed = (result.returncode == 0 and not diagnostics and not suppressions
                  and not unparsed and not result.stderr.strip() and unchanged)
        record = {
            "source": relative,
            "sha256": hashlib.sha256(before).hexdigest(),
            "returncode": result.returncode,
            "status": "passed" if passed else "failed",
            "warning_or_error_count": len(diagnostics),
            "linter_suppression_count": len(suppressions),
            "source_unchanged_during_check": unchanged,
        }
        if not passed:
            record.update(diagnostics=diagnostics, unparsed_stdout=unparsed,
                          stderr=result.stderr, suppressions=suppressions)
        return record

    started = time.monotonic()
    save_report()
    # Independent read-only elaborations use the already-built import artifacts.
    with ThreadPoolExecutor(max_workers=workers) as pool:
        for record in pool.map(check, sources):
            report["results"].append(record)
            print(f"STYLE {record['status'].upper()} {record['source']}", flush=True)
            if record["status"] != "passed":
                print(json.dumps(record, ensure_ascii=False), flush=True)
            save_report()
    passed = all(record["status"] == "passed" for record in report["results"])
    report.update(
        status="passed" if passed else "failed",
        returncode=0 if passed else 1,
        finished_at=datetime.now(timezone.utc).isoformat(),
        duration_seconds=round(time.monotonic() - started, 3),
        warning_or_error_count=sum(r["warning_or_error_count"] for r in report["results"]),
    )
    save_report()
    if not passed:
        raise SystemExit(1)
    print(f"PASS strict style gate for {len(sources)} maintained library sources", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packages", type=Path, help="existing package mapping to validate")
    args = parser.parse_args()
    project = Path(__file__).resolve().parent.parent
    with validated_packages(project, args.packages) as packages:
        check_style(project, packages)


if __name__ == "__main__":
    main()
