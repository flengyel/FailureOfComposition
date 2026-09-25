#!/usr/bin/env python3
"""Re-elaborate maintained proofs and evaluator imports with warnings as errors."""

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
from prepare_packages import (
    bounded_lake_command,
    clean_environment,
    positive_setting,
    validated_packages,
)


# These declaration-local exceptions already occur in the accepted evaluator
# checkpoint d2100df. The 72 FailureOfComposition sources permit none. Extending
# the gate must not silently turn these into a file-wide or open-ended exception.
EXISTING_FLEXIBLE_EXCEPTIONS = {
    "CategoricalRiceShapiro/ArithmeticCode/Evaluation.lean": {"eval_codeLift_iff"},
    "CategoricalRiceShapiro/ArithmeticCode/FoundationCompat.lean": {
        "evalAux_unique", "eval_unique",
    },
}


def style_sources(project):
    library = project / "FailureOfComposition"
    maintained = [project / "FailureOfComposition.lean", *sorted(library.glob("*.lean"))]
    provenance = json.loads((library / "Porting/EVALUATOR_PROVENANCE.json").read_text())
    evaluator = []
    for entry in provenance["files"]:
        source = project / entry["path"]
        if (not source.resolve().is_relative_to(project.resolve())
                or source.suffix != ".lean" or not source.is_file()):
            raise SystemExit(f"Invalid evaluator style source: {entry['path']}")
        evaluator.append(source)
    sources = maintained + sorted(evaluator)
    if len(sources) != len(set(sources)):
        raise SystemExit("Duplicate source in strict style inventory")
    return sources


def suppression_inventory(relative, text):
    existing = []
    unexpected = []
    for match in re.finditer(
        r"^[ \t]*set_option\s+(?:weak\.)?linter\.\S+\s+(?:false|0)\b[^\n]*",
        text, re.M,
    ):
        declaration = re.match(r"\n(?:private )?theorem (\w+)\b", text[match.end():])
        name = declaration[1] if declaration else None
        if (match[0].strip() == "set_option linter.flexible false in"
                and name in EXISTING_FLEXIBLE_EXCEPTIONS.get(relative, set())
                and name not in existing):
            existing.append(name)
        else:
            unexpected.append(match[0])
    return existing, unexpected


def check_style(project, packages):
    workers = positive_setting("FAILCOMP_STYLE_JOBS")
    evidence = project.parent / ".codex-work/logs/port-verification"
    sources = style_sources(project)
    command = bounded_lake_command(
        project, "--packages=" + str(packages), "env", "lean", "--json",
        "-Dlinter.mathlibStandardSet=true", "-DwarningAsError=true",
    )
    report = {
        "status": "running",
        "started_at": datetime.now(timezone.utc).isoformat(),
        "scope": "72 FailureOfComposition sources and all 31 pinned evaluator sources",
        "excluded": {
            "Verification/*.lean": "Diagnostic audit commands, run separately by verify.sh",
            "External dependencies": "Pinned dependency packages",
            "CategoricalRiceShapiro.lean": "Re-export-only umbrella; its 31 imports are checked",
        },
        "command_template": [*command, "{source}"],
        "source_count": len(sources),
        "worker_processes": workers,
        "warnings_are_errors": True,
        "new_linter_suppressions_allowed": False,
        "existing_scoped_exceptions": {
            path: sorted(names) for path, names in EXISTING_FLEXIBLE_EXCEPTIONS.items()
        },
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
        existing, suppressions = suppression_inventory(relative, before.decode())
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
            "existing_scoped_exception_count": len(existing),
            "existing_scoped_exceptions": existing,
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
