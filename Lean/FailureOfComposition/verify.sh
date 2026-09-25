#!/usr/bin/env bash
# Run the repository's native Lean library build, audits, and kernel replay.
set -euo pipefail
check_environment=false
if (( $# == 1 )) && [[ $1 == --check-environment ]]; then
  check_environment=true
elif (( $# != 0 )); then
  echo "Usage: $0 [--check-environment] (uses the repository's Lean project)" >&2
  exit 2
fi
for tool in python3 git lean lake; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "Required tool not found: $tool" >&2
    exit 1
  }
done
python3 -c 'import sys; raise SystemExit(0 if sys.version_info >= (3, 9) else 1)' || {
  echo "Python 3.9 or later is required" >&2
  exit 1
}
# Resolve caller paths before changing to the repository Lake root.
if [[ -n ${CRS_LAKE_PACKAGES:-} ]]; then
  CRS_LAKE_PACKAGES=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' \
    "$CRS_LAKE_PACKAGES")
  export CRS_LAKE_PACKAGES
fi
if [[ -n ${PCATS_DST:-} ]]; then
  PCATS_DST=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$PCATS_DST")
  export PCATS_DST
fi
# Caller search paths must never replace the verified package environment.
unset LEAN_PATH LEAN_SRC_PATH
export GIT_TERMINAL_PROMPT=0
export PYTHONDONTWRITEBYTECODE=1
# Lake's runtime pool and independent style processes have separate controls.
# The bounded launcher also gives every Lean compiler `-j 1 -M 12288`.
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS-1}
export FAILCOMP_STYLE_JOBS=${FAILCOMP_STYLE_JOBS-1}
if [[ $LEAN_NUM_THREADS != 1 || $FAILCOMP_STYLE_JOBS != 1 ]]; then
  echo "The port verifier requires LEAN_NUM_THREADS=1 and FAILCOMP_STYLE_JOBS=1" >&2
  exit 2
fi
echo "RESOURCE Lake runtime threads: $LEAN_NUM_THREADS; style processes: $FAILCOMP_STYLE_JOBS; Lean: -j 1 -M 12288"
script_root=$(cd -- "$(dirname -- "$0")" && pwd)
lean_root=$(cd -- "$script_root/.." && pwd)
evidence_root="$lean_root/../.codex-work/logs/port-verification"
bounded_lake="$script_root/bounded_lake.sh"
active=$(ps -eo comm=,args= | awk '$1 == "lean" || $1 == "lake"')
if [[ -n $active ]]; then
  printf 'Refusing overlapping Lean/Lake processes:\n%s\n' "$active" >&2
  exit 75
fi
cd "$lean_root"
package_work=$(mktemp -d)
trap 'rm -rf -- "$package_work"' EXIT
packages="$package_work/packages.json"

python3 - <<'PY'
import json
from pathlib import Path

manifest = json.loads(Path("lake-manifest.json").read_text())
versions = {package["name"]: package["rev"] for package in manifest["packages"]}
provenance = json.loads(
    Path("FailureOfComposition/Porting/EVALUATOR_PROVENANCE.json").read_text()
)
expected = {
    "Foundation": "e72cfe981aa65166f37fa4e2584f4806bc48d72f",
    "mathlib": "065356127b1dc0016f66b7283ce0ce2c4055aa55",
}
for package, revision in expected.items():
    if versions.get(package) != revision:
        raise SystemExit(f"Unexpected {package} revision: {versions.get(package)}")
if Path("lean-toolchain").read_text().strip() != "leanprover/lean4:v4.35.0-rc2":
    raise SystemExit("Unexpected Lean toolchain")
if provenance["toolchain"] != "leanprover/lean4:v4.35.0-rc2":
    raise SystemExit("Unexpected toolchain in port provenance")
if provenance["foundation_revision"] != expected["Foundation"]:
    raise SystemExit("Unexpected Foundation revision in port provenance")
if provenance["mathlib_revision"] != expected["mathlib"]:
    raise SystemExit("Unexpected Mathlib revision in port provenance")
print("PASS dependency and toolchain pins", flush=True)
PY

python3 "$script_root/build_evaluator.py" --check-only
python3 - "$script_root" "$lean_root" <<'PY'
from pathlib import Path
import sys
sys.path.insert(0, sys.argv[1])
from prepare_packages import check_runtime
check_runtime(Path(sys.argv[2]))
PY
python3 "$script_root/prepare_packages.py" --project "$lean_root" --output "$packages"
if "$check_environment"; then
  echo "PASS environment check; no Lake command was run"
  exit 0
fi

run_lake() {
  "$bounded_lake" --packages="$packages" "$@"
}

# The report describes the actual native build, independently of later audits.
# Its exit code is propagated; no manual-compilation fallback can mask failure.
python3 - "$evidence_root" "$packages" "$bounded_lake" <<'PY'
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

project = Path.cwd()
evidence = Path(sys.argv[1]).resolve()
evidence.mkdir(parents=True, exist_ok=True)
pins = json.loads(
    (project / "FailureOfComposition/Porting/EVALUATOR_PROVENANCE.json").read_text()
)
umbrella = project / "FailureOfComposition.lean"
imports = re.findall(
    r"^import\s+(FailureOfComposition\.[\w.]+)\s*$",
    umbrella.read_text(), flags=re.M,
)
source_modules = {
    "FailureOfComposition." + source.stem
    for source in (project / "FailureOfComposition").glob("*.lean")
}
if len(imports) != len(set(imports)) or set(imports) != source_modules:
    raise SystemExit("Library umbrella and mathematical source inventory differ")
library_modules = ["FailureOfComposition", *imports]
evaluator_modules = [
    ".".join(Path(entry["path"]).with_suffix("").parts) for entry in pins["files"]
]
verification_sources = sorted(
    str(source.relative_to(project))
    for source in (project / "FailureOfComposition/Verification").glob("*.lean")
)
manifest = json.loads((project / "lake-manifest.json").read_text())
versions = {package["name"]: package["rev"] for package in manifest["packages"]}
command = [
    sys.argv[3], "--no-cache", "--packages=" + sys.argv[2],
    "build", "FailureOfComposition",
]
report = {
    "verification_mode": "native_lake",
    "project": "Lean",
    "command": command,
    "lake_worker_pool": int(os.environ["LEAN_NUM_THREADS"]),
    "style_worker_processes": int(os.environ["FAILCOMP_STYLE_JOBS"]),
    "status": "running",
    "returncode": None,
    "started_at": datetime.now(timezone.utc).isoformat(),
    "lean_toolchain": (project / "lean-toolchain").read_text().strip(),
    "foundation_revision": versions["Foundation"],
    "mathlib_revision": versions["mathlib"],
    "original_evaluator_pin_commit": pins["original_evaluator_commit"],
    "evaluator_port_checkpoint": pins["port_source_checkpoint"],
    "mathematical_module_counts": {
        "FailureOfComposition": len(library_modules),
        "CategoricalRiceShapiro": len(evaluator_modules),
        "total": len(library_modules) + len(evaluator_modules),
    },
    "mathematical_modules": library_modules + evaluator_modules,
    "verification_sources": verification_sources,
}
report_path = evidence / "native-build.json"

def save_report():
    temporary = report_path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(report, indent=2) + "\n")
    temporary.replace(report_path)

save_report()
print(
    f"Native source inventory: {len(library_modules)} FailureOfComposition modules + "
    f"{len(evaluator_modules)} pinned evaluator modules; "
    f"{len(verification_sources)} separate verification sources",
    flush=True,
)
print("BUILD " + " ".join(command), flush=True)
started = time.monotonic()
try:
    result = subprocess.run(command, check=False)
except OSError as error:
    report.update(status="failed", returncode=127, error=str(error))
    report["finished_at"] = datetime.now(timezone.utc).isoformat()
    report["duration_seconds"] = round(time.monotonic() - started, 3)
    save_report()
    raise
report.update(
    status="passed" if result.returncode == 0 else "failed",
    returncode=result.returncode,
    finished_at=datetime.now(timezone.utc).isoformat(),
    duration_seconds=round(time.monotonic() - started, 3),
)
save_report()
if result.returncode:
    raise SystemExit(result.returncode if result.returncode >= 0 else 128 - result.returncode)
print("PASS native lake build FailureOfComposition", flush=True)
PY

python3 "$script_root/check_style.py" --packages "$packages"

for check in CheckTypes CheckAxioms CheckDependencies; do
  echo "CHECK FailureOfComposition.Verification.$check"
  run_lake env lean "$script_root/Verification/$check.lean"
done
run_lake env leanchecker --verbose FailureOfComposition
run_lake env leanchecker --verbose CategoricalRiceShapiro
python3 "$script_root/prepare_packages.py" --project "$lean_root" --check "$packages"
python3 "$script_root/Palomar/check_draft.py"
echo "PASS native build, module inventory, strict style gate, theorem/type and axiom audits, dependency audit, both kernel replays, and nine paired draft checks"
