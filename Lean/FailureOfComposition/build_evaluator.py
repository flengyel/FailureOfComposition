#!/usr/bin/env python3
"""Check evaluator source pins; optionally build them with the native Lake project."""

import argparse
from graphlib import TopologicalSorter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
from prepare_packages import clean_environment, validated_packages


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check-only",
        action="store_true",
        help="verify source blobs and their local dependency closure without building",
    )
    parser.add_argument("--packages", type=Path, help="existing package mapping to validate")
    args = parser.parse_args()
    lean_root = Path(__file__).resolve().parent.parent
    evidence = lean_root.parent / "Audit/failure-composition-v36/evidence"
    pins = json.loads((evidence / "evaluator-source-pins.json").read_text())
    sources = {}
    for entry in pins["files"]:
        relative = Path(entry["path"])
        source = (lean_root / relative).resolve()
        if not source.is_relative_to(lean_root):
            raise SystemExit(f"Pinned source is outside the Lean project: {relative}")
        data = source.read_bytes()
        blob = hashlib.sha1(
            b"blob " + str(len(data)).encode() + b"\0" + data
        ).hexdigest()
        if blob != entry["blob_sha"]:
            raise SystemExit(f"Evaluator source differs from its Git blob pin: {relative}")
        module = ".".join(relative.with_suffix("").parts)
        if module in sources:
            raise SystemExit(f"Duplicate pinned module: {module}")
        sources[module] = source

    dependencies = {}
    for module, source in sources.items():
        imports = re.findall(r"^import\s+([\w.]+)", source.read_text(), flags=re.M)
        local = {name for name in imports if name.startswith("CategoricalRiceShapiro.")}
        missing = local - sources.keys()
        if missing:
            raise SystemExit(f"Unpinned local dependencies of {module}: {sorted(missing)}")
        dependencies[module] = tuple(sorted(local))

    order = list(TopologicalSorter(dependencies).static_order())
    print(
        f"PASS {len(sources)} evaluator source pins and dependency closure "
        f"(relative to Lean; pin commit {pins['commit']})",
        flush=True,
    )
    if args.check_only:
        return 0

    # Keep all build outputs in Lake's build tree, never beside source files.
    with validated_packages(lean_root, args.packages) as packages:
        result = subprocess.run(
            ["lake", "--packages=" + str(packages), "build", *order],
            cwd=lean_root, env=clean_environment(), check=False,
        )
    if result.returncode == 0:
        print(f"PASS native Lake build of {len(order)} pinned evaluator modules", flush=True)
    return result.returncode if result.returncode >= 0 else 128 - result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
