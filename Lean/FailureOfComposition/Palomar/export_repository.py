#!/usr/bin/env python3
"""Export a source-only repository candidate into a new directory.

The nested Lean layout and exact dependency pins are retained. No Git operation,
network access, build, or publication is performed. Existing destinations,
source/destination overlaps, and symbolic-link paths are refused. An interrupted
export is retained for inspection and is never silently overwritten on rerun.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys


SOURCE_REPOSITORY = "flengyel/Categorical_Rice_Shapiro"
BASELINE = "202194e54e883648f0d9f22a65afee6987ef2134"
PIN = "Audit/failure-composition-v36/evidence/evaluator-source-pins.json"
SUPPORT_SUFFIXES = {".lean", ".py", ".sh", ".md"}
DRAFT_SUFFIXES = SUPPORT_SUFFIXES | {".json", ".yaml", ".yml", ".toml"}


class ExportError(Exception):
    """An export prerequisite was not satisfied."""


def no_symlinks(path):
    for component in reversed((path, *path.parents)):
        if component.is_symlink():
            raise ExportError(f"symbolic-link path component is not allowed: {component}")


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def restricted_lakefile(text):
    """Retain package identity, options, requirements, and the two required libraries."""
    pieces = re.split(r"(?m)^\[\[lean_lib\]\]\s*\n", text)
    if len(pieces) < 3:
        raise ExportError("expected separate lean_lib tables in the source Lakefile")
    prefix, changed = re.subn(
        r"(?m)^defaultTargets\s*=\s*\[[^\n]*\]\s*$",
        'defaultTargets = ["FailureOfComposition"]', pieces[0],
    )
    if changed != 1:
        raise ExportError("expected exactly one single-line defaultTargets declaration")
    libraries = {}
    for block in pieces[1:]:
        match = re.fullmatch(r'\s*name\s*=\s*"([A-Za-z][A-Za-z0-9_]*)"\s*', block)
        if match is None:
            raise ExportError("unexpected library configuration; inspect it before exporting")
        name = match.group(1)
        if name in libraries:
            raise ExportError(f"duplicate library in source Lakefile: {name}")
        libraries[name] = block
    retained = ("CategoricalRiceShapiro", "FailureOfComposition")
    if not set(retained).issubset(libraries):
        raise ExportError("source Lakefile lacks a required library")
    result = prefix.rstrip() + "\n\n" + "\n\n".join(
        f'[[lean_lib]]\nname = "{name}"' for name in retained
    ) + "\n"
    return result, sorted(set(libraries) - set(retained))


def root_readme(baseline):
    return f"""# FailureOfComposition: standalone repository candidate

This source-only export prepares a separate repository for the Lean
formalization of *Pointwise provable equality and the failure of composition*.
It has not initialized Git, created a remote repository, or published anything.

The mathematical development and its verifier remain in `Lean/`. The only
libraries declared here are `FailureOfComposition` and its 31 pinned
`CategoricalRiceShapiro` evaluator modules. The default target is
`FailureOfComposition`. The historical Lake package name remains
`CategoricalRiceShapiro` so that the committed dependency manifest is unchanged;
it does not determine the eventual repository name.

The source repository is [{SOURCE_REPOSITORY}](https://github.com/{SOURCE_REPOSITORY}).
The supplied baseline reference is `{baseline}`; this is not a claim that every
exported byte belongs to that commit. `ROOTPROVENANCE.json` records the exact
source and exported file hashes and every packaging transformation. No theorem
source or dependency pin was changed by the export.

## Verification

With Lean 4.32.2 and the pinned dependencies already installed under
`${{PCATS_DST:-$HOME/src/PCats}}/.lake/packages`, run from this directory:

```sh
./scripts/verify-failure-composition.sh --check-environment
./scripts/verify-failure-composition.sh
```

The environment check invokes no Lake command. Full verification builds the
native library and runs the maintained style, theorem, dependency, and kernel
checks. `CRS_LAKE_PACKAGES` may provide the existing validated package mapping.
No dependency checkout is copied into this export or fetched by those scripts.

For a source checkout on `/mnt/c`, use `./scripts/syncfailcomp.sh` to maintain
a Linux verification mirror. Choose a new `FAILCOMP_DST` if an existing mirror
belongs to the original repository; mirror ownership is tied to its source.
See [scripts/README.md](scripts/README.md). The exporter has not run these checks
on this new tree; results must be obtained separately and recorded honestly.

## Palomar preparation and licensing

The nine paired statement drafts are in
[Lean/FailureOfComposition/Palomar](Lean/FailureOfComposition/Palomar/README.md).
The export supplies a repository-root `LICENSE`, copied unchanged from the
existing Lean code license. Manuscripts, PDFs, unrelated projects, build
artifacts, dependency checkouts, and prior audit reports were not copied.

This packaging does not fix Palomar's current minimum-toolchain or Challenge
import-policy blockers. No Comparator or Palomar check has been run by the
exporter. The copied draft metadata retains original-repository provenance and
baseline-specific licensing discussion. Before any submission, update its
repository identity and checked revision, distinguish this root-license
packaging from the original baseline, and complete the outstanding gates.
The draft Challenge's deliberate theorem holes remain outside the maintained
proof umbrella. Source license and third-party dependency licenses remain
distinct; no manuscript license is declared by this code-only export.
"""


SCRIPTS_README = """# Verification entry points

This standalone export contains only the FailureOfComposition workflow.
The original repository's unrelated mirror and production runners are absent.

From a Linux checkout, run:

```sh
./scripts/verify-failure-composition.sh --check-environment
./scripts/verify-failure-composition.sh
```

From a checkout on `/mnt/c`, use a persistent Linux mirror:

```sh
FAILCOMP_DST="$HOME/src/FailureOfCompositionStandalone" ./scripts/syncfailcomp.sh --check-environment
FAILCOMP_DST="$HOME/src/FailureOfCompositionStandalone" ./scripts/syncfailcomp.sh
```

The selected mirror must be absent or an empty dedicated directory, or already
owned by this exact source checkout. Existing mirrors owned by the original
repository are refused. `--sync-only` copies sources without a native build.
The mirror retains its build tree, logs, reports, and temporary package mappings.
Synchronization refuses local edits to managed files and preserves its lock
through verification; interrupted source updates are journaled for recovery.

Both entry points reuse the exact 16 pinned checkouts supplied by
`${PCATS_DST:-$HOME/src/PCats}/.lake/packages` or `CRS_LAKE_PACKAGES`. They do not
clone, fetch, pull, or update dependencies. Each Lake command receives a validated
path override. Use the provided environment check instead of bare `lake env`.
Defaults `LEAN_NUM_THREADS=1` and `FAILCOMP_STYLE_JOBS=1` reduce concurrency;
they are not an aggregate memory limit. Failures propagate nonzero exit codes.
"""


GITIGNORE = """/Lean/.lake/
**/__pycache__/
*.py[cod]
*.olean
*.ilean
*.trace
/Audit/failure-composition-v36/evidence/*
!/Audit/failure-composition-v36/evidence/evaluator-source-pins.json
"""


def prepare_export(source, baseline):
    """Read and validate the entire selection before creating the destination."""
    inputs, outputs, transformations = {}, {}, []

    def read(relative):
        relative = Path(relative)
        if relative.is_absolute() or ".." in relative.parts:
            raise ExportError(f"invalid source path: {relative}")
        path = source / relative
        no_symlinks(path)
        if not path.is_file():
            raise ExportError(f"required regular source file is missing: {relative}")
        data = path.read_bytes()
        record = {"sha256": sha256(data), "bytes": len(data),
                  "mode": stat.S_IMODE(path.stat().st_mode)}
        key = relative.as_posix()
        if key in inputs and inputs[key] != record:
            raise ExportError(f"source changed during export preparation: {key}")
        inputs[key] = record
        return data, record["mode"]

    def copy(relative, destination=None):
        target = destination or relative
        if target in outputs:
            raise ExportError(f"duplicate export target: {target}")
        data, mode = read(relative)
        outputs[target] = (data, mode, {"source": relative})

    def generated(relative, data, note, sources=()):
        if relative in outputs:
            raise ExportError(f"duplicate generated target: {relative}")
        if isinstance(data, str):
            data = data.encode()
        outputs[relative] = (data, 0o644, {"generated": True})
        transformations.append({"path": relative, "description": note,
                                "source_paths": list(sources)})

    for relative in ("Lean/FailureOfComposition.lean", "Lean/lean-toolchain",
                     "Lean/lake-manifest.json", "Lean/LICENSE", PIN):
        copy(relative)
    copy("Lean/LICENSE", "LICENSE")

    library = source / "Lean/FailureOfComposition"
    for path in sorted(library.iterdir()):
        if path.suffix in SUPPORT_SUFFIXES:
            copy(path.relative_to(source).as_posix())
    for path in sorted((library / "Verification").glob("*.lean")):
        copy(path.relative_to(source).as_posix())
    for parent, directories, files in os.walk(library / "Palomar", followlinks=False):
        for name in list(directories):
            child = Path(parent) / name
            if child.is_symlink():
                raise ExportError(f"symbolic-link draft directory is not allowed: {child}")
            if name.startswith(".") or name == "__pycache__":
                directories.remove(name)
        for name in sorted(files):
            path = Path(parent) / name
            if not name.startswith(".") and path.suffix in DRAFT_SUFFIXES:
                copy(path.relative_to(source).as_posix())

    pin_data = json.loads(outputs[PIN][0])
    entries = pin_data.get("files")
    if not isinstance(entries, list) or len(entries) != 31:
        raise ExportError("expected the reviewed inventory of exactly 31 evaluator source pins")
    modules = []
    for entry in entries:
        relative = Path(entry["path"])
        if (relative.is_absolute() or ".." in relative.parts or relative.suffix != ".lean"
                or relative.parts[0] != "CategoricalRiceShapiro"):
            raise ExportError(f"invalid evaluator pin path: {relative}")
        path = "Lean/" + relative.as_posix()
        copy(path)
        data = outputs[path][0]
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if blob != entry.get("blob_sha"):
            raise ExportError(f"evaluator source differs from its pinned Git blob: {relative}")
        modules.append(".".join(relative.with_suffix("").parts))
    generated("Lean/CategoricalRiceShapiro.lean",
              "\n".join("import " + module for module in sorted(modules)) + "\n",
              "Import-only evaluator umbrella generated from the unchanged 31-file pin inventory.",
              (PIN,))

    lakefile, _ = read("Lean/lakefile.toml")
    restricted, removed = restricted_lakefile(lakefile.decode())
    generated("Lean/lakefile.toml", restricted,
              "Preserve package identity, version, options and requirements; default to "
              "FailureOfComposition and remove unrelated libraries: " + ", ".join(removed),
              ("Lean/lakefile.toml",))
    for name in ("syncfailcomp.sh", "sync_failcomp.py", "verify-failure-composition.sh"):
        copy("scripts/" + name)
    generated("README.md", root_readme(baseline), "Standalone export scope and verification instructions.")
    generated("scripts/README.md", SCRIPTS_README, "Document only the exported verification workflows.")
    generated(".gitignore", GITIGNORE, "Ignore future build outputs and reports; retain evaluator pins.")

    # Detect an editing race before materializing the prepared snapshot.
    for relative, record in inputs.items():
        data, mode = read(relative)
        if sha256(data) != record["sha256"] or mode != record["mode"]:
            raise ExportError(f"source changed during export preparation: {relative}")
    provenance = {
        "format": 1,
        "source_repository": SOURCE_REPOSITORY,
        "baseline_reference": baseline,
        "baseline_reference_scope": "Historical reference, not a claim that all current bytes match it.",
        "exported_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_files": [{"path": key, **value} for key, value in sorted(inputs.items())],
        "exported_files": [{"path": key, "sha256": sha256(value[0]), "bytes": len(value[0]),
                            "mode": value[1], **value[2]} for key, value in sorted(outputs.items())],
        "transformations": transformations,
        "license_copy": {"source": "Lean/LICENSE", "destinations": ["LICENSE", "Lean/LICENSE"]},
        "excluded": ["manuscripts and PDFs", "unrelated project libraries", "dependency checkouts",
                     "build artifacts", "old Audit reports", "Git metadata"],
        "verification_at_export": {"31_evaluator_git_blob_pins": "passed",
                                   "standalone_native_build": "not run",
                                   "style_and_theorem_audits": "not run",
                                   "kernel_replay": "not run", "palomar_comparator": "not run"},
        "git_initialized": False,
        "remote_repository_created": False,
        "manifest_note": "ROOTPROVENANCE.json does not recursively hash itself.",
    }
    outputs["ROOTPROVENANCE.json"] = (
        (json.dumps(provenance, indent=2) + "\n").encode(), 0o644, {"generated": True})
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path,
                        help="new absolute destination with an existing parent directory")
    parser.add_argument("--source-commit", default=BASELINE,
                        help="historical baseline reference; exact source file hashes are recorded separately")
    args = parser.parse_args()
    if sys.version_info < (3, 9):
        raise ExportError("Python 3.9 or later is required")
    if not re.fullmatch(r"[0-9a-f]{40}", args.source_commit):
        raise ExportError("--source-commit must be a full lowercase 40-character revision")
    source = Path(__file__).resolve().parents[3]
    destination = args.destination
    if not destination.is_absolute():
        raise ExportError("destination must be absolute")
    no_symlinks(destination)
    destination = destination.resolve()
    if destination == source or source in destination.parents or destination in source.parents:
        raise ExportError("destination must neither contain nor lie within the source repository")
    if destination.exists():
        raise ExportError(f"destination already exists; nothing was overwritten: {destination}")
    if not destination.parent.is_dir():
        raise ExportError("destination parent must already be a directory")
    outputs = prepare_export(source, args.source_commit)
    # Exclusive creation refuses an existing target even if it appeared during preflight.
    destination.mkdir()
    for relative, (data, mode, _) in sorted(outputs.items()):
        path = destination / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("xb") as stream:
            stream.write(data)
        path.chmod(mode)
    print(f"PASS exported {len(outputs)} source/configuration files to {destination}")
    print("31 evaluator source pins matched; no build, Git initialization, or publication performed")


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    try:
        main()
    except (ExportError, OSError, ValueError, KeyError) as error:
        raise SystemExit(str(error)) from error
