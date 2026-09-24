#!/usr/bin/env python3
"""Validate the isolated port checkouts and create a path-only Lake override.

No Lake command or network operation is used here. Caller overrides are only
package-name-to-directory mappings; resolution metadata comes from the project's
committed manifest. Ignored build artifacts are allowed, but tracked changes and
untracked source files are rejected.
"""

import argparse
from contextlib import contextmanager
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"
EXPECTED_LEAN_VERSION = "4.35.0-rc2"


def positive_setting(name, default=1):
    value = os.environ.get(name, str(default))
    if not re.fullmatch(r"[1-9][0-9]*", value):
        raise SystemExit(f"{name} must be a positive integer; got {value!r}")
    return int(value)


def clean_environment():
    environment = os.environ.copy()
    environment.pop("LEAN_PATH", None)
    environment.pop("LEAN_SRC_PATH", None)
    environment["GIT_TERMINAL_PROMPT"] = "0"
    environment["LEAN_NUM_THREADS"] = str(positive_setting("LEAN_NUM_THREADS"))
    return environment


def check_runtime(project):
    """Check the installed compiler directly, without invoking Lake."""
    if sys.version_info < (3, 9):
        raise SystemExit("Python 3.9 or later is required")
    if (project / "lean-toolchain").read_text().strip() != EXPECTED_TOOLCHAIN:
        raise SystemExit(f"Unexpected Lean toolchain; expected {EXPECTED_TOOLCHAIN}")
    result = subprocess.run(
        ["lean", "--version"], cwd=project, env=clean_environment(),
        capture_output=True, text=True, check=False,
    )
    version = re.search(r"\bversion\s+([^\s,)]+)", result.stdout)
    if result.returncode or not version or version.group(1) != EXPECTED_LEAN_VERSION:
        raise SystemExit(
            f"Expected installed Lean {EXPECTED_LEAN_VERSION}; got "
            + (result.stdout.strip() or result.stderr.strip() or "no version output")
        )
    print(result.stdout.strip(), flush=True)
    print(f"PASS installed Lean {EXPECTED_LEAN_VERSION} (checked without Lake)", flush=True)


def _read_manifest(path):
    value = json.loads(path.read_text())
    if not isinstance(value, dict) or not isinstance(value.get("packages"), list):
        raise SystemExit(f"Expected a manifest-shaped object with a packages array: {path}")
    entries = value["packages"]
    if any(not isinstance(entry, dict) or not isinstance(entry.get("name"), str)
           for entry in entries):
        raise SystemExit(f"Every package entry must have a name: {path}")
    names = [entry["name"] for entry in entries]
    if len(names) != len(set(names)):
        raise SystemExit(f"Duplicate package names: {path}")
    return value, {entry["name"]: entry for entry in entries}


def _relative_file(value, name, field):
    if not isinstance(value, str) or not value:
        raise SystemExit(f"{name}: invalid {field}: {value!r}")
    path = Path(value)
    if path.is_absolute() or ".." in path.parts:
        raise SystemExit(f"{name}: {field} escapes the checkout: {value!r}")
    return path


def _git(directory, *arguments):
    result = subprocess.run(
        ["git", "--no-optional-locks", "-C", str(directory), *arguments],
        env=clean_environment(), capture_output=True, text=True, check=False,
    )
    if result.returncode:
        raise SystemExit(f"{directory}: git {' '.join(arguments)} failed: {result.stderr.strip()}")
    return result.stdout.strip()


def canonical_packages(project, supplied=None):
    """Validate every manifest package and return freshly generated path entries."""
    project = Path(project).resolve(strict=True)
    manifest, pinned = _read_manifest(project / "lake-manifest.json")
    if not pinned:
        raise SystemExit("The project manifest has no pinned packages")
    mapping = {}
    if supplied is not None:
        _, entries = _read_manifest(Path(supplied).resolve(strict=True))
        if entries.keys() != pinned.keys():
            raise SystemExit(
                "Override package-name set differs from the manifest: "
                f"missing {sorted(pinned.keys() - entries.keys())}, "
                f"extra {sorted(entries.keys() - pinned.keys())}"
            )
        for name, entry in entries.items():
            if entry.get("type") != "path":
                raise SystemExit(f'{name}: override type must be exactly "path"')
            directory = entry.get("dir")
            if not isinstance(directory, str) or not Path(directory).is_absolute():
                raise SystemExit(f"{name}: override dir must be an absolute path")
            for field, default in (("configFile", "lakefile.toml"),
                                   ("manifestFile", "lake-manifest.json")):
                if field in entry and entry[field] != pinned[name].get(field, default):
                    raise SystemExit(f"{name}: supplied {field} conflicts with pinned metadata")
            for field in ("url", "rev", "inputRev", "subDir", "scope"):
                if field in entry and entry[field] != pinned[name].get(field):
                    raise SystemExit(f"{name}: supplied {field} conflicts with pinned metadata")
            mapping[name] = Path(directory).resolve(strict=True)
    else:
        package_directory = (
            project / manifest.get("packagesDir", ".lake/packages")
        ).resolve(strict=True)
        for name in pinned:
            mapping[name] = (package_directory / name.strip("«»")).resolve(strict=True)

    canonical = []
    for name, pin in pinned.items():
        directory = mapping[name]
        if not directory.is_dir():
            raise SystemExit(f"{name}: checkout directory does not exist: {directory}")
        if pin.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", pin.get("rev", "")):
            raise SystemExit(f"{name}: expected a Git package pinned to a full revision")
        if not isinstance(pin.get("url"), str) or not pin["url"]:
            raise SystemExit(f"{name}: missing pinned origin URL")
        if pin.get("subDir") is not None:
            raise SystemExit(f"{name}: Git subdirectory packages are not supported")
        config = pin.get("configFile", "lakefile.toml")
        package_manifest = pin.get("manifestFile", "lake-manifest.json")
        for field, value in (("configFile", config), ("manifestFile", package_manifest)):
            relative = _relative_file(value, name, field)
            source = (directory / relative).resolve(strict=True)
            if not source.is_relative_to(directory) or not source.is_file():
                raise SystemExit(f"{name}: missing or escaping {field}: {value}")
        top = Path(_git(directory, "rev-parse", "--show-toplevel")).resolve(strict=True)
        if top != directory:
            raise SystemExit(f"{name}: package directory is not its Git checkout root")
        head = _git(directory, "rev-parse", "HEAD")
        if head != pin["rev"]:
            raise SystemExit(f"{name}: HEAD {head} != pinned {pin['rev']}")
        origin = _git(directory, "remote", "get-url", "origin").removesuffix(".git")
        if origin != pin["url"].removesuffix(".git"):
            raise SystemExit(f"{name}: origin {origin!r} != pinned {pin['url']!r}")
        if _git(directory, "status", "--porcelain", "--untracked-files=all"):
            raise SystemExit(f"{name}: checkout has tracked changes or untracked files")
        canonical.append({
            "type": "path", "name": name, "dir": str(directory),
            "configFile": config, "manifestFile": package_manifest,
            "inherited": pin.get("inherited", False),
        })
    return {
        "version": manifest["version"],
        "packagesDir": manifest.get("packagesDir", ".lake/packages"),
        "packages": canonical,
    }


def prepare_packages(project, output, supplied=None):
    if supplied is None:
        supplied = os.environ.get("CRS_LAKE_PACKAGES") or None
    canonical = canonical_packages(project, supplied)
    Path(output).write_text(json.dumps(canonical, indent=2) + "\n")
    print(f"PASS validated {len(canonical['packages'])} pinned local packages", flush=True)


def check_packages(project, override):
    canonical = canonical_packages(project, override)
    existing = json.loads(Path(override).read_text())
    if existing != canonical:
        raise SystemExit("Canonical package override changed or contains noncanonical metadata")
    print(f"PASS revalidated {len(canonical['packages'])} pinned local packages", flush=True)


@contextmanager
def validated_packages(project, supplied=None):
    check_runtime(project)
    work = Path(project).resolve().parent / ".codex-work" / "tmp"
    work.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix="failure-composition-packages-", dir=work
    ) as temporary:
        override = Path(temporary) / "packages.json"
        prepare_packages(project, override, supplied)
        try:
            yield override
        finally:
            check_packages(project, override)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, required=True)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--output", type=Path)
    action.add_argument("--check", type=Path)
    args = parser.parse_args()
    if args.output is not None:
        prepare_packages(args.project, args.output)
    else:
        check_packages(args.project, args.check)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error
