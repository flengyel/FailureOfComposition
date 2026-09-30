#!/usr/bin/env python3
"""Run the authenticated current Palomar Challenge source audit."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

EXPECTED_SUBMISSION = "65f0154ed776cd26c224254aa57b379137f28b0d"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def git_head(path: Path) -> str:
    return subprocess.run(
        ["git", "-C", str(path), "rev-parse", "HEAD"],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    ).stdout.strip()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", type=Path, required=True)
    parser.add_argument("--dependency-checkout", type=Path)
    parser.add_argument("--submission", type=Path, required=True)
    parser.add_argument("--source-deps", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repository = args.repository.resolve()
    lean_root = repository / "Lean"
    dependency_repository = (
        args.dependency_checkout.resolve()
        if args.dependency_checkout is not None
        else repository
    )
    dependency_lean_root = dependency_repository / "Lean"
    submission = args.submission.resolve()
    actual = git_head(submission)
    if actual != EXPECTED_SUBMISSION:
        raise SystemExit(f"PalomarSubmission is {actual}, expected {EXPECTED_SUBMISSION}")
    sys.path.insert(0, str(submission))
    from scripts.verify_submission import audit_challenge_sources, manifest_packages

    dependency_sources = sorted({
        Path(line.strip()).resolve()
        for line in args.source_deps.read_text(encoding="utf-8").splitlines()
        if line.strip()
    })
    candidate_toolchain = (lean_root / "lean-toolchain").read_bytes()
    dependency_toolchain = (dependency_lean_root / "lean-toolchain").read_bytes()
    if candidate_toolchain != dependency_toolchain:
        raise SystemExit("dependency checkout uses a different Lean toolchain")
    candidate_manifest = json.loads(
        (lean_root / "lake-manifest.json").read_text(encoding="utf-8")
    )
    dependency_manifest = json.loads(
        (dependency_lean_root / "lake-manifest.json").read_text(encoding="utf-8")
    )
    identity = lambda value: sorted(
        (item.get("name"), item.get("url"), item.get("rev"))
        for item in value.get("packages", [])
    )
    if identity(candidate_manifest) != identity(dependency_manifest):
        raise SystemExit("dependency checkout package identities differ from the candidate")
    mathlib = dependency_lean_root / ".lake/packages/mathlib"
    allowed = {"mathlib"}
    allowed.update(package["name"] for package in manifest_packages(mathlib))
    allowlist = {
        name: ("leanprover-community/mathlib4", "high") for name in sorted(allowed)
    }
    prefix = subprocess.run(
        ["lean", "--print-prefix"], cwd=lean_root, check=True,
        text=True, stdout=subprocess.PIPE,
    ).stdout.strip()
    audit = audit_challenge_sources(
        dependency_lean_root,
        checkout=dependency_repository,
        dependency_sources=dependency_sources,
        lean_prefix=Path(prefix),
        allowlist=allowlist,
        writable_directories=[dependency_lean_root / ".lake/build"],
    )
    challenge = lean_root / "FailureOfComposition/Palomar/ChallengeNine.lean"
    text = challenge.read_text(encoding="utf-8")
    lines = text.count("\n") + int(bool(text) and not text.endswith("\n"))
    record = {
        "generated_at": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "repository_head": git_head(repository),
        "dependency_checkout": str(dependency_repository),
        "dependency_checkout_head": git_head(dependency_repository),
        "dependency_identity_matches_candidate": True,
        "palomar_submission_commit": actual,
        "verify_submission_sha256": sha256(submission / "scripts/verify_submission.py"),
        "challenge": "Lean/FailureOfComposition/Palomar/ChallengeNine.lean",
        "challenge_bytes": challenge.stat().st_size,
        "challenge_lines": lines,
        "hard_limits": {"bytes": 100 * 1024, "lines": 1000},
        "preferred_limits": {"bytes": 32 * 1024, "lines": 300},
        "resolved_sources": [str(path) for path in dependency_sources],
        "audit": audit,
        "preferred_surface_warning": challenge.stat().st_size > 32 * 1024 or lines > 300,
        "result": "pass" if not audit["untrusted_sources"] else "fail",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2, sort_keys=True))
    if challenge.stat().st_size > 100 * 1024 or lines > 1000:
        raise SystemExit("ChallengeNine exceeds a hard source limit")
    if audit["untrusted_sources"]:
        raise SystemExit("ChallengeNine has untrusted source dependencies")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
