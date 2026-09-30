#!/usr/bin/env python3
"""Run the pinned Palomar source-policy audit on ChallengeNine."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import types
from datetime import datetime, timezone
from pathlib import Path

REPOSITORY = Path("/home/flengyel/src/FailureOfComposition-port")
LEAN_ROOT = REPOSITORY / "Lean"
SUBMISSION = REPOSITORY / ".codex-work/palomar/upstream/PalomarSubmission"
EXPECTED_SUBMISSION = "a59f25bd8a66bf6faf3a4f4260d412989c0185ea"

sys.path.insert(0, str(SUBMISSION))
yaml_stub = types.ModuleType("yaml")
yaml_stub.YAMLError = RuntimeError


class _UnusedSafeLoader:
    @classmethod
    def add_constructor(cls, *_args, **_kwargs):
        return None


yaml_stub.SafeLoader = _UnusedSafeLoader
yaml_stub.nodes = types.SimpleNamespace(MappingNode=object)
yaml_stub.resolver = types.SimpleNamespace(
    BaseResolver=types.SimpleNamespace(DEFAULT_MAPPING_TAG="unused")
)
yaml_stub.safe_load = lambda *_args, **_kwargs: (_ for _ in ()).throw(
    RuntimeError("PyYAML stub must not be used by the source audit")
)
yaml_stub.safe_dump = yaml_stub.safe_load
sys.modules.setdefault("yaml", yaml_stub)
from scripts.verify_submission import audit_challenge_sources, manifest_packages  # noqa: E402


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def git_head(path: Path) -> str:
    return subprocess.run(
        ["git", "-C", str(path), "rev-parse", "HEAD"],
        check=True, text=True, stdout=subprocess.PIPE,
    ).stdout.strip()


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: run_source_policy.py SOURCE_DEPS OUTPUT_JSON")
    source_list = Path(sys.argv[1])
    output = Path(sys.argv[2])
    submission_head = git_head(SUBMISSION)
    if submission_head != EXPECTED_SUBMISSION:
        raise SystemExit(f"PalomarSubmission is {submission_head}, expected {EXPECTED_SUBMISSION}")
    dependency_sources = sorted({
        Path(line.strip()).resolve()
        for line in source_list.read_text(encoding="utf-8").splitlines()
        if line.strip()
    })
    mathlib = LEAN_ROOT / ".lake/packages/mathlib"
    mathlib_closure = {"mathlib"}
    mathlib_closure.update(package["name"] for package in manifest_packages(mathlib))
    allowlist = {
        name: ("leanprover-community/mathlib4", "high")
        for name in sorted(mathlib_closure)
    }
    lean_prefix = Path("/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2")
    audit = audit_challenge_sources(
        LEAN_ROOT,
        checkout=REPOSITORY,
        dependency_sources=dependency_sources,
        lean_prefix=lean_prefix,
        allowlist=allowlist,
        writable_directories=[LEAN_ROOT / ".lake/build"],
    )
    challenge = LEAN_ROOT / "FailureOfComposition/Palomar/ChallengeNine.lean"
    record = {
        "audit_kind": "pinned audit_challenge_sources with authenticated Mathlib closure",
        "generated_at": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "repository_head": git_head(REPOSITORY),
        "challenge": "Lean/FailureOfComposition/Palomar/ChallengeNine.lean",
        "challenge_bytes": challenge.stat().st_size,
        "challenge_lines": len(challenge.read_text(encoding="utf-8").splitlines()),
        "hard_limits": {"bytes": 100 * 1024, "lines": 1000},
        "preferred_limits": {"bytes": 32 * 1024, "lines": 300},
        "palomar_submission_commit": submission_head,
        "verify_submission_sha256": sha256(SUBMISSION / "scripts/verify_submission.py"),
        "allowlist_policy_sha256": sha256(SUBMISSION / "allowed-challenge-repositories.json"),
        "mathlib_commit": git_head(mathlib),
        "retained_allowlisted_package_names": sorted(mathlib_closure),
        "resolved_sources": [str(path) for path in dependency_sources],
        "audit": audit,
        "warning": challenge.stat().st_size > 32 * 1024 or len(challenge.read_text(encoding="utf-8").splitlines()) > 300,
        "result": "pass" if not audit["untrusted_sources"] else "fail",
    }
    output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2, sort_keys=True))
    if challenge.stat().st_size > 100 * 1024 or record["challenge_lines"] > 1000:
        raise SystemExit("ChallengeNine exceeds a pinned hard source limit")
    if audit["untrusted_sources"]:
        raise SystemExit("ChallengeNine has untrusted source dependencies")


if __name__ == "__main__":
    main()
