#!/usr/bin/env python3
"""Verify the post-execution size/SHA-256 record against retained local files."""

from __future__ import annotations

import hashlib
from pathlib import Path
import sys


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as src:
        for chunk in iter(lambda: src.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def main() -> int:
    if len(sys.argv) != 2:
        print(f"usage: {Path(sys.argv[0]).name} OUTPUT_HASHES", file=sys.stderr)
        return 2
    record = Path(sys.argv[1])
    checked = 0
    for raw in record.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("recorded_at=") or line.startswith("source_commit="):
            continue
        expected_hash, expected_size, name = line.split(maxsplit=2)
        path = Path(name)
        actual_size = path.stat().st_size
        actual_hash = digest(path)
        if actual_size != int(expected_size) or actual_hash != expected_hash:
            print(
                f"FAIL {path}: expected {expected_size}/{expected_hash}, "
                f"got {actual_size}/{actual_hash}",
                file=sys.stderr,
            )
            return 1
        checked += 1
        print(f"OK {actual_size} {actual_hash} {path}")
    print(f"verified {checked} retained output identities")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
