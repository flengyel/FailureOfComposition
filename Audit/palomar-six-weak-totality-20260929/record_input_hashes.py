#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from datetime import datetime, timezone


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def main() -> None:
    if len(sys.argv) != 6:
        raise SystemExit(
            "usage: record_input_hashes.py OUTPUT CHALLENGE SOLUTION PORTABLE PROTECTED"
        )
    output = pathlib.Path(sys.argv[1])
    keys = ("challenge_export", "solution_export", "portable_config", "protected_config")
    paths = [pathlib.Path(value).resolve() for value in sys.argv[2:]]
    value = {
        "recorded_at": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "inputs": {
            key: {"path": str(path), "bytes": path.stat().st_size, "sha256": sha256(path)}
            for key, path in zip(keys, paths, strict=True)
        },
    }
    output.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
