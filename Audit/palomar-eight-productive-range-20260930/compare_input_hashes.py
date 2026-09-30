#!/usr/bin/env python3
from __future__ import annotations

import json
import pathlib
import sys


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: compare_input_hashes.py BEFORE AFTER")
    before = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
    after = json.loads(pathlib.Path(sys.argv[2]).read_text(encoding="utf-8"))
    if before.get("inputs") != after.get("inputs"):
        raise SystemExit("FAIL Comparator export/config input identity changed")
    print("PASS Comparator export/config input identities unchanged")


if __name__ == "__main__":
    main()
