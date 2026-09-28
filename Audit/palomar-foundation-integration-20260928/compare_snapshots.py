#!/usr/bin/env python3
"""Compare exact normalized Foundation snapshot records from two Lean runs."""

from __future__ import annotations

import argparse
from pathlib import Path


def records(path: Path) -> dict[tuple[str, str], str]:
    result: dict[tuple[str, str], str] = {}
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        marker = "SNAPSHOT\t"
        offset = raw_line.find(marker)
        if offset < 0:
            continue
        fields = raw_line[offset:].split("\t", 3)
        if len(fields) != 4:
            raise SystemExit(f"malformed snapshot line in {path}: {raw_line}")
        _, label, kind, value = fields
        key = (label, kind)
        if key in result:
            raise SystemExit(f"duplicate snapshot record {key} in {path}")
        result[key] = value
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("baseline", type=Path)
    parser.add_argument("repaired", type=Path)
    args = parser.parse_args()
    baseline = records(args.baseline)
    repaired = records(args.repaired)
    expected = {
        ("blueprint", "TYPE"),
        ("blueprint", "BODY"),
        ("construction", "TYPE"),
        ("func_obligation", "TYPE"),
    }
    if set(baseline) != expected:
        raise SystemExit(f"unexpected baseline keys: {sorted(baseline)}")
    if set(repaired) != expected:
        raise SystemExit(f"unexpected repaired keys: {sorted(repaired)}")
    mismatches = [key for key in sorted(expected) if baseline[key] != repaired[key]]
    if mismatches:
        for key in mismatches:
            print(f"MISMATCH\t{key[0]}\t{key[1]}")
            left = baseline[key]
            right = repaired[key]
            difference = next(
                (index for index, pair in enumerate(zip(left, right)) if pair[0] != pair[1]),
                min(len(left), len(right)),
            )
            start = max(0, difference - 160)
            stop = difference + 320
            print(f"FIRST_DIFFERENCE\toffset={difference}")
            print(f"BASELINE_CONTEXT\t{left[start:stop]}")
            print(f"REPAIRED_CONTEXT\t{right[start:stop]}")
        return 1
    for label, kind in sorted(expected):
        print(f"PASS\t{label}\t{kind}\texact normalized expression match")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
