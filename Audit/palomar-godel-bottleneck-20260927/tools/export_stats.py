#!/usr/bin/env python3
"""Stream compact statistics from a pinned leanexport NDJSON output."""

from __future__ import annotations

import hashlib
import json
import sys
from collections import Counter
from pathlib import Path


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: export_stats.py INPUT.ndjson OUTPUT.json")
    source = Path(sys.argv[1])
    output = Path(sys.argv[2])
    digest = hashlib.sha256()
    records: Counter[str] = Counter()
    lines = 0
    metadata = None
    with source.open("rb") as handle:
        for raw in handle:
            digest.update(raw)
            lines += 1
            value = json.loads(raw)
            if not isinstance(value, dict):
                raise SystemExit(f"unexpected NDJSON record on line {lines}")
            if "ie" in value:
                records["ie"] += 1
            elif "in" in value and ("str" in value or "num" in value):
                records["in"] += 1
            elif "il" in value:
                records["il"] += 1
            elif "meta" in value:
                records["meta"] += 1
                metadata = value["meta"]
            else:
                kinds = [
                    key
                    for key in ("axiom", "def", "opaque", "thm", "quot", "inductive")
                    if key in value
                ]
                if len(kinds) != 1:
                    raise SystemExit(
                        f"unexpected NDJSON record on line {lines}: {sorted(value)}"
                    )
                records[kinds[0]] += 1
    result = {
        "path": str(source),
        "bytes": source.stat().st_size,
        "sha256": digest.hexdigest(),
        "lines": lines,
        "expression_records": records["ie"],
        "name_records": records["in"],
        "level_records": records["il"],
        "declaration_records": sum(
            records[key]
            for key in ("axiom", "def", "opaque", "thm", "quot", "inductive")
        ),
        "record_kinds": dict(sorted(records.items())),
        "metadata": metadata,
        "format_note": "Lean 4 NDJSON export; expression records are exporter DAG records",
    }
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
