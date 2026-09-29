#!/usr/bin/env python3
"""Stream compact statistics from the pinned leanexport NDJSON output."""

from __future__ import annotations

import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path("/home/flengyel/src/FailureOfComposition-port")
EVIDENCE = ROOT / ".codex-work/palomar/first-result-validation/20260927T161145Z"
SOURCE = Path(sys.argv[1]) if len(sys.argv) > 1 else EVIDENCE / "export/solution-one.ndjson"
OUTPUT = (
    Path(sys.argv[2]) if len(sys.argv) > 2
    else EVIDENCE / "analysis/solution-one-export-stats.json"
)


def main() -> None:
    digest = hashlib.sha256()
    records: Counter[str] = Counter()
    lines = 0
    with SOURCE.open("rb") as handle:
        for raw in handle:
            digest.update(raw)
            lines += 1
            value = json.loads(raw)
            if not isinstance(value, dict):
                raise SystemExit(f"unexpected NDJSON record on line {lines}")
            if "ie" in value:
                records["ie"] += 1
            elif "in" in value:
                records["in"] += 1
            elif "il" in value:
                records["il"] += 1
            elif "meta" in value:
                records["meta"] += 1
            else:
                kinds = [
                    key for key in ("axiom", "def", "opaque", "thm", "quot", "inductive")
                    if key in value
                ]
                if len(kinds) != 1:
                    raise SystemExit(f"unexpected NDJSON record on line {lines}: {sorted(value)}")
                records[kinds[0]] += 1
    result = {
        "path": str(SOURCE),
        "bytes": SOURCE.stat().st_size,
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
        "command_scope": (
            "exact command is retained in the matching run script and GNU-time record; "
            "targets include Quot, the selected root, permitted axioms, and pinned Comparator primitives"
        ),
        "format": "Lean 4 NDJSON export 3.1.0",
    }
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
