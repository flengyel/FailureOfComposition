#!/usr/bin/env python3
"""Resolve declaration names and print an export-order window around one name."""

from __future__ import annotations

import json
import sys
from pathlib import Path

KINDS = ("axiom", "def", "opaque", "thm", "quot", "inductive")


def main() -> None:
    if len(sys.argv) not in (3, 4):
        raise SystemExit("usage: export_decl_window.py EXPORT NAME [RADIUS]")
    source = Path(sys.argv[1])
    target = sys.argv[2]
    radius = int(sys.argv[3]) if len(sys.argv) == 4 else 20
    name_parts: dict[int, tuple[int, str]] = {}
    declarations: list[tuple[str, int | list[int] | None]] = []
    with source.open("r", encoding="utf-8") as handle:
        for raw in handle:
            value = json.loads(raw)
            if "in" in value and ("str" in value or "num" in value):
                item = value.get("str", value.get("num"))
                segment = item["str"] if "str" in item else str(item["i"])
                name_parts[value["in"]] = (item["pre"], segment)
                continue
            kinds = [kind for kind in KINDS if kind in value]
            if len(kinds) == 1:
                kind = kinds[0]
                payload = value[kind]
                if "name" in payload:
                    declarations.append((kind, payload["name"]))
                elif kind == "inductive":
                    declarations.append((kind, [item["name"] for item in payload["types"]]))
                else:
                    declarations.append((kind, None))

    resolved: dict[int, str] = {0: ""}

    def resolve(identifier: int) -> str:
        if identifier in resolved:
            return resolved[identifier]
        prefix_id, segment = name_parts[identifier]
        prefix = resolve(prefix_id)
        result = f"{prefix}.{segment}" if prefix else segment
        resolved[identifier] = result
        return result

    def declaration_name(kind: str, identifier: int | list[int] | None) -> str:
        if isinstance(identifier, int):
            return resolve(identifier)
        if isinstance(identifier, list):
            return ",".join(resolve(item) for item in identifier)
        return f"<{kind}-record>"

    named = [(kind, declaration_name(kind, identifier)) for kind, identifier in declarations]
    matches = [index for index, (_, name) in enumerate(named) if name == target]
    if len(matches) != 1:
        raise SystemExit(f"expected one match for {target!r}, found {len(matches)}")
    center = matches[0]
    lo = max(0, center - radius)
    hi = min(len(named), center + radius + 1)
    for index in range(lo, hi):
        marker = "TARGET" if index == center else ""
        kind, name = named[index]
        print(f"{index}\t{kind}\t{name}\t{marker}")


if __name__ == "__main__":
    main()
