#!/usr/bin/env python3
"""Stream declaration names and axioms from the standalone Lean export."""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOTS = {
    "FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubstDiagnostic.constructionBvarDefinedExact",
    "FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubstDiagnostic.constructionBvarFieldDefined",
}
FORBIDDEN = {
    "FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction",
    "FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarDefined",
    "FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.constructionBvarDefinedExact",
    "FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_2",
}
PERMITTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DECLARATION_KINDS = ("axiom", "def", "opaque", "thm", "quot", "inductive")


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: verify_export_roots.py EXPORT OUTPUT_JSON")
    source = Path(sys.argv[1])
    output = Path(sys.argv[2])
    names = [""]
    declarations: set[str] = set()
    axioms: set[str] = set()
    with source.open("rb") as handle:
        for line_number, raw in enumerate(handle, start=1):
            record = json.loads(raw)
            if "in" in record:
                index = record["in"]
                if index != len(names):
                    raise SystemExit(f"nonsequential name index on line {line_number}")
                if "str" in record:
                    item = record["str"]
                    component = item["str"]
                else:
                    item = record["num"]
                    component = str(item["i"])
                parent = names[item["pre"]]
                names.append(f"{parent}.{component}" if parent else component)
                continue
            kinds = [kind for kind in DECLARATION_KINDS if kind in record]
            if len(kinds) != 1:
                continue
            kind = kinds[0]
            item = record[kind]
            if "name" not in item:
                continue
            name = names[item["name"]]
            declarations.add(name)
            if kind == "axiom":
                axioms.add(name)
    missing = sorted(ROOTS - declarations)
    reached_forbidden = sorted(FORBIDDEN & declarations)
    unexpected_axioms = sorted(axioms - PERMITTED_AXIOMS)
    result = {
        "export": str(source.resolve()),
        "roots_required": sorted(ROOTS),
        "roots_missing": missing,
        "forbidden_declarations_present": reached_forbidden,
        "axioms": sorted(axioms),
        "unexpected_axioms": unexpected_axioms,
        "declaration_names_seen": len(declarations),
    }
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    if missing or reached_forbidden or unexpected_axioms:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
