#!/usr/bin/env python3
"""Compare baseline and patched TermSubst expression snapshots.

The snapshot format preserves Lean Name.str/Name.num constructors through Expr's
repr rather than flattening names.  Source metadata can differ, so exact helper
type equality is established separately inside Lean with Expr.eqv; this script
checks body-sensitive contracts for the record and its computational fields.
"""

from __future__ import annotations

import argparse
from pathlib import Path


def parse(path: Path) -> tuple[dict[tuple[str, str], str], dict[int, str], dict[str, str]]:
    snapshots: dict[tuple[str, str], str] = {}
    arguments: dict[int, str] = {}
    construction: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        fields = line.split("\t")
        if fields[0] == "SNAPSHOT" and len(fields) == 4:
            snapshots[(fields[1], fields[2])] = fields[3]
        elif fields[0] == "CONSTRUCTION_ARG" and len(fields) == 3:
            arguments[int(fields[1])] = fields[2]
        elif fields[0] in {"CONSTRUCTION_HEAD", "CONSTRUCTION_ARG_COUNT"}:
            construction[fields[0]] = fields[1]
    return snapshots, arguments, construction


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"FAIL {message}")
    print(f"PASS {message}")


def normalize_generated_names(value: str) -> str:
    """Normalize only generated names whose renumbering the source diff explains."""
    replacements = {
        "TermSubst.construction._proof_5": "TermSubst.construction._proof_BVAR_INDEX",
        "TermSubst.construction._proof_4": "TermSubst.construction._proof_BVAR_INDEX",
        "TermSubst.construction._proof_9": "TermSubst.construction._proof_FVAR_DEFINED",
        "TermSubst.construction._proof_7": "TermSubst.construction._proof_FVAR_DEFINED",
        "TermSubst.construction._proof_12": "TermSubst.construction._proof_FUNC_DEFINED",
        "TermSubst.construction._proof_10": "TermSubst.construction._proof_FUNC_DEFINED",
    }
    for source, target in replacements.items():
        value = value.replace(source, target)
    return value


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("baseline", type=Path)
    parser.add_argument("patched", type=Path)
    args = parser.parse_args()
    baseline, baseline_args, baseline_construction = parse(args.baseline)
    patched, patched_args, patched_construction = parse(args.patched)

    require(
        baseline[("blueprint", "TYPE")] == patched[("blueprint", "TYPE")],
        "blueprint type is structurally identical",
    )
    require(
        baseline[("blueprint", "BODY")] == patched[("blueprint", "BODY")],
        "blueprint body is structurally identical",
    )
    require(
        baseline[("construction", "TYPE")] == patched[("construction", "TYPE")],
        "construction public type is structurally identical",
    )
    require(
        baseline_construction == patched_construction,
        "construction head and constructor-argument count are identical",
    )
    require(set(baseline_args) == set(range(10)), "baseline exposes ten constructor arguments")
    require(set(patched_args) == set(range(10)), "patched module exposes ten constructor arguments")

    # Construction.mk arguments 4, 5, and 6 are bvar/fvar/func.  The preceding
    # arguments carry parameters/instances; 7, 8, and 9 are their proof fields.
    # Only argument 7 (bvar_defined) is deliberately replaced.
    for index in range(7):
        require(
            normalize_generated_names(baseline_args[index])
            == normalize_generated_names(patched_args[index]),
            f"construction argument {index} is structurally identical after documented generated-name renaming",
        )
    require(
        normalize_generated_names(baseline_args[8])
        == normalize_generated_names(patched_args[8]),
        "fvar_defined record argument is structurally identical after documented generated-name renaming",
    )
    require(
        normalize_generated_names(baseline_args[9])
        == normalize_generated_names(patched_args[9]),
        "func_defined record argument is structurally identical after documented generated-name renaming",
    )
    require(
        baseline_args[7] != patched_args[7],
        "only the intended bvar_defined record argument changes",
    )
    require(
        "constructionBvarDefined" in patched_args[7],
        "patched bvar_defined argument names the factored field proof",
    )


if __name__ == "__main__":
    main()
