#!/usr/bin/env python3
"""Assemble the block-level Lean modules for Stage Five rows 200--299.

The chunk generators carry the large exact certificates.  This script keeps
the two small block-level bridge modules synchronized with those chunks and
extracts the survivor list directly from the checked reduction data.
"""

from __future__ import annotations

import ast
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "lean" / "TraceEuclidean"
SOURCE_SUFFIX = "Rows100To199"
TARGET_SUFFIX = "Rows200To299"


def survivor_coefficients() -> list[list[int]]:
    directory = (
        LEAN_ROOT
        / "DegreeSevenRolleStageSevenRows200To299ReductionParts"
    )
    rows: list[list[int]] = []
    for path in sorted(directory.glob("Chunk*Part*.lean")):
        source = path.read_text(encoding="utf-8")
        for match in re.finditer(r"\.survivor\s+(\[[^\]]+\])", source):
            row = ast.literal_eval(match.group(1))
            if not isinstance(row, list) or len(row) != 8:
                raise ArithmeticError(f"invalid survivor in {path}")
            rows.append(row)
    if len(rows) != 94 or len({tuple(row) for row in rows}) != 94:
        raise ArithmeticError(
            f"expected 94 distinct survivors, found {len(rows)}"
        )
    return rows


def render_survivor_list(rows: list[list[int]]) -> str:
    body = ",\n".join(
        "    [" + ", ".join(str(value) for value in row) + "]"
        for row in rows
    )
    return (
        "set_option maxHeartbeats 0 in\n"
        "-- The exact 94-row list exceeds the default elaboration heartbeat budget.\n"
        "def degreeSevenStageSevenSurvivorCoefficientsRows200To299 :\n"
        "    List (List ℤ) :=\n"
        "  [\n"
        f"{body}\n"
        "  ]"
    )


def render_closure() -> str:
    source = (
        LEAN_ROOT
        / "DegreeSevenRolleStageSevenRows100To199Closure.lean"
    ).read_text(encoding="utf-8")
    source = source.replace(SOURCE_SUFFIX, TARGET_SUFFIX)
    source = source.replace("rows 100 through 199", "rows 200 through 299")
    source = source.replace("Rows 100 through 199", "Rows 200 through 299")
    source = source.replace("= 1805 := by", "= 3170 := by")
    source = source.replace("= 1369 := by", "= 2725 := by")
    source = source.replace("= 364 := by", "= 373 := by")
    return source


def render_reduction(rows: list[list[int]]) -> str:
    source = (
        LEAN_ROOT
        / "DegreeSevenRolleStageSevenRows100To199Reduction.lean"
    ).read_text(encoding="utf-8")
    source = source.replace(SOURCE_SUFFIX, TARGET_SUFFIX)
    source = source.replace("rows 100 through 199", "rows 200 through 299")
    source = source.replace("Rows 100 through 199", "Rows 200 through 299")
    source = source.replace(
        "The exact `a0` intervals contain 599 final monic septics.  Checked nontrivial\n"
        "factorizations remove 590 of them.  This file combines the ten independent\n"
        "chunks and reduces every irreducible Hunter candidate to nine explicit\n"
        "coefficient lists.",
        "The exact `a0` intervals contain 1,381 final monic septics.  Checked\n"
        "nontrivial factorizations remove 1,287 of them.  This file combines the ten\n"
        "independent chunks and reduces every irreducible Hunter candidate to 94\n"
        "explicit coefficient lists.",
    )
    start = source.index(
        "def degreeSevenStageSevenSurvivorCoefficientsRows200To299 :"
    )
    end = source.index("\n\ntheorem", start)
    source = source[:start] + render_survivor_list(rows) + source[end:]
    source = source.replace("= 1369 := by", "= 2725 := by")
    source = source.replace("= 599 := by", "= 1381 := by")
    source = source.replace("one of the nine explicitly retained", "one of the 94 explicitly retained")
    source = source.replace("one of the nine retained", "one of the 94 retained")
    source = source.replace("reduces_to_nine", "reduces_to_ninetyFour")
    return source


def main() -> None:
    rows = survivor_coefficients()
    outputs = {
        LEAN_ROOT / "DegreeSevenRolleStageSevenRows200To299Closure.lean":
            render_closure(),
        LEAN_ROOT / "DegreeSevenRolleStageSevenRows200To299Reduction.lean":
            render_reduction(rows),
    }
    for path, source in outputs.items():
        path.write_text(source, encoding="utf-8", newline="\n")
        print(f"wrote {path.relative_to(ROOT)}")
    print("degree-seven rows 200--299 aggregates: PASS (94 survivors)")


if __name__ == "__main__":
    main()
