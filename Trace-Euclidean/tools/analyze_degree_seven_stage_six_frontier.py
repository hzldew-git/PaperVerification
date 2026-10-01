#!/usr/bin/env python3
"""Measure the exact a1 frontier represented by the Stage Six families.

The generated Lean files store one dyadic five-root certificate for an
interval of a2 values.  This script replays the same rational interval
evaluation used by the Lean definition of ``a1Candidates`` and reports the
resulting finite-set sizes.  It is an audit and planning tool; Lean remains
the proof checker for the certificates themselves.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import re

from generate_degree_seven_rolle_stage_three import RootInterval, interval_eval


ROOT = Path(__file__).resolve().parents[1]
CHUNK_DIRECTORY = (
    ROOT
    / "lean"
    / "TraceEuclidean"
    / "DegreeSevenRolleStageSixStrongCompactCoverages"
)
DENOMINATOR = 65536
INTEGER_PATTERN = re.compile(r"\(([-0-9]+) : ℤ\)")
FAMILY_PATTERN = re.compile(r", some ⟨(.*?)⟩⟩,?\s*$")


@dataclass(frozen=True)
class Family:
    a6: int
    a5: int
    a4: int
    a3: int
    a2_lower: int
    a2_upper: int
    root_cells: tuple[int, int, int, int, int, int, int, int, int, int]
    denominator: int = DENOMINATOR


def parse_families() -> list[Family]:
    families: list[Family] = []
    for path in sorted(CHUNK_DIRECTORY.glob("Chunk*.lean")):
        for line in path.read_text(encoding="utf-8").splitlines():
            match = FAMILY_PATTERN.search(line)
            if match is None:
                continue
            values = tuple(int(value) for value in INTEGER_PATTERN.findall(match.group(1)))
            if len(values) != 16:
                continue
            families.append(Family(*values[:6], values[6:]))
    if len(families) != 38384:
        raise ArithmeticError(f"expected 38384 families, found {len(families)}")
    return families


def floor(value: Fraction) -> int:
    return value.numerator // value.denominator


def ceil(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def a1_bounds(family: Family, a2: int) -> tuple[int, int]:
    base = [0, 2 * a2, 3 * family.a3, 4 * family.a4, 5 * family.a5, 6 * family.a6, 7]
    left = Fraction(-family.a6 - 38, 7)
    right = Fraction(-family.a6 + 38, 7)
    cells = family.root_cells
    roots = tuple(
        RootInterval(Fraction(cells[index], family.denominator),
                     Fraction(cells[index + 1], family.denominator))
        for index in range(0, 10, 2)
    )
    left_range = interval_eval(base, RootInterval(left, left))
    right_range = interval_eval(base, RootInterval(right, right))
    root_ranges = tuple(interval_eval(base, root) for root in roots)
    lower = max(
        ceil(-left_range[1]),
        ceil(-root_ranges[1][1]),
        ceil(-root_ranges[3][1]),
        ceil(-right_range[1]),
    )
    upper = min(
        floor(-root_ranges[0][0]),
        floor(-root_ranges[2][0]),
        floor(-root_ranges[4][0]),
    )
    return lower, upper


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family-limit", type=int)
    parser.add_argument("--progress-every", type=int, default=2000)
    args = parser.parse_args()

    families = parse_families()
    if args.family_limit is not None:
        families = families[: args.family_limit]

    histogram: Counter[int] = Counter()
    a2_count = 0
    a1_count = 0
    empty_count = 0
    widest = 0
    for family_index, family in enumerate(families, start=1):
        for a2 in range(family.a2_lower, family.a2_upper + 1):
            lower, upper = a1_bounds(family, a2)
            count = max(0, upper - lower + 1)
            histogram[count] += 1
            a2_count += 1
            a1_count += count
            empty_count += count == 0
            widest = max(widest, count)
        if args.progress_every and family_index % args.progress_every == 0:
            print(
                f"processed {family_index}/{len(families)} families; "
                f"{a2_count} a2 values; {a1_count} a1 candidates",
                flush=True,
            )

    average = Fraction(a1_count, a2_count) if a2_count else Fraction(0)
    print(f"families: {len(families)}")
    print(f"a2 values: {a2_count}")
    print(f"a1 candidates: {a1_count}")
    print(f"average a1 candidates per a2: {float(average):.6f} ({average})")
    print(f"empty a1 sets: {empty_count}")
    print(f"maximum a1-set size: {widest}")
    print("a1-set size histogram:")
    for size in sorted(histogram):
        print(f"  {size}: {histogram[size]}")


if __name__ == "__main__":
    main()
