#!/usr/bin/env python3
"""Generate parametric root certificates for the sixth septic Rolle stage.

The input is the checked compact Stage Five frontier.  For each row we locate
the maximal integer interval on which the quintic has five simple real roots.
One pair of endpoint quintics then supplies five common dyadic root intervals
for that whole interval.  Values outside it receive either a rational common
root witness or a refined critical-sign witness.  Lean rechecks all arithmetic.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import re

from sympy import Poly, Rational, gcd, symbols

from generate_degree_seven_rolle_stage_three import (
    RootInterval,
    interval_eval,
    lean_int,
)


ROOT = Path(__file__).resolve().parents[1]
STAGE_FIVE_CHUNKS = (
    ROOT / "lean" / "TraceEuclidean" /
    "DegreeSevenRolleStageFiveCertificates"
)
STAGE_FIVE_LINKS = (
    ROOT / "lean" / "TraceEuclidean" /
    "DegreeSevenRolleStageFiveLinks"
)
PRODUCTION_OUTPUT = (
    ROOT / "lean" / "TraceEuclidean" /
    "DegreeSevenRolleStageSixStrongCompactCoverages"
)
COMPLETENESS_OUTPUT = (
    ROOT / "lean" / "TraceEuclidean" /
    "DegreeSevenRolleStageSixStrongCompactCompleteness.lean"
)
PILOT_OUTPUT = (
    ROOT / "lean" / "TraceEuclidean" /
    "DegreeSevenRolleStageSixPilot.lean"
)
STAGE_FIVE_DENOMINATOR = 4096
FAMILY_DENOMINATOR = 2**16
X = symbols("x")

ENTRY_PATTERN = re.compile(
    r"⟨\(([-0-9]+) : ℤ\), \(([-0-9]+) : ℤ\), "
    r"\(([-0-9]+) : ℤ\), \(([-0-9]+) : ℤ\), "
    r"\(([-0-9]+) : ℤ\), \(([-0-9]+) : ℤ\), "
    r"\(([-0-9]+) : ℤ\), \(([-0-9]+) : ℤ\)⟩"
)


@dataclass(frozen=True)
class StageFiveRow:
    a6: int
    a5: int
    a4: int
    a3: int
    cells: tuple[int, int, int, int]


@dataclass(frozen=True)
class StageSixFamily:
    row: StageFiveRow
    a2_lower: int
    a2_upper: int
    cells: tuple[
        tuple[int, int],
        tuple[int, int],
        tuple[int, int],
        tuple[int, int],
        tuple[int, int],
    ]


@dataclass(frozen=True)
class MultipleRootWitness:
    row: StageFiveRow
    a2: int
    common_root: Fraction


@dataclass(frozen=True)
class CriticalSignWitness:
    row: StageFiveRow
    a2: int
    point: int
    refined_roots: tuple[
        RootInterval, RootInterval, RootInterval, RootInterval
    ]


@dataclass(frozen=True)
class RowCoverage:
    row: StageFiveRow
    candidate_lower: int
    candidate_upper: int
    family: StageSixFamily | None
    multiple_roots: tuple[MultipleRootWitness, ...]
    critical_signs: tuple[CriticalSignWitness, ...]


@dataclass(frozen=True)
class LowerBoundary:
    bound: int
    critical: CriticalSignWitness
    multiple: MultipleRootWitness | None


@dataclass(frozen=True)
class UpperBoundary:
    bound: int
    critical: CriticalSignWitness
    multiple: MultipleRootWitness | None


@dataclass(frozen=True)
class StrongCoverage:
    row: StageFiveRow
    lower: LowerBoundary
    upper: UpperBoundary
    family: StageSixFamily | None


@dataclass(frozen=True)
class CompactLowerBoundary:
    bound: int
    critical: CriticalSignWitness
    edge: MultipleRootWitness | CriticalSignWitness | None


@dataclass(frozen=True)
class CompactUpperBoundary:
    bound: int
    critical: CriticalSignWitness
    edge: MultipleRootWitness | CriticalSignWitness | None


@dataclass(frozen=True)
class StrongCompactCoverage:
    row: StageFiveRow
    lower: CompactLowerBoundary
    upper: CompactUpperBoundary
    family: StageSixFamily | None


def as_fraction(value: Rational) -> Fraction:
    return Fraction(int(value.p), int(value.q))


def exact_value(polynomial: Poly, value: Fraction) -> Fraction:
    result = polynomial.eval(Rational(value.numerator, value.denominator))
    return as_fraction(result)


def fraction_floor(value: Fraction) -> int:
    return value.numerator // value.denominator


def fraction_ceil(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def parse_stage_five_rows() -> list[StageFiveRow]:
    rows: list[StageFiveRow] = []
    for path in sorted(STAGE_FIVE_CHUNKS.glob("Chunk*.lean")):
        source = path.read_text(encoding="utf-8")
        for match in ENTRY_PATTERN.finditer(source):
            values = tuple(map(int, match.groups()))
            rows.append(StageFiveRow(*values[:4], values[4:]))
    if len(rows) != 48594:
        raise ArithmeticError(f"expected 48594 Stage Five rows, found {len(rows)}")
    return rows


def parse_stage_five_aligned_lengths() -> list[int]:
    lengths: list[int] = []
    pattern = re.compile(
        r"degreeSevenStageFiveAlignedEntriesChunk\d+\.length = (\d+)"
    )
    for path in sorted(STAGE_FIVE_LINKS.glob("Chunk*.lean")):
        source = path.read_text(encoding="utf-8")
        match = pattern.search(source)
        if match is None:
            raise ArithmeticError(f"missing aligned length in {path}")
        lengths.append(int(match.group(1)))
    if len(lengths) != 66 or sum(lengths) != 48594:
        raise ArithmeticError(
            f"unexpected aligned chunks: {len(lengths)}, total {sum(lengths)}"
        )
    return lengths


def stage_five_interval(cell: int) -> RootInterval:
    return RootInterval(
        Fraction(cell, STAGE_FIVE_DENOMINATOR),
        Fraction(cell + 2, STAGE_FIVE_DENOMINATOR),
    )


def a2_bounds(row: StageFiveRow) -> tuple[int, int]:
    base = [0, 3 * row.a3, 6 * row.a4, 10 * row.a5, 15 * row.a6, 21]
    roots = tuple(stage_five_interval(cell) for cell in row.cells)
    left = Fraction(-row.a6 - 38, 7)
    right = Fraction(-row.a6 + 38, 7)
    samples = (
        interval_eval(base, RootInterval(left, left)),
        *(interval_eval(base, root) for root in roots),
        interval_eval(base, RootInterval(right, right)),
    )
    lower = max(fraction_ceil(-samples[index][1]) for index in (1, 3, 5))
    upper = min(fraction_floor(-samples[index][0]) for index in (0, 2, 4))
    return lower, upper


def quintic(row: StageFiveRow, a2: int) -> Poly:
    return Poly(
        21 * X**5
        + 15 * row.a6 * X**4
        + 10 * row.a5 * X**3
        + 6 * row.a4 * X**2
        + 3 * row.a3 * X
        + a2,
        X,
        domain="QQ",
    )


def quartic(row: StageFiveRow) -> Poly:
    return Poly(
        35 * X**4
        + 20 * row.a6 * X**3
        + 10 * row.a5 * X**2
        + 4 * row.a4 * X
        + row.a3,
        X,
        domain="QQ",
    )


@lru_cache(maxsize=4096)
def isolated_quartic_roots(
    row: StageFiveRow, precision: int
) -> tuple[RootInterval, ...]:
    return isolated_roots(quartic(row), precision)


def isolated_roots(polynomial: Poly, precision: int) -> tuple[RootInterval, ...]:
    raw = polynomial.intervals(eps=Rational(1, 2**precision))
    roots: list[RootInterval] = []
    for (lower, upper), multiplicity in raw:
        if multiplicity != 1:
            raise ArithmeticError(f"non-simple interval for {polynomial}")
        lo = as_fraction(lower)
        hi = as_fraction(upper)
        if lo == hi:
            delta = Fraction(1, 2**precision)
            lo -= delta
            hi += delta
        roots.append(RootInterval(lo, hi))
    return tuple(roots)


def dyadic_quartic_roots(
    row: StageFiveRow, precision: int
) -> tuple[RootInterval, RootInterval, RootInterval, RootInterval]:
    """Enclose the four critical points by uniform dyadic intervals."""
    denominator = 2**precision
    polynomial = quartic(row)
    roots = isolated_quartic_roots(row, precision + 4)
    result: list[RootInterval] = []
    for root in roots:
        lower_cell = fraction_floor(root.lower * denominator) - 1
        upper_cell = fraction_ceil(root.upper * denominator) + 1
        for _ in range(32):
            lower = Fraction(lower_cell, denominator)
            upper = Fraction(upper_cell, denominator)
            left = exact_value(polynomial, lower)
            right = exact_value(polynomial, upper)
            if left * right < 0:
                result.append(RootInterval(lower, upper))
                break
            if left == 0 or left * right > 0:
                lower_cell -= 1
            if right == 0 or left * right > 0:
                upper_cell += 1
        else:
            raise ArithmeticError(f"cannot form dyadic quartic interval: {row}")
    if len(result) != 4:
        raise ArithmeticError(f"quartic does not have four dyadic roots: {row}")
    if any(left.upper >= right.lower for left, right in zip(result, result[1:])):
        raise ArithmeticError(f"overlapping dyadic quartic intervals: {row}")
    return tuple(result)  # type: ignore[return-value]


def rational_common_root(polynomial: Poly) -> Fraction | None:
    common = gcd(polynomial, polynomial.diff())
    if common.degree() <= 0:
        return None
    roots = common.all_roots()
    rational = [root for root in roots if bool(root.is_Rational)]
    if not rational:
        raise ArithmeticError(f"non-rational common root for {polynomial}: {common}")
    return as_fraction(rational[0])


def is_simple_real_split(polynomial: Poly) -> bool:
    intervals = polynomial.intervals()
    return len(intervals) == 5 and all(
        multiplicity == 1 for _, multiplicity in intervals
    )


def critical_sign_witness(
    row: StageFiveRow, a2: int
) -> CriticalSignWitness:
    coefficients = [a2, 3 * row.a3, 6 * row.a4, 10 * row.a5, 15 * row.a6, 21]
    derivative = quartic(row)
    last_ranges: list[tuple[Fraction, Fraction]] = []
    for precision in (16, 20, 24, 32, 40, 56, 72):
        roots = isolated_quartic_roots(row, precision)
        if len(roots) != 4:
            raise ArithmeticError(f"quartic does not have four roots: {derivative}")
        ranges = [interval_eval(coefficients, root) for root in roots]
        contradictory = [
            index
            for index, value_range in enumerate(ranges)
            if (index in (0, 2) and value_range[1] < 0)
            or (index in (1, 3) and 0 < value_range[0])
        ]
        if contradictory:
            return CriticalSignWitness(
                row, a2, contradictory[0], roots  # type: ignore[arg-type]
            )
        last_ranges = ranges
    raise ArithmeticError(
        f"no critical-sign contradiction for {row}, a2={a2}: {last_ranges}"
    )


def directional_critical_sign_witness(
    row: StageFiveRow, a2: int, lower_side: bool
) -> CriticalSignWitness:
    coefficients = [a2, 3 * row.a3, 6 * row.a4, 10 * row.a5, 15 * row.a6, 21]
    last_ranges: list[tuple[Fraction, Fraction]] = []
    for precision in (16, 20, 24, 32, 40, 56, 72):
        roots = isolated_quartic_roots(row, precision)
        ranges = [interval_eval(coefficients, root) for root in roots]
        points = (
            [index for index in (0, 2) if ranges[index][1] < 0]
            if lower_side
            else [index for index in (1, 3) if 0 < ranges[index][0]]
        )
        if points:
            return CriticalSignWitness(
                row, a2, points[0], roots  # type: ignore[arg-type]
            )
        last_ranges = ranges
    side = "lower" if lower_side else "upper"
    raise ArithmeticError(
        f"no {side} critical-sign contradiction for {row}, a2={a2}: "
        f"{last_ranges}"
    )


def classify_rejected(
    row: StageFiveRow, a2: int
) -> MultipleRootWitness | CriticalSignWitness | None:
    polynomial = quintic(row, a2)
    common_root = rational_common_root(polynomial)
    if common_root is not None:
        return MultipleRootWitness(row, a2, common_root)
    if is_simple_real_split(polynomial):
        return None
    return critical_sign_witness(row, a2)


def critical_point_signs(row: StageFiveRow, a2: int) -> tuple[int, int, int, int]:
    """Return the exact signs of the quintic at its four critical points."""
    polynomial = quintic(row, a2)
    common = gcd(polynomial, polynomial.diff())
    common_roots = [
        as_fraction(root) for root in common.all_roots()
        if bool(root.is_Rational)
    ] if common.degree() > 0 else []
    coefficients = [a2, 3 * row.a3, 6 * row.a4, 10 * row.a5, 15 * row.a6, 21]
    last_ranges: list[tuple[Fraction, Fraction]] = []
    for precision in (16, 20, 24, 32, 40, 56, 72):
        roots = isolated_quartic_roots(row, precision)
        ranges = [interval_eval(coefficients, root) for root in roots]
        signs: list[int | None] = []
        for root, value_range in zip(roots, ranges):
            if any(root.lower <= value <= root.upper for value in common_roots):
                signs.append(0)
            elif value_range[1] < 0:
                signs.append(-1)
            elif 0 < value_range[0]:
                signs.append(1)
            else:
                signs.append(None)
        if all(sign is not None for sign in signs):
            return tuple(signs)  # type: ignore[return-value]
        last_ranges = ranges
    raise ArithmeticError(
        f"undecided critical signs for {row}, a2={a2}: {last_ranges}"
    )


def exact_surviving_bounds(row: StageFiveRow) -> tuple[int, int]:
    """Find the exact integer interval satisfying the four strict signs."""
    candidate_lower, candidate_upper = a2_bounds(row)
    lower = candidate_lower - 2
    for _ in range(64):
        signs = critical_point_signs(row, lower)
        if 0 < signs[0] and 0 < signs[2]:
            break
        lower += 1
    else:
        raise ArithmeticError(f"lower boundary search failed for {row}")
    while True:
        previous = critical_point_signs(row, lower - 1)
        if not (0 < previous[0] and 0 < previous[2]):
            break
        lower -= 1

    upper = candidate_upper + 2
    for _ in range(64):
        signs = critical_point_signs(row, upper)
        if signs[1] < 0 and signs[3] < 0:
            break
        upper -= 1
    else:
        raise ArithmeticError(f"upper boundary search failed for {row}")
    while True:
        following = critical_point_signs(row, upper + 1)
        if not (following[1] < 0 and following[3] < 0):
            break
        upper += 1
    return lower, upper


def paired_critical_witnesses(
    row: StageFiveRow, lower_a2: int, upper_a2: int
) -> tuple[CriticalSignWitness, CriticalSignWitness]:
    lower_coefficients = [
        lower_a2, 3 * row.a3, 6 * row.a4, 10 * row.a5, 15 * row.a6, 21
    ]
    upper_coefficients = [
        upper_a2, 3 * row.a3, 6 * row.a4, 10 * row.a5, 15 * row.a6, 21
    ]
    for precision in (16, 20, 24, 28, 32, 40, 56):
        roots = dyadic_quartic_roots(row, precision)
        lower_ranges = [interval_eval(lower_coefficients, root) for root in roots]
        upper_ranges = [interval_eval(upper_coefficients, root) for root in roots]
        lower_points = [index for index in (0, 2) if lower_ranges[index][1] < 0]
        upper_points = [index for index in (1, 3) if 0 < upper_ranges[index][0]]
        if lower_points and upper_points:
            refined = roots  # type: ignore[assignment]
            return (
                CriticalSignWitness(row, lower_a2, lower_points[0], refined),
                CriticalSignWitness(row, upper_a2, upper_points[0], refined),
            )
    raise ArithmeticError(f"cannot certify both half-line boundaries for {row}")


def compute_strong_coverage(row: StageFiveRow) -> StrongCoverage:
    lower, upper = exact_surviving_bounds(row)
    lower_multiple_root = rational_common_root(quintic(row, lower - 1))
    upper_multiple_root = rational_common_root(quintic(row, upper + 1))
    lower_multiple = (
        None if lower_multiple_root is None
        else MultipleRootWitness(row, lower - 1, lower_multiple_root)
    )
    upper_multiple = (
        None if upper_multiple_root is None
        else MultipleRootWitness(row, upper + 1, upper_multiple_root)
    )
    lower_critical_a2 = lower - (2 if lower_multiple is not None else 1)
    upper_critical_a2 = upper + (2 if upper_multiple is not None else 1)
    lower_critical, upper_critical = paired_critical_witnesses(
        row, lower_critical_a2, upper_critical_a2
    )
    family = build_family(row, lower, upper) if lower <= upper else None
    return StrongCoverage(
        row,
        LowerBoundary(lower, lower_critical, lower_multiple),
        UpperBoundary(upper, upper_critical, upper_multiple),
        family,
    )


def coarse_critical_witness(
    row: StageFiveRow, a2: int, lower_side: bool
) -> CriticalSignWitness | None:
    roots = tuple(stage_five_interval(cell) for cell in row.cells)
    coefficients = [a2, 3 * row.a3, 6 * row.a4, 10 * row.a5, 15 * row.a6, 21]
    ranges = [interval_eval(coefficients, root) for root in roots]
    points = (
        [index for index in (0, 2) if ranges[index][1] < 0]
        if lower_side
        else [index for index in (1, 3) if 0 < ranges[index][0]]
    )
    if not points:
        return None
    return CriticalSignWitness(
        row, a2, points[0], roots  # type: ignore[arg-type]
    )


def compact_boundary(
    row: StageFiveRow, bound: int, lower_side: bool
) -> CompactLowerBoundary | CompactUpperBoundary:
    edge_a2 = bound - 1 if lower_side else bound + 1
    common_root = rational_common_root(quintic(row, edge_a2))
    edge: MultipleRootWitness | CriticalSignWitness | None
    if common_root is not None:
        edge = MultipleRootWitness(row, edge_a2, common_root)
        critical_a2 = edge_a2 - 1 if lower_side else edge_a2 + 1
    else:
        coarse_edge = coarse_critical_witness(row, edge_a2, lower_side)
        if coarse_edge is not None:
            edge = None
            critical_a2 = edge_a2
        else:
            edge = directional_critical_sign_witness(
                row, edge_a2, lower_side
            )
            critical_a2 = edge_a2 - 1 if lower_side else edge_a2 + 1
    critical = coarse_critical_witness(row, critical_a2, lower_side)
    if critical is None:
        raise ArithmeticError(f"coarse half-line sign failed: {row}, {bound}")
    if lower_side:
        return CompactLowerBoundary(bound, critical, edge)
    return CompactUpperBoundary(bound, critical, edge)


def compute_strong_compact_coverage(row: StageFiveRow) -> StrongCompactCoverage:
    lower, upper = exact_surviving_bounds(row)
    lower_boundary = compact_boundary(row, lower, True)
    upper_boundary = compact_boundary(row, upper, False)
    if not isinstance(lower_boundary, CompactLowerBoundary):
        raise TypeError("expected compact lower boundary")
    if not isinstance(upper_boundary, CompactUpperBoundary):
        raise TypeError("expected compact upper boundary")
    family = build_family(row, lower, upper) if lower <= upper else None
    return StrongCompactCoverage(
        row, lower_boundary, upper_boundary, family
    )


def cell_before_root(polynomial: Poly, root: RootInterval, sign: int) -> int:
    cell = fraction_floor(root.lower * FAMILY_DENOMINATOR) - 1
    for _ in range(256):
        value = exact_value(polynomial, Fraction(cell, FAMILY_DENOMINATOR))
        if (sign < 0 and value < 0) or (0 < sign and 0 < value):
            return cell
        cell -= 1
    raise ArithmeticError(f"cannot find left dyadic endpoint for {polynomial}")


def cell_after_root(polynomial: Poly, root: RootInterval, sign: int) -> int:
    cell = fraction_ceil(root.upper * FAMILY_DENOMINATOR) + 1
    for _ in range(256):
        value = exact_value(polynomial, Fraction(cell, FAMILY_DENOMINATOR))
        if (sign < 0 and value < 0) or (0 < sign and 0 < value):
            return cell
        cell += 1
    raise ArithmeticError(f"cannot find right dyadic endpoint for {polynomial}")


def dyadic_numerator(row: StageFiveRow, a2: int, cell: int) -> int:
    denominator = FAMILY_DENOMINATOR
    return (
        a2 * denominator**5
        + (3 * row.a3) * cell * denominator**4
        + (6 * row.a4) * cell**2 * denominator**3
        + (10 * row.a5) * cell**3 * denominator**2
        + (15 * row.a6) * cell**4 * denominator
        + 21 * cell**5
    )


def verify_family(family: StageSixFamily) -> None:
    pairs = family.cells
    if family.a2_upper < family.a2_lower:
        raise ArithmeticError(f"reversed family: {family}")
    if any(upper <= lower for lower, upper in pairs):
        raise ArithmeticError(f"reversed root interval: {family}")
    if any(left[1] >= right[0] for left, right in zip(pairs, pairs[1:])):
        raise ArithmeticError(f"overlapping root intervals: {family}")
    for index, (lower, upper) in enumerate(pairs):
        if index % 2 == 0:
            left = dyadic_numerator(family.row, family.a2_upper, lower)
            right = dyadic_numerator(family.row, family.a2_lower, upper)
            valid = left < 0 < right
        else:
            left = dyadic_numerator(family.row, family.a2_lower, lower)
            right = dyadic_numerator(family.row, family.a2_upper, upper)
            valid = right < 0 < left
        if not valid:
            raise ArithmeticError(f"invalid uniform signs at root {index}: {family}")


def build_family(row: StageFiveRow, lower: int, upper: int) -> StageSixFamily:
    lower_polynomial = quintic(row, lower)
    upper_polynomial = quintic(row, upper)
    lower_roots = isolated_roots(lower_polynomial, 24)
    upper_roots = isolated_roots(upper_polynomial, 24)
    if len(lower_roots) != 5 or len(upper_roots) != 5:
        raise ArithmeticError(f"family endpoint is not simple split: {row}")
    cells: list[tuple[int, int]] = []
    for index in range(5):
        if index % 2 == 0:
            left = cell_before_root(upper_polynomial, upper_roots[index], -1)
            right = cell_after_root(lower_polynomial, lower_roots[index], 1)
        else:
            left = cell_before_root(lower_polynomial, lower_roots[index], 1)
            right = cell_after_root(upper_polynomial, upper_roots[index], -1)
        cells.append((left, right))
    family = StageSixFamily(row, lower, upper, tuple(cells))  # type: ignore[arg-type]
    verify_family(family)
    return family


def compute_coverage(row: StageFiveRow) -> RowCoverage:
    candidate_lower, candidate_upper = a2_bounds(row)
    rejected: dict[int, MultipleRootWitness | CriticalSignWitness] = {}
    lower = candidate_lower
    while lower <= candidate_upper:
        classification = classify_rejected(row, lower)
        if classification is None:
            break
        rejected[lower] = classification
        lower += 1
    if candidate_upper < lower:
        family = None
    else:
        upper = candidate_upper
        while lower <= upper:
            classification = classify_rejected(row, upper)
            if classification is None:
                break
            rejected[upper] = classification
            upper -= 1
        family = build_family(row, lower, upper)
    multiples = tuple(
        witness for _, witness in sorted(rejected.items())
        if isinstance(witness, MultipleRootWitness)
    )
    critical = tuple(
        witness for _, witness in sorted(rejected.items())
        if isinstance(witness, CriticalSignWitness)
    )
    covered = (0 if family is None else family.a2_upper - family.a2_lower + 1)
    covered += len(multiples) + len(critical)
    expected = max(0, candidate_upper - candidate_lower + 1)
    if covered != expected:
        raise ArithmeticError(
            f"coverage mismatch for {row}: {covered} != {expected}"
        )
    return RowCoverage(
        row, candidate_lower, candidate_upper, family, multiples, critical
    )


def lean_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return f"({lean_int(value.numerator)} : ℚ)"
    return (
        f"(({lean_int(value.numerator)} : ℚ) / "
        f"({value.denominator} : ℚ))"
    )


def lean_root_interval(interval: RootInterval) -> str:
    return f"⟨{lean_fraction(interval.lower)}, {lean_fraction(interval.upper)}⟩"


def render_family(family: StageSixFamily) -> str:
    values = (
        family.row.a6,
        family.row.a5,
        family.row.a4,
        family.row.a3,
        family.a2_lower,
        family.a2_upper,
        *(value for pair in family.cells for value in pair),
    )
    return "⟨" + ", ".join(lean_int(value) for value in values) + "⟩"


def render_parent(row: StageFiveRow) -> str:
    values = (row.a6, row.a5, row.a4, row.a3, *row.cells)
    return "⟨" + ", ".join(lean_int(value) for value in values) + "⟩"


def render_multiple(witness: MultipleRootWitness) -> str:
    values = (
        witness.row.a6,
        witness.row.a5,
        witness.row.a4,
        witness.row.a3,
        witness.a2,
    )
    return (
        "⟨" + ", ".join(lean_int(value) for value in values) + ", "
        + lean_fraction(witness.common_root) + "⟩"
    )


def render_critical(witness: CriticalSignWitness) -> str:
    point = (".first", ".second", ".third", ".fourth")[witness.point]
    parent_values = (
        lean_int(witness.row.a6),
        lean_int(witness.row.a5),
        lean_int(witness.row.a4),
        lean_int(witness.row.a3),
        *(lean_root_interval(root) for root in witness.refined_roots),
    )
    parent = "⟨" + ", ".join(parent_values) + "⟩"
    return f"⟨{parent}, {lean_int(witness.a2)}, {point}⟩"


def render_rejection(
    witness: MultipleRootWitness | CriticalSignWitness,
) -> str:
    if isinstance(witness, MultipleRootWitness):
        return f".multipleRoot {render_multiple(witness)}"
    return f".criticalSign {render_critical(witness)}"


def render_coverage(coverage: RowCoverage) -> str:
    family = (
        "none" if coverage.family is None
        else f"some {render_family(coverage.family)}"
    )
    rejections = sorted(
        (*coverage.multiple_roots, *coverage.critical_signs),
        key=lambda witness: witness.a2,
    )
    rejection_source = ", ".join(render_rejection(w) for w in rejections)
    return (
        f"⟨{render_parent(coverage.row)}, "
        f"{lean_int(coverage.candidate_lower)}, "
        f"{lean_int(coverage.candidate_upper)}, "
        f"{family}, [{rejection_source}]⟩"
    )


def render_lower_boundary(boundary: LowerBoundary) -> str:
    multiple = (
        "none" if boundary.multiple is None
        else f"some {render_multiple(boundary.multiple)}"
    )
    return (
        f"⟨{lean_int(boundary.bound)}, {render_critical(boundary.critical)}, "
        f"{multiple}⟩"
    )


def render_upper_boundary(boundary: UpperBoundary) -> str:
    multiple = (
        "none" if boundary.multiple is None
        else f"some {render_multiple(boundary.multiple)}"
    )
    return (
        f"⟨{lean_int(boundary.bound)}, {render_critical(boundary.critical)}, "
        f"{multiple}⟩"
    )


def render_strong_coverage(coverage: StrongCoverage) -> str:
    family = (
        "none" if coverage.family is None
        else f"some {render_family(coverage.family)}"
    )
    return (
        f"⟨{render_parent(coverage.row)}, "
        f"{render_lower_boundary(coverage.lower)}, "
        f"{render_upper_boundary(coverage.upper)}, {family}⟩"
    )


def render_coarse_critical(witness: CriticalSignWitness) -> str:
    point = (".first", ".second", ".third", ".fourth")[witness.point]
    return f"⟨{lean_int(witness.a2)}, {point}⟩"


@lru_cache(maxsize=None)
def scaled_refined_roots(
    witness: CriticalSignWitness,
) -> tuple[int, tuple[tuple[int, int], ...]]:
    """Replace arbitrary refined endpoints by checked dyadic endpoints.

    The interval is rounded outwards and then rechecked exactly.  Increasing
    the common power-of-two denominator preserves the original strict signs
    once the rounding error is small enough.
    """

    derivative = [
        witness.row.a3,
        4 * witness.row.a4,
        10 * witness.row.a5,
        20 * witness.row.a6,
        35,
    ]
    critical = [
        witness.a2,
        3 * witness.row.a3,
        6 * witness.row.a4,
        10 * witness.row.a5,
        15 * witness.row.a6,
        21,
    ]
    for exponent in range(12, 81):
        denominator = 1 << exponent
        endpoints: list[tuple[int, int]] = []
        for root in witness.refined_roots:
            lower = (root.lower.numerator * denominator) // root.lower.denominator
            upper = -(
                (-root.upper.numerator * denominator) // root.upper.denominator
            )
            endpoints.append((lower, upper))
        if any(lower >= upper for lower, upper in endpoints):
            continue
        if any(
            endpoints[index][1] >= endpoints[index + 1][0]
            for index in range(3)
        ):
            continue
        intervals = tuple(
            RootInterval(Fraction(lower, denominator), Fraction(upper, denominator))
            for lower, upper in endpoints
        )
        if any(
            interval_eval(derivative, interval)[0]
            * interval_eval(derivative, interval)[1] >= 0
            for interval in intervals
        ):
            continue
        selected_range = interval_eval(critical, intervals[witness.point])
        if witness.point in (0, 2):
            if selected_range[1] >= 0:
                continue
        elif selected_range[0] <= 0:
            continue
        return denominator, tuple(endpoints)
    raise ArithmeticError(
        "could not find a common dyadic refinement for "
        f"{witness.row} at a2={witness.a2}"
    )


def render_refined_compact_critical(witness: CriticalSignWitness) -> str:
    point = (".first", ".second", ".third", ".fourth")[witness.point]
    denominator, endpoints = scaled_refined_roots(witness)
    roots = ", ".join(
        [lean_int(denominator)]
        + [lean_int(value) for interval in endpoints for value in interval]
    )
    return f"⟨{lean_int(witness.a2)}, {point}, ⟨{roots}⟩⟩"


def render_compact_edge(
    edge: MultipleRootWitness | CriticalSignWitness | None,
) -> str:
    if edge is None:
        return "none"
    if isinstance(edge, MultipleRootWitness):
        return f"some (.multipleRoot {render_multiple(edge)})"
    return f"some (.criticalSign {render_refined_compact_critical(edge)})"


def render_compact_lower_boundary(boundary: CompactLowerBoundary) -> str:
    return (
        f"⟨{lean_int(boundary.bound)}, {render_coarse_critical(boundary.critical)}, "
        f"{render_compact_edge(boundary.edge)}⟩"
    )


def render_compact_upper_boundary(boundary: CompactUpperBoundary) -> str:
    return (
        f"⟨{lean_int(boundary.bound)}, {render_coarse_critical(boundary.critical)}, "
        f"{render_compact_edge(boundary.edge)}⟩"
    )


def render_strong_compact_coverage(coverage: StrongCompactCoverage) -> str:
    family = (
        "none" if coverage.family is None
        else f"some {render_family(coverage.family)}"
    )
    return (
        f"⟨{render_parent(coverage.row)}, "
        f"{render_compact_lower_boundary(coverage.lower)}, "
        f"{render_compact_upper_boundary(coverage.upper)}, {family}⟩"
    )


def render_strong_compact_pilot(
    coverages: list[StrongCompactCoverage],
) -> str:
    coverage_source = ",\n".join(
        f"    {render_strong_compact_coverage(coverage)}"
        for coverage in coverages
    )
    return f"""import TraceEuclidean.DegreeSevenRolleStageSixStrongCompact

/-! Generated pilot certificates for compact strong sixth-stage coverage. -/

namespace TraceEuclidean

noncomputable section

def degreeSevenStageSixStrongCompactPilotCoverages :
    List DegreeSevenStageSixStrongCompactCoverage :=
  [
{coverage_source}
  ]

def degreeSevenStageSixStrongCompactPilotEdges :
    List DegreeSevenStageSixMultipleRootWitness :=
  degreeSevenStageSixStrongCompactPilotCoverages.flatMap
    DegreeSevenStageSixStrongCompactCoverage.edgeRejections

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeSevenStageSixStrongCompactPilotSkeletons_valid :
    degreeSevenStageSixStrongCompactPilotCoverages.Forall
      DegreeSevenStageSixStrongCompactCoverage.SkeletonValid := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeSevenStageSixStrongCompactPilotEdges_valid :
    degreeSevenStageSixStrongCompactPilotEdges.Forall
      DegreeSevenStageSixMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageSixStrongCompactPilotEdges,
    degreeSevenStageSixStrongCompactPilotCoverages,
    DegreeSevenStageSixStrongCompactCoverage.edgeRejections,
    DegreeSevenStageSixCompactLowerBoundary.edgeRejections,
    DegreeSevenStageSixCompactUpperBoundary.edgeRejections,
    DegreeSevenStageSixCompactRejection.exactWitnesses,
    DegreeSevenStageSixMultipleRootWitness.Valid,
    DegreeSevenStageSixMultipleRootWitness.coefficients,
    integerPolynomialRationalEval,
    DensePolynomial.derivative,
    DensePolynomial.add,
    DensePolynomial.eval]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeSevenStageSixStrongCompactPilotCoverages_valid :
    degreeSevenStageSixStrongCompactPilotCoverages.Forall
      DegreeSevenStageSixStrongCompactCoverage.Valid := by
  apply List.Forall.imp
    DegreeSevenStageSixStrongCompactCoverage.valid_of_arithmeticValid
  apply
    DegreeSevenStageSixStrongCompactCoverage.list_forall_arithmeticValid_of_skeletons_and_edges
  · exact degreeSevenStageSixStrongCompactPilotSkeletons_valid
  · exact degreeSevenStageSixStrongCompactPilotEdges_valid

end

end TraceEuclidean
"""


def render_strong_compact_chunk(
    chunk_index: int, coverages: list[StrongCompactCoverage]
) -> str:
    suffix = f"{chunk_index:03d}"
    coverage_batches = [
        coverages[index:index + 256]
        for index in range(0, len(coverages), 256)
    ]
    if not coverage_batches:
        coverage_batches = [[]]
    coverage_part_names: list[str] = []
    coverage_part_valid_names: list[str] = []
    coverage_part_blocks: list[str] = []
    for part_index, coverage_batch in enumerate(coverage_batches):
        part_suffix = f"{part_index:03d}"
        part_name = (
            f"degreeSevenStageSixStrongCompactCoveragesChunk{suffix}Part{part_suffix}"
        )
        valid_name = (
            f"degreeSevenStageSixStrongCompactSkeletonsChunk{suffix}Part{part_suffix}_valid"
        )
        coverage_part_names.append(part_name)
        coverage_part_valid_names.append(valid_name)
        part_source = ",\n".join(
            f"    {render_strong_compact_coverage(coverage)}"
            for coverage in coverage_batch
        )
        coverage_part_blocks.append(f"""def {part_name} :
    List DegreeSevenStageSixStrongCompactCoverage :=
  [
{part_source}
  ]

set_option maxHeartbeats 0 in
theorem {valid_name} :
    {part_name}.Forall
      DegreeSevenStageSixStrongCompactCoverage.SkeletonValid := by
  decide
""")
    coverage_part_source = "\n".join(coverage_part_blocks)
    coverage_parts_expression = " ++\n      ".join(coverage_part_names)
    coverage_valid_expression = coverage_part_valid_names[0]
    for valid_name in coverage_part_valid_names[1:]:
        coverage_valid_expression = f"⟨{coverage_valid_expression}, {valid_name}⟩"
    edges = [
        boundary.edge
        for coverage in coverages
        for boundary in (coverage.lower, coverage.upper)
        if isinstance(boundary.edge, MultipleRootWitness)
    ]
    # Keep each arithmetic proof small.  One aligned Stage Five chunk can
    # contain several hundred exceptional edges, and a single `norm_num`
    # call then exceeds the simplifier step limit and retains too much state.
    edge_batches = [edges[index:index + 64] for index in range(0, len(edges), 64)]
    if not edge_batches:
        edge_batches = [[]]
    edge_part_names: list[str] = []
    edge_part_valid_names: list[str] = []
    edge_part_blocks: list[str] = []
    for part_index, edge_batch in enumerate(edge_batches):
        part_suffix = f"{part_index:03d}"
        part_name = (
            f"degreeSevenStageSixStrongCompactEdgesChunk{suffix}Part{part_suffix}"
        )
        valid_name = (
            f"degreeSevenStageSixStrongCompactEdgesChunk{suffix}Part{part_suffix}_valid"
        )
        edge_part_names.append(part_name)
        edge_part_valid_names.append(valid_name)
        part_source = ",\n".join(
            f"    {render_multiple(edge)}" for edge in edge_batch
        )
        edge_part_blocks.append(f"""def {part_name} :
    List DegreeSevenStageSixMultipleRootWitness :=
  [
{part_source}
  ]

set_option maxHeartbeats 0 in
theorem {valid_name} :
    {part_name}.Forall
      DegreeSevenStageSixMultipleRootWitness.Valid := by
  norm_num (config := {{ maxSteps := 1000000 }}) [{part_name},
    DegreeSevenStageSixMultipleRootWitness.Valid,
    DegreeSevenStageSixMultipleRootWitness.coefficients,
    integerPolynomialRationalEval,
    DensePolynomial.derivative,
    DensePolynomial.add,
    DensePolynomial.eval]
""")
    edge_part_source = "\n".join(edge_part_blocks)
    edge_parts_expression = " ++\n      ".join(edge_part_names)
    edge_valid_expression = edge_part_valid_names[0]
    for valid_name in edge_part_valid_names[1:]:
        edge_valid_expression = f"⟨{edge_valid_expression}, {valid_name}⟩"
    return f"""import TraceEuclidean.DegreeSevenRolleStageSixStrongCompact
import TraceEuclidean.DegreeSevenRolleStageFiveLinks.Chunk{suffix}

/-! Generated compact strong sixth-stage coverages, Chunk{suffix}. -/

namespace TraceEuclidean

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

{coverage_part_source}
def degreeSevenStageSixStrongCompactCoveragesChunk{suffix} :
    List DegreeSevenStageSixStrongCompactCoverage :=
  {coverage_parts_expression}

{edge_part_source}
def degreeSevenStageSixStrongCompactEdgesChunk{suffix} :
    List DegreeSevenStageSixMultipleRootWitness :=
  {edge_parts_expression}

set_option maxHeartbeats 0 in
theorem degreeSevenStageSixStrongCompactEdgesChunk{suffix}_checked :
    degreeSevenStageSixStrongCompactCoveragesChunk{suffix}.flatMap
        DegreeSevenStageSixStrongCompactCoverage.edgeRejections =
      degreeSevenStageSixStrongCompactEdgesChunk{suffix} := by
  rfl

set_option maxHeartbeats 0 in
theorem degreeSevenStageSixStrongCompactSkeletonsChunk{suffix}_valid :
    degreeSevenStageSixStrongCompactCoveragesChunk{suffix}.Forall
      DegreeSevenStageSixStrongCompactCoverage.SkeletonValid := by
  simp only [degreeSevenStageSixStrongCompactCoveragesChunk{suffix},
    List.forall_append]
  exact {coverage_valid_expression}

set_option maxHeartbeats 0 in
theorem degreeSevenStageSixStrongCompactEdgesChunk{suffix}_valid :
    degreeSevenStageSixStrongCompactEdgesChunk{suffix}.Forall
      DegreeSevenStageSixMultipleRootWitness.Valid := by
  simp only [degreeSevenStageSixStrongCompactEdgesChunk{suffix},
    List.forall_append]
  exact {edge_valid_expression}

set_option maxHeartbeats 0 in
theorem degreeSevenStageSixStrongCompactCoveragesChunk{suffix}_valid :
    degreeSevenStageSixStrongCompactCoveragesChunk{suffix}.Forall
      DegreeSevenStageSixStrongCompactCoverage.Valid := by
  apply List.Forall.imp
    DegreeSevenStageSixStrongCompactCoverage.valid_of_arithmeticValid
  apply
    DegreeSevenStageSixStrongCompactCoverage.list_forall_arithmeticValid_of_skeletons_and_edges
  · exact degreeSevenStageSixStrongCompactSkeletonsChunk{suffix}_valid
  · rw [degreeSevenStageSixStrongCompactEdgesChunk{suffix}_checked]
    exact degreeSevenStageSixStrongCompactEdgesChunk{suffix}_valid

set_option maxHeartbeats 0 in
theorem degreeSevenStageSixStrongCompactCoveragesChunk{suffix}_parents :
    degreeSevenStageSixStrongCompactCoveragesChunk{suffix}.map
        DegreeSevenStageSixStrongCompactCoverage.parent =
      degreeSevenStageFiveAlignedEntriesChunk{suffix} := by
  rfl

end

end TraceEuclidean
"""


def write_strong_compact_production(
    coverages: list[StrongCompactCoverage], chunk_limit: int | None = None
) -> None:
    lengths = parse_stage_five_aligned_lengths()
    if chunk_limit is not None:
        lengths = lengths[:chunk_limit]
    expected = sum(lengths)
    if len(coverages) != expected:
        raise ArithmeticError(
            f"production rows {len(coverages)} do not match requested total {expected}"
        )
    PRODUCTION_OUTPUT.mkdir(parents=True, exist_ok=True)
    offset = 0
    for chunk_index, length in enumerate(lengths):
        chunk = coverages[offset:offset + length]
        output = PRODUCTION_OUTPUT / f"Chunk{chunk_index:03d}.lean"
        output.write_text(
            render_strong_compact_chunk(chunk_index, chunk),
            encoding="utf-8",
            newline="\n",
        )
        print(f"wrote {output} ({length} rows)", flush=True)
        offset += length
    if len(lengths) == 66:
        COMPLETENESS_OUTPUT.write_text(
            render_strong_compact_completeness(len(lengths)),
            encoding="utf-8",
            newline="\n",
        )
        print(f"wrote {COMPLETENESS_OUTPUT}", flush=True)


def render_strong_compact_completeness(chunk_count: int) -> str:
    suffixes = [f"{index:03d}" for index in range(chunk_count)]
    imports = "\n".join(
        "import TraceEuclidean."
        f"DegreeSevenRolleStageSixStrongCompactCoverages.Chunk{suffix}"
        for suffix in suffixes
    )
    coverage_expression = " ++\n    ".join(
        f"degreeSevenStageSixStrongCompactCoveragesChunk{suffix}"
        for suffix in suffixes
    )
    valid_names = [
        f"degreeSevenStageSixStrongCompactCoveragesChunk{suffix}_valid"
        for suffix in suffixes
    ]
    valid_expression = valid_names[0]
    for valid_name in valid_names[1:]:
        valid_expression = f"⟨{valid_expression}, {valid_name}⟩"
    parent_names = ",\n    ".join(
        f"degreeSevenStageSixStrongCompactCoveragesChunk{suffix}_parents"
        for suffix in suffixes
    )
    return f"""import TraceEuclidean.DegreeSevenRolleStageFiveCompleteness
{imports}

/-! Complete root-isolated sixth-stage coverage for degree seven. -/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def degreeSevenStageSixStrongCompactCoverages :
    List DegreeSevenStageSixStrongCompactCoverage :=
  {coverage_expression}

theorem degreeSevenStageSixStrongCompactCoverages_valid :
    degreeSevenStageSixStrongCompactCoverages.Forall
      DegreeSevenStageSixStrongCompactCoverage.Valid := by
  simp only [degreeSevenStageSixStrongCompactCoverages,
    List.forall_append]
  exact {valid_expression}

theorem degreeSevenStageSixStrongCompactCoverages_parents :
    degreeSevenStageSixStrongCompactCoverages.map
        DegreeSevenStageSixStrongCompactCoverage.parent =
      degreeSevenStageFiveEntries := by
  simp only [degreeSevenStageSixStrongCompactCoverages,
    degreeSevenStageFiveEntries, List.map_append,
    {parent_names}]

theorem degreeSevenStageSixStrongCompactCoverage_count :
    degreeSevenStageSixStrongCompactCoverages.length = 48594 := by
  have hlength := congrArg List.length
    degreeSevenStageSixStrongCompactCoverages_parents
  simpa [degreeSevenStageFive_entry_count] using hlength

/-- Every sharpened septic Hunter candidate belongs to a certified parametric
Stage Six family.  This stronger form also retains the four fixed top
coefficients needed by later refinements of the `a2` interval. -/
theorem degreeSeven_minimumHunterCandidate_stageSix_complete_with_top
    {{f : ℤ[X]}} (h : HunterPolynomialCandidate 7 194 f) :
    ∃ coverage ∈ degreeSevenStageSixStrongCompactCoverages,
      coverage.parent.a6 = f.coeff 6 ∧
      coverage.parent.a5 = f.coeff 5 ∧
      coverage.parent.a4 = f.coeff 4 ∧
      coverage.parent.a3 = f.coeff 3 ∧
      ∃ family,
        coverage.family = some family ∧
        f.coeff 2 ∈ family.toFamily.a2Candidates ∧
        f.coeff 1 ∈
          (family.toFamily.toEntry (f.coeff 2)).a1Candidates := by
  obtain ⟨entry, hentry, ha6, ha5, ha4, ha3⟩ :=
    degreeSeven_minimumHunterCandidate_stageFive_complete h
  have hentryMap :
      entry ∈ degreeSevenStageSixStrongCompactCoverages.map
        DegreeSevenStageSixStrongCompactCoverage.parent := by
    rw [degreeSevenStageSixStrongCompactCoverages_parents]
    exact hentry
  obtain ⟨coverage, hcoverage, hparent⟩ := List.mem_map.mp hentryMap
  have hvalid : coverage.Valid :=
    (List.forall_iff_forall_mem.mp
      degreeSevenStageSixStrongCompactCoverages_valid) coverage hcoverage
  have ha6' : coverage.parent.a6 = f.coeff 6 := by rw [hparent]; exact ha6
  have ha5' : coverage.parent.a5 = f.coeff 5 := by rw [hparent]; exact ha5
  have ha4' : coverage.parent.a4 = f.coeff 4 := by rw [hparent]; exact ha4
  have ha3' : coverage.parent.a3 = f.coeff 3 := by rw [hparent]; exact ha3
  obtain ⟨family, hfamily, ha2, ha1⟩ :=
    coverage.hunter_a1_mem h hvalid ha6' ha5' ha4' ha3'
  exact ⟨coverage, hcoverage, ha6', ha5', ha4', ha3',
    family, hfamily, ha2, ha1⟩

/-- Every sharpened septic Hunter candidate belongs to a certified parametric
Stage Six family, including its exact `a1` root-isolated candidate list. -/
theorem degreeSeven_minimumHunterCandidate_stageSix_complete
    {{f : ℤ[X]}} (h : HunterPolynomialCandidate 7 194 f) :
    ∃ coverage ∈ degreeSevenStageSixStrongCompactCoverages,
      ∃ family,
        coverage.family = some family ∧
        f.coeff 2 ∈ family.toFamily.a2Candidates ∧
        f.coeff 1 ∈
          (family.toFamily.toEntry (f.coeff 2)).a1Candidates := by
  obtain ⟨coverage, hcoverage, _, _, _, _, family, hfamily, ha2, ha1⟩ :=
    degreeSeven_minimumHunterCandidate_stageSix_complete_with_top h
  exact ⟨coverage, hcoverage, family, hfamily, ha2, ha1⟩

end

end TraceEuclidean
"""


def render_strong_pilot(coverages: list[StrongCoverage]) -> str:
    coverage_source = ",\n".join(
        f"    {render_strong_coverage(coverage)}" for coverage in coverages
    )
    return f"""import TraceEuclidean.DegreeSevenRolleStageSixStrongCoverage

/-! Generated pilot certificates for strong parametric sixth-stage coverage. -/

namespace TraceEuclidean

noncomputable section

def degreeSevenStageSixStrongPilotCoverages :
    List DegreeSevenStageSixStrongCoverage :=
  [
{coverage_source}
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeSevenStageSixStrongPilotCoverages_valid :
    degreeSevenStageSixStrongPilotCoverages.Forall
      DegreeSevenStageSixStrongCoverage.Valid := by
  apply List.Forall.imp
    DegreeSevenStageSixStrongCoverage.valid_of_arithmeticValid
  norm_decide

end

end TraceEuclidean
"""


def render_pilot(coverages: list[RowCoverage]) -> str:
    families = [coverage.family for coverage in coverages if coverage.family]
    multiples = [w for coverage in coverages for w in coverage.multiple_roots]
    critical = [w for coverage in coverages for w in coverage.critical_signs]
    family_source = ",\n".join(f"    {render_family(f)}" for f in families)
    multiple_source = ",\n".join(f"    {render_multiple(w)}" for w in multiples)
    critical_source = ",\n".join(f"    {render_critical(w)}" for w in critical)
    coverage_source = ",\n".join(
        f"    {render_coverage(coverage)}" for coverage in coverages
    )
    return f"""import TraceEuclidean.DegreeSevenRolleStageSixCoverage

/-! Generated pilot certificates for the parametric sixth Rolle stage. -/

namespace TraceEuclidean

noncomputable section

def degreeSevenStageSixPilotFamilies :
    List DegreeSevenStageSixDyadicFamily :=
  [
{family_source}
  ]

def degreeSevenStageSixPilotMultipleRootWitnesses :
    List DegreeSevenStageSixMultipleRootWitness :=
  [
{multiple_source}
  ]

def degreeSevenStageSixPilotCriticalSignWitnesses :
    List DegreeSevenStageSixCriticalSignWitness :=
  [
{critical_source}
  ]

def degreeSevenStageSixPilotCoverages :
    List DegreeSevenStageSixCoverage :=
  [
{coverage_source}
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeSevenStageSixPilotFamilies_valid :
    degreeSevenStageSixPilotFamilies.Forall
      DegreeSevenStageSixDyadicFamily.Valid := by
  apply List.Forall.imp
    DegreeSevenStageSixDyadicFamily.valid_of_arithmeticValid
  norm_num [degreeSevenStageSixPilotFamilies,
    DegreeSevenStageSixDyadicFamily.ArithmeticValid,
    DegreeSevenStageSixDyadicFamily.dyadicNumerator]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeSevenStageSixPilotMultipleRootWitnesses_valid :
    degreeSevenStageSixPilotMultipleRootWitnesses.Forall
      DegreeSevenStageSixMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageSixPilotMultipleRootWitnesses,
    DegreeSevenStageSixMultipleRootWitness.Valid,
    DegreeSevenStageSixMultipleRootWitness.coefficients,
    DensePolynomial.derivative, DensePolynomial.add,
    integerPolynomialRationalEval, DensePolynomial.eval]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeSevenStageSixPilotCriticalSignWitnesses_valid :
    degreeSevenStageSixPilotCriticalSignWitnesses.Forall
      DegreeSevenStageSixCriticalSignWitness.Valid := by
  norm_num [degreeSevenStageSixPilotCriticalSignWitnesses,
    DegreeSevenStageSixCriticalSignWitness.Valid,
    DegreeSevenStageSixCriticalSignWitness.criticalValueRange,
    DegreeSevenStageSixCriticalSignWitness.coefficients,
    DegreeSevenStageSixCriticalPoint.interval,
    DegreeSevenStageFiveEntry.Valid,
    DegreeSevenStageFiveEntry.derivativeCoefficients,
    DegreeSevenStageFiveEntry.rootIntervals,
    GeneralRationalRootIntervalCertificate.Valid,
    integerPolynomialRationalEval,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4,
    DensePolynomial.eval, min_def, max_def]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeSevenStageSixPilotCoverages_valid :
    degreeSevenStageSixPilotCoverages.Forall
      DegreeSevenStageSixCoverage.Valid := by
  apply List.Forall.imp
    DegreeSevenStageSixCoverage.valid_of_arithmeticValid
  norm_num [degreeSevenStageSixPilotCoverages,
    DegreeSevenStageSixCoverage.ArithmeticValid,
    DegreeSevenStageSixCoverage.FamilySameTop,
    DegreeSevenStageSixCoverage.coveredA2,
    DegreeSevenStageSixCoverage.familyA2,
    DegreeSevenStageSixCoverage.rejectedA2,
    DegreeSevenStageSixCoverage.computedLower,
    DegreeSevenStageSixCoverage.computedUpper,
    DegreeSevenStageSixRejection.Valid,
    DegreeSevenStageSixRejection.SameTop,
    DegreeSevenStageSixRejection.a2,
    DegreeSevenStageSixDyadicFamily.ArithmeticValid,
    DegreeSevenStageSixDyadicFamily.dyadicNumerator,
    DegreeSevenStageSixDyadicFamily.toFamily,
    DegreeSevenStageSixFamily.a2Candidates,
    DegreeSevenStageSixMultipleRootWitness.Valid,
    DegreeSevenStageSixMultipleRootWitness.coefficients,
    DegreeSevenStageSixCriticalSignWitness.Valid,
    DegreeSevenStageSixCriticalSignWitness.criticalValueRange,
    DegreeSevenStageSixCriticalSignWitness.coefficients,
    DegreeSevenStageSixCriticalPoint.interval,
    DegreeSevenStageFiveDyadicEntry.ArithmeticValid,
    DegreeSevenStageFiveDyadicEntry.dyadicNumerator,
    DegreeSevenStageFiveDyadicEntry.a2Candidates,
    DegreeSevenStageFiveDyadicEntry.toEntry,
    degreeSevenStageFiveDyadicInterval,
    degreeSevenStageFiveDyadicDenominator,
    DegreeSevenStageFiveEntry.a2Candidates,
    DegreeSevenStageFiveEntry.baseCoefficients,
    DegreeSevenStageFiveEntry.leftEndpoint,
    DegreeSevenStageFiveEntry.rightEndpoint,
    DegreeSevenStageFiveEntry.Valid,
    DegreeSevenStageFiveEntry.derivativeCoefficients,
    DegreeSevenStageFiveEntry.rootIntervals,
    GeneralRationalRootIntervalCertificate.Valid,
    quinticTranslationCandidates,
    quinticTranslationLowerBound,
    quinticTranslationUpperBound,
    integerIcc,
    integerPolynomialRationalEval,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4,
    DensePolynomial.derivative,
    DensePolynomial.add,
    DensePolynomial.eval, min_def, max_def]

end

end TraceEuclidean
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int)
    parser.add_argument("--write-pilot", action="store_true")
    parser.add_argument("--strong", action="store_true")
    parser.add_argument("--write-strong-pilot", action="store_true")
    parser.add_argument("--compact", action="store_true")
    parser.add_argument("--write-compact-pilot", action="store_true")
    parser.add_argument("--write-production", action="store_true")
    parser.add_argument("--production-chunks", type=int)
    args = parser.parse_args()
    rows = parse_stage_five_rows()
    if args.production_chunks is not None:
        lengths = parse_stage_five_aligned_lengths()
        if not 1 <= args.production_chunks <= len(lengths):
            raise ValueError("--production-chunks must be between 1 and 66")
        rows = rows[:sum(lengths[:args.production_chunks])]
    elif args.limit is not None:
        rows = rows[: args.limit]
    if args.compact or args.write_compact_pilot or args.write_production:
        compact_coverages: list[StrongCompactCoverage] = []
        for index, row in enumerate(rows, start=1):
            compact_coverages.append(compute_strong_compact_coverage(row))
            if index % 1000 == 0:
                print(f"processed {index}/{len(rows)}", flush=True)
        families = [
            coverage.family for coverage in compact_coverages
            if coverage.family is not None
        ]
        family_values = sum(
            family.a2_upper - family.a2_lower + 1 for family in families
        )
        multiple_edges = sum(
            isinstance(boundary.edge, MultipleRootWitness)
            for coverage in compact_coverages
            for boundary in (coverage.lower, coverage.upper)
        )
        critical_edges = sum(
            isinstance(boundary.edge, CriticalSignWitness)
            for coverage in compact_coverages
            for boundary in (coverage.lower, coverage.upper)
        )
        print(
            "compact-strong-stage-six:",
            len(rows),
            "rows,",
            len(families),
            "families covering",
            family_values,
            "values,",
            multiple_edges,
            "multiple-root edges,",
            critical_edges,
            "refined critical edges",
        )
        if args.write_compact_pilot:
            PILOT_OUTPUT.write_text(
                render_strong_compact_pilot(compact_coverages),
                encoding="utf-8",
                newline="\n",
            )
            print(f"wrote {PILOT_OUTPUT}")
        if args.write_production:
            write_strong_compact_production(
                compact_coverages, args.production_chunks
            )
        return

    if args.strong or args.write_strong_pilot:
        strong_coverages: list[StrongCoverage] = []
        for index, row in enumerate(rows, start=1):
            strong_coverages.append(compute_strong_coverage(row))
            if index % 1000 == 0:
                print(f"processed {index}/{len(rows)}", flush=True)
        families = [
            coverage.family for coverage in strong_coverages
            if coverage.family is not None
        ]
        family_values = sum(
            family.a2_upper - family.a2_lower + 1 for family in families
        )
        lower_multiples = sum(
            coverage.lower.multiple is not None for coverage in strong_coverages
        )
        upper_multiples = sum(
            coverage.upper.multiple is not None for coverage in strong_coverages
        )
        print(
            "strong-stage-six:",
            len(rows),
            "rows,",
            len(families),
            "families covering",
            family_values,
            "values,",
            lower_multiples,
            "lower multiple boundaries,",
            upper_multiples,
            "upper multiple boundaries",
        )
        if args.write_strong_pilot:
            PILOT_OUTPUT.write_text(
                render_strong_pilot(strong_coverages),
                encoding="utf-8",
                newline="\n",
            )
            print(f"wrote {PILOT_OUTPUT}")
        return

    coverages: list[RowCoverage] = []
    for index, row in enumerate(rows, start=1):
        coverages.append(compute_coverage(row))
        if index % 1000 == 0:
            print(f"processed {index}/{len(rows)}", flush=True)
    families = [coverage.family for coverage in coverages if coverage.family]
    multiples = [w for coverage in coverages for w in coverage.multiple_roots]
    critical = [w for coverage in coverages for w in coverage.critical_signs]
    candidates = sum(
        max(0, coverage.candidate_upper - coverage.candidate_lower + 1)
        for coverage in coverages
    )
    family_values = sum(
        family.a2_upper - family.a2_lower + 1 for family in families
    )
    print(
        "stage-six:",
        len(rows),
        "rows,",
        candidates,
        "candidate a2 values,",
        len(families),
        "families covering",
        family_values,
        "values,",
        len(multiples),
        "multiple-root,",
        len(critical),
        "critical-sign",
    )
    if family_values + len(multiples) + len(critical) != candidates:
        raise ArithmeticError("global Stage Six coverage mismatch")
    if args.write_pilot:
        PILOT_OUTPUT.write_text(render_pilot(coverages), encoding="utf-8", newline="\n")
        print(f"wrote {PILOT_OUTPUT}")


if __name__ == "__main__":
    main()
