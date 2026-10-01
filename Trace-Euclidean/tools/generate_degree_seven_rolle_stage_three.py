#!/usr/bin/env python3
"""Generate the first exact Rolle stage for the degree-seven minimum search.

The exact Hunter reduction gives

    -3 <= a6 <= 0,  -13 <= a5 <= 4,
    2 a5 <= (-a6)^2,  6 (-a6)^2 - 14 a5 < 194.

The normalized fifth derivative is ``21*x^2 + 6*a6*x + a5``.
For each admissible split and separable pair, SymPy only finds rational
isolating intervals.  Lean rechecks every interval and the resulting exact
integer range for ``a4`` using ordinary kernel reduction.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

from sympy import Poly, Rational, symbols


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "lean" / "TraceEuclidean" / "DegreeSevenRolleStageThree.lean"
X = symbols("x")
ROOT_INTERVAL_EPSILON = Rational(1, 2**12)


@dataclass(frozen=True)
class RootInterval:
    lower: Fraction
    upper: Fraction


@dataclass(frozen=True)
class Entry:
    a6: int
    a5: int
    first_root: RootInterval
    second_root: RootInterval
    a4_lower: int
    a4_upper: int


def as_fraction(value: Rational) -> Fraction:
    return Fraction(int(value.p), int(value.q))


def interval_add(
    left: tuple[Fraction, Fraction], right: tuple[Fraction, Fraction]
) -> tuple[Fraction, Fraction]:
    return left[0] + right[0], left[1] + right[1]


def interval_mul(
    left: tuple[Fraction, Fraction], right: tuple[Fraction, Fraction]
) -> tuple[Fraction, Fraction]:
    products = (
        left[0] * right[0],
        left[0] * right[1],
        left[1] * right[0],
        left[1] * right[1],
    )
    return min(products), max(products)


def interval_eval(
    coefficients: list[int], interval: RootInterval
) -> tuple[Fraction, Fraction]:
    result = (Fraction(0), Fraction(0))
    input_interval = (interval.lower, interval.upper)
    for coefficient in reversed(coefficients):
        result = interval_add(
            (Fraction(coefficient), Fraction(coefficient)),
            interval_mul(input_interval, result),
        )
    return result


def fraction_ceil(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def fraction_floor(value: Fraction) -> int:
    return value.numerator // value.denominator


def isolate_two_roots(a6: int, a5: int) -> tuple[RootInterval, RootInterval] | None:
    polynomial = Poly(21 * X**2 + 6 * a6 * X + a5, X, domain="QQ")
    raw_intervals = polynomial.intervals(eps=ROOT_INTERVAL_EPSILON)
    if len(raw_intervals) != 2 or any(
        multiplicity != 1 for _, multiplicity in raw_intervals
    ):
        return None
    intervals: list[RootInterval] = []
    for (lower, upper), _ in raw_intervals:
        lo = as_fraction(lower)
        hi = as_fraction(upper)
        if lo == hi:
            delta = Fraction(1, 2**12)
            lo -= delta
            hi += delta
        intervals.append(RootInterval(lo, hi))
    if not intervals[0].upper < intervals[1].lower:
        raise ArithmeticError("root intervals are not strictly separated")
    return intervals[0], intervals[1]


def candidate_bounds(
    a6: int, a5: int, first: RootInterval, second: RootInterval
) -> tuple[int, int]:
    base = [0, 5 * a5, 15 * a6, 35]
    first_value = interval_eval(base, first)
    second_value = interval_eval(base, second)
    left_value = interval_eval(base, RootInterval(Fraction(-16), Fraction(-16)))
    right_value = interval_eval(base, RootInterval(Fraction(16), Fraction(16)))
    lower = max(-first_value[1], -right_value[1])
    upper = min(-second_value[0], -left_value[0])
    lower_integer = fraction_ceil(lower)
    upper_integer = fraction_floor(upper)
    if lower_integer > upper_integer:
        raise ArithmeticError("empty coefficient interval")
    return lower_integer, upper_integer


def compute_entries() -> list[Entry]:
    entries: list[Entry] = []
    rejected: list[tuple[int, int]] = []
    for a6 in range(-3, 1):
        s1 = -a6
        for a5 in range(-13, 5):
            if 2 * a5 > s1**2:
                continue
            if 6 * s1**2 - 14 * a5 >= 194:
                continue
            roots = isolate_two_roots(a6, a5)
            if roots is None:
                rejected.append((a6, a5))
                continue
            lower, upper = candidate_bounds(a6, a5, roots[0], roots[1])
            entries.append(Entry(a6, a5, roots[0], roots[1], lower, upper))

    expected_rejected = [(-3, 4), (-2, 2), (0, 0)]
    if rejected != expected_rejected:
        raise ArithmeticError(f"unexpected nonsimple quadratics: {rejected}")
    if len(entries) != 54:
        raise ArithmeticError(f"expected 54 entries, found {len(entries)}")
    total = sum(entry.a4_upper - entry.a4_lower + 1 for entry in entries)
    if total != 1641:
        raise ArithmeticError(f"expected 1641 prefixes, found {total}")
    return entries


def lean_int(value: int) -> str:
    return f"({value} : ℤ)"


def lean_rational(value: Fraction) -> str:
    if value.denominator == 1:
        return f"({value.numerator} : ℚ)"
    return f"({value.numerator} : ℚ) / {value.denominator}"


def lean_interval(interval: RootInterval) -> str:
    return f"⟨{lean_rational(interval.lower)}, {lean_rational(interval.upper)}⟩"


def render(entries: list[Entry]) -> str:
    entry_lines = ",\n".join(
        "    ⟨"
        + ", ".join(
            (
                lean_int(entry.a6),
                lean_int(entry.a5),
                lean_interval(entry.first_root),
                lean_interval(entry.second_root),
            )
        )
        + "⟩"
        for entry in entries
    )
    expected_ranges = ",\n".join(
        f"    ({lean_int(entry.a6)}, {lean_int(entry.a5)}, "
        f"{lean_int(entry.a4_lower)}, {lean_int(entry.a4_upper)})"
        for entry in entries
    )
    return f"""import TraceEuclidean.VoightCoefficientPruning

/-!
# Generated degree-seven Rolle certificates: quadratic stage

This file is generated by
`tools/generate_degree_seven_rolle_stage_three.py`.  It contains exact
rational isolating intervals for the two roots of every possible normalized
fifth derivative `21*x^2 + 6*a6*x + a5` below the degree-seven minimum.

All checks use ordinary kernel reduction and exact rational arithmetic.
-/

namespace TraceEuclidean

set_option linter.style.longLine false

structure DegreeSevenStageThreeEntry where
  a6 : ℤ
  a5 : ℤ
  firstRoot : RationalRootInterval
  secondRoot : RationalRootInterval
deriving DecidableEq, Repr

namespace DegreeSevenStageThreeEntry

def derivativeCoefficients (entry : DegreeSevenStageThreeEntry) : List ℤ :=
  [entry.a5, 6 * entry.a6, 21]

def baseCoefficients (entry : DegreeSevenStageThreeEntry) : List ℤ :=
  [0, 5 * entry.a5, 15 * entry.a6, 35]

def rootIntervals (entry : DegreeSevenStageThreeEntry) :
    List RationalRootInterval :=
  [entry.firstRoot, entry.secondRoot]

def Valid (entry : DegreeSevenStageThreeEntry) : Prop :=
  GeneralRationalRootIntervalCertificate.Valid 2
    entry.derivativeCoefficients entry.rootIntervals

def a4Candidates (entry : DegreeSevenStageThreeEntry) : Finset ℤ :=
  cubicTranslationCandidates entry.baseCoefficients
    (-16) 16 entry.firstRoot entry.secondRoot

end DegreeSevenStageThreeEntry

def degreeSevenStageThreeEntries :
    List DegreeSevenStageThreeEntry :=
  [
{entry_lines}
  ]

def degreeSevenStageThreeExpectedRanges :
    List (ℤ × ℤ × ℤ × ℤ) :=
  [
{expected_ranges}
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exact rational root isolation checks for all generated quadratic rows.
theorem degreeSevenStageThreeEntries_valid :
    degreeSevenStageThreeEntries.Forall
      DegreeSevenStageThreeEntry.Valid := by
  norm_num [degreeSevenStageThreeEntries,
    DegreeSevenStageThreeEntry.Valid,
    DegreeSevenStageThreeEntry.derivativeCoefficients,
    DegreeSevenStageThreeEntry.rootIntervals,
    GeneralRationalRootIntervalCertificate.Valid,
    integerPolynomialRationalEval, DensePolynomial.eval]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exact Horner interval evaluation of every next-coefficient range.
theorem degreeSevenStageThreeRanges_checked :
    degreeSevenStageThreeEntries.map (fun entry =>
      (entry.a6, entry.a5,
        cubicTranslationLowerBound entry.baseCoefficients
          entry.firstRoot 16,
        cubicTranslationUpperBound entry.baseCoefficients
          (-16) entry.secondRoot)) =
      degreeSevenStageThreeExpectedRanges := by
  norm_num [degreeSevenStageThreeEntries,
    degreeSevenStageThreeExpectedRanges,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The first exact septic frontier contains 1,641 coefficient prefixes.
theorem degreeSevenStageThree_prefix_count :
    (degreeSevenStageThreeEntries.flatMap fun entry =>
      entry.a4Candidates.toList.map fun a4 =>
        (entry.a6, entry.a5, a4)).length = 1641 := by
  norm_num [degreeSevenStageThreeEntries,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat]

end TraceEuclidean
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if the committed generated file differs",
    )
    args = parser.parse_args()
    content = render(compute_entries())
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text(encoding="utf-8") != content:
            raise SystemExit(f"generated file is stale: {OUTPUT}")
        print(f"checked {OUTPUT}")
        return
    OUTPUT.write_text(content, encoding="utf-8", newline="\n")
    print(f"wrote {OUTPUT}")


if __name__ == "__main__":
    main()
