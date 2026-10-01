#!/usr/bin/env python3
"""Generate exact six-root pilot certificates for the septic final stage."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

from sympy import Poly, symbols

from analyze_degree_seven_stage_six_frontier import a1_bounds
from generate_degree_seven_rolle_stage_six_families import (
    StageFiveRow,
    exact_value,
    fraction_ceil,
    fraction_floor,
    isolated_roots,
    lean_int,
    rational_common_root,
    compute_strong_compact_coverage,
    parse_stage_five_rows,
)
from generate_degree_seven_rolle_stage_six_piecewise import (
    ScaledStageSixFamily,
    audit_family,
    build_scaled_family,
    refine_family_adaptive,
    render_scaled_family,
)
from generate_degree_seven_rolle_stage_three import (
    RootInterval,
    interval_eval,
    lean_rational,
)


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = (
    ROOT
    / "lean"
    / "TraceEuclidean"
    / "DegreeSevenRolleStageSevenPilot.lean"
)
X = symbols("x")


@dataclass(frozen=True)
class StageSevenScaledEntry:
    row: StageFiveRow
    a2: int
    a1: int
    denominator: int
    cells: tuple[
        tuple[int, int],
        tuple[int, int],
        tuple[int, int],
        tuple[int, int],
        tuple[int, int],
        tuple[int, int],
    ]


@dataclass(frozen=True)
class StageSevenMultipleRootWitness:
    row: StageFiveRow
    a2: int
    a1: int
    common_root: Fraction


@dataclass(frozen=True)
class StageSevenCriticalSignWitness:
    parent: ScaledStageSixFamily
    a1: int
    point: int


def sextic(row: StageFiveRow, a2: int, a1: int) -> Poly:
    return Poly(
        7 * X**6
        + 6 * row.a6 * X**5
        + 5 * row.a5 * X**4
        + 4 * row.a4 * X**3
        + 3 * row.a3 * X**2
        + 2 * a2 * X
        + a1,
        X,
        domain="ZZ",
    )


def scaled_root_cell(
    polynomial: Poly, root: RootInterval, denominator: int
) -> tuple[int, int]:
    lower = fraction_floor(root.lower * denominator) - 1
    upper = fraction_ceil(root.upper * denominator) + 1
    for _ in range(512):
        left_value = exact_value(polynomial, Fraction(lower, denominator))
        right_value = exact_value(polynomial, Fraction(upper, denominator))
        if left_value * right_value < 0:
            return lower, upper
        lower -= 1
        upper += 1
    raise ArithmeticError(f"cannot enclose a simple sextic root of {polynomial}")


def build_entry(
    row: StageFiveRow, a2: int, a1: int, precision: int
) -> StageSevenScaledEntry | None:
    polynomial = sextic(row, a2, a1)
    try:
        roots = isolated_roots(polynomial, precision + 8)
    except ArithmeticError:
        return None
    if len(roots) != 6:
        return None
    denominator = 2**precision
    cells = tuple(
        scaled_root_cell(polynomial, root, denominator) for root in roots
    )
    if any(left >= right for left, right in cells):
        raise ArithmeticError("reversed Stage Seven root interval")
    if any(left[1] >= right[0] for left, right in zip(cells, cells[1:])):
        raise ArithmeticError("overlapping Stage Seven root intervals")
    return StageSevenScaledEntry(
        row,
        a2,
        a1,
        denominator,
        cells,  # type: ignore[arg-type]
    )


def a0_bounds(entry: StageSevenScaledEntry) -> tuple[int, int]:
    row = entry.row
    base = [0, entry.a1, entry.a2, row.a3, row.a4, row.a5, row.a6, 1]
    roots = tuple(
        RootInterval(
            Fraction(lower, entry.denominator),
            Fraction(upper, entry.denominator),
        )
        for lower, upper in entry.cells
    )
    left = Fraction(-row.a6 - 38, 7)
    right = Fraction(-row.a6 + 38, 7)
    values = tuple(interval_eval(base, root) for root in roots)
    left_value = interval_eval(base, RootInterval(left, left))
    right_value = interval_eval(base, RootInterval(right, right))
    lower = max(
        fraction_ceil(-values[0][1]),
        fraction_ceil(-values[2][1]),
        fraction_ceil(-values[4][1]),
        fraction_ceil(-right_value[1]),
    )
    upper = min(
        fraction_floor(-left_value[0]),
        fraction_floor(-values[1][0]),
        fraction_floor(-values[3][0]),
        fraction_floor(-values[5][0]),
    )
    return lower, upper


def build_critical_sign_witness(
    row: StageFiveRow, a2: int, a1: int, precision: int
) -> StageSevenCriticalSignWitness | None:
    """Certify a sign pattern incompatible with six simple real roots."""
    parent = build_scaled_family(row, a2, a2, precision + 8)
    coefficients = [
        a1,
        2 * a2,
        3 * row.a3,
        4 * row.a4,
        5 * row.a5,
        6 * row.a6,
        7,
    ]
    for point, (lower, upper) in enumerate(parent.cells):
        value_lower, value_upper = interval_eval(
            coefficients,
            RootInterval(
                Fraction(lower, parent.denominator),
                Fraction(upper, parent.denominator),
            ),
        )
        if point % 2 == 0 and value_lower > 0:
            return StageSevenCriticalSignWitness(parent, a1, point)
        if point % 2 == 1 and value_upper < 0:
            return StageSevenCriticalSignWitness(parent, a1, point)
    return None


def stage_six_pieces(
    rows: list[StageFiveRow], max_a1_per_a2: int, precision: int
) -> list[ScaledStageSixFamily]:
    pieces: list[ScaledStageSixFamily] = []
    for row in rows:
        coverage = compute_strong_compact_coverage(row)
        if coverage.family is not None:
            pieces.extend(
                refine_family_adaptive(
                    coverage.family, max_a1_per_a2, precision
                )
            )
    return pieces


def candidate_tuples(
    pieces: list[ScaledStageSixFamily],
) -> list[tuple[StageFiveRow, int, int]]:
    candidates: list[tuple[StageFiveRow, int, int]] = []
    for piece in pieces:
        audit = audit_family(piece)
        for a2 in range(piece.a2_lower, piece.a2_upper + 1):
            lower, upper = a1_bounds(audit, a2)
            for a1 in range(lower, upper + 1):
                candidates.append((piece.row, a2, a1))
    return candidates


def render_entry(entry: StageSevenScaledEntry) -> str:
    row = entry.row
    values = (
        row.a6,
        row.a5,
        row.a4,
        row.a3,
        entry.a2,
        entry.a1,
        entry.denominator,
        *(value for pair in entry.cells for value in pair),
    )
    return "⟨" + ", ".join(lean_int(value) for value in values) + "⟩"


def render_multiple_root(witness: StageSevenMultipleRootWitness) -> str:
    row = witness.row
    values = (
        lean_int(row.a6),
        lean_int(row.a5),
        lean_int(row.a4),
        lean_int(row.a3),
        lean_int(witness.a2),
        lean_int(witness.a1),
        lean_rational(witness.common_root),
    )
    return "⟨" + ", ".join(values) + "⟩"


def render_critical_sign(witness: StageSevenCriticalSignWitness) -> str:
    point_names = ("first", "second", "third", "fourth", "fifth")
    return (
        "⟨"
        + render_scaled_family(witness.parent)
        + f", {lean_int(witness.parent.a2_lower)}, {lean_int(witness.a1)}, "
        + f".{point_names[witness.point]}⟩"
    )


def render_classification(
    classification: StageSevenScaledEntry
    | StageSevenMultipleRootWitness
    | StageSevenCriticalSignWitness,
) -> str:
    if isinstance(classification, StageSevenScaledEntry):
        return ".scaled " + render_entry(classification)
    if isinstance(classification, StageSevenMultipleRootWitness):
        return ".multipleRoot " + render_multiple_root(classification)
    return ".criticalSign " + render_critical_sign(classification)


def render_critical_sign_definitions() -> str:
    return f"""def degreeSevenStageSevenScaledCriticalSignPilot :
    List DegreeSevenStageSevenScaledCriticalSignWitness :=
  DegreeSevenStageSevenClassification.criticalSigns
    degreeSevenStageSevenClassificationsPilot

set_option maxHeartbeats 0 in
-- Kernel reduction checks every scaled parent and forbidden interval sign.
theorem degreeSevenStageSevenScaledCriticalSignPilot_arithmeticValid :
    degreeSevenStageSevenScaledCriticalSignPilot.Forall
      DegreeSevenStageSevenScaledCriticalSignWitness.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledCriticalSignPilot_valid :
    degreeSevenStageSevenScaledCriticalSignPilot.Forall
      (fun witness => witness.toWitness.Valid) := by
  exact degreeSevenStageSevenScaledCriticalSignPilot_arithmeticValid.imp
    DegreeSevenStageSevenScaledCriticalSignWitness.valid_of_arithmeticValid

def degreeSevenStageSevenCriticalSignPilot :
    List DegreeSevenStageSevenCriticalSignWitness :=
  degreeSevenStageSevenScaledCriticalSignPilot.map
    DegreeSevenStageSevenScaledCriticalSignWitness.toWitness

theorem degreeSevenStageSevenCriticalSignPilot_valid :
    degreeSevenStageSevenCriticalSignPilot.Forall
      DegreeSevenStageSevenCriticalSignWitness.Valid := by
  rw [degreeSevenStageSevenCriticalSignPilot, List.forall_map_iff]
  change degreeSevenStageSevenScaledCriticalSignPilot.Forall
    (fun witness => witness.toWitness.Valid)
  exact degreeSevenStageSevenScaledCriticalSignPilot_valid
"""


def render_pilot(
    classifications: list[
        StageSevenScaledEntry
        | StageSevenMultipleRootWitness
        | StageSevenCriticalSignWitness
    ],
    entries: list[StageSevenScaledEntry],
    multiple_roots: list[StageSevenMultipleRootWitness],
    critical_signs: list[StageSevenCriticalSignWitness],
    dataset_name: str = "Pilot",
) -> str:
    classification_body = ",\n    ".join(
        render_classification(classification)
        for classification in classifications
    )
    critical_sign_definitions = render_critical_sign_definitions()
    all_empty = all(a0_bounds(entry)[0] > a0_bounds(entry)[1] for entry in entries)
    empty_theorem = ""
    if all_empty:
        empty_theorem = """
set_option maxHeartbeats 0 in
-- Kernel reduction checks that the certified final interval is empty.
theorem degreeSevenStageSevenScaledPilot_a0Candidates_empty :
    degreeSevenStageSevenScaledPilot.Forall
      (fun entry => entry.toEntry.a0Candidates = ∅) := by
  norm_num [degreeSevenStageSevenScaledPilot,
    degreeSevenStageSevenClassificationsPilot,
    DegreeSevenStageSevenClassification.scaledEntries,
    DegreeSevenStageSevenEntry.a0Candidates,
    DegreeSevenStageSevenEntry.baseCoefficients,
    DegreeSevenStageSevenEntry.leftEndpoint,
    DegreeSevenStageSevenEntry.rightEndpoint,
    DegreeSevenStageSevenScaledEntry.toEntry,
    DegreeSevenStageSevenScaledEntry.interval,
    septicTranslationCandidates, integerIcc,
    septicTranslationLowerBound, septicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat]
"""
    source = f"""import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge

/-! Pilot data for exact six-root Stage Seven certificates. -/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSevenClassificationsPilot :
    List DegreeSevenStageSevenClassification :=
  [
    {classification_body}
  ]

def degreeSevenStageSevenScaledPilot :
    List DegreeSevenStageSevenScaledEntry :=
  DegreeSevenStageSevenClassification.scaledEntries
    degreeSevenStageSevenClassificationsPilot

def degreeSevenStageSevenMultipleRootPilot :
    List DegreeSevenStageSevenMultipleRootWitness :=
  DegreeSevenStageSevenClassification.multipleRoots
    degreeSevenStageSevenClassificationsPilot

{critical_sign_definitions}

set_option maxHeartbeats 0 in
theorem degreeSevenStageSevenScaledPilot_arithmeticValid :
    degreeSevenStageSevenScaledPilot.Forall
      DegreeSevenStageSevenScaledEntry.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledPilot_valid :
    degreeSevenStageSevenScaledPilot.Forall
      (fun entry => entry.toEntry.Valid) := by
  exact degreeSevenStageSevenScaledPilot_arithmeticValid.imp
    DegreeSevenStageSevenScaledEntry.valid_of_arithmeticValid
{empty_theorem}
theorem degreeSevenStageSevenMultipleRootPilot_valid :
    degreeSevenStageSevenMultipleRootPilot.Forall
      DegreeSevenStageSevenMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageSevenMultipleRootPilot,
    degreeSevenStageSevenClassificationsPilot,
    DegreeSevenStageSevenClassification.multipleRoots,
    DegreeSevenStageSevenMultipleRootWitness.Valid,
    DegreeSevenStageSevenMultipleRootWitness.coefficients,
    integerPolynomialRationalEval,
    DensePolynomial.derivative, DensePolynomial.add,
    DensePolynomial.eval]

theorem degreeSevenStageSevenClassificationsPilot_valid :
    degreeSevenStageSevenClassificationsPilot.Forall
      DegreeSevenStageSevenClassification.Valid := by
  apply DegreeSevenStageSevenClassification.forall_valid_of_projections
  · exact degreeSevenStageSevenScaledPilot_valid
  · exact degreeSevenStageSevenMultipleRootPilot_valid
  · exact degreeSevenStageSevenScaledCriticalSignPilot_valid

/-- Every Hunter candidate matching a certified pilot row has its constant
coefficient in that row's exact final finite set. -/
theorem degreeSevenStageSevenPilot_a0_mem
    {{f : ℤ[X]}} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledPilot)
    (ha6 : entry.a6 = f.coeff 6)
    (ha5 : entry.a5 = f.coeff 5)
    (ha4 : entry.a4 = f.coeff 4)
    (ha3 : entry.a3 = f.coeff 3)
    (ha2 : entry.a2 = f.coeff 2)
    (ha1 : entry.a1 = f.coeff 1) :
    f.coeff 0 ∈ entry.toEntry.a0Candidates := by
  apply degreeSeven_minimumHunterCandidate_a0_mem_of_stageSeven
    h entry.toEntry
  · exact (List.forall_iff_forall_mem.mp
      degreeSevenStageSevenScaledPilot_valid) entry hentry
  · exact ha6
  · exact ha5
  · exact ha4
  · exact ha3
  · exact ha2
  · exact ha1

end

end TraceEuclidean
"""
    return source.replace("Pilot", dataset_name)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--row-start", type=int, default=0)
    parser.add_argument("--row-limit", type=int, default=10)
    parser.add_argument("--max-a1-per-a2", type=int, default=3)
    parser.add_argument("--precision", type=int, default=24)
    parser.add_argument("--dataset-name", default="Pilot")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--write-pilot", action="store_true")
    args = parser.parse_args()
    if args.row_start < 0:
        raise ValueError("--row-start must be nonnegative")
    if args.row_limit <= 0:
        raise ValueError("--row-limit must be positive")
    if args.max_a1_per_a2 <= 0:
        raise ValueError("--max-a1-per-a2 must be positive")
    if args.precision < 16:
        raise ValueError("--precision must be at least 16")
    if not args.dataset_name.isalnum() or not args.dataset_name[0].isalpha():
        raise ValueError("--dataset-name must be a nonempty alphanumeric Lean suffix")

    output = args.output
    if output is None:
        output = OUTPUT if args.dataset_name == "Pilot" else (
            ROOT / "lean" / "TraceEuclidean" /
            f"DegreeSevenRolleStageSeven{args.dataset_name}.lean"
        )
    elif not output.is_absolute():
        output = ROOT / output

    rows = parse_stage_five_rows()[
        args.row_start : args.row_start + args.row_limit
    ]
    pieces = stage_six_pieces(rows, args.max_a1_per_a2, args.precision)
    candidates = candidate_tuples(pieces)
    classifications: list[
        StageSevenScaledEntry
        | StageSevenMultipleRootWitness
        | StageSevenCriticalSignWitness
    ] = []
    entries: list[StageSevenScaledEntry] = []
    multiple_roots: list[StageSevenMultipleRootWitness] = []
    critical_signs: list[StageSevenCriticalSignWitness] = []
    unresolved = 0
    total_a0_candidates = 0
    maximum_a0_candidates = 0
    for row, a2, a1 in candidates:
        entry = build_entry(row, a2, a1, args.precision)
        if entry is None:
            common_root = rational_common_root(sextic(row, a2, a1))
            if common_root is None:
                critical_sign = build_critical_sign_witness(
                    row, a2, a1, args.precision
                )
                if critical_sign is None:
                    unresolved += 1
                else:
                    critical_signs.append(critical_sign)
                    classifications.append(critical_sign)
            else:
                multiple_root = StageSevenMultipleRootWitness(
                    row, a2, a1, common_root
                )
                multiple_roots.append(multiple_root)
                classifications.append(multiple_root)
            continue
        entries.append(entry)
        classifications.append(entry)
        lower, upper = a0_bounds(entry)
        count = max(0, upper - lower + 1)
        total_a0_candidates += count
        maximum_a0_candidates = max(maximum_a0_candidates, count)

    print(f"rows: {len(rows)}")
    print(f"Stage Six pieces: {len(pieces)}")
    print(f"a1 candidates: {len(candidates)}")
    print(f"simple split sextics: {len(entries)}")
    print(f"multiple-root sextics: {len(multiple_roots)}")
    print(f"critical-sign rejections: {len(critical_signs)}")
    print(f"unresolved nonsplit sextics: {unresolved}")
    print(f"a0 candidates: {total_a0_candidates}")
    print(f"maximum a0-set size: {maximum_a0_candidates}")
    if args.write_pilot:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(
            render_pilot(
                classifications,
                entries,
                multiple_roots,
                critical_signs,
                args.dataset_name,
            ),
            encoding="utf-8",
            newline="\n",
        )
        print(f"wrote {output}")


if __name__ == "__main__":
    main()
