#!/usr/bin/env python3
"""Generate pilot piecewise refinements of the septic Stage Six frontier."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

from analyze_degree_seven_stage_six_frontier import Family as AuditFamily
from analyze_degree_seven_stage_six_frontier import a1_bounds
from generate_degree_seven_rolle_stage_six_families import (
    StageSixFamily,
    StageFiveRow,
    StrongCompactCoverage,
    exact_value,
    fraction_ceil,
    fraction_floor,
    isolated_roots,
    lean_int,
    quintic,
    build_family,
    compute_strong_compact_coverage,
    parse_stage_five_rows,
    render_family,
    render_strong_compact_coverage,
)


ROOT = Path(__file__).resolve().parents[1]
PILOT_OUTPUT = (
    ROOT
    / "lean"
    / "TraceEuclidean"
    / "DegreeSevenRolleStageSixPiecewisePilot.lean"
)


@dataclass(frozen=True)
class ScaledStageSixFamily:
    row: StageFiveRow
    a2_lower: int
    a2_upper: int
    denominator: int
    cells: tuple[
        tuple[int, int],
        tuple[int, int],
        tuple[int, int],
        tuple[int, int],
        tuple[int, int],
    ]


def scaled_numerator(
    family: ScaledStageSixFamily, a2: int, cell: int
) -> int:
    denominator = family.denominator
    row = family.row
    return (
        a2 * denominator**5
        + (3 * row.a3) * cell * denominator**4
        + (6 * row.a4) * cell**2 * denominator**3
        + (10 * row.a5) * cell**3 * denominator**2
        + (15 * row.a6) * cell**4 * denominator
        + 21 * cell**5
    )


def scaled_cell_before_root(polynomial, root, sign: int, denominator: int) -> int:
    cell = fraction_floor(root.lower * denominator) - 1
    for _ in range(256):
        value = exact_value(polynomial, Fraction(cell, denominator))
        if (sign < 0 and value < 0) or (0 < sign and 0 < value):
            return cell
        cell -= 1
    raise ArithmeticError(f"cannot find scaled left endpoint for {polynomial}")


def scaled_cell_after_root(polynomial, root, sign: int, denominator: int) -> int:
    cell = fraction_ceil(root.upper * denominator) + 1
    for _ in range(256):
        value = exact_value(polynomial, Fraction(cell, denominator))
        if (sign < 0 and value < 0) or (0 < sign and 0 < value):
            return cell
        cell += 1
    raise ArithmeticError(f"cannot find scaled right endpoint for {polynomial}")


def build_scaled_family(
    row: StageFiveRow, lower: int, upper: int, precision: int
) -> ScaledStageSixFamily:
    denominator = 2**precision
    lower_polynomial = quintic(row, lower)
    upper_polynomial = quintic(row, upper)
    lower_roots = isolated_roots(lower_polynomial, precision + 8)
    upper_roots = isolated_roots(upper_polynomial, precision + 8)
    if len(lower_roots) != 5 or len(upper_roots) != 5:
        raise ArithmeticError(f"scaled family endpoint is not simple split: {row}")
    cells: list[tuple[int, int]] = []
    for index in range(5):
        if index % 2 == 0:
            left = scaled_cell_before_root(
                upper_polynomial, upper_roots[index], -1, denominator
            )
            right = scaled_cell_after_root(
                lower_polynomial, lower_roots[index], 1, denominator
            )
        else:
            left = scaled_cell_before_root(
                lower_polynomial, lower_roots[index], 1, denominator
            )
            right = scaled_cell_after_root(
                upper_polynomial, upper_roots[index], -1, denominator
            )
        cells.append((left, right))
    family = ScaledStageSixFamily(
        row, lower, upper, denominator, tuple(cells)  # type: ignore[arg-type]
    )
    if any(right <= left for left, right in family.cells):
        raise ArithmeticError(f"reversed scaled root interval: {family}")
    if any(left[1] >= right[0] for left, right in zip(family.cells, family.cells[1:])):
        raise ArithmeticError(f"overlapping scaled root intervals: {family}")
    for index, (left, right) in enumerate(family.cells):
        if index % 2 == 0:
            valid = (
                scaled_numerator(family, upper, left) < 0
                < scaled_numerator(family, lower, right)
            )
        else:
            valid = (
                scaled_numerator(family, upper, right) < 0
                < scaled_numerator(family, lower, left)
            )
        if not valid:
            raise ArithmeticError(f"invalid scaled uniform sign: {family}, root {index}")
    return family


def refine_family(
    family: StageSixFamily, segment_width: int, precision: int
) -> list[ScaledStageSixFamily]:
    pieces: list[ScaledStageSixFamily] = []
    lower = family.a2_lower
    while lower <= family.a2_upper:
        upper = min(family.a2_upper, lower + segment_width - 1)
        pieces.append(build_scaled_family(family.row, lower, upper, precision))
        lower = upper + 1
    return pieces


def family_candidate_statistics(
    family: StageSixFamily | ScaledStageSixFamily,
) -> tuple[int, int]:
    audit = audit_family(family)
    total = 0
    maximum = 0
    for a2 in range(family.a2_lower, family.a2_upper + 1):
        lower, upper = a1_bounds(audit, a2)
        count = max(0, upper - lower + 1)
        total += count
        maximum = max(maximum, count)
    return total, maximum


def refine_family_adaptive(
    family: StageSixFamily, max_a1_per_a2: int, precision: int
) -> list[ScaledStageSixFamily]:
    """Use the longest consecutive segments meeting the requested a1 width."""
    pieces: list[ScaledStageSixFamily] = []
    lower = family.a2_lower
    while lower <= family.a2_upper:
        singleton = build_scaled_family(family.row, lower, lower, precision)
        if family_candidate_statistics(singleton)[1] > max_a1_per_a2:
            pieces.append(singleton)
            lower += 1
            continue
        best = singleton
        search_lower = lower + 1
        search_upper = family.a2_upper
        while search_lower <= search_upper:
            middle = (search_lower + search_upper) // 2
            candidate = build_scaled_family(family.row, lower, middle, precision)
            if family_candidate_statistics(candidate)[1] <= max_a1_per_a2:
                best = candidate
                search_lower = middle + 1
            else:
                search_upper = middle - 1
        pieces.append(best)
        lower = best.a2_upper + 1
    return pieces


def audit_family(family: StageSixFamily | ScaledStageSixFamily) -> AuditFamily:
    return AuditFamily(
        family.row.a6,
        family.row.a5,
        family.row.a4,
        family.row.a3,
        family.a2_lower,
        family.a2_upper,
        tuple(value for pair in family.cells for value in pair),
        getattr(family, "denominator", 65536),
    )


def candidate_count(family: StageSixFamily | ScaledStageSixFamily) -> int:
    return family_candidate_statistics(family)[0]


def render_scaled_family(family: ScaledStageSixFamily) -> str:
    values = (
        family.row.a6,
        family.row.a5,
        family.row.a4,
        family.row.a3,
        family.a2_lower,
        family.a2_upper,
        family.denominator,
        *(value for pair in family.cells for value in pair),
    )
    return "⟨" + ", ".join(lean_int(value) for value in values) + "⟩"


def render_scaled_a1_bound_certificates(
    refinements: list[tuple[StrongCompactCoverage, list[ScaledStageSixFamily]]],
) -> str:
    """Render kernel-reducible bounds for every refined family and a2."""
    certificates = []
    certificate_index = 0
    for _coverage, pieces in refinements:
        for piece in pieces:
            audit = audit_family(piece)
            rendered_piece = render_scaled_family(piece)
            for a2 in range(piece.a2_lower, piece.a2_upper + 1):
                lower, upper = a1_bounds(audit, a2)
                certificates.append(
                    "@[simp] theorem "
                    "degreeSevenStageSixPiecewisePilotA1LowerBound"
                    f"{certificate_index:03d} :\n"
                    "    let family : DegreeSevenStageSixScaledFamily :=\n"
                    f"      {rendered_piece}\n"
                    "    family.scaledA1LowerBound "
                    f"{lean_int(a2)} = {lean_int(lower)} := by\n"
                    "  rfl"
                )
                certificates.append(
                    "@[simp] theorem "
                    "degreeSevenStageSixPiecewisePilotA1UpperBound"
                    f"{certificate_index:03d} :\n"
                    "    let family : DegreeSevenStageSixScaledFamily :=\n"
                    f"      {rendered_piece}\n"
                    "    family.scaledA1UpperBound "
                    f"{lean_int(a2)} = {lean_int(upper)} := by\n"
                    "  rfl"
                )
                certificate_index += 1
    return "\n\n".join(certificates)


def render_pilot(
    refinements: list[tuple[StrongCompactCoverage, list[ScaledStageSixFamily]]],
    dataset_name: str = "Pilot",
) -> str:
    records = []
    for coverage, pieces in refinements:
        rendered_pieces = ",\n        ".join(
            render_scaled_family(piece) for piece in pieces
        )
        records.append(
            f"⟨{render_strong_compact_coverage(coverage)},\n"
            f"      [{rendered_pieces}]⟩"
        )
    body = ",\n    ".join(records)
    bound_certificates = render_scaled_a1_bound_certificates(refinements)
    source = f"""import TraceEuclidean.DegreeSevenRolleStageSixPiecewise
import TraceEuclidean.DegreeSevenRolleStageSixScaledCandidates

/-! Pilot data for piecewise Stage Six parameter refinement. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def degreeSevenStageSixPiecewisePilot :
    List DegreeSevenStageSixPiecewiseCoverage :=
  [
    {body}
  ]

{bound_certificates}

def degreeSevenStageSixPiecewisePilotCoarseCoverages :
    List DegreeSevenStageSixStrongCompactCoverage :=
  degreeSevenStageSixPiecewisePilot.map
    DegreeSevenStageSixPiecewiseCoverage.coverage

def degreeSevenStageSixPiecewisePilotEdges :
    List DegreeSevenStageSixMultipleRootWitness :=
  degreeSevenStageSixPiecewisePilotCoarseCoverages.flatMap
    DegreeSevenStageSixStrongCompactCoverage.edgeRejections

theorem degreeSevenStageSixPiecewisePilotSkeletons_valid :
    degreeSevenStageSixPiecewisePilotCoarseCoverages.Forall
      DegreeSevenStageSixStrongCompactCoverage.SkeletonValid := by
  decide

theorem degreeSevenStageSixPiecewisePilotEdges_valid :
    degreeSevenStageSixPiecewisePilotEdges.Forall
      DegreeSevenStageSixMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageSixPiecewisePilotEdges,
    degreeSevenStageSixPiecewisePilotCoarseCoverages,
    degreeSevenStageSixPiecewisePilot,
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

theorem degreeSevenStageSixPiecewisePilotCoarseCoverages_valid :
    degreeSevenStageSixPiecewisePilotCoarseCoverages.Forall
      DegreeSevenStageSixStrongCompactCoverage.Valid := by
  apply List.Forall.imp
    DegreeSevenStageSixStrongCompactCoverage.valid_of_arithmeticValid
  apply
    DegreeSevenStageSixStrongCompactCoverage.list_forall_arithmeticValid_of_skeletons_and_edges
  · exact degreeSevenStageSixPiecewisePilotSkeletons_valid
  · exact degreeSevenStageSixPiecewisePilotEdges_valid

theorem degreeSevenStageSixPiecewisePilotPieces_valid :
    degreeSevenStageSixPiecewisePilot.Forall
      DegreeSevenStageSixPiecewiseCoverage.PiecesValid := by
  decide

theorem degreeSevenStageSixPiecewisePilot_valid :
    degreeSevenStageSixPiecewisePilot.Forall
      DegreeSevenStageSixPiecewiseCoverage.Valid := by
  apply DegreeSevenStageSixPiecewiseCoverage.list_forall_valid_of_parts
  · exact degreeSevenStageSixPiecewisePilotCoarseCoverages_valid
  · exact degreeSevenStageSixPiecewisePilotPieces_valid

end

end TraceEuclidean
"""
    return source.replace("Pilot", dataset_name)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--row-start", type=int, default=0)
    parser.add_argument("--limit", type=int, default=10)
    parser.add_argument("--segment-width", type=int, default=1)
    parser.add_argument("--max-a1-per-a2", type=int)
    parser.add_argument("--precision", type=int, default=24)
    parser.add_argument("--progress-every", type=int, default=100)
    parser.add_argument("--dataset-name", default="Pilot")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--write-pilot", action="store_true")
    args = parser.parse_args()
    if args.row_start < 0:
        raise ValueError("--row-start must be nonnegative")
    if args.limit <= 0:
        raise ValueError("--limit must be positive")
    if args.segment_width <= 0:
        raise ValueError("--segment-width must be positive")
    if args.max_a1_per_a2 is not None and args.max_a1_per_a2 <= 0:
        raise ValueError("--max-a1-per-a2 must be positive")
    if args.precision < 16:
        raise ValueError("--precision must be at least 16")
    if not args.dataset_name.isalnum() or not args.dataset_name[0].isalpha():
        raise ValueError("--dataset-name must be a nonempty alphanumeric Lean suffix")

    output = args.output
    if output is None:
        output = PILOT_OUTPUT if args.dataset_name == "Pilot" else (
            ROOT / "lean" / "TraceEuclidean" /
            f"DegreeSevenRolleStageSixPiecewise{args.dataset_name}.lean"
        )
    elif not output.is_absolute():
        output = ROOT / output

    rows = parse_stage_five_rows()[
        args.row_start : args.row_start + args.limit
    ]
    refinements: list[tuple[StrongCompactCoverage, list[ScaledStageSixFamily]]] = []
    coarse_count = 0
    refined_count = 0
    a2_count = 0
    piece_count = 0
    for index, row in enumerate(rows, start=1):
        coverage = compute_strong_compact_coverage(row)
        pieces = [] if coverage.family is None else (
            refine_family_adaptive(
                coverage.family, args.max_a1_per_a2, args.precision
            )
            if args.max_a1_per_a2 is not None
            else refine_family(
                coverage.family, args.segment_width, args.precision
            )
        )
        refinements.append((coverage, pieces))
        if coverage.family is not None:
            coarse_count += candidate_count(coverage.family)
            refined_count += sum(candidate_count(piece) for piece in pieces)
            a2_count += coverage.family.a2_upper - coverage.family.a2_lower + 1
            piece_count += len(pieces)
        if args.progress_every and index % args.progress_every == 0:
            print(f"processed {index}/{len(rows)}", flush=True)

    print(f"rows: {len(rows)}")
    print(f"a2 values: {a2_count}")
    print(f"pieces: {piece_count}")
    print(f"coarse a1 candidates: {coarse_count}")
    print(f"refined a1 candidates: {refined_count}")
    if args.write_pilot:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(
            render_pilot(refinements, args.dataset_name),
            encoding="utf-8",
            newline="\n",
        )
        print(f"wrote {output}")


if __name__ == "__main__":
    main()
