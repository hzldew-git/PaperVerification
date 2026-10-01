#!/usr/bin/env python3
"""Generate kernel certificates for a block of septic Stage Five rows.

The output partitions every final constant-coefficient candidate into either
a checked nontrivial factorization or a short residual coefficient list.  The
residual list is intentionally kept separate: later Lean modules combine it
with the power-order discriminant equation without trusting Python's
irreducibility or number-field routines.
"""

from __future__ import annotations

import argparse
from pathlib import Path

from sympy import Poly

from generate_degree_seven_stage_seven_prefix100_reducibility import (
    FactorCertificate,
    a0_bounds,
    coefficients,
    factor_certificate,
    final_entries,
    nested_forall_proof,
    render_certificate,
    render_entry,
    render_list,
    right_associated,
)


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = (
    ROOT
    / "lean"
    / "TraceEuclidean"
    / "DegreeSevenRolleStageSevenRows100To199Reduction"
)
PART_OUTPUT = (
    ROOT
    / "lean"
    / "TraceEuclidean"
    / "DegreeSevenRolleStageSevenRows100To199ReductionParts"
)
ROW_BASE = 100
CHUNK_SIZE = 10
CHUNK_COUNT = 10
DATASET_PREFIX = "Rows100To199"
STAGE_SEVEN_MODULE_DIRECTORY = (
    "DegreeSevenRolleStageSevenRows100To199Chunks"
)
REDUCTION_PARTS_MODULE_DIRECTORY = (
    "DegreeSevenRolleStageSevenRows100To199ReductionParts"
)
EXPECTED_FINAL_COUNTS = (26, 46, 4, 90, 26, 14, 144, 36, 11, 202)
EXPECTED_SURVIVOR_COUNTS = (0, 0, 0, 0, 0, 0, 2, 0, 0, 7)
# The compact Boolean certificate avoids the large normalization proof terms
# produced by the preceding generator, so twenty-five entries remain safely
# below the observed Windows elaboration-memory ceiling.
PART_SIZE = 25


def is_reducible(polynomial: Poly) -> bool:
    unit, factors = polynomial.factor_list()
    return unit != 1 or len(factors) != 1 or factors[0][1] != 1


def render_candidate(polynomial: Poly) -> tuple[str, bool]:
    if is_reducible(polynomial):
        return ".reducible " + render_certificate(factor_certificate(polynomial)), False
    return ".survivor " + render_list(coefficients(polynomial)), True


def render_part(
    chunk_index: int,
    part_index: int,
    part: list[tuple[object, list[Poly]]],
) -> tuple[str, int, int]:
    chunk = f"Chunk{chunk_index:03d}"
    suffix = f"Part{part_index:03d}"
    dataset = f"{DATASET_PREFIX}{chunk}{suffix}"
    factor_count = 0
    survivor_count = 0
    rendered_entries: list[str] = []
    for entry, polynomials in part:
        rendered_candidates: list[str] = []
        for polynomial in polynomials:
            rendered, survivor = render_candidate(polynomial)
            rendered_candidates.append(rendered)
            if survivor:
                survivor_count += 1
            else:
                factor_count += 1
        candidates_body = ", ".join(rendered_candidates)
        lower, upper = a0_bounds(entry)
        rendered_entries.append(
            f"⟨{render_entry(entry)}, ({lower} : ℤ), ({upper} : ℤ), "
            f"[{candidates_body}]⟩"
        )
    entries_body = ",\n    ".join(rendered_entries)
    source = f"""import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Candidate-reduction subchunk {part_index} for Stage Five rows {ROW_BASE + chunk_index * CHUNK_SIZE} through {ROW_BASE + chunk_index * CHUNK_SIZE + CHUNK_SIZE - 1}. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificates{dataset} :
    List DegreeSevenFinalEntryCertificate :=
  [
    {entries_body}
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks the exact a0 list and every factorization.
theorem degreeSevenStageSevenFinalEntryCertificates{dataset}_valid :
    degreeSevenStageSevenFinalEntryCertificates{dataset}.Forall
      (fun certificate => certificate.check = true) := by
  decide

theorem degreeSevenStageSevenFinalEntryCertificates{dataset}_entry_count :
    degreeSevenStageSevenFinalEntryCertificates{dataset}.length =
      {len(part)} := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificates{dataset}_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificates{dataset}).length =
      {factor_count + survivor_count} := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificates{dataset}_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificates{dataset}).length =
      {survivor_count} := by
  rfl

end

end TraceEuclidean
"""
    return source, factor_count, survivor_count


def render_aggregator(
    chunk_index: int,
    part_count: int,
    entry_count: int,
    factor_count: int,
    survivor_count: int,
) -> str:
    chunk = f"Chunk{chunk_index:03d}"
    dataset = f"{DATASET_PREFIX}{chunk}"
    imports = "\n".join(
        "import "
        f"TraceEuclidean.{REDUCTION_PARTS_MODULE_DIRECTORY}."
        f"{chunk}Part{part_index:03d}"
        for part_index in range(part_count)
    )
    certificate_names = [
        f"degreeSevenStageSevenFinalEntryCertificates{dataset}Part{part_index:03d}"
        for part_index in range(part_count)
    ]
    valid_names = [
        f"degreeSevenStageSevenFinalEntryCertificates{dataset}Part{part_index:03d}_valid"
        for part_index in range(part_count)
    ]
    row_start = ROW_BASE + chunk_index * CHUNK_SIZE
    return f"""import TraceEuclidean.{STAGE_SEVEN_MODULE_DIRECTORY}.{chunk}
{imports}

/-! Candidate reduction for Stage Five rows {row_start} through {row_start + CHUNK_SIZE - 1}. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificates{dataset} :
    List DegreeSevenFinalEntryCertificate :=
  {right_associated(certificate_names)}

theorem degreeSevenStageSevenScaled{dataset}_parts :
    degreeSevenStageSevenScaled{dataset} =
      degreeSevenStageSevenFinalEntryCertificates{dataset}.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificates{dataset}_valid :
    degreeSevenStageSevenFinalEntryCertificates{dataset}.Forall
      (fun certificate => certificate.check = true) := by
  exact {nested_forall_proof(valid_names)}

theorem degreeSevenStageSevenFinalEntryCertificates{dataset}_entry_count :
    degreeSevenStageSevenFinalEntryCertificates{dataset}.length =
      {entry_count} := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificates{dataset}_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificates{dataset}).length =
      {factor_count + survivor_count} := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificates{dataset}_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificates{dataset}).length =
      {survivor_count} := by
  rfl

end

end TraceEuclidean
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--row-base", type=int, default=100)
    parser.add_argument("--chunk-count", type=int, default=10)
    parser.add_argument("--dataset-prefix", default="Rows100To199")
    parser.add_argument("--stage-seven-module-directory")
    parser.add_argument("--reduction-module-directory")
    parser.add_argument("--reduction-parts-module-directory")
    parser.add_argument("--part-size", type=int, default=25)
    args = parser.parse_args()
    if args.row_base < 0:
        raise ValueError("--row-base must be nonnegative")
    if args.chunk_count <= 0:
        raise ValueError("--chunk-count must be positive")
    if args.part_size <= 0:
        raise ValueError("--part-size must be positive")
    if not args.dataset_prefix.isalnum() or not args.dataset_prefix[0].isalpha():
        raise ValueError("--dataset-prefix must be a nonempty alphanumeric Lean suffix")

    global OUTPUT, PART_OUTPUT, ROW_BASE, CHUNK_COUNT, DATASET_PREFIX
    global STAGE_SEVEN_MODULE_DIRECTORY, REDUCTION_PARTS_MODULE_DIRECTORY
    global PART_SIZE
    ROW_BASE = args.row_base
    CHUNK_COUNT = args.chunk_count
    DATASET_PREFIX = args.dataset_prefix
    STAGE_SEVEN_MODULE_DIRECTORY = args.stage_seven_module_directory or (
        f"DegreeSevenRolleStageSeven{DATASET_PREFIX}Chunks"
    )
    reduction_module_directory = args.reduction_module_directory or (
        f"DegreeSevenRolleStageSeven{DATASET_PREFIX}Reduction"
    )
    REDUCTION_PARTS_MODULE_DIRECTORY = (
        args.reduction_parts_module_directory
        or f"DegreeSevenRolleStageSeven{DATASET_PREFIX}ReductionParts"
    )
    for option, value in (
        ("--stage-seven-module-directory", STAGE_SEVEN_MODULE_DIRECTORY),
        ("--reduction-module-directory", reduction_module_directory),
        ("--reduction-parts-module-directory", REDUCTION_PARTS_MODULE_DIRECTORY),
    ):
        if not value.isalnum() or not value[0].isalpha():
            raise ValueError(f"{option} must be a nonempty alphanumeric Lean module name")
    OUTPUT = ROOT / "lean" / "TraceEuclidean" / reduction_module_directory
    PART_OUTPUT = (
        ROOT / "lean" / "TraceEuclidean" / REDUCTION_PARTS_MODULE_DIRECTORY
    )
    PART_SIZE = args.part_size

    use_default_expectations = (
        ROW_BASE == 100
        and CHUNK_COUNT == 10
        and DATASET_PREFIX == "Rows100To199"
    )
    OUTPUT.mkdir(parents=True, exist_ok=True)
    PART_OUTPUT.mkdir(parents=True, exist_ok=True)
    desired_parts: set[Path] = set()
    total_final = 0
    total_factors = 0
    total_survivors = 0
    for index in range(CHUNK_COUNT):
        entries_with_polynomials = final_entries(ROW_BASE + index * CHUNK_SIZE)
        polynomials = [
            polynomial
            for _, entry_polynomials in entries_with_polynomials
            for polynomial in entry_polynomials
        ]
        expected_final = len(polynomials)
        expected_survivors = None
        if use_default_expectations:
            expected_final = EXPECTED_FINAL_COUNTS[index]
            expected_survivors = EXPECTED_SURVIVOR_COUNTS[index]
        if len(polynomials) != expected_final:
            raise ArithmeticError(
                f"chunk {index}: expected {expected_final} final polynomials, "
                f"found {len(polynomials)}"
            )
        coefficient_rows = [coefficients(polynomial) for polynomial in polynomials]
        if len(set(coefficient_rows)) != len(coefficient_rows):
            raise ArithmeticError(f"chunk {index}: duplicate final polynomial")
        parts = [
            entries_with_polynomials[start : start + PART_SIZE]
            for start in range(0, len(entries_with_polynomials), PART_SIZE)
        ]
        if not parts:
            parts = [[]]
        factor_total = 0
        survivor_total = 0
        for part_index, part in enumerate(parts):
            source, factor_count, survivor_count = render_part(
                index, part_index, part
            )
            part_path = PART_OUTPUT / f"Chunk{index:03d}Part{part_index:03d}.lean"
            part_path.write_text(source, encoding="utf-8", newline="\n")
            desired_parts.add(part_path)
            factor_total += factor_count
            survivor_total += survivor_count
        if factor_total + survivor_total != expected_final:
            raise ArithmeticError(
                f"chunk {index}: classified {factor_total + survivor_total}, "
                f"expected {expected_final}"
            )
        if expected_survivors is not None and survivor_total != expected_survivors:
            raise ArithmeticError(
                f"chunk {index}: expected {expected_survivors} survivors, "
                f"found {survivor_total}"
            )
        aggregator = render_aggregator(
            index, len(parts), len(entries_with_polynomials),
            factor_total, survivor_total
        )
        path = OUTPUT / f"Chunk{index:03d}.lean"
        path.write_text(aggregator, encoding="utf-8", newline="\n")
        total_final += expected_final
        total_factors += factor_total
        total_survivors += survivor_total
        print(
            f"wrote {path.relative_to(ROOT)} "
            f"({len(parts)} parts, {factor_total} factors, "
            f"{survivor_total} survivors)"
        )
    for stale in PART_OUTPUT.glob("Chunk*Part*.lean"):
        if stale not in desired_parts:
            stale.unlink()
    if use_default_expectations and (
        total_final, total_factors, total_survivors
    ) != (599, 590, 9):
        raise ArithmeticError(
            "expected totals (599, 590, 9), found "
            f"({total_final}, {total_factors}, {total_survivors})"
        )
    print(
        f"degree-seven rows {ROW_BASE}--"
        f"{ROW_BASE + CHUNK_COUNT * CHUNK_SIZE - 1} candidate reduction: "
        f"PASS ({total_final} = {total_factors} reducible + "
        f"{total_survivors} survivors)"
    )


if __name__ == "__main__":
    main()
