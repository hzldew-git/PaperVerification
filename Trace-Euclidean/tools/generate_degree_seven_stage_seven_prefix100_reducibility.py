#!/usr/bin/env python3
"""Generate pure-kernel factor certificates for the first 100 septic rows."""

from __future__ import annotations

from pathlib import Path

from sympy import Poly

from generate_degree_seven_rolle_stage_seven_pilot import (
    X,
    StageSevenScaledEntry,
    a0_bounds,
    build_entry,
    candidate_tuples,
    parse_stage_five_rows,
    render_entry,
    stage_six_pieces,
)


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = (
    ROOT
    / "lean"
    / "TraceEuclidean"
    / "DegreeSevenRolleStageSevenPrefix100Reducibility"
)
PART_OUTPUT = (
    ROOT
    / "lean"
    / "TraceEuclidean"
    / "DegreeSevenRolleStageSevenPrefix100ReducibilityParts"
)
EXPECTED_COUNTS = (0, 3, 4, 4, 5, 12, 11, 12, 25, 19)
# Keep kernel normalization below the Windows memory ceiling.  Some entries
# have empty final intervals, so this bounds entry count rather than factor
# certificate count.
PART_SIZE = 5

FactorCertificate = tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]


def coefficients(polynomial: Poly) -> tuple[int, ...]:
    return tuple(int(polynomial.nth(index)) for index in range(polynomial.degree() + 1))


def render_list(values: tuple[int, ...]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def final_entries(
    row_start: int,
) -> list[tuple[StageSevenScaledEntry, list[Poly]]]:
    rows = parse_stage_five_rows()[row_start : row_start + 10]
    pieces = stage_six_pieces(rows, 3, 24)
    result: list[tuple[StageSevenScaledEntry, list[Poly]]] = []
    for row, a2, a1 in candidate_tuples(pieces):
        entry = build_entry(row, a2, a1, 24)
        if entry is None:
            continue
        lower, upper = a0_bounds(entry)
        polynomials: list[Poly] = []
        for a0 in range(lower, upper + 1):
            ascending = (a0, a1, a2, row.a3, row.a4, row.a5, row.a6, 1)
            polynomials.append(
                Poly(
                    sum(
                        value * X**index
                        for index, value in enumerate(ascending)
                    ),
                    X,
                    domain="ZZ",
                )
            )
        result.append((entry, polynomials))
    return result


def factor_certificate(polynomial: Poly) -> FactorCertificate:
    unit, factors = polynomial.factor_list()
    if unit != 1 or (len(factors) == 1 and factors[0][1] == 1):
        raise ArithmeticError(f"expected a reducible monic septic, found {polynomial}")
    left = factors[0][0]
    right = polynomial.exquo(left)
    if left.degree() <= 0 or right.degree() <= 0 or left * right != polynomial:
        raise ArithmeticError(f"invalid nontrivial factorization of {polynomial}")
    return coefficients(polynomial), coefficients(left), coefficients(right)


def render_certificate(certificate: FactorCertificate) -> str:
    polynomial, left, right = certificate
    return (
        "⟨"
        + render_list(polynomial)
        + ", "
        + render_list(left)
        + ", "
        + render_list(right)
        + f", {len(left) - 1}, {len(right) - 1}⟩"
    )


def right_associated(names: list[str]) -> str:
    if not names:
        return "[]"
    if len(names) == 1:
        return names[0]
    return names[0] + " ++\n    (" + right_associated(names[1:]) + ")"


def nested_forall_proof(valid_names: list[str]) -> str:
    if len(valid_names) == 1:
        return valid_names[0]
    return (
        "List.forall_append.mpr ⟨"
        + valid_names[0]
        + ",\n    "
        + nested_forall_proof(valid_names[1:])
        + "⟩"
    )


def render_part(
    chunk_index: int,
    part_index: int,
    part: list[tuple[StageSevenScaledEntry, list[Poly]]],
) -> tuple[str, int]:
    chunk = f"Chunk{chunk_index:03d}"
    suffix = f"Part{part_index:03d}"
    dataset = f"Prefix100{chunk}{suffix}"
    certificates = [
        factor_certificate(polynomial)
        for _, polynomials in part
        for polynomial in polynomials
    ]
    entries_body = ",\n    ".join(render_entry(entry) for entry, _ in part)
    certificates_body = ",\n    ".join(
        render_certificate(certificate) for certificate in certificates
    )
    source = f"""import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk {part_index} for Stage Five rows {chunk_index * 10} through {chunk_index * 10 + 9}. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaled{dataset} :
    List DegreeSevenStageSevenScaledEntry :=
  [
    {entries_body}
  ]

def degreeSevenStageSevenFactorCertificates{dataset} :
    List PolynomialFactorCertificate :=
  [
    {certificates_body}
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificates{dataset}_valid :
    degreeSevenStageSevenFactorCertificates{dataset}.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificates{dataset}_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaled{dataset} ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificates{dataset}.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := {{ maxSteps := 300000 }})
    [degreeSevenStageSevenFactorCertificates{dataset},
    degreeSevenStageSevenScaled{dataset},
    degreeSevenStageSevenFinalCoefficients,
    DegreeSevenStageSevenScaledEntry.scaledA0Candidates,
    DegreeSevenStageSevenScaledEntry.scaledA0LowerBound,
    DegreeSevenStageSevenScaledEntry.scaledA0UpperBound,
    DegreeSevenStageSevenScaledEntry.scaledRootValueRange,
    DegreeSevenStageSevenScaledEntry.scaledEndpointValueRange,
    DegreeSevenStageSevenScaledEntry.scaledBaseCoefficients,
    scaledIntegerPolynomialIntervalEval, integerMin4,
    integerMax4, integerIcc, min_def, max_def, Int.toNat]

end

end TraceEuclidean
"""
    return source, len(certificates)


def render_aggregator(chunk_index: int, part_count: int, certificate_count: int) -> str:
    chunk = f"Chunk{chunk_index:03d}"
    dataset = f"Prefix100{chunk}"
    imports = "\n".join(
        "import "
        "TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts."
        f"{chunk}Part{part_index:03d}"
        for part_index in range(part_count)
    )
    scaled_names = [
        f"degreeSevenStageSevenScaled{dataset}Part{part_index:03d}"
        for part_index in range(part_count)
    ]
    certificate_names = [
        f"degreeSevenStageSevenFactorCertificates{dataset}Part{part_index:03d}"
        for part_index in range(part_count)
    ]
    valid_names = [
        f"degreeSevenStageSevenFactorCertificates{dataset}Part{part_index:03d}_valid"
        for part_index in range(part_count)
    ]
    complete_names = [
        f"degreeSevenStageSevenFactorCertificates{dataset}Part{part_index:03d}_complete"
        for part_index in range(part_count)
    ]
    scaled_concat = right_associated(scaled_names)
    certificate_concat = right_associated(certificate_names)
    valid_proof = nested_forall_proof(valid_names)
    completeness_rewrites = ",\n    ".join(
        f"{name} coefficients" for name in complete_names
    )
    if part_count == 1:
        complete_proof = f"""  rw [degreeSevenStageSevenScaled{dataset}_parts]
  simpa only [degreeSevenStageSevenFactorCertificates{dataset}] using
    {complete_names[0]} coefficients"""
    else:
        complete_proof = f"""  rw [degreeSevenStageSevenScaled{dataset}_parts]
  simp only [degreeSevenStageSevenFinalCoefficients_append,
    degreeSevenStageSevenFactorCertificates{dataset},
    List.map_append, List.mem_append]
  rw [{completeness_rewrites}]"""
    return f"""import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.{chunk}
{imports}

/-! Reducibility closure for Stage Five rows {chunk_index * 10} through {chunk_index * 10 + 9}. -/

namespace TraceEuclidean

noncomputable section

def degreeSevenStageSevenFactorCertificates{dataset} :
    List PolynomialFactorCertificate :=
  {certificate_concat}

theorem degreeSevenStageSevenScaled{dataset}_parts :
    degreeSevenStageSevenScaled{dataset} =
      {scaled_concat} := by
  rfl

theorem degreeSevenStageSevenFactorCertificates{dataset}_valid :
    degreeSevenStageSevenFactorCertificates{dataset}.Forall
      (fun certificate => certificate.check = true) := by
  exact {valid_proof}

theorem degreeSevenStageSevenFactorCertificates{dataset}_count :
    degreeSevenStageSevenFactorCertificates{dataset}.length =
      {certificate_count} := by
  rfl

theorem degreeSevenStageSevenFactorCertificates{dataset}_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaled{dataset} ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificates{dataset}.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
{complete_proof}

end

end TraceEuclidean
"""


def main() -> None:
    OUTPUT.mkdir(parents=True, exist_ok=True)
    PART_OUTPUT.mkdir(parents=True, exist_ok=True)
    desired_parts: set[Path] = set()
    total = 0
    for index, expected in enumerate(EXPECTED_COUNTS):
        entries_with_polynomials = final_entries(index * 10)
        polynomials = [
            polynomial
            for _, entry_polynomials in entries_with_polynomials
            for polynomial in entry_polynomials
        ]
        if len(polynomials) != expected:
            raise ArithmeticError(
                f"chunk {index}: expected {expected} final polynomials, "
                f"found {len(polynomials)}"
            )
        rendered = [factor_certificate(polynomial) for polynomial in polynomials]
        if len({certificate[0] for certificate in rendered}) != len(rendered):
            raise ArithmeticError(f"chunk {index}: duplicate final polynomial")
        part_size = PART_SIZE
        parts = [
            entries_with_polynomials[start : start + part_size]
            for start in range(0, len(entries_with_polynomials), part_size)
        ]
        if not parts:
            parts = [[]]
        part_total = 0
        for part_index, part in enumerate(parts):
            source, count = render_part(index, part_index, part)
            part_path = PART_OUTPUT / f"Chunk{index:03d}Part{part_index:03d}.lean"
            part_path.write_text(source, encoding="utf-8", newline="\n")
            desired_parts.add(part_path)
            part_total += count
        if part_total != expected:
            raise ArithmeticError(
                f"chunk {index}: part total {part_total} does not match {expected}"
            )
        aggregator = render_aggregator(index, len(parts), expected)
        path = OUTPUT / f"Chunk{index:03d}.lean"
        path.write_text(aggregator, encoding="utf-8", newline="\n")
        total += expected
        print(
            f"wrote {path.relative_to(ROOT)} "
            f"({len(parts)} parts, {expected} certificates)"
        )
    for stale in PART_OUTPUT.glob("Chunk*Part*.lean"):
        if stale not in desired_parts:
            stale.unlink()
    if total != 95:
        raise ArithmeticError(f"expected 95 certificates, found {total}")
    print("degree-seven prefix-100 reducibility certificates: PASS (95/95)")


if __name__ == "__main__":
    main()
