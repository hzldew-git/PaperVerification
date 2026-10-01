#!/usr/bin/env python3
"""Generate exact discriminant certificates for rows 200--299 survivors."""

from __future__ import annotations

import ast
import re
from pathlib import Path

from sympy import Poly, ZZ, factorint, symbols

from generate_degree_seven_survivor_discriminants import (
    ROOT,
    THRESHOLD,
    render_case,
)


LEAN_ROOT = ROOT / "lean" / "TraceEuclidean"
REDUCTION_PARTS = (
    LEAN_ROOT / "DegreeSevenRolleStageSevenRows200To299ReductionParts"
)
LEGACY_CASE_OUTPUT = (
    LEAN_ROOT / "DegreeSevenRows200To299SurvivorDiscriminants"
)
GROUP_OUTPUT = (
    LEAN_ROOT / "DegreeSevenRows200To299SurvivorDiscriminantGroups"
)
EXCEPTIONAL_OUTPUT = (
    LEAN_ROOT / "DegreeSevenRows200To299ExceptionalDiscriminant.lean"
)
AGGREGATOR_OUTPUT = (
    LEAN_ROOT / "DegreeSevenRows200To299SurvivorDiscriminants.lean"
)
NAMESPACE_PREFIX = "DegreeSevenRows200To299SurvivorDiscriminantCase"
EXCEPTIONAL_NAMESPACE_PREFIX = (
    "DegreeSevenRows200To299ExceptionalDiscriminantCase"
)
X = symbols("x")
GROUP_SIZE = 5


def survivors() -> list[list[int]]:
    rows: list[list[int]] = []
    for path in sorted(REDUCTION_PARTS.glob("Chunk*Part*.lean")):
        source = path.read_text(encoding="utf-8")
        for match in re.finditer(r"\.survivor\s+(\[[^\]]+\])", source):
            rows.append(ast.literal_eval(match.group(1)))
    if len(rows) != 94 or len({tuple(row) for row in rows}) != 94:
        raise ArithmeticError(f"expected 94 distinct survivors, found {len(rows)}")
    return rows


def discriminant(coefficients: list[int]) -> int:
    polynomial = Poly(
        sum(value * X**exponent
            for exponent, value in enumerate(coefficients)),
        X,
        domain=ZZ,
    )
    value = int(polynomial.discriminant())
    if value <= 0:
        raise ArithmeticError("expected positive totally-real discriminant")
    return value


def squarefree_kernel(value: int) -> int:
    return int(
        __import__("math").prod(
            prime for prime, exponent in factorint(value).items()
            if exponent % 2
        )
    )


def render_aggregator(
    data: list[tuple[int, list[int], int]], group_count: int
) -> str:
    imports = [
        "import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Reduction",
        "import TraceEuclidean.DegreeSevenRows200To299ExceptionalMaximalOrder",
    ] + [
        "import TraceEuclidean."
        f"DegreeSevenRows200To299SurvivorDiscriminantGroups.Group{index:03d}"
        for index in range(group_count)
    ]
    entries = []
    for index, _, _ in data:
        if index == 6:
            entries.append(
                "DegreeSevenRows200To299ExceptionalMaximalOrder."
                "lowerBoundCertificate"
            )
        else:
            entries.append(
                f"{NAMESPACE_PREFIX}{index:03d}.certificate."
                "toLowerBoundCertificate"
            )
    entry_source = ",\n".join(f"    {entry}" for entry in entries)
    return "\n".join(imports) + f"""

/-!
# Discriminant closure for Stage Five rows 200 through 299

Exact resultant certificates and one Dedekind maximal-order certificate cover
the complete 94-polynomial irreducible frontier.
-/

namespace TraceEuclidean

open Polynomial

noncomputable section

def degreeSevenFieldDiscriminantLowerBoundCertificatesRows200To299 :
    List DegreeSevenFieldDiscriminantLowerBoundCertificate :=
  [
{entry_source}
  ]

theorem degreeSevenFieldDiscriminantLowerBoundCertificatesRows200To299_count :
    degreeSevenFieldDiscriminantLowerBoundCertificatesRows200To299.length =
      94 := by
  rfl

theorem degreeSevenFieldDiscriminantLowerBoundCertificatesRows200To299_coefficients :
    degreeSevenFieldDiscriminantLowerBoundCertificatesRows200To299.map
        DegreeSevenFieldDiscriminantLowerBoundCertificate.coefficients =
      degreeSevenStageSevenSurvivorCoefficientsRows200To299 := by
  rfl

/-- Every retained coefficient list from rows 200 through 299 forces the
target field-discriminant lower bound. -/
theorem degreeSevenRows200To299_fieldDiscriminant_lowerBound_of_survivor
    {{K : Type*}} [Field K] [NumberField K]
    {{f : ℤ[X]}} (hfield : HunterFieldPolynomialCandidate K 7 194 f)
    (hcoefficients :
      [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
        f.coeff 4, f.coeff 5, f.coeff 6, 1] ∈
          degreeSevenStageSevenSurvivorCoefficientsRows200To299) :
    20134393 ≤ (NumberField.discr K).natAbs := by
  rw [←
    degreeSevenFieldDiscriminantLowerBoundCertificatesRows200To299_coefficients]
    at hcoefficients
  obtain ⟨certificate, hcertificate, hcertificateCoefficients⟩ :=
    List.mem_map.mp hcoefficients
  exact certificate.lowerBound hfield hcertificateCoefficients

/-- End-to-end discriminant lower bound for a Hunter septic whose first four
nonconstant coefficients lie in Stage Five rows 200 through 299. -/
theorem degreeSevenStageSevenRows200To299_fieldDiscriminant_lowerBound
    {{K : Type*}} [Field K] [NumberField K]
    {{f : ℤ[X]}} (hfield : HunterFieldPolynomialCandidate K 7 194 f)
    (refinement : DegreeSevenStageSixPiecewiseCoverage)
    (hrefinement : refinement ∈ degreeSevenStageSixPiecewiseRows200To299)
    (ha6 : refinement.coverage.parent.a6 = f.coeff 6)
    (ha5 : refinement.coverage.parent.a5 = f.coeff 5)
    (ha4 : refinement.coverage.parent.a4 = f.coeff 4)
    (ha3 : refinement.coverage.parent.a3 = f.coeff 3) :
    20134393 ≤ (NumberField.discr K).natAbs := by
  apply degreeSevenRows200To299_fieldDiscriminant_lowerBound_of_survivor
    hfield
  exact degreeSevenStageSevenRows200To299_reduces_to_ninetyFour
    hfield.1 refinement hrefinement ha6 ha5 ha4 ha3

/-- No row in the certified 200 through 299 block can occur for a field of
absolute discriminant strictly below `20134393`. -/
theorem degreeSevenStageSevenRows200To299_excludes_discriminant_lt
    {{K : Type*}} [Field K] [NumberField K]
    {{f : ℤ[X]}} (hfield : HunterFieldPolynomialCandidate K 7 194 f)
    (refinement : DegreeSevenStageSixPiecewiseCoverage)
    (hrefinement : refinement ∈ degreeSevenStageSixPiecewiseRows200To299)
    (ha6 : refinement.coverage.parent.a6 = f.coeff 6)
    (ha5 : refinement.coverage.parent.a5 = f.coeff 5)
    (ha4 : refinement.coverage.parent.a4 = f.coeff 4)
    (ha3 : refinement.coverage.parent.a3 = f.coeff 3)
    (hdiscriminant : (NumberField.discr K).natAbs < 20134393) : False := by
  exact (not_lt_of_ge
    (degreeSevenStageSevenRows200To299_fieldDiscriminant_lowerBound
      hfield refinement hrefinement ha6 ha5 ha4 ha3)) hdiscriminant

end

end TraceEuclidean
"""


def main() -> None:
    rows = survivors()
    data = [
        (index, coefficients, discriminant(coefficients))
        for index, coefficients in enumerate(rows)
    ]
    exceptional = [
        item for item in data if squarefree_kernel(item[2]) < THRESHOLD
    ]
    if exceptional != [
        (6, [-1, -5, -2, 13, 7, -9, -3, 1], 1_222_840_301)
    ]:
        raise ArithmeticError(f"unexpected exceptional survivors: {exceptional}")

    if LEGACY_CASE_OUTPUT.exists():
        LEGACY_CASE_OUTPUT.resolve().relative_to(ROOT.resolve())
        for stale in LEGACY_CASE_OUTPUT.glob("Case*.lean"):
            stale.unlink()
        if not any(LEGACY_CASE_OUTPUT.iterdir()):
            LEGACY_CASE_OUTPUT.rmdir()

    GROUP_OUTPUT.mkdir(parents=True, exist_ok=True)
    normal = [item for item in data if item[0] != 6]
    groups = [
        normal[start : start + GROUP_SIZE]
        for start in range(0, len(normal), GROUP_SIZE)
    ]
    desired_groups: set[Path] = set()
    for group_index, group in enumerate(groups):
        bodies = []
        for index, coefficients, value in group:
            case_source = render_case(
                index,
                coefficients,
                value,
                namespace_prefix=NAMESPACE_PREFIX,
            )
            import_line, body = case_source.split("\n", 1)
            if import_line != (
                "import TraceEuclidean.DegreeSevenSurvivorDiscriminant"
            ):
                raise ArithmeticError("unexpected case-module import")
            bodies.append(body.lstrip("\n"))
        group_path = GROUP_OUTPUT / f"Group{group_index:03d}.lean"
        group_path.write_text(
            "import TraceEuclidean.DegreeSevenSurvivorDiscriminant\n\n"
            + "\n".join(bodies),
            encoding="utf-8",
            newline="\n",
        )
        desired_groups.add(group_path)
    for stale in GROUP_OUTPUT.glob("Group*.lean"):
        if stale not in desired_groups:
            stale.unlink()

    index, coefficients, value = exceptional[0]
    EXCEPTIONAL_OUTPUT.write_text(
        render_case(
            index,
            coefficients,
            value,
            namespace_prefix=EXCEPTIONAL_NAMESPACE_PREFIX,
            require_threshold=False,
            emit_certificate=False,
        ),
        encoding="utf-8",
        newline="\n",
    )
    AGGREGATOR_OUTPUT.write_text(
        render_aggregator(data, len(groups)), encoding="utf-8", newline="\n"
    )
    print(
        "degree-seven rows 200--299 discriminants: PASS "
        "(93 kernel bounds + 1 maximal-order exception)"
    )


if __name__ == "__main__":
    main()
