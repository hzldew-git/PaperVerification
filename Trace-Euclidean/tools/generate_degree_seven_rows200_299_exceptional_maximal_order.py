#!/usr/bin/env python3
"""Generate the maximal power-order certificate for the lone exceptional septic."""

from __future__ import annotations

import re
from pathlib import Path

from generate_voight_irreducibility_certificates import PRIMES, try_prime
from generate_voight_maximal_order_pilot import (
    ROOT,
    build_order,
    dedekind_global_certificate,
    emit,
)


OUTPUT = (
    ROOT
    / "lean"
    / "TraceEuclidean"
    / "DegreeSevenRows200To299ExceptionalMaximalOrder.lean"
)
NAMESPACE = "DegreeSevenRows200To299ExceptionalMaximalOrder"
COEFFICIENTS = [-1, -5, -2, 13, 7, -9, -3, 1]
DISCRIMINANT = 1_222_840_301


def lean_list(values) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def rabin_source() -> str:
    coefficients = tuple(COEFFICIENTS)
    certificate = next(
        try_prime(coefficients, 7, prime, full=True)
        for prime in PRIMES
        if try_prime(coefficients, 7, prime, full=False) is not None
    )
    return f"""def irreducibilityCertificate :
    RabinIrreducibilityCertificate :=
  ⟨{certificate.prime},
    {lean_list([list(row) for row in certificate.states])},
    {lean_list([list(row) for row in certificate.quotients])},
    {lean_list([list(row) for row in certificate.bezout_left])},
    {lean_list([list(row) for row in certificate.bezout_right])}⟩

lemma irreducibilityCertificate_checked :
    irreducibilityCertificate.check 7 row = true := by
  decide

lemma T_irreducible : Irreducible T :=
  RabinIrreducibilityCertificate.irreducible_of_check_eq_true
    irreducibilityCertificate_checked
"""


def record() -> dict:
    return {
        "degree": 7,
        "row_number": 0,
        "field_discriminant": DISCRIMINANT,
        "coefficients": COEFFICIENTS,
        "index": 1,
        "matrix": [
            [[int(i == j), 1] for j in range(7)]
            for i in range(7)
        ],
    }


def main() -> None:
    data = record()
    order = build_order(data)
    dedekind = dedekind_global_certificate(COEFFICIENTS)
    if dedekind["bad"] or dedekind["good"] != [73, 229469]:
        raise ArithmeticError(f"unexpected Dedekind split: {dedekind}")
    source = emit(data, order, dedekind, {}, namespace=NAMESPACE)
    source = source.replace(
        "import TraceEuclidean.VoightAllIrreducible\n",
        "import TraceEuclidean.DegreeSevenRows200To299ExceptionalDiscriminant\n"
        "import TraceEuclidean.FiniteFieldIrreducibilityCertificate\n"
        "import TraceEuclidean.CriticalFieldBridge\n",
    )
    source = source.replace(
        "set_option maxHeartbeats 5000000\n",
        "set_option maxHeartbeats 5000000\nset_option maxRecDepth 100000\n",
    )
    source = re.sub(
        r"lemma row_mem : row ∈ voightPolynomialRowsSeven := by native_decide\n"
        r"lemma T_irreducible : Irreducible T :=\n"
        r"  voightPolynomialRowsSeven_irreducible row row_mem\n",
        rabin_source(),
        source,
        count=1,
    )
    source = re.sub(
        r"lemma P_det_index_sq :\n"
        r"    P\.det \^ 2 \* \(row\.index : ℚ\) \^ 2 = 1 := by\n"
        r".*?(?=\n\ntheorem field_discriminant_eq_recorded)",
        """lemma P_det_index_sq :
    P.det ^ 2 * (row.index : ℚ) ^ 2 = 1 := by
  have hP : P = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, basisNumerator, basisDenominator]
  rw [hP]
  norm_num [row]
""",
        source,
        count=1,
        flags=re.S,
    )
    old_recorded = """  have hrecorded :
      T.discr = (row.index : ℤ) ^ 2 *
        (row.fieldDiscriminant : ℤ) := by
    simpa [T] using
      (voightPolynomialDiscriminantInput 7 row row_mem)
"""
    new_recorded = """  have hrecorded :
      T.discr = (row.index : ℤ) ^ 2 *
        (row.fieldDiscriminant : ℤ) := by
    simpa [T, row,
      DegreeSevenRows200To299ExceptionalDiscriminantCase006.row] using
      DegreeSevenRows200To299ExceptionalDiscriminantCase006.polynomial_discr
"""
    if old_recorded not in source:
        raise ArithmeticError("could not locate recorded-discriminant block")
    source = source.replace(old_recorded, new_recorded, 1)

    endpoint = f"""

/-- The exceptional polynomial generates only fields with its exact model
discriminant, because Dedekind's criterion proves that its power order is
already the full ring of integers. -/
theorem fieldDiscriminant_lowerBound
    {{K' : Type*}} [Field K'] [NumberField K']
    {{f : ℤ[X]}} (hfield : HunterFieldPolynomialCandidate K' 7 194 f)
    (hcoefficients : {lean_list(COEFFICIENTS)} =
      [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
        f.coeff 4, f.coeff 5, f.coeff 6, 1]) :
    20134393 ≤ (NumberField.discr K').natAbs := by
  have hf :
      f = polynomialOfCoefficients
        [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
          f.coeff 4, f.coeff 5, f.coeff 6, 1] :=
    degreeSeven_eq_polynomialOfCoefficients
      hfield.1.1 hfield.1.2.2.1
  have hT : T = f := by
    calc
      T = polynomialOfCoefficients {lean_list(COEFFICIENTS)} := by rfl
      _ = polynomialOfCoefficients
          [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
            f.coeff 4, f.coeff 5, f.coeff 6, 1] := by rw [hcoefficients]
      _ = f := hf.symm
  rcases hfield.2 with ⟨a, hgen, hminpoly, index, hindex, hrelation⟩
  have hexact : NumberField.discr K' = ({DISCRIMINANT} : ℤ) :=
    numberField_discr_eq_of_adjoinRoot_model
      field_discriminant_eq_recorded a (hT.trans hminpoly) hgen
  rw [hexact]
  norm_num

def lowerBoundCertificate :
    DegreeSevenFieldDiscriminantLowerBoundCertificate :=
  {{ coefficients := {lean_list(COEFFICIENTS)}
    lowerBound := fun hfield hcoefficients =>
      fieldDiscriminant_lowerBound hfield hcoefficients }}
"""
    marker = f"\nend\n\nend {NAMESPACE}\nend TraceEuclidean\n"
    if marker not in source:
        raise ArithmeticError("could not locate namespace footer")
    source = source.replace(marker, endpoint + marker, 1)
    if "native_decide" in source or "row_mem" in source:
        raise ArithmeticError("native or archived-row dependency survived")
    OUTPUT.write_text(source, encoding="utf-8", newline="\n")
    print(
        "degree-seven rows 200--299 exceptional maximal order: PASS "
        "(Dedekind primes 73 and 229469)"
    )


if __name__ == "__main__":
    main()
