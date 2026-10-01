#!/usr/bin/env python3
"""Generate pure-kernel resultant certificates for the nine septic survivors."""

from __future__ import annotations

from pathlib import Path

from sympy import Poly, QQ, Rational, factorint, resultant, symbols


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = (
    ROOT
    / "lean"
    / "TraceEuclidean"
    / "DegreeSevenSurvivorDiscriminants"
)
X = symbols("x")
THRESHOLD = 20_134_393
COEFFICIENTS = [
    [-1, -4, 0, 12, 5, -9, -3, 1],
    [-1, -5, -1, 14, 5, -9, -3, 1],
    [1, -3, -4, 12, 6, -9, -3, 1],
    [1, -5, -4, 14, 6, -9, -3, 1],
    [1, -4, -3, 14, 6, -9, -3, 1],
    [-1, -5, -2, 14, 6, -9, -3, 1],
    [-1, -6, -2, 15, 6, -9, -3, 1],
    [-1, -5, -1, 15, 6, -9, -3, 1],
    [-1, -5, 0, 16, 6, -9, -3, 1],
]
EXPECTED_DISCRIMINANTS = [
    69_678_137,
    114_075_673,
    374_305_189,
    237_777_973,
    1_054_317_249,
    509_185_429,
    1_534_648_768,
    2_581_099_233,
    2_289_940_909,
]


def lean_rat(value: Rational) -> str:
    value = Rational(value)
    numerator = int(value.p)
    denominator = int(value.q)
    if denominator == 1:
        return f"({numerator} : ℚ)"
    return f"(({numerator} : ℚ) / {denominator})"


def lean_polynomial(polynomial: Poly) -> str:
    terms: list[str] = []
    for exponent in range(polynomial.degree() + 1):
        coefficient = Rational(polynomial.nth(exponent))
        if coefficient == 0:
            continue
        term = f"C {lean_rat(coefficient)}"
        if exponent > 0:
            term += f" * X ^ {exponent}"
        terms.append(term)
    return " + ".join(terms) if terms else "0"


def lean_int_list(values: list[int]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def right_associated_product(values: list[int]) -> str:
    if len(values) == 1:
        return str(values[0])
    return f"{values[0]} * ({right_associated_product(values[1:])})"


def squarefree_proof(kernel: int) -> str:
    factors = sorted(factorint(kernel))
    if not factors:
        raise ArithmeticError("the residual kernel must be positive")
    declarations = "\n".join(
        f"  have hp{index} : Prime ({prime} : ℕ) :=\n"
        f"    Nat.prime_iff.mp (by norm_num)"
        for index, prime in enumerate(factors)
    )

    def proof(start: int) -> str:
        if start == len(factors) - 1:
            return f"hp{start}.squarefree"
        tail = right_associated_product(factors[start + 1 :])
        return (
            f"(Nat.squarefree_mul (m := {factors[start]}) (n := {tail}) "
            f"(by norm_num)).mpr ⟨hp{start}.squarefree, {proof(start + 1)}⟩"
        )

    factorization = right_associated_product(factors)
    return (
        declarations
        + f"\n  rw [show {kernel} = {factorization} by norm_num]\n"
        + f"  exact {proof(0)}"
    )


def euclidean_chain(polynomial: Poly) -> tuple[list[Poly], list[Poly]]:
    remainders = [polynomial, polynomial.diff()]
    quotients: list[Poly] = []
    while remainders[-1].degree() > 0:
        quotient, remainder = remainders[-2].div(remainders[-1])
        if remainder.is_zero:
            raise ArithmeticError("survivor polynomial has a repeated factor")
        quotients.append(quotient)
        remainders.append(remainder)
    return remainders, quotients


def render_case(
    index: int,
    coefficients: list[int],
    discriminant: int,
    *,
    namespace_prefix: str = "DegreeSevenSurvivorDiscriminantCase",
    require_threshold: bool = True,
    emit_certificate: bool = True,
) -> str:
    polynomial = Poly(
        sum(Rational(value) * X**exponent
            for exponent, value in enumerate(coefficients)),
        X,
        domain=QQ,
    )
    actual_discriminant = int(polynomial.discriminant())
    if actual_discriminant != discriminant:
        raise ArithmeticError(
            f"case {index}: expected discriminant {discriminant}, "
            f"found {actual_discriminant}"
        )
    remainders, quotients = euclidean_chain(polynomial)
    if [item.degree() for item in remainders] != list(range(7, -1, -1)):
        raise ArithmeticError(f"case {index}: non-generic Euclidean degree chain")
    if len(quotients) != 6 or any(item.degree() != 1 for item in quotients):
        raise ArithmeticError(f"case {index}: unexpected quotient degrees")
    signed_resultant = int(resultant(polynomial.as_expr(), polynomial.diff().as_expr(), X))
    if signed_resultant != -discriminant:
        raise ArithmeticError(f"case {index}: incorrect signed resultant")

    factors = factorint(discriminant)
    square_part = 1
    for prime, exponent in factors.items():
        square_part *= int(prime) ** (int(exponent) // 2)
    kernel = discriminant // (square_part * square_part)
    if require_threshold and kernel < THRESHOLD:
        raise ArithmeticError(f"case {index}: residual kernel below threshold")

    polynomial_defs = "\n\n".join(
        f"def p{position} : ℚ[X] :=\n  {lean_polynomial(item)}"
        for position, item in enumerate(remainders)
    )
    quotient_defs = "\n\n".join(
        f"def q{position} : ℚ[X] :=\n  {lean_polynomial(item)}"
        for position, item in enumerate(quotients)
    )
    degree_lemmas = "\n\n".join(
        f"lemma p{position}_degree : p{position}.natDegree = {item.degree()} := by\n"
        f"  unfold p{position}\n"
        f"  compute_degree <;> norm_num"
        for position, item in enumerate(remainders)
    )
    quotient_degree_lemmas = "\n\n".join(
        f"lemma q{position}_degree : q{position}.natDegree = 1 := by\n"
        f"  unfold q{position}\n"
        f"  compute_degree <;> norm_num"
        for position in range(len(quotients))
    )
    divisions = "\n\n".join(
        f"lemma division{position} : p{position} = "
        f"p{position + 2} + p{position + 1} * q{position} := by\n"
        f"  apply Polynomial.funext\n"
        f"  intro x\n"
        f"  simp [p{position}, p{position + 1}, p{position + 2}, q{position}]\n"
        f"  ring"
        for position in range(len(quotients))
    )

    steps: list[str] = []
    for position in range(len(quotients)):
        left_degree = remainders[position].degree()
        divisor_degree = remainders[position + 1].degree()
        remainder_degree = remainders[position + 2].degree()
        gap = left_degree - remainder_degree
        leading = Rational(remainders[position + 1].LC())
        sign = -1 if (divisor_degree * gap + remainder_degree * divisor_degree) % 2 else 1
        multiplier = Rational(sign) * leading**gap
        multiplier_text = lean_rat(multiplier)
        steps.append(
            f"lemma resultantStep{position} :\n"
            f"    p{position}.resultant p{position + 1} {left_degree} {divisor_degree} = "
            f"{multiplier_text} *\n"
            f"      p{position + 1}.resultant p{position + 2} "
            f"{divisor_degree} {remainder_degree} := by\n"
            f"  calc\n"
            f"    p{position}.resultant p{position + 1} {left_degree} {divisor_degree} =\n"
            f"        (p{position + 2} + p{position + 1} * q{position}).resultant "
            f"p{position + 1} {left_degree} {divisor_degree} := by\n"
            f"      rw [division{position}]\n"
            f"    _ = p{position + 2}.resultant p{position + 1} "
            f"{left_degree} {divisor_degree} :=\n"
            f"      Polynomial.resultant_add_mul_left p{position + 2} "
            f"p{position + 1} q{position} {left_degree} {divisor_degree}\n"
            f"        (by rw [q{position}_degree])\n"
            f"        (by rw [p{position + 1}_degree])\n"
            f"    _ = (-1 : ℚ) ^ ({divisor_degree} * {gap}) * "
            f"p{position + 1}.coeff {divisor_degree} ^ {gap} *\n"
            f"        p{position + 2}.resultant p{position + 1} "
            f"{remainder_degree} {divisor_degree} := by\n"
            f"      simpa using Polynomial.resultant_add_left_deg\n"
            f"        p{position + 2} p{position + 1} "
            f"{remainder_degree} {divisor_degree} {gap}\n"
            f"          (by rw [p{position + 2}_degree])\n"
            f"    _ = (-1 : ℚ) ^ ({divisor_degree} * {gap}) * "
            f"p{position + 1}.coeff {divisor_degree} ^ {gap} *\n"
            f"        ((-1 : ℚ) ^ ({remainder_degree} * {divisor_degree}) *\n"
            f"          p{position + 1}.resultant p{position + 2} "
            f"{divisor_degree} {remainder_degree}) := by\n"
            f"      rw [Polynomial.resultant_comm p{position + 2} "
            f"p{position + 1} {remainder_degree} {divisor_degree}]\n"
            f"    _ = {multiplier_text} *\n"
            f"        p{position + 1}.resultant p{position + 2} "
            f"{divisor_degree} {remainder_degree} := by\n"
            f"      norm_num [p{position + 1}, Polynomial.coeff_one, "
            f"Polynomial.coeff_X]"
        )
    resultant_steps = "\n\n".join(steps)
    last_constant = Rational(remainders[-1].nth(0))
    last_text = lean_rat(last_constant)
    rewrite_steps = ", ".join(
        [f"resultantStep{position}" for position in range(len(quotients))]
        + ["resultantLast"]
    )
    namespace = f"{namespace_prefix}{index:03d}"
    kernel_proof = squarefree_proof(kernel)
    certificate_source = ""
    if emit_certificate:
        certificate_source = f"""
theorem kernel_squarefree : Squarefree {kernel} := by
{kernel_proof}

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  {{ coefficients := {lean_int_list(coefficients)}
    discriminant := {discriminant}
    squarePart := {square_part}
    kernel := {kernel}
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = ({discriminant} : ℤ)
      exact polynomial_discr }}
"""
    return f"""import TraceEuclidean.DegreeSevenSurvivorDiscriminant

/-! Pure-kernel resultant certificate for retained septic {index:03d}. -/

namespace TraceEuclidean
namespace {namespace}

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨{discriminant}, {lean_int_list(coefficients)}, 1⟩

{polynomial_defs}

{quotient_defs}

{degree_lemmas}

{quotient_degree_lemmas}

{divisions}

{resultant_steps}

lemma resultantLast :
    p6.resultant p7 1 0 = {last_text} := by
  rw [show p7 = C {last_text} by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 {last_text})

theorem resultant_eq : p0.resultant p1 7 6 = ({signed_resultant} : ℚ) := by
  rw [{rewrite_steps}]
  norm_num

lemma polynomial_map_eq :
    row.polynomial.map (Int.castRingHom ℚ) = p0 := by
  ext n
  rw [voightPolynomial_map_coeff]
  by_cases hn : n ≤ 7
  · interval_cases n <;>
      norm_num [row, p0, voightCoefficient, Polynomial.coeff_one,
        Polynomial.coeff_X]
  · have hn8 : 8 ≤ n := by omega
    have hget : ({lean_int_list(coefficients)} : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((({lean_int_list(coefficients)} : List ℤ).getD n 0 : ℤ) : ℚ) = 0
      rw [hget]
      norm_num
    · rw [p0_degree]
      omega

lemma derivative_eq : p0.derivative = p1 := by
  apply Polynomial.funext
  intro x
  simp [p0, p1]
  ring

lemma row_resultant :
    let polynomial := row.polynomial.map (Int.castRingHom ℚ)
    polynomial.resultant polynomial.derivative 7 6 =
      voightExpectedResultant 7 row := by
  simp only
  rw [polynomial_map_eq, derivative_eq]
  norm_num [voightExpectedResultant, row]
  exact resultant_eq

theorem polynomial_discr :
    row.polynomial.discr = ({discriminant} : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h

{certificate_source}

end

end {namespace}
end TraceEuclidean
"""


def main() -> None:
    OUTPUT.mkdir(parents=True, exist_ok=True)
    desired: set[Path] = set()
    for index, (coefficients, discriminant) in enumerate(
        zip(COEFFICIENTS, EXPECTED_DISCRIMINANTS, strict=True)
    ):
        path = OUTPUT / f"Case{index:03d}.lean"
        path.write_text(
            render_case(index, coefficients, discriminant),
            encoding="utf-8",
            newline="\n",
        )
        desired.add(path)
        print(f"wrote {path.relative_to(ROOT)}")
    for stale in OUTPUT.glob("Case*.lean"):
        if stale not in desired:
            stale.unlink()
    print("degree-seven survivor discriminants: PASS (9 cases)")


if __name__ == "__main__":
    main()
