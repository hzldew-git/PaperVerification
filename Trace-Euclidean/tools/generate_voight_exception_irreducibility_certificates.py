#!/usr/bin/env python3
"""Generate multi-prime irreducibility certificates for Voight exceptions.

The single-prime Rabin method cannot handle a small number of defining
polynomials whose Galois groups have no full cycle.  For each possible proper
factor degree, this generator chooses a small prime, completely factors the
polynomial over that prime field, and certifies every displayed irreducible
factor with the same Rabin kernel used by the main generator.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path

from sympy import Poly, symbols

from generate_voight_discriminant_data import (
    ROOT,
    SUPPLEMENTAL_TABLES,
    TABLES,
    PolynomialRow,
    read_table,
    validate_hashes,
)
from generate_voight_irreducibility_certificates import (
    RabinCertificate,
    divmod_polynomial,
    lean_list,
    lean_nested,
    lean_row,
    mul,
    primes_below,
    trim,
    try_prime,
)


OUTPUT = (
    ROOT / "lean" / "TraceEuclidean"
    / "V15VoightExceptionalIrreducibilityCertificates.lean"
)
SPECIAL_DEGREE = 8
SPECIAL_INDEX = 130
SEARCH_PRIMES = primes_below(31)
X = symbols("x")

EXCEPTION_INDICES = {
    6: [8, 76, 94, 109, 274, 289, 297, 376, 445, 483, 505, 507, 551, 575, 769, 804],
    8: [2, 4, 5, 20, 22, 30, 46, 65, 106, 126, 130, 148],
    9: [6],
    10: [69, 166],
}


@dataclass(frozen=True)
class CompleteFactorization:
    prime: int
    factors: tuple[tuple[int, ...], ...]
    certificates: tuple[RabinCertificate, ...]


@dataclass(frozen=True)
class MultiPrimeCertificate:
    factorizations: tuple[CompleteFactorization, ...]
    assignments: tuple[int, ...]


def factor_mod_prime(
    coefficients: tuple[int, ...], prime: int
) -> tuple[tuple[int, ...], ...]:
    """Factor a monic polynomial over a prime field exactly with SymPy."""
    reduced = trim([coefficient % prime for coefficient in coefficients])
    if not reduced or reduced[-1] != 1:
        raise ValueError("factorization input must remain monic")
    polynomial = Poly.from_list(list(reversed(reduced)), gens=X, modulus=prime)
    unit, sympy_factors = polynomial.factor_list()
    if int(unit) % prime != 1:
        raise ArithmeticError("unexpected nonmonic factorization unit")
    factors: list[tuple[int, ...]] = []
    for factor, multiplicity in sympy_factors:
        ascending = tuple(
            int(value) % prime for value in reversed(factor.all_coeffs())
        )
        factors.extend([ascending] * multiplicity)
    product = [1]
    for factor in factors:
        product = mul(product, list(factor), prime)
    if product != reduced:
        raise ArithmeticError("finite-field factorization product mismatch")
    return tuple(factors)


def signed_divisors(value: int) -> set[int]:
    if value == 0:
        raise ValueError("the defining polynomial has zero constant term")
    absolute = abs(value)
    return {
        sign * divisor
        for divisor in range(1, absolute + 1)
        if absolute % divisor == 0
        for sign in (-1, 1)
    }


def subset_signatures(
    factors: tuple[tuple[int, ...], ...], prime: int
) -> set[tuple[int, int]]:
    signatures = {(0, 1)}
    for factor in factors:
        degree = len(factor) - 1
        constant = factor[0] % prime
        signatures |= {
            (old_degree + degree, old_constant * constant % prime)
            for old_degree, old_constant in tuple(signatures)
        }
    return signatures


def excludes_degree(
    row: PolynomialRow,
    degree: int,
    prime: int,
    factors: tuple[tuple[int, ...], ...],
) -> bool:
    allowed = {value % prime for value in signed_divisors(row.coefficients[0])}
    possible = {
        constant
        for subset_degree, constant in subset_signatures(factors, prime)
        if subset_degree == degree
    }
    return possible.isdisjoint(allowed)


def complete_factorization(
    coefficients: tuple[int, ...], prime: int
) -> CompleteFactorization:
    factors = factor_mod_prime(coefficients, prime)
    certificates = []
    for factor in factors:
        certificate = try_prime(
            factor, len(factor) - 1, prime, full=True
        )
        if certificate is None:
            raise ArithmeticError(
                f"displayed finite-field factor is reducible: p={prime}, "
                f"factor={factor}, source={coefficients}"
            )
        certificates.append(certificate)
    return CompleteFactorization(prime, factors, tuple(certificates))


def certificate_for_row(
    row: PolynomialRow, degree: int, *, special: bool = False
) -> MultiPrimeCertificate:
    upper_degree = degree // 2 - (1 if special else 0)
    factorization_cache: dict[int, CompleteFactorization] = {}
    selected_primes: list[int] = []
    for factor_degree in range(1, upper_degree + 1):
        best: tuple[int, int] | None = None
        for prime in SEARCH_PRIMES:
            factorization = factorization_cache.get(prime)
            if factorization is None:
                factorization = complete_factorization(row.coefficients, prime)
                factorization_cache[prime] = factorization
            if excludes_degree(
                row, factor_degree, prime, factorization.factors
            ):
                candidate = (prime**factor_degree, prime)
                if best is None or candidate < best:
                    best = candidate
        if best is None:
            raise ArithmeticError(
                f"degree {degree}, discriminant {row.field_discriminant}: "
                f"no exclusion for factor degree {factor_degree}"
            )
        selected_primes.append(best[1])
    unique_primes: list[int] = []
    for prime in selected_primes:
        if prime not in unique_primes:
            unique_primes.append(prime)
    factorizations = tuple(factorization_cache[p] for p in unique_primes)
    assignments = tuple(unique_primes.index(p) for p in selected_primes)
    return MultiPrimeCertificate(factorizations, assignments)


def lean_rabin(certificate: RabinCertificate) -> str:
    return (
        f"⟨{certificate.prime}, {lean_nested(certificate.states)}, "
        f"{lean_nested(certificate.quotients)}, "
        f"{lean_nested(certificate.bezout_left)}, "
        f"{lean_nested(certificate.bezout_right)}⟩"
    )


def lean_factorization(certificate: CompleteFactorization) -> str:
    entries = []
    for factor, rabin in zip(
        certificate.factors, certificate.certificates, strict=True
    ):
        factor_row = PolynomialRow(0, factor, 0)
        entries.append(f"({lean_row(factor_row)}, {lean_rabin(rabin)})")
    return f"⟨{certificate.prime}, [" + ", ".join(entries) + "]⟩"


def lean_multi(certificate: MultiPrimeCertificate) -> str:
    return (
        "⟨["
        + ",\n      ".join(
            lean_factorization(factorization)
            for factorization in certificate.factorizations
        )
        + f"], {lean_list(certificate.assignments)}⟩"
    )


def table_for_degree(degree: int):
    return next(
        table
        for table in TABLES + SUPPLEMENTAL_TABLES
        if table.degree == degree
    )


def render() -> str:
    out = [
        "import TraceEuclidean.V15ModularFactorizationCertificate",
        "import TraceEuclidean.V15VoightIrreducibilityExceptions",
        "",
        "/-! Generated multi-prime certificates for the Rabin exceptions. -/",
        "",
        "namespace TraceEuclidean",
        "",
        "set_option linter.style.longLine false",
        "set_option maxRecDepth 100000",
        "",
    ]
    for degree, indices in EXCEPTION_INDICES.items():
        table = table_for_degree(degree)
        rows = read_table(table)
        regular_indices = [
            index
            for index in indices
            if (degree, index) != (SPECIAL_DEGREE, SPECIAL_INDEX)
        ]
        names = []
        for index in regular_indices:
            row = rows[index]
            certificate = certificate_for_row(row, degree)
            name = f"v15VoightMultiPrimeCertificate{table.lean_name}{index}"
            names.append(name)
            out.extend(
                [
                    f"def {name} : V15MultiPrimeIrreducibilityCertificate :=",
                    f"  {lean_multi(certificate)}",
                    "",
                ]
            )
        row_list_name = f"v15VoightMultiPrimeRows{table.lean_name}"
        certificate_list_name = (
            f"v15VoightMultiPrimeCertificates{table.lean_name}"
        )
        out.extend(
            [
                f"def {row_list_name} : List V15VoightPolynomialRow :=",
                "  [" + ",\n    ".join(
                    lean_row(rows[index]) for index in regular_indices
                ) + "]",
                "",
                f"def {certificate_list_name} :",
                "    List V15MultiPrimeIrreducibilityCertificate :=",
                "  [" + ", ".join(names) + "]",
                "",
                "set_option maxHeartbeats 0 in",
                "-- Large generated certificate replay; bounded structurally by the finite data.",
                f"theorem v15_voightMultiPrimeCertificates{table.lean_name}_check :",
                f"    v15MultiPrimeCertificateBatchCheck {degree}",
                f"      {row_list_name} {certificate_list_name} = true := by",
                "  native_decide",
                "",
                f"theorem v15_voightMultiPrimeRows{table.lean_name}_irreducible :",
                f"    ∀ row ∈ {row_list_name}, Irreducible row.polynomial :=",
                f"  v15_irreducible_of_multiPrimeBatchCheck_eq_true {degree}",
                f"    (certificates := {certificate_list_name})",
                f"    v15_voightMultiPrimeCertificates{table.lean_name}_check",
                "",
            ]
        )
    special_rows = read_table(table_for_degree(SPECIAL_DEGREE))
    special_row = special_rows[SPECIAL_INDEX]
    special_certificate = certificate_for_row(
        special_row, SPECIAL_DEGREE, special=True
    )
    if len(special_certificate.factorizations) != 1:
        raise ArithmeticError("special row should use one factorization")
    special_factorization_three = special_certificate.factorizations[0]
    if special_factorization_three.prime != 3:
        raise ArithmeticError("special exclusion factorization should use p=3")
    special_factorization_five = complete_factorization(
        special_row.coefficients, 5
    )
    out.extend(
        [
            "def v15VoightSpecialEightRow : V15VoightPolynomialRow :=",
            f"  {lean_row(special_row)}",
            "",
            "def v15VoightSpecialEightFactorizationThree :",
            "    V15ModularFactorizationCertificate :=",
            f"  {lean_factorization(special_factorization_three)}",
            "",
            "def v15VoightSpecialEightFactorizationFive :",
            "    V15ModularFactorizationCertificate :=",
            f"  {lean_factorization(special_factorization_five)}",
            "",
            "set_option maxHeartbeats 0 in",
            "-- Large generated certificate replay; bounded structurally by the finite data.",
            "theorem v15_voightSpecialEightFactorizationThree_valid :",
            "    v15VoightSpecialEightFactorizationThree.Valid 8",
            "      v15VoightSpecialEightRow := by",
            "  native_decide",
            "",
            "set_option maxHeartbeats 0 in",
            "-- Large generated certificate replay; bounded structurally by the finite data.",
            "theorem v15_voightSpecialEightFactorizationFive_valid :",
            "    v15VoightSpecialEightFactorizationFive.Valid 8",
            "      v15VoightSpecialEightRow := by",
            "  native_decide",
            "",
        ]
    )
    for factor_degree in range(1, 4):
        if not excludes_degree(
            special_row,
            factor_degree,
            special_factorization_three.prime,
            special_factorization_three.factors,
        ):
            raise ArithmeticError("special factorization does not exclude degree")
        out.extend(
            [
                "set_option maxHeartbeats 0 in",
                "-- Large generated certificate replay; bounded structurally by the finite data.",
                f"theorem v15_voightSpecialEight_excludes_degree_{factor_degree} :",
                "    v15VoightSpecialEightFactorizationThree.excludesDegree",
                f"      v15VoightSpecialEightRow {factor_degree} = true := by",
                "  native_decide",
                "",
            ]
        )
    for factorization, residue, suffix in (
        (special_factorization_three, 1, "Three"),
        (special_factorization_five, 4, "Five"),
    ):
        possible = {
            constant
            for degree, constant in subset_signatures(
                factorization.factors, factorization.prime
            )
            if degree == 4
        }
        if possible != {residue}:
            raise ArithmeticError(
                f"special p={factorization.prime} factorization does not "
                f"force residue {residue}: {possible}"
            )
        out.extend(
            [
                "set_option maxHeartbeats 0 in",
                "-- Large generated certificate replay; bounded structurally by the finite data.",
                f"theorem v15_voightSpecialEight_forces_constant_{suffix.lower()} :",
                f"    v15VoightSpecialEightFactorization{suffix}.forcesConstantResidue",
                f"      4 ({residue} : ZMod {factorization.prime}) = true := by",
                "  native_decide",
                "",
            ]
        )
    out.extend(["end TraceEuclidean", ""])
    return "\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    validate_hashes()
    generated = render()
    if args.check:
        if OUTPUT.read_text(encoding="utf-8") != generated:
            raise SystemExit(
                "V15VoightExceptionalIrreducibilityCertificates.lean is stale"
            )
        print("Voight exceptional irreducibility certificates: PASS")
        return
    OUTPUT.write_text(generated, encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
