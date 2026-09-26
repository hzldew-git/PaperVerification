#!/usr/bin/env python3
"""Generate Lean Rabin certificates for the archived Voight polynomials.

The generated certificates use only exact arithmetic over finite prime fields.
Rows for which no irreducible reduction is found below the documented search
limit are placed in an explicit exception list for later criteria.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path

from generate_voight_discriminant_data import (
    ROOT,
    ROW_CHUNK_SIZE,
    SUPPLEMENTAL_TABLES,
    TABLES,
    PolynomialRow,
    Table,
    read_table,
    validate_hashes,
)


LEAN_ROOT = ROOT / "lean" / "TraceEuclidean"
EXCEPTIONS_OUTPUT = LEAN_ROOT / "V15VoightIrreducibilityExceptions.lean"
UMBRELLA_OUTPUT = LEAN_ROOT / "V15VoightIrreducibilityCertificates.lean"
CHUNK_DIR = LEAN_ROOT / "V15VoightIrreducibilityCertificates"
PART_SIZE = 100
PRIME_SEARCH_LIMIT = 5000


def trim(values: list[int]) -> list[int]:
    while values and values[-1] == 0:
        values.pop()
    return values


def add(left: list[int], right: list[int], p: int) -> list[int]:
    size = max(len(left), len(right))
    return trim(
        [
            ((left[index] if index < len(left) else 0)
             + (right[index] if index < len(right) else 0))
            % p
            for index in range(size)
        ]
    )


def sub(left: list[int], right: list[int], p: int) -> list[int]:
    size = max(len(left), len(right))
    return trim(
        [
            ((left[index] if index < len(left) else 0)
             - (right[index] if index < len(right) else 0))
            % p
            for index in range(size)
        ]
    )


def scale(scalar: int, values: list[int], p: int) -> list[int]:
    return trim([(scalar * value) % p for value in values])


def mul(left: list[int], right: list[int], p: int) -> list[int]:
    if not left or not right:
        return []
    result = [0] * (len(left) + len(right) - 1)
    for left_index, left_value in enumerate(left):
        for right_index, right_value in enumerate(right):
            result[left_index + right_index] = (
                result[left_index + right_index]
                + left_value * right_value
            ) % p
    return trim(result)


def power(values: list[int], exponent: int, p: int) -> list[int]:
    result = [1]
    base = values[:]
    remaining = exponent
    while remaining:
        if remaining & 1:
            result = mul(result, base, p)
        remaining >>= 1
        if remaining:
            base = mul(base, base, p)
    return result


def divmod_polynomial(
    dividend: list[int], divisor: list[int], p: int
) -> tuple[list[int], list[int]]:
    dividend = trim(dividend[:])
    divisor = trim(divisor[:])
    if not divisor:
        raise ZeroDivisionError("zero polynomial")
    if len(dividend) < len(divisor):
        return [], dividend
    quotient = [0] * (len(dividend) - len(divisor) + 1)
    inverse_lead = pow(divisor[-1], -1, p)
    while dividend and len(dividend) >= len(divisor):
        shift = len(dividend) - len(divisor)
        coefficient = dividend[-1] * inverse_lead % p
        quotient[shift] = coefficient
        for index, value in enumerate(divisor):
            dividend[index + shift] = (
                dividend[index + shift] - coefficient * value
            ) % p
        trim(dividend)
    return trim(quotient), dividend


def mul_mod(
    left: list[int], right: list[int], modulus: list[int], p: int
) -> list[int]:
    return divmod_polynomial(mul(left, right, p), modulus, p)[1]


def power_mod(
    values: list[int], exponent: int, modulus: list[int], p: int
) -> list[int]:
    result = [1]
    base = divmod_polynomial(values, modulus, p)[1]
    remaining = exponent
    while remaining:
        if remaining & 1:
            result = mul_mod(result, base, modulus, p)
        remaining >>= 1
        if remaining:
            base = mul_mod(base, base, modulus, p)
    return result


def xgcd(
    left: list[int], right: list[int], p: int
) -> tuple[list[int], list[int], list[int]]:
    old_remainder, remainder = trim(left[:]), trim(right[:])
    old_left, current_left = [1], []
    old_right, current_right = [], [1]
    while remainder:
        quotient, next_remainder = divmod_polynomial(
            old_remainder, remainder, p
        )
        old_remainder, remainder = remainder, next_remainder
        old_left, current_left = (
            current_left,
            sub(old_left, mul(quotient, current_left, p), p),
        )
        old_right, current_right = (
            current_right,
            sub(old_right, mul(quotient, current_right, p), p),
        )
    if not old_remainder:
        return [], [], []
    normalization = pow(old_remainder[-1], -1, p)
    return (
        scale(normalization, old_remainder, p),
        scale(normalization, old_left, p),
        scale(normalization, old_right, p),
    )


def primes_below(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * limit
    if limit:
        sieve[0] = 0
    if limit > 1:
        sieve[1] = 0
    for candidate in range(2, int(limit**0.5) + 1):
        if sieve[candidate]:
            sieve[candidate * candidate : limit : candidate] = (
                b"\x00" * (((limit - 1 - candidate * candidate) // candidate) + 1)
            )
    return [value for value in range(2, limit) if sieve[value]]


PRIMES = primes_below(PRIME_SEARCH_LIMIT)


@dataclass(frozen=True)
class RabinCertificate:
    prime: int
    states: tuple[tuple[int, ...], ...]
    quotients: tuple[tuple[int, ...], ...]
    bezout_left: tuple[tuple[int, ...], ...]
    bezout_right: tuple[tuple[int, ...], ...]


def try_prime(
    coefficients: tuple[int, ...], degree: int, p: int, full: bool
) -> RabinCertificate | None:
    modulus = trim([coefficient % p for coefficient in coefficients])
    if len(modulus) != degree + 1 or modulus[-1] != 1:
        return None
    if degree == 1:
        powered = power([0, 1], p, p)
        quotient, remainder = divmod_polynomial(
            sub(powered, [0, 1], p), modulus, p
        )
        if remainder:
            return None
        if not full:
            return RabinCertificate(p, (), (), (), ())
        return RabinCertificate(
            p,
            ((0, 1), (0, 1)),
            (tuple(quotient),),
            ((),),
            ((),),
        )
    states = [[0, 1]]
    for _ in range(degree):
        states.append(power_mod(states[-1], p, modulus, p))
    if states[-1] != [0, 1]:
        return None
    left_certificates = [[] for _ in range(degree)]
    right_certificates = [[] for _ in range(degree)]
    for factor_degree in range(1, degree):
        if degree % factor_degree:
            continue
        difference = sub(states[factor_degree], [0, 1], p)
        gcd, left, right = xgcd(modulus, difference, p)
        if gcd != [1]:
            return None
        left_certificates[factor_degree] = left
        right_certificates[factor_degree] = right
    if not full:
        return RabinCertificate(p, (), (), (), ())
    quotients = []
    exact_states = [[0, 1]]
    for _ in range(degree):
        powered = power(exact_states[-1], p, p)
        quotient, next_state = divmod_polynomial(powered, modulus, p)
        quotients.append(quotient)
        exact_states.append(next_state)
    if exact_states != states:
        raise ArithmeticError("modular and exact Frobenius replays disagree")
    for factor_degree in range(1, degree):
        if degree % factor_degree:
            continue
        difference = sub(exact_states[factor_degree], [0, 1], p)
        bezout = add(
            mul(left_certificates[factor_degree], modulus, p),
            mul(right_certificates[factor_degree], difference, p),
            p,
        )
        if bezout != [1]:
            raise ArithmeticError("invalid generated Bezout identity")
    return RabinCertificate(
        p,
        tuple(tuple(values) for values in exact_states),
        tuple(tuple(values) for values in quotients),
        tuple(tuple(values) for values in left_certificates),
        tuple(tuple(values) for values in right_certificates),
    )


def certificate_for_row(
    row: PolynomialRow, degree: int
) -> RabinCertificate | None:
    for prime in PRIMES:
        if try_prime(row.coefficients, degree, prime, full=False) is not None:
            certificate = try_prime(row.coefficients, degree, prime, full=True)
            if certificate is None:
                raise AssertionError("certificate vanished on exact replay")
            return certificate
    return None


def lean_list(values: tuple[int, ...] | list[int]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def lean_nested(values: tuple[tuple[int, ...], ...]) -> str:
    return "[" + ", ".join(lean_list(value) for value in values) + "]"


def lean_row(row: PolynomialRow) -> str:
    return (
        "⟨"
        f"{row.field_discriminant}, {lean_list(row.coefficients)}, {row.index}"
        "⟩"
    )


def lean_certificate(certificate: RabinCertificate) -> str:
    return "\n".join(
        [
            f"    ⟨{certificate.prime},",
            f"      {lean_nested(certificate.states)},",
            f"      {lean_nested(certificate.quotients)},",
            f"      {lean_nested(certificate.bezout_left)},",
            f"      {lean_nested(certificate.bezout_right)}⟩",
        ]
    )


def all_data() -> dict[int, tuple[Table, list[PolynomialRow]]]:
    return {
        table.degree: (table, read_table(table))
        for table in TABLES + SUPPLEMENTAL_TABLES
    }


def compute_certificates(
    data: dict[int, tuple[Table, list[PolynomialRow]]]
) -> tuple[
    dict[int, list[RabinCertificate | None]],
    dict[int, list[PolynomialRow]],
]:
    certificates: dict[int, list[RabinCertificate | None]] = {}
    exceptions: dict[int, list[PolynomialRow]] = {}
    for degree, (_, rows) in data.items():
        degree_certificates = []
        degree_exceptions = []
        for row in rows:
            certificate = certificate_for_row(row, degree)
            degree_certificates.append(certificate)
            if certificate is None:
                degree_exceptions.append(row)
        certificates[degree] = degree_certificates
        exceptions[degree] = degree_exceptions
        print(
            f"degree {degree}: {len(rows) - len(degree_exceptions)} Rabin "
            f"certificates, {len(degree_exceptions)} exceptions"
        )
    return certificates, exceptions


def render_exceptions(
    data: dict[int, tuple[Table, list[PolynomialRow]]],
    exceptions: dict[int, list[PolynomialRow]],
) -> str:
    out = [
        "import TraceEuclidean.V15FiniteFieldIrreducibilityCertificate",
        "",
        "/-! Explicit boundary of the single-prime Rabin certificate method. -/",
        "",
        "namespace TraceEuclidean",
        "",
    ]
    for degree, (table, _) in data.items():
        exception_body = (
            "[]"
            if not exceptions[degree]
            else "[\n"
            + ",\n".join(
                f"    {lean_row(row)}" for row in exceptions[degree]
            )
            + "\n  ]"
        )
        out.extend(
            [
                f"def v15VoightRabinExceptions{table.lean_name} :",
                "    List V15VoightPolynomialRow :=",
                f"  {exception_body}",
                "",
            ]
        )
    out.extend(
        [
            "/-- Rows not covered by one irreducible modular reduction. -/",
            "def v15VoightRabinExceptions : ℕ → List V15VoightPolynomialRow",
        ]
    )
    for degree in range(5):
        out.append(f"  | {degree} => []")
    for _, (table, _) in data.items():
        out.append(
            f"  | {table.degree} => v15VoightRabinExceptions{table.lean_name}"
        )
    out.extend(
        [
            "  | _ => []",
            "",
            "end TraceEuclidean",
            "",
        ]
    )
    return "\n".join(out)


def part_metadata(
    data: dict[int, tuple[Table, list[PolynomialRow]]]
) -> list[dict[str, object]]:
    metadata: list[dict[str, object]] = []
    for degree, (table, rows) in data.items():
        for chunk_index, chunk_start in enumerate(
            range(0, len(rows), ROW_CHUNK_SIZE)
        ):
            chunk_count = min(ROW_CHUNK_SIZE, len(rows) - chunk_start)
            chunk_name = (
                f"v15VoightPolynomialRows{table.lean_name}Chunk{chunk_index}"
            )
            for part_index, part_start in enumerate(
                range(0, chunk_count, PART_SIZE)
            ):
                part_count = min(PART_SIZE, chunk_count - part_start)
                module = (
                    f"{table.lean_name}Chunk{chunk_index}Part{part_index}"
                )
                raw_expression = (
                    f"({chunk_name}.drop {part_start}).take {part_count}"
                )
                expression = (
                    f"({raw_expression}).filter fun row => decide "
                    f"(row ∉ v15VoightRabinExceptions{table.lean_name})"
                )
                metadata.append(
                    {
                        "degree": degree,
                        "table": table,
                        "chunk_start": chunk_start,
                        "part_start": part_start,
                        "part_count": part_count,
                        "module": module,
                        "expression": expression,
                    }
                )
    return metadata


def render_chunks(
    data: dict[int, tuple[Table, list[PolynomialRow]]],
    certificates: dict[int, list[RabinCertificate | None]],
) -> dict[str, str]:
    rendered: dict[str, str] = {}
    previous_module: str | None = None
    for part in part_metadata(data):
        table = part["table"]
        assert isinstance(table, Table)
        degree = int(part["degree"])
        absolute_start = int(part["chunk_start"]) + int(part["part_start"])
        absolute_end = absolute_start + int(part["part_count"])
        part_certificates = [
            certificate
            for certificate in certificates[degree][absolute_start:absolute_end]
            if certificate is not None
        ]
        module = str(part["module"])
        certificate_name = f"v15VoightRabinCertificates{module}"
        check_name = f"v15_voightRabinCertificates{module}_check"
        theorem_name = f"v15_voightRows{module}_irreducible"
        import_line = (
            "import TraceEuclidean.V15VoightIrreducibilityExceptions"
            if previous_module is None
            else "import TraceEuclidean.V15VoightIrreducibilityCertificates."
            + previous_module
        )
        certificate_body = (
            "[\n" + ",\n".join(
                lean_certificate(certificate)
                for certificate in part_certificates
            ) + "\n  ]"
        )
        expression = str(part["expression"])
        certificate_resource_options = (
            [
                "set_option maxHeartbeats 0 in",
                "-- Degree-ten certificate terms exceed the default elaboration budget.",
            ]
            if degree == 10
            else []
        )
        rendered[module + ".lean"] = "\n".join(
            [
                import_line,
                "",
                "/-! Generated Rabin certificates for at most one hundred rows. -/",
                "",
                "namespace TraceEuclidean",
                "",
                "set_option linter.style.longLine false",
                "set_option maxRecDepth 100000",
                "",
                *certificate_resource_options,
                f"def {certificate_name} :",
                "    List V15RabinIrreducibilityCertificate :=",
                f"  {certificate_body}",
                "",
                "set_option maxRecDepth 100000 in",
                "set_option maxHeartbeats 0 in",
                "-- Native replay is exact but intentionally has no heartbeat limit.",
                f"theorem {check_name} :",
                f"    v15RabinCertificateBatchCheck {degree}",
                f"      ({expression}) {certificate_name} = true := by",
                "  native_decide",
                "",
                f"theorem {theorem_name} :",
                f"    ∀ row ∈ ({expression}), Irreducible row.polynomial :=",
                f"  v15_irreducible_of_batchCheck_eq_true {degree}",
                f"    (certificates := {certificate_name}) {check_name}",
                "",
                "end TraceEuclidean",
                "",
            ]
        )
        previous_module = module
    return rendered


def nested_append(theorems: list[str]) -> str:
    if not theorems:
        return "by simp"
    expression = theorems[0]
    for theorem in theorems[1:]:
        expression = f"v15_forall_mem_append ({expression}) {theorem}"
    return expression


def render_umbrella(
    data: dict[int, tuple[Table, list[PolynomialRow]]]
) -> str:
    metadata = part_metadata(data)
    out = [
        *[
            "import TraceEuclidean.V15VoightIrreducibilityCertificates."
            + str(part["module"])
            for part in metadata
        ],
        "",
        "/-! Rabin irreducibility theorems for all single-prime rows. -/",
        "",
        "namespace TraceEuclidean",
        "",
        "set_option linter.style.longLine false",
        "",
    ]
    for degree, (table, _) in data.items():
        parts = [part for part in metadata if int(part["degree"]) == degree]
        expressions = [f"({part['expression']})" for part in parts]
        theorems = [
            f"v15_voightRows{part['module']}_irreducible" for part in parts
        ]
        predicate = (
            f"fun row => decide (row ∉ "
            f"v15VoightRabinExceptions{table.lean_name})"
        )
        out.extend(
            [
                f"theorem v15_voightPolynomialRows{table.lean_name}_rabin_irreducible :",
                f"    ∀ row ∈ v15VoightPolynomialRows{table.lean_name}.filter",
                f"      ({predicate}), Irreducible row.polynomial := by",
                f"  have hsplit : v15VoightPolynomialRows{table.lean_name}.filter",
                f"      ({predicate}) =",
                "      " + " ++\n      ".join(expressions) + " := by",
                "    native_decide",
                "  rw [hsplit]",
                f"  exact {nested_append(theorems)}",
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
    data = all_data()
    certificates, exceptions = compute_certificates(data)
    generated_exceptions = render_exceptions(data, exceptions)
    generated_chunks = render_chunks(data, certificates)
    generated_umbrella = render_umbrella(data)
    if args.check:
        if EXCEPTIONS_OUTPUT.read_text(encoding="utf-8") != generated_exceptions:
            raise SystemExit("V15VoightIrreducibilityExceptions.lean is stale")
        if UMBRELLA_OUTPUT.read_text(encoding="utf-8") != generated_umbrella:
            raise SystemExit("V15VoightIrreducibilityCertificates.lean is stale")
        actual = {path.name for path in CHUNK_DIR.glob("*.lean")}
        if actual != set(generated_chunks):
            raise SystemExit("irreducibility certificate chunk set is stale")
        for filename, contents in generated_chunks.items():
            if (CHUNK_DIR / filename).read_text(encoding="utf-8") != contents:
                raise SystemExit(f"{filename} is stale")
        print("Voight Rabin irreducibility certificates: PASS")
        return
    EXCEPTIONS_OUTPUT.write_text(
        generated_exceptions, encoding="utf-8", newline="\n"
    )
    UMBRELLA_OUTPUT.write_text(
        generated_umbrella, encoding="utf-8", newline="\n"
    )
    CHUNK_DIR.mkdir(parents=True, exist_ok=True)
    for stale in CHUNK_DIR.glob("*.lean"):
        if stale.name not in generated_chunks:
            stale.unlink()
    for filename, contents in generated_chunks.items():
        (CHUNK_DIR / filename).write_text(
            contents, encoding="utf-8", newline="\n"
        )


if __name__ == "__main__":
    main()
