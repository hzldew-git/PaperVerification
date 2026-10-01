#!/usr/bin/env python3
"""Test local monogenicity of the certified integral orders.

For each prime dividing the power-order index, this script searches for an
element whose powers form a basis modulo that prime.  Such an element reduces
the corresponding local maximality proof to Dedekind's criterion.  Exhaustive
search is used when the residue algebra is small; otherwise a deterministic
candidate stream is used.
"""

from __future__ import annotations

import itertools
import json
import random
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "results" / "voight-nonsquarefree-basis-matrices.json"
OUTPUT = ROOT / "results" / "voight-local-monogenicity.json"
EXHAUSTIVE_LIMIT = 500_000
RANDOM_ATTEMPTS = 2_000


def as_fraction(pair: list[int]) -> Fraction:
    return Fraction(pair[0], pair[1])


def inverse(matrix: list[list[Fraction]]) -> list[list[Fraction]]:
    n = len(matrix)
    work = [
        row[:] + [Fraction(int(i == j)) for j in range(n)]
        for i, row in enumerate(matrix)
    ]
    for column in range(n):
        pivot = next(i for i in range(column, n) if work[i][column])
        work[column], work[pivot] = work[pivot], work[column]
        scale = work[column][column]
        work[column] = [value / scale for value in work[column]]
        for row in range(n):
            if row == column:
                continue
            scale = work[row][column]
            if scale:
                work[row] = [
                    a - scale * b
                    for a, b in zip(work[row], work[column])
                ]
    return [row[n:] for row in work]


def mat_vec(matrix: list[list[Fraction]], vector: list[Fraction]) -> list[Fraction]:
    return [sum(a * b for a, b in zip(row, vector)) for row in matrix]


def reduce_product(
    left: list[Fraction], right: list[Fraction], defining: list[int]
) -> list[Fraction]:
    n = len(defining) - 1
    result = [Fraction(0) for _ in range(2 * n - 1)]
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    for degree in range(2 * n - 2, n - 1, -1):
        leading = result[degree]
        if leading:
            for i in range(n):
                result[degree - n + i] -= leading * defining[i]
    return result[:n]


def multiplication_table(record: dict) -> tuple[list[list[list[int]]], list[int], list[int]]:
    n = record["degree"]
    basis = [[as_fraction(x) for x in row] for row in record["matrix"]]
    basis_inverse = inverse(basis)
    columns = [[basis[row][column] for row in range(n)] for column in range(n)]
    table: list[list[list[int]]] = []
    for left in columns:
        table_row = []
        for right in columns:
            coordinates = mat_vec(
                basis_inverse,
                reduce_product(left, right, record["coefficients"]),
            )
            if any(value.denominator != 1 for value in coordinates):
                raise ArithmeticError(
                    f"nonintegral product at degree {n}, row {record['row_number']}"
                )
            table_row.append([int(value) for value in coordinates])
        table.append(table_row)
    one = mat_vec(basis_inverse, [Fraction(1)] + [Fraction(0)] * (n - 1))
    alpha = mat_vec(basis_inverse, [Fraction(0), Fraction(1)] + [Fraction(0)] * (n - 2))
    if any(value.denominator != 1 for value in one + alpha):
        raise ArithmeticError("one or alpha has nonintegral coordinates")
    return table, [int(x) for x in one], [int(x) for x in alpha]


def prime_factors(value: int) -> list[int]:
    factors = []
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            factors.append(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor = 3 if divisor == 2 else divisor + 2
    if value > 1:
        factors.append(value)
    return factors


def det_nonzero_mod_p(columns: list[list[int]], prime: int) -> bool:
    n = len(columns)
    matrix = [[columns[column][row] % prime for column in range(n)] for row in range(n)]
    for column in range(n):
        pivot = next((row for row in range(column, n) if matrix[row][column]), None)
        if pivot is None:
            return False
        matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
        inverse_pivot = pow(matrix[column][column], -1, prime)
        for row in range(column + 1, n):
            if not matrix[row][column]:
                continue
            scale = matrix[row][column] * inverse_pivot % prime
            for j in range(column, n):
                matrix[row][j] = (matrix[row][j] - scale * matrix[column][j]) % prime
    return True


def is_generator(
    table: list[list[list[int]]], one: list[int], candidate: tuple[int, ...], prime: int
) -> bool:
    n = len(one)
    multiplication = [
        [
            sum(candidate[i] * table[i][column][row] for i in range(n)) % prime
            for column in range(n)
        ]
        for row in range(n)
    ]
    powers = [[value % prime for value in one]]
    for _ in range(1, n):
        previous = powers[-1]
        powers.append([
            sum(multiplication[row][column] * previous[column] for column in range(n)) % prime
            for row in range(n)
        ])
    return det_nonzero_mod_p(powers, prime)


def find_generator(
    table: list[list[list[int]]], one: list[int], alpha: list[int], prime: int,
    seed: int,
) -> tuple[tuple[int, ...] | None, bool, int]:
    n = len(one)
    tested: set[tuple[int, ...]] = set()

    def test(candidate: tuple[int, ...]) -> tuple[int, ...] | None:
        reduced = tuple(value % prime for value in candidate)
        if reduced in tested:
            return None
        tested.add(reduced)
        return reduced if is_generator(table, one, reduced, prime) else None

    candidates = [tuple(alpha)]
    candidates.extend(tuple(int(i == j) for i in range(n)) for j in range(n))
    for i in range(n):
        for j in range(i + 1, n):
            for coefficient in range(1, min(prime, 8)):
                candidate = [0] * n
                candidate[i] = 1
                candidate[j] = coefficient
                candidates.append(tuple(candidate))
    for candidate in candidates:
        answer = test(candidate)
        if answer is not None:
            return answer, False, len(tested)

    # Translation by scalars does not change the generated subalgebra.  The
    # Mathematica bases always begin with 1, which we verify here.
    if one != [1] + [0] * (n - 1):
        raise ArithmeticError(f"unexpected coordinates for one: {one}")
    search_size = prime ** (n - 1)
    if search_size <= EXHAUSTIVE_LIMIT:
        for tail in itertools.product(range(prime), repeat=n - 1):
            answer = test((0,) + tail)
            if answer is not None:
                return answer, True, len(tested)
        return None, True, len(tested)

    rng = random.Random(seed)
    for _ in range(RANDOM_ATTEMPTS):
        answer = test((0,) + tuple(rng.randrange(prime) for _ in range(n - 1)))
        if answer is not None:
            return answer, False, len(tested)
    return None, False, len(tested)


def main() -> None:
    payload = json.loads(SOURCE.read_text(encoding="utf-8"))
    results = []
    failures = []
    total = 0
    for position, record in enumerate(payload["records"], 1):
        factors = prime_factors(record["index"])
        if not factors:
            continue
        table, one, alpha = multiplication_table(record)
        local = []
        for prime in factors:
            total += 1
            generator, exhaustive, tested = find_generator(
                table, one, alpha, prime,
                seed=(record["degree"] * 1_000_000 + record["row_number"] * 1000 + prime),
            )
            item = {
                "prime": prime,
                "generator": list(generator) if generator is not None else None,
                "exhaustive": exhaustive,
                "tested": tested,
            }
            local.append(item)
            if generator is None:
                failures.append({
                    "degree": record["degree"],
                    "row_number": record["row_number"],
                    **item,
                })
        results.append({
            "degree": record["degree"],
            "row_number": record["row_number"],
            "index": record["index"],
            "local": local,
        })
        if position % 100 == 0:
            print(f"scanned {position}/{len(payload['records'])}; failures={len(failures)}")
    output = {
        "source_record_count": len(payload["records"]),
        "nontrivial_index_record_count": len(results),
        "local_problem_count": total,
        "failure_count": len(failures),
        "failures": failures,
        "records": results,
    }
    OUTPUT.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(
        "VOIGHT LOCAL MONOGENICITY:",
        f"{total - len(failures)}/{total} found;",
        f"{len(failures)} unresolved",
    )


if __name__ == "__main__":
    main()
