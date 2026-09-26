#!/usr/bin/env python3
"""Generate the Lean discriminant lists from Voight's archived field tables."""

from __future__ import annotations

import ast
import argparse
import hashlib
import math
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
INPUT_DIR = ROOT / "inputs" / "voight"
OUTPUT = ROOT / "lean" / "TraceEuclidean" / "V15VoightDiscriminantData.lean"
ROW_CHUNK_SIZE = 100


@dataclass(frozen=True)
class Table:
    degree: int
    filename: str
    expected_count: int
    expected_minimum: int
    lean_name: str
    line_records: bool = False


@dataclass(frozen=True)
class PolynomialRow:
    field_discriminant: int
    coefficients: tuple[int, ...]
    index: int


TABLES = (
    Table(5, "5-17.txt", 674, 14641, "Five"),
    Table(6, "6-16.txt", 827, 300125, "Six"),
    Table(7, "7-15.5.txt", 301, 20134393, "Seven"),
    Table(8, "8-15.txt", 164, 282300416, "Eight"),
    Table(9, "9-14.5.txt", 15, 9685993193, "Nine"),
)

SUPPLEMENTAL_TABLES = (
    Table(10, "10.txt", 792, 443952558373, "Ten", line_records=True),
)

EXPECTED_HASHES = {
    "5-17.txt": "7c2ce57f51de3ad34bb60ade85659689fc629406315e9699a144f737d1b34192",
    "6-16.txt": "6e6bc75b54ad2643a42a3dfdd9497347eb89735d00c5b7367e934ad32d8ae082",
    "7-15.5.txt": "95ed179560eb866445eee3da22826cf98cc5eb0bc7f5091c27f4d332dc421a3d",
    "8-15.txt": "204a0ea04e2f4079f6fea20369ad8822d4d678a718272b9aaea68cf144b83294",
    "9-14.5.txt": "9c14aa90371184020bb121c36e63ceaa5bd4ada0eb55198fd94d4df67d6d3821",
    "10.txt": "cceac525009d9ab6b947e17186a5e74df2643eace152955702d306af6defbe83",
}


def validate_hashes() -> None:
    for filename, expected in EXPECTED_HASHES.items():
        actual = hashlib.sha256((INPUT_DIR / filename).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"{filename}: expected SHA-256 {expected}, found {actual}")


def bareiss_determinant(matrix: list[list[int]]) -> int:
    """Compute an exact integer determinant by fraction-free elimination."""
    size = len(matrix)
    if size == 0:
        return 1
    work = [row.copy() for row in matrix]
    sign = 1
    previous_pivot = 1
    for pivot_index in range(size - 1):
        pivot_row = next(
            (
                row
                for row in range(pivot_index, size)
                if work[row][pivot_index] != 0
            ),
            None,
        )
        if pivot_row is None:
            return 0
        if pivot_row != pivot_index:
            work[pivot_index], work[pivot_row] = (
                work[pivot_row],
                work[pivot_index],
            )
            sign = -sign
        pivot = work[pivot_index][pivot_index]
        for row in range(pivot_index + 1, size):
            for column in range(pivot_index + 1, size):
                numerator = (
                    work[row][column] * pivot
                    - work[row][pivot_index] * work[pivot_index][column]
                )
                quotient, remainder = divmod(numerator, previous_pivot)
                if remainder != 0:
                    raise ArithmeticError("nonexact Bareiss division")
                work[row][column] = quotient
            work[row][pivot_index] = 0
        previous_pivot = pivot
    return sign * work[-1][-1]


def polynomial_discriminant(coefficients: list[int]) -> int:
    """Return the discriminant of a monic polynomial in ascending order."""
    degree = len(coefficients) - 1
    if degree <= 1:
        return 1
    polynomial_descending = list(reversed(coefficients))
    derivative_descending = [
        coefficient * exponent
        for exponent, coefficient in zip(
            range(degree, 0, -1), polynomial_descending[:-1]
        )
    ]
    derivative_degree = degree - 1
    size = degree + derivative_degree
    sylvester = [[0 for _ in range(size)] for _ in range(size)]
    for row in range(derivative_degree):
        sylvester[row][row : row + degree + 1] = polynomial_descending
    for offset in range(degree):
        row = derivative_degree + offset
        sylvester[row][offset : offset + derivative_degree + 1] = (
            derivative_descending
        )
    resultant = bareiss_determinant(sylvester)
    sign = -1 if degree * (degree - 1) // 2 % 2 else 1
    return sign * resultant // coefficients[-1]


def read_table(table: Table) -> list[PolynomialRow]:
    source = (INPUT_DIR / table.filename).read_text(encoding="utf-8")
    if table.line_records:
        rows = [ast.literal_eval(line) for line in source.splitlines() if line.strip()]
    else:
        rows = ast.literal_eval(source)
    if len(rows) != table.expected_count:
        raise ValueError(
            f"{table.filename}: expected {table.expected_count} rows, found {len(rows)}"
        )
    parsed_rows: list[PolynomialRow] = []
    for row_number, row in enumerate(rows, 1):
        if not (
            isinstance(row, list)
            and len(row) == 2
            and isinstance(row[0], int)
            and isinstance(row[1], list)
            and all(isinstance(c, int) for c in row[1])
        ):
            raise ValueError(f"{table.filename}:{row_number}: malformed row")
        discriminant, coefficients = row
        if discriminant <= 0:
            raise ValueError(f"{table.filename}:{row_number}: nonpositive discriminant")
        if len(coefficients) != table.degree + 1 or coefficients[-1] != 1:
            raise ValueError(f"{table.filename}:{row_number}: malformed monic polynomial")
        polynomial_disc = polynomial_discriminant(coefficients)
        quotient, remainder = divmod(polynomial_disc, discriminant)
        index = math.isqrt(quotient) if quotient >= 0 else -1
        if remainder != 0 or index <= 0 or index * index != quotient:
            raise ValueError(
                f"{table.filename}:{row_number}: polynomial discriminant "
                f"{polynomial_disc} is not a positive square multiple of "
                f"field discriminant {discriminant}"
            )
        parsed_rows.append(
            PolynomialRow(discriminant, tuple(coefficients), index)
        )
    discriminants = [row.field_discriminant for row in parsed_rows]
    if discriminants[0] != table.expected_minimum:
        raise ValueError(
            f"{table.filename}: expected first discriminant {table.expected_minimum}, "
            f"found {discriminants[0]}"
        )
    if discriminants != sorted(discriminants):
        raise ValueError(f"{table.filename}: discriminants are not sorted")
    return parsed_rows


def format_list(values: list[int]) -> str:
    lines = []
    for start in range(0, len(values), 6):
        chunk = ", ".join(str(value) for value in values[start : start + 6])
        lines.append(f"    {chunk}")
    return "[\n" + ",\n".join(lines) + "\n  ]"


def format_integer_list(values: tuple[int, ...]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def format_polynomial_rows(rows: list[PolynomialRow]) -> str:
    rendered = [
        "    ⟨"
        f"{row.field_discriminant}, "
        f"{format_integer_list(row.coefficients)}, "
        f"{row.index}"
        "⟩"
        for row in rows
    ]
    return "[\n" + ",\n".join(rendered) + "\n  ]"


def format_chunk_concatenation(names: list[str]) -> str:
    return " ++\n    ".join(names)


def render() -> str:
    validate_hashes()
    data = {table.degree: read_table(table) for table in TABLES}
    supplemental = {
        table.degree: read_table(table) for table in SUPPLEMENTAL_TABLES
    }
    if supplemental[10][0].field_discriminant <= 14**10:
        raise ValueError("10.txt: first discriminant does not exceed 14^10")
    out = [
        "import Mathlib",
        "",
        "/-!",
        "# Discriminants from Voight's archived totally real field tables",
        "",
        "This file is generated by `tools/generate_voight_discriminant_data.py`.",
        "It contains the archived defining-polynomial rows and their discriminant",
        "columns.  The source tables, archive timestamps, and checksums are",
        "recorded under `inputs/voight`.",
        "-/",
        "",
        "namespace TraceEuclidean",
        "",
        "open scoped Polynomial",
        "",
        "/-- One archived Voight row: field discriminant, ascending defining-",
        "polynomial coefficients, and the positive power-order index. -/",
        "structure V15VoightPolynomialRow where",
        "  fieldDiscriminant : ℕ",
        "  coefficients : List ℤ",
        "  index : ℕ",
        "deriving DecidableEq, Repr",
        "",
        "/-- The integral defining polynomial encoded by an archived row. -/",
        "def V15VoightPolynomialRow.polynomial",
        "    (row : V15VoightPolynomialRow) : ℤ[X] :=",
        "  Polynomial.ofFinsupp",
        "    (AddMonoidAlgebra.ofCoeff row.coefficients.toFinsupp)",
        "",
    ]
    for table in TABLES + SUPPLEMENTAL_TABLES:
        rows = data[table.degree] if table.degree in data else supplemental[table.degree]
        chunk_names = []
        for chunk_index, start in enumerate(range(0, len(rows), ROW_CHUNK_SIZE)):
            chunk_name = (
                f"v15VoightPolynomialRows{table.lean_name}Chunk{chunk_index}"
            )
            chunk_names.append(chunk_name)
            chunk = rows[start : start + ROW_CHUNK_SIZE]
            out.extend(
                [
                    f"/-- Chunk {chunk_index + 1} of the archived degree-"
                    f"{table.degree} polynomial rows. -/",
                    f"def {chunk_name} : List V15VoightPolynomialRow :=",
                    f"  {format_polynomial_rows(chunk)}",
                    "",
                ]
            )
        out.extend(
            [
                f"/-- Complete archived degree-{table.degree} polynomial rows. -/",
                f"def v15VoightPolynomialRows{table.lean_name} :",
                "    List V15VoightPolynomialRow :=",
                f"  {format_chunk_concatenation(chunk_names)}",
                "",
            ]
        )
    for table in TABLES:
        out.extend(
            [
                f"/-- Degree-{table.degree} discriminants in Voight's `{table.filename}` table. -/",
                f"def v15VoightDiscriminants{table.lean_name} : List ℕ :=",
                f"  {format_list([row.field_discriminant for row in data[table.degree]])}",
                "",
            ]
        )
    out.extend(
        [
            "/-- The archived table selected by a degree from five through nine;",
            "degree ten has no field at root discriminant at most fourteen. -/",
            "def v15VoightDiscriminants : ℕ → List ℕ",
            "  | 5 => v15VoightDiscriminantsFive",
            "  | 6 => v15VoightDiscriminantsSix",
            "  | 7 => v15VoightDiscriminantsSeven",
            "  | 8 => v15VoightDiscriminantsEight",
            "  | 9 => v15VoightDiscriminantsNine",
            "  | _ => []",
            "",
            "/-- The complete archived polynomial-row table selected by degree. -/",
            "def v15VoightPolynomialRows : ℕ → List V15VoightPolynomialRow",
            "  | 5 => v15VoightPolynomialRowsFive",
            "  | 6 => v15VoightPolynomialRowsSix",
            "  | 7 => v15VoightPolynomialRowsSeven",
            "  | 8 => v15VoightPolynomialRowsEight",
            "  | 9 => v15VoightPolynomialRowsNine",
            "  | 10 => v15VoightPolynomialRowsTen",
            "  | _ => []",
            "",
            "/-- Executable structural checks for a polynomial row. -/",
            "def V15VoightPolynomialRow.structurallyValid",
            "    (degree : ℕ) (row : V15VoightPolynomialRow) : Bool :=",
            "  row.coefficients.length == degree + 1 &&",
            "    row.coefficients.getLast? == some 1 &&",
            "    0 < row.fieldDiscriminant && 0 < row.index",
            "",
            "/-- Maximum recorded power-order index in a row list. -/",
            "def v15VoightMaximumIndex",
            "    (rows : List V15VoightPolynomialRow) : ℕ :=",
            "  rows.foldl (fun current row => max current row.index) 0",
            "",
            "/-- One native certificate checks all row counts and the sorted order",
            "of every imported discriminant column. -/",
            "theorem v15_voightDiscriminantData_certificate :",
            "    v15VoightDiscriminantsFive.length = 674 ∧",
            "    v15VoightDiscriminantsFive.Pairwise (· ≤ ·) ∧",
            "    v15VoightDiscriminantsSix.length = 827 ∧",
            "    v15VoightDiscriminantsSix.Pairwise (· ≤ ·) ∧",
            "    v15VoightDiscriminantsSeven.length = 301 ∧",
            "    v15VoightDiscriminantsSeven.Pairwise (· ≤ ·) ∧",
            "    v15VoightDiscriminantsEight.length = 164 ∧",
            "    v15VoightDiscriminantsEight.Pairwise (· ≤ ·) ∧",
            "    v15VoightDiscriminantsNine.length = 15 ∧",
            "    v15VoightDiscriminantsNine.Pairwise (· ≤ ·) := by",
            "  native_decide",
            "",
            "set_option maxRecDepth 10000 in",
            "/-- A separate native certificate checks that the generated full rows",
            "project to the imported discriminant columns, have the advertised",
            "shape and positive indices, and have the recorded maximum indices.",
            "The coefficient-to-discriminant calculation is independently rerun by",
            "the Python generator and `checks/voight_polynomial_integrity.wls`. -/",
            "theorem v15_voightPolynomialRowData_certificate :",
            "    v15VoightPolynomialRowsFive.length = 674 ∧",
            "    v15VoightPolynomialRowsSix.length = 827 ∧",
            "    v15VoightPolynomialRowsSeven.length = 301 ∧",
            "    v15VoightPolynomialRowsEight.length = 164 ∧",
            "    v15VoightPolynomialRowsNine.length = 15 ∧",
            "    v15VoightPolynomialRowsTen.length = 792 ∧",
            "    v15VoightPolynomialRowsFive.map (·.fieldDiscriminant) =",
            "      v15VoightDiscriminantsFive ∧",
            "    v15VoightPolynomialRowsSix.map (·.fieldDiscriminant) =",
            "      v15VoightDiscriminantsSix ∧",
            "    v15VoightPolynomialRowsSeven.map (·.fieldDiscriminant) =",
            "      v15VoightDiscriminantsSeven ∧",
            "    v15VoightPolynomialRowsEight.map (·.fieldDiscriminant) =",
            "      v15VoightDiscriminantsEight ∧",
            "    v15VoightPolynomialRowsNine.map (·.fieldDiscriminant) =",
            "      v15VoightDiscriminantsNine ∧",
            "    v15VoightPolynomialRowsFive.all",
            "      (V15VoightPolynomialRow.structurallyValid 5) = true ∧",
            "    v15VoightPolynomialRowsSix.all",
            "      (V15VoightPolynomialRow.structurallyValid 6) = true ∧",
            "    v15VoightPolynomialRowsSeven.all",
            "      (V15VoightPolynomialRow.structurallyValid 7) = true ∧",
            "    v15VoightPolynomialRowsEight.all",
            "      (V15VoightPolynomialRow.structurallyValid 8) = true ∧",
            "    v15VoightPolynomialRowsNine.all",
            "      (V15VoightPolynomialRow.structurallyValid 9) = true ∧",
            "    v15VoightPolynomialRowsTen.all",
            "      (V15VoightPolynomialRow.structurallyValid 10) = true ∧",
            "    v15VoightMaximumIndex v15VoightPolynomialRowsFive = 28 ∧",
            "    v15VoightMaximumIndex v15VoightPolynomialRowsSix = 1651 ∧",
            "    v15VoightMaximumIndex v15VoightPolynomialRowsSeven = 9 ∧",
            "    v15VoightMaximumIndex v15VoightPolynomialRowsEight = 4096 ∧",
            "    v15VoightMaximumIndex v15VoightPolynomialRowsNine = 1 ∧",
            "    v15VoightMaximumIndex v15VoightPolynomialRowsTen = 3581 := by",
            "  native_decide",
            "",
            "theorem v15_voightDiscriminantsFive_pairwise :",
            "    v15VoightDiscriminantsFive.Pairwise (· ≤ ·) :=",
            "  v15_voightDiscriminantData_certificate.2.1",
            "",
            "theorem v15_voightDiscriminantsSix_pairwise :",
            "    v15VoightDiscriminantsSix.Pairwise (· ≤ ·) :=",
            "  v15_voightDiscriminantData_certificate.2.2.2.1",
            "",
            "theorem v15_voightDiscriminantsSeven_pairwise :",
            "    v15VoightDiscriminantsSeven.Pairwise (· ≤ ·) :=",
            "  v15_voightDiscriminantData_certificate.2.2.2.2.2.1",
            "",
            "theorem v15_voightDiscriminantsEight_pairwise :",
            "    v15VoightDiscriminantsEight.Pairwise (· ≤ ·) :=",
            "  v15_voightDiscriminantData_certificate.2.2.2.2.2.2.2.1",
            "",
            "theorem v15_voightDiscriminantsNine_pairwise :",
            "    v15VoightDiscriminantsNine.Pairwise (· ≤ ·) :=",
            "  v15_voightDiscriminantData_certificate.2.2.2.2.2.2.2.2.2",
            "",
            "end TraceEuclidean",
            "",
        ]
    )
    return "\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="validate the source tables and fail if the generated Lean file is stale",
    )
    args = parser.parse_args()
    generated = render()
    if args.check:
        current = OUTPUT.read_text(encoding="utf-8")
        if current != generated:
            raise SystemExit(
                "V15VoightDiscriminantData.lean is stale; rerun the generator"
            )
        print(
            "Voight source tables, polynomial discriminant indices, "
            "and generated Lean data: PASS"
        )
        return
    OUTPUT.write_text(generated, encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
