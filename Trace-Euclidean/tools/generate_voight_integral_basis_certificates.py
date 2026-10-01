#!/usr/bin/env python3
"""Render Lean integral-basis certificates from exact Mathematica output."""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import shutil
import sys
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "results" / "voight-squarefree-integral-bases.json"
OUTPUT_DIR = (
    ROOT / "lean" / "TraceEuclidean" / "VoightIntegralBasisCertificates"
)
UMBRELLA = (
    ROOT / "lean" / "TraceEuclidean" /
    "VoightIntegralBasisCertificates.lean"
)
CHUNK_SIZE = 20


def load_discriminant_generator():
    path = ROOT / "tools" / "generate_voight_discriminant_data.py"
    spec = importlib.util.spec_from_file_location("voight_data", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def is_squarefree(value: int) -> bool:
    if value <= 0:
        return False
    factor = 2
    remaining = value
    while factor * factor <= remaining:
        if remaining % factor == 0:
            remaining //= factor
            if remaining % factor == 0:
                return False
            while remaining % factor == 0:
                remaining //= factor
        factor = 3 if factor == 2 else factor + 2
    return True


def trim(values: list[Fraction]) -> list[Fraction]:
    result = values.copy()
    while result and result[-1] == 0:
        result.pop()
    return result


def add(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    size = max(len(left), len(right))
    return trim([
        (left[i] if i < len(left) else Fraction(0))
        + (right[i] if i < len(right) else Fraction(0))
        for i in range(size)
    ])


def mul(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    if not left or not right:
        return []
    result = [Fraction(0) for _ in range(len(left) + len(right) - 1)]
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return trim(result)


def compose(outer: list[Fraction], inner: list[Fraction]) -> list[Fraction]:
    result: list[Fraction] = []
    for coefficient in reversed(outer):
        result = add([coefficient], mul(inner, result))
    return trim(result)


def determinant(matrix: list[list[Fraction]]) -> Fraction:
    size = len(matrix)
    work = [row.copy() for row in matrix]
    sign = 1
    result = Fraction(1)
    for column in range(size):
        pivot = next(
            (row for row in range(column, size) if work[row][column]),
            None,
        )
        if pivot is None:
            return Fraction(0)
        if pivot != column:
            work[column], work[pivot] = work[pivot], work[column]
            sign = -sign
        pivot_value = work[column][column]
        result *= pivot_value
        for j in range(column, size):
            work[column][j] /= pivot_value
        for row in range(column + 1, size):
            scale = work[row][column]
            for j in range(column, size):
                work[row][j] -= scale * work[column][j]
    return sign * result


def fraction(pair: list[int]) -> Fraction:
    if len(pair) != 2 or pair[1] <= 0:
        raise ValueError(f"invalid rational pair {pair}")
    return Fraction(pair[0], pair[1])


def validate_records(records: list[dict]) -> None:
    module = load_discriminant_generator()
    tables = module.TABLES + module.SUPPLEMENTAL_TABLES
    source_rows: dict[tuple[int, int], object] = {}
    selected: list[tuple[int, int]] = []
    for table in tables:
        for row_number, row in enumerate(module.read_table(table), 1):
            source_rows[(table.degree, row_number)] = row
            if row.index > 1 and is_squarefree(row.field_discriminant):
                selected.append((table.degree, row_number))
    keys = [(record["degree"], record["row_number"]) for record in records]
    if keys != selected:
        raise ValueError("certificate records do not exactly match selected rows")
    if len(records) != 156:
        raise ValueError(f"expected 156 records, found {len(records)}")

    for record in records:
        degree = record["degree"]
        key = (degree, record["row_number"])
        row = source_rows[key]
        if (
            record["field_discriminant"] != row.field_discriminant
            or tuple(record["coefficients"]) != row.coefficients
            or record["index"] != row.index
        ):
            raise ValueError(f"source-row mismatch at {key}")
        matrix = [
            [fraction(value) for value in matrix_row]
            for matrix_row in record["matrix"]
        ]
        if len(matrix) != degree or any(len(r) != degree for r in matrix):
            raise ValueError(f"matrix shape mismatch at {key}")
        if abs(determinant(matrix)) != Fraction(1, row.index):
            raise ValueError(f"matrix determinant mismatch at {key}")
        annihilators = record["annihilators"]
        quotients = [
            [fraction(value) for value in quotient]
            for quotient in record["quotients"]
        ]
        if len(annihilators) != degree or len(quotients) != degree:
            raise ValueError(f"certificate count mismatch at {key}")
        defining = [Fraction(c) for c in row.coefficients]
        for column in range(degree):
            annihilator = [Fraction(c) for c in annihilators[column]]
            if not annihilator or annihilator[-1] != 1:
                raise ValueError(f"nonmonic annihilator at {key}, column {column}")
            element = [matrix[p][column] for p in range(degree)]
            if compose(annihilator, element) != mul(defining, quotients[column]):
                raise ValueError(
                    f"annihilator identity mismatch at {key}, column {column}"
                )


def lean_int(value: int) -> str:
    return str(value)


def lean_rat(value: list[int]) -> str:
    numerator, denominator = value
    if denominator == 1:
        return str(numerator)
    return f"({numerator} / {denominator} : ℚ)"


def lean_int_list(values: list[int]) -> str:
    return "[" + ", ".join(lean_int(value) for value in values) + "]"


def lean_rat_list(values: list[list[int]]) -> str:
    return "[" + ", ".join(lean_rat(value) for value in values) + "]"


def lean_matrix(matrix: list[list[list[int]]], indent: str) -> str:
    rows = [", ".join(lean_rat(value) for value in row) for row in matrix]
    return ("!![" + (";\n" + indent + "   ").join(rows) + "]")


def render_entry(record: dict) -> str:
    degree = record["degree"]
    matrix = lean_matrix(record["matrix"], "        ")
    annihilators = ",\n          ".join(
        lean_int_list(values) for values in record["annihilators"]
    )
    quotients = ",\n          ".join(
        lean_rat_list(values) for values in record["quotients"]
    )
    return "\n".join([
        "    ⟨",
        f"      {degree},",
        "      ⟨" +
        f"{record['field_discriminant']}, " +
        f"{lean_int_list(record['coefficients'])}, " +
        f"{record['index']}⟩,",
        "      {",
        f"        matrix := {matrix}",
        "        annihilators := ![",
        f"          {annihilators}",
        "        ]",
        "        quotients := ![",
        f"          {quotients}",
        "        ]",
        "      }",
        "    ⟩",
    ])


def render_chunk(index: int, records: list[dict]) -> str:
    name = f"voightIntegralBasisCertificatesChunk{index:02d}"
    entries = ",\n".join(render_entry(record) for record in records)
    imported = (
        "TraceEuclidean.VoightIntegralBasisCertificate"
        if index == 0 else
        f"TraceEuclidean.VoightIntegralBasisCertificates.Chunk{index - 1:02d}"
    )
    return "\n".join([
        f"import {imported}",
        "",
        "/-! Generated exact integral-basis certificate chunk. -/",
        "",
        "namespace TraceEuclidean",
        "",
        "set_option maxHeartbeats 0 in",
        "-- Generated certificate literals need extra elaboration time.",
        "set_option maxRecDepth 100000 in",
        f"def {name} :",
        "    List VoightIntegralBasisCertificateEntry := [",
        entries,
        "  ]",
        "",
        "set_option maxHeartbeats 0 in",
        "-- Exact replay of a large generated certificate batch.",
        "set_option maxRecDepth 100000 in",
        f"theorem {name}_check :",
        "    List.Forall",
        "      VoightIntegralBasisCertificateEntry.Valid",
        f"      {name} := by",
        "  have hchecks : List.Forall",
        "      (fun entry ↦ entry.check = true)",
        f"      {name} := by",
        "    native_decide",
        "  exact hchecks.imp fun entry hcheck ↦",
        "    entry.valid_of_check_eq_true hcheck",
        "",
        "end TraceEuclidean",
        "",
    ])


def render_umbrella(chunk_count: int) -> str:
    imports = [
        f"import TraceEuclidean.VoightIntegralBasisCertificates.Chunk{i:02d}"
        for i in range(chunk_count)
    ]
    names = [f"voightIntegralBasisCertificatesChunk{i:02d}"
             for i in range(chunk_count)]
    checks = [name + "_check" for name in names]
    append_expr = " ++\n    ".join(names)
    # The generated `++` expression is parsed left-associatively, so repeated
    # `List.forall_append` produces a left-associated conjunction as well.
    proof = checks[0]
    for check in checks[1:]:
        proof = f"⟨{proof}, {check}⟩"
    return "\n".join([
        *imports,
        "",
        "/-! All squarefree, nontrivial-index Voight integral-basis certificates. -/",
        "",
        "namespace TraceEuclidean",
        "",
        "def voightSquarefreeNontrivialIndexCertificates :",
        "    List VoightIntegralBasisCertificateEntry :=",
        f"  {append_expr}",
        "",
        "theorem voightSquarefreeNontrivialIndexCertificates_valid :",
        "    List.Forall",
        "      VoightIntegralBasisCertificateEntry.Valid",
        "      voightSquarefreeNontrivialIndexCertificates := by",
        "  dsimp [voightSquarefreeNontrivialIndexCertificates]",
        "  simp only [List.forall_append]",
        f"  exact {proof}",
        "",
        "/-- The generated certificate rows are exactly the archived",
        "squarefree rows with recorded index greater than one. -/",
        "theorem voightSquarefreeNontrivialIndexCertificates_complete :",
        "    voightSquarefreeNontrivialIndexCertificates.map",
        "        (·.row) =",
        "      voightSquarefreeNontrivialIndexRows := by",
        "  native_decide",
        "",
        "end TraceEuclidean",
        "",
    ])


def write_outputs(records: list[dict]) -> None:
    chunks = [
        records[start:start + CHUNK_SIZE]
        for start in range(0, len(records), CHUNK_SIZE)
    ]
    if OUTPUT_DIR.exists():
        shutil.rmtree(OUTPUT_DIR)
    OUTPUT_DIR.mkdir(parents=True)
    for index, chunk in enumerate(chunks):
        (OUTPUT_DIR / f"Chunk{index:02d}.lean").write_text(
            render_chunk(index, chunk), encoding="utf-8", newline="\n"
        )
    UMBRELLA.write_text(
        render_umbrella(len(chunks)), encoding="utf-8", newline="\n"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    payload = json.loads(SOURCE.read_text(encoding="utf-8"))
    records = payload["records"]
    if payload.get("record_count") != len(records):
        raise ValueError("record_count does not match records")
    validate_records(records)

    if args.check:
        temporary = ROOT / "results" / ".integral-basis-render-check"
        if temporary.exists():
            shutil.rmtree(temporary)
        temporary.mkdir(parents=True)
        current_dir, current_umbrella = OUTPUT_DIR, UMBRELLA
        expected = {
            path.name: path.read_bytes() for path in current_dir.glob("*.lean")
        }
        expected_umbrella = current_umbrella.read_bytes()
        chunks = [
            records[start:start + CHUNK_SIZE]
            for start in range(0, len(records), CHUNK_SIZE)
        ]
        actual = {
            f"Chunk{index:02d}.lean": render_chunk(index, chunk).encode()
            for index, chunk in enumerate(chunks)
        }
        actual_umbrella = render_umbrella(len(chunks)).encode()
        shutil.rmtree(temporary)
        if actual != expected or actual_umbrella != expected_umbrella:
            raise SystemExit("generated Lean integral-basis files are stale")
        print("VOIGHT INTEGRAL-BASIS GENERATOR: PASS")
        return

    write_outputs(records)
    print(f"Wrote {len(records)} certificates in "
          f"{math.ceil(len(records) / CHUNK_SIZE)} chunks")


if __name__ == "__main__":
    main()
