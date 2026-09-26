#!/usr/bin/env python3
"""Generate exact rational root-interval certificates for Voight's tables.

Each interval has a strict rational sign change.  The intervals for one
polynomial are strictly ordered and their number equals the polynomial degree.
The generic Lean theorem converts these finite checks into complete splitting
over the real numbers.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path

from sympy import Poly, Rational, symbols

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
CHUNK_DIR = LEAN_ROOT / "V15VoightTotalRealityCertificates"
UMBRELLA_OUTPUT = LEAN_ROOT / "V15VoightTotalRealityCertificates.lean"
ROOT_INTERVAL_EPSILON = Rational(1, 2**10)
X = symbols("x")


@dataclass(frozen=True)
class RootInterval:
    lower_numerator: int
    lower_denominator: int
    upper_numerator: int
    upper_denominator: int


def all_data() -> dict[int, tuple[Table, list[PolynomialRow]]]:
    return {
        table.degree: (table, read_table(table))
        for table in TABLES + SUPPLEMENTAL_TABLES
    }


def isolate_roots(row: PolynomialRow, degree: int) -> list[RootInterval]:
    polynomial = Poly.from_list(
        list(reversed(row.coefficients)), gens=X, domain="QQ"
    )
    intervals = []
    for (lower, upper), multiplicity in polynomial.intervals():
        if multiplicity != 1:
            raise ArithmeticError(
                f"degree {degree}, D={row.field_discriminant}: "
                "non-simple real root"
            )
        lower, upper = polynomial.refine_root(
            lower, upper, eps=ROOT_INTERVAL_EPSILON
        )
        if not lower < upper:
            raise ArithmeticError("degenerate root interval")
        if not polynomial.eval(lower) * polynomial.eval(upper) < 0:
            raise ArithmeticError("interval has no strict sign change")
        intervals.append(
            RootInterval(
                int(lower.p), int(lower.q), int(upper.p), int(upper.q)
            )
        )
    if len(intervals) != degree:
        raise ArithmeticError(
            f"degree {degree}, D={row.field_discriminant}: "
            f"found {len(intervals)} real roots"
        )
    for left, right in zip(intervals, intervals[1:], strict=False):
        left_upper = Rational(
            left.upper_numerator, left.upper_denominator
        )
        right_lower = Rational(
            right.lower_numerator, right.lower_denominator
        )
        if not left_upper < right_lower:
            raise ArithmeticError("root intervals are not strictly separated")
    return intervals


def compute_certificates(
    data: dict[int, tuple[Table, list[PolynomialRow]]]
) -> dict[int, list[list[RootInterval]]]:
    certificates = {}
    for degree, (_, rows) in data.items():
        certificates[degree] = [
            isolate_roots(row, degree) for row in rows
        ]
        print(
            f"degree {degree}: {len(rows)} polynomials, "
            f"{sum(map(len, certificates[degree]))} real-root intervals"
        )
    return certificates


def lean_rational(numerator: int, denominator: int) -> str:
    if denominator == 1:
        return f"({numerator} : ℚ)"
    return f"({numerator} : ℚ) / {denominator}"


def lean_interval(interval: RootInterval) -> str:
    return (
        "⟨"
        + lean_rational(
            interval.lower_numerator, interval.lower_denominator
        )
        + ", "
        + lean_rational(
            interval.upper_numerator, interval.upper_denominator
        )
        + "⟩"
    )


def lean_certificate(intervals: list[RootInterval]) -> str:
    return "[" + ", ".join(map(lean_interval, intervals)) + "]"


def chunk_metadata(
    data: dict[int, tuple[Table, list[PolynomialRow]]]
) -> list[dict[str, object]]:
    metadata = []
    for degree, (table, rows) in data.items():
        for chunk_index, chunk_start in enumerate(
            range(0, len(rows), ROW_CHUNK_SIZE)
        ):
            metadata.append(
                {
                    "degree": degree,
                    "table": table,
                    "chunk_index": chunk_index,
                    "chunk_start": chunk_start,
                    "chunk_end": min(chunk_start + ROW_CHUNK_SIZE, len(rows)),
                    "module": f"{table.lean_name}Chunk{chunk_index}",
                    "rows": (
                        f"v15VoightPolynomialRows{table.lean_name}"
                        f"Chunk{chunk_index}"
                    ),
                }
            )
    return metadata


def render_chunks(
    data: dict[int, tuple[Table, list[PolynomialRow]]],
    certificates: dict[int, list[list[RootInterval]]],
) -> dict[str, str]:
    rendered = {}
    previous_module: str | None = None
    for part in chunk_metadata(data):
        degree = int(part["degree"])
        module = str(part["module"])
        rows_name = str(part["rows"])
        start = int(part["chunk_start"])
        end = int(part["chunk_end"])
        certificate_name = f"v15VoightRootIntervals{module}"
        check_name = f"v15_voightRootIntervals{module}_check"
        theorem_name = f"v15_voightRows{module}_splits"
        import_line = (
            "import TraceEuclidean.V15RealRootIntervalCertificate"
            if previous_module is None
            else "import TraceEuclidean.V15VoightTotalRealityCertificates."
            + previous_module
        )
        body = "[\n" + ",\n".join(
            "    " + lean_certificate(certificate)
            for certificate in certificates[degree][start:end]
        ) + "\n  ]"
        resource_options = (
            [
                "set_option maxHeartbeats 0 in",
                "-- Degree-ten interval data exceed the default elaboration budget.",
            ]
            if degree == 10
            else []
        )
        rendered[module + ".lean"] = "\n".join(
            [
                import_line,
                "",
                "/-! Generated rational root intervals for at most one hundred rows. -/",
                "",
                "namespace TraceEuclidean",
                "",
                "set_option linter.style.longLine false",
                "set_option maxRecDepth 100000",
                "",
                *resource_options,
                f"def {certificate_name} :",
                "    List (List V15RationalRootInterval) :=",
                f"  {body}",
                "",
                "set_option maxRecDepth 100000 in",
                "set_option maxHeartbeats 0 in",
                "-- Native replay is exact but intentionally has no heartbeat limit.",
                f"theorem {check_name} :",
                f"    v15RootIntervalCertificateBatchCheck {degree}",
                f"      {rows_name} {certificate_name} = true := by",
                "  native_decide",
                "",
                f"theorem {theorem_name} :",
                f"    ∀ row ∈ {rows_name}, row.realPolynomial.Splits :=",
                f"  v15_splits_of_rootIntervalBatchCheck_eq_true {degree}",
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
    result = theorems[0]
    for theorem in theorems[1:]:
        result = f"v15_forall_mem_append ({result}) {theorem}"
    return result


def render_umbrella(
    data: dict[int, tuple[Table, list[PolynomialRow]]]
) -> str:
    metadata = chunk_metadata(data)
    out = [
        *[
            "import TraceEuclidean.V15VoightTotalRealityCertificates."
            + str(part["module"])
            for part in metadata
        ],
        "import TraceEuclidean.V15VoightAllIrreducible",
        "",
        "/-! Real splitting of all archived Voight defining polynomials. -/",
        "",
        "namespace TraceEuclidean",
        "",
        "set_option linter.style.longLine false",
        "",
    ]
    degree_theorems = []
    for degree, (table, _) in data.items():
        parts = [part for part in metadata if int(part["degree"]) == degree]
        chunk_theorems = [
            f"v15_voightRows{part['module']}_splits" for part in parts
        ]
        theorem_name = (
            f"v15_voightPolynomialRows{table.lean_name}_splits"
        )
        degree_theorems.append(theorem_name)
        out.extend(
            [
                f"theorem {theorem_name} :",
                f"    ∀ row ∈ v15VoightPolynomialRows{table.lean_name},",
                "      row.realPolynomial.Splits := by",
                f"  dsimp [v15VoightPolynomialRows{table.lean_name}]",
                f"  exact {nested_append(chunk_theorems)}",
                "",
            ]
        )
    out.extend(
        [
            "/-- Every one of the 2,773 archived defining polynomials splits",
            "completely over the real numbers. -/",
            "theorem v15_allVoightPolynomialRows_splits :",
            "    ∀ row ∈ v15AllVoightPolynomialRows,",
            "      row.realPolynomial.Splits := by",
            "  dsimp [v15AllVoightPolynomialRows]",
            "  exact v15_forall_mem_append",
            f"    {degree_theorems[0]}",
            "    (v15_forall_mem_append",
            f"      {degree_theorems[1]}",
            "      (v15_forall_mem_append",
            f"        {degree_theorems[2]}",
            "        (v15_forall_mem_append",
            f"          {degree_theorems[3]}",
            "          (v15_forall_mem_append",
            f"            {degree_theorems[4]}",
            f"            {degree_theorems[5]}))))",
            "",
            "end TraceEuclidean",
            "",
        ]
    )
    return "\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    validate_hashes()
    data = all_data()
    certificates = compute_certificates(data)
    generated_chunks = render_chunks(data, certificates)
    generated_umbrella = render_umbrella(data)
    if args.check:
        if UMBRELLA_OUTPUT.read_text(encoding="utf-8") != generated_umbrella:
            raise SystemExit("V15VoightTotalRealityCertificates.lean is stale")
        actual = {path.name for path in CHUNK_DIR.glob("*.lean")}
        if actual != set(generated_chunks):
            raise SystemExit("total-reality certificate chunk set is stale")
        for filename, contents in generated_chunks.items():
            if (CHUNK_DIR / filename).read_text(encoding="utf-8") != contents:
                raise SystemExit(f"{filename} is stale")
        print("Voight total-reality certificates: PASS")
        return
    CHUNK_DIR.mkdir(parents=True, exist_ok=True)
    for stale in CHUNK_DIR.glob("*.lean"):
        if stale.name not in generated_chunks:
            stale.unlink()
    for filename, contents in generated_chunks.items():
        (CHUNK_DIR / filename).write_text(
            contents, encoding="utf-8", newline="\n"
        )
    UMBRELLA_OUTPUT.write_text(
        generated_umbrella, encoding="utf-8", newline="\n"
    )


if __name__ == "__main__":
    main()
