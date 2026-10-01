#!/usr/bin/env python3
"""Aggregate per-row maximal-order theorems into exact-field endpoints."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results"
LEAN_ROOT = ROOT / "lean" / "TraceEuclidean"
NONTRIVIAL_MANIFEST = RESULTS / "voight-maximal-order-certificates.json"
INDEX_ONE_MANIFEST = (
    RESULTS / "voight-maximal-order-indexonecertificates.json"
)


def read_records(path: Path) -> list[dict]:
    return json.loads(path.read_text(encoding="utf-8"))["records"]


def all_rows_membership_term(degree: int) -> str:
    if degree < 5 or degree > 10:
        raise ValueError(f"unsupported Voight degree {degree}")
    if degree == 10:
        term = "List.mem_append.mpr (Or.inr row_mem)"
        previous_degrees = range(8, 4, -1)
    else:
        term = "List.mem_append.mpr (Or.inl row_mem)"
        previous_degrees = range(degree - 1, 4, -1)
    for _ in previous_degrees:
        term = f"List.mem_append.mpr (Or.inr ({term}))"
    return term


def theorem_source(record: dict) -> str:
    namespace = record["namespace"].removeprefix("TraceEuclidean.")
    membership = all_rows_membership_term(record["degree"])
    return f"""namespace {namespace}

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact {membership}
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end {namespace}
"""


def chunks(values: list, size: int):
    for start in range(0, len(values), size):
        yield values[start:start + size]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--chunk-size", type=int, default=25)
    parser.add_argument("--chain-width", type=int, default=4)
    parser.add_argument(
        "--module-prefix", default="VoightMaximalOrderExact"
    )
    args = parser.parse_args()
    if args.chunk_size <= 0 or args.chain_width <= 0:
        parser.error("chunk size and chain width must be positive")

    records = read_records(NONTRIVIAL_MANIFEST) + read_records(
        INDEX_ONE_MANIFEST
    )
    records.sort(key=lambda record: (record["degree"], record["row_number"]))
    if len(records) != 1509:
        raise ArithmeticError(
            f"expected 1509 nonsquarefree records, found {len(records)}"
        )
    keys = [(record["degree"], record["row_number"]) for record in records]
    if len(set(keys)) != len(keys):
        raise ArithmeticError("duplicate degree/row key in maximal-order manifests")

    output_dir = LEAN_ROOT / args.module_prefix
    output_dir.mkdir(parents=True, exist_ok=True)
    module_names: list[str] = []
    chunk_names: list[str] = []
    for chunk_number, group in enumerate(chunks(records, args.chunk_size)):
        stem = f"Chunk{chunk_number:03d}"
        module = f"TraceEuclidean.{args.module_prefix}.{stem}"
        imports = [
            "import TraceEuclidean.VoightMaximalOrderIndexOneCertificates",
            "import TraceEuclidean.VoightMaximalOrderExactBase",
            "import Mathlib.Tactic",
        ]
        if chunk_number >= args.chain_width:
            imports.insert(
                0,
                f"import TraceEuclidean.{args.module_prefix}."
                f"Chunk{chunk_number - args.chain_width:03d}",
            )
        lines = imports + [
            "",
            "set_option linter.all false",
            "",
            "namespace TraceEuclidean",
            "",
        ]
        for record in group:
            lines.append(theorem_source(record))
        chunk_namespace = f"{args.module_prefix}{stem}"
        lines += [
            f"namespace {chunk_namespace}",
            "",
            "def entries : List VoightExactFieldCertificate := [",
        ]
        for position, record in enumerate(group):
            namespace = record["namespace"].removeprefix("TraceEuclidean.")
            comma = "," if position + 1 < len(group) else ""
            lines.append(
                f"  ⟨{namespace}.row, "
                f"{namespace}.row_presents_exact_totallyRealNumberField⟩"
                f"{comma}"
            )
        lines += [
            "]",
            "",
            f"end {chunk_namespace}",
            "end TraceEuclidean",
            "",
        ]
        (output_dir / f"{stem}.lean").write_text(
            "\n".join(lines), encoding="utf-8"
        )
        module_names.append(module)
        chunk_names.append(chunk_namespace)

    terminal_modules = module_names[-min(args.chain_width, len(module_names)):]
    aggregator = LEAN_ROOT / f"{args.module_prefix}.lean"
    lines = [f"import {module}" for module in terminal_modules]
    lines += [
        "",
        "set_option linter.all false",
        "",
        "namespace TraceEuclidean",
        "",
        "/-- Proof-carrying exact-field certificates for all 1,509 archived",
        "rows with nonsquarefree recorded field discriminant. -/",
        "def voightNonsquarefreeExactFieldCertificates :",
        "    List VoightExactFieldCertificate :=",
    ]
    for position, chunk_namespace in enumerate(chunk_names):
        prefix = "  " if position == 0 else "    "
        suffix = " ++" if position + 1 < len(chunk_names) else ""
        lines.append(f"{prefix}{chunk_namespace}.entries{suffix}")
    lines += [
        "",
        "/-- The generated certificate list contains exactly 1,509 rows. -/",
        "theorem voightNonsquarefreeExactFieldCertificates_length :",
        "    voightNonsquarefreeExactFieldCertificates.length = 1509 := by",
        "  native_decide",
        "",
        "/-- The generated proof-carrying list has exactly the same rows and",
        "order as the executable nonsquarefree selector. -/",
        "theorem voightNonsquarefreeExactFieldCertificates_complete :",
        "    voightNonsquarefreeExactFieldCertificates.map (·.row) =",
        "      voightNonsquarefreeFieldDiscriminantRows := by",
        "  native_decide",
        "",
        "/-- Every archived row with nonsquarefree recorded discriminant",
        "presents an actual totally real field with exactly that discriminant. -/",
        "theorem voightNonsquarefreeFieldDiscriminantRows_present_exactTotallyRealNumberField :",
        "    ∀ row ∈ voightNonsquarefreeFieldDiscriminantRows,",
        "      row.PresentsExactTotallyRealNumberField := by",
        "  intro row hrow",
        "  have hmapped :",
        "      row ∈ voightNonsquarefreeExactFieldCertificates.map",
        "        (·.row) := by",
        "    rw [voightNonsquarefreeExactFieldCertificates_complete]",
        "    exact hrow",
        "  rcases List.mem_map.mp hmapped with ⟨entry, hentry, heq⟩",
        "  subst row",
        "  exact entry.exactness",
        "",
        "/-- Every one of the 2,773 archived Voight rows now has exact field",
        "semantics, including equality with its recorded field discriminant. -/",
        "theorem allVoightPolynomialRows_present_exactTotallyRealNumberField :",
        "    ∀ row ∈ allVoightPolynomialRows,",
        "      row.PresentsExactTotallyRealNumberField := by",
        "  intro row hrow",
        "  by_cases hsquarefree : Squarefree row.fieldDiscriminant",
        "  · apply",
        "      voightSquarefreeFieldDiscriminantRows_present_exactTotallyRealNumberField",
        "        row",
        "    exact List.mem_filter.mpr",
        "      ⟨hrow,",
        "        (voightPolynomialRow_squarefreeFieldDiscriminant_iff row).2",
        "          hsquarefree⟩",
        "  · apply",
        "      voightNonsquarefreeFieldDiscriminantRows_present_exactTotallyRealNumberField",
        "        row",
        "    exact List.mem_filter.mpr",
        "      ⟨hrow,",
        "        (voightPolynomialRow_nonsquarefreeFieldDiscriminant_iff row).2",
        "          hsquarefree⟩",
        "",
        "end TraceEuclidean",
        "",
    ]
    aggregator.write_text("\n".join(lines), encoding="utf-8")

    manifest = {
        "record_count": len(records),
        "chunk_size": args.chunk_size,
        "chain_width": args.chain_width,
        "module_prefix": f"TraceEuclidean.{args.module_prefix}",
        "aggregator": str(aggregator.relative_to(ROOT)).replace("\\", "/"),
        "modules": module_names,
        "source_manifests": [
            str(NONTRIVIAL_MANIFEST.relative_to(ROOT)).replace("\\", "/"),
            str(INDEX_ONE_MANIFEST.relative_to(ROOT)).replace("\\", "/"),
        ],
    }
    manifest_path = RESULTS / "voight-maximal-order-exact.json"
    manifest_path.write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
    )
    print(
        "VOIGHT MAXIMAL-ORDER EXACT AGGREGATION: PASS",
        f"records={len(records)}",
        f"chunks={len(module_names)}",
        f"aggregator={aggregator}",
        f"manifest={manifest_path}",
    )


if __name__ == "__main__":
    main()
