#!/usr/bin/env python3
"""Generate chunked Lean certificates for archived Voight maximal orders.

The discovery phase uses exact rational and finite-field arithmetic.  Every
emitted identity is checked again by Lean.  By default the script generates
all nonsquarefree rows for which integral-basis matrices were archived.
"""

from __future__ import annotations

import argparse
import json
import time
import warnings
from pathlib import Path

from sympy.utilities.exceptions import SymPyDeprecationWarning

from generate_voight_maximal_order_pilot import (
    build_order,
    dedekind_global_certificate,
    emit,
    maximality_certificate,
)


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "results" / "voight-nonsquarefree-basis-matrices.json"
LEAN_ROOT = ROOT / "lean" / "TraceEuclidean"

HEADER = """import TraceEuclidean.VoightAllIrreducible
import TraceEuclidean.VoightIntegralBasisCertificate
import TraceEuclidean.VoightPolynomialBridge
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.CertifyAdjoinRootCore
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.MaximalAPI
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.CertificateDedekind
import Mathlib.Tactic

set_option linter.all false
set_option maxHeartbeats 5000000

namespace TraceEuclidean

"""


# A few degree-ten unramified Frobenius checks exceed Lean's default recursion
# depth when replayed with kernel `decide`.  Keep the larger limit local to the
# affected proof fields so previously compiled certificate rows and the
# project's global elaboration settings remain unchanged.  The index-one
# degree-ten batch has not yet been compiled, so apply the same local guard to
# that batch up front.
HIGH_RECURSION_WFROB_ROWS = {
    (10, 106),
    (10, 327),
    # The final dependency chain was still uncompiled when the same limit was
    # observed at row 486.  Guard every row in those remaining chunks so the
    # clean build is deterministic rather than discovering them one at a time.
    (10, 486),
    (10, 488),
    (10, 489),
    (10, 493),
    (10, 545),
    (10, 546),
    (10, 547),
    (10, 551),
    (10, 628),
    (10, 630),
    (10, 631),
    (10, 642),
    (10, 688),
    (10, 689),
    (10, 693),
    (10, 695),
    (10, 715),
    (10, 746),
    (10, 750),
    (10, 751),
    (10, 755),
}


def parse_row_key(text: str) -> tuple[int, int]:
    try:
        degree, row_number = text.split(":", maxsplit=1)
        return int(degree), int(row_number)
    except (TypeError, ValueError) as error:
        raise argparse.ArgumentTypeError(
            f"row key must have the form DEGREE:ROW, not {text!r}"
        ) from error


def select_records(records: list[dict], scope: str,
                   only: list[tuple[int, int]]) -> list[dict]:
    selected = records
    if scope == "nontrivial":
        selected = [record for record in selected if record["index"] > 1]
    elif scope == "index-one":
        selected = [record for record in selected if record["index"] == 1]
    if only:
        keys = set(only)
        selected = [
            record for record in selected
            if (record["degree"], record["row_number"]) in keys
        ]
        missing = keys - {
            (record["degree"], record["row_number"])
            for record in selected
        }
        if missing:
            raise LookupError(f"requested rows are absent: {sorted(missing)}")
    return sorted(selected, key=lambda record: (
        record["degree"], record["row_number"]
    ))


def row_body(source: str) -> str:
    opening = "namespace TraceEuclidean\n"
    closing = "end TraceEuclidean\n"
    start = source.index(opening) + len(opening)
    end = source.rindex(closing)
    return source[start:end].strip() + "\n"


def generate_row(record: dict, native_finite_checks: bool) -> tuple[str, dict]:
    order = build_order(record)
    dedekind = dedekind_global_certificate(record["coefficients"])
    maximalities = {
        prime: maximality_certificate(record, order, prime)
        for prime in dedekind["bad"]
    }
    namespace = (
        f"VoightMaximalOrderD{record['degree']}R{record['row_number']}"
    )
    source = emit(
        record,
        order,
        dedekind,
        maximalities,
        namespace=namespace,
    )
    needs_high_recursion = (
        (record["degree"], record["row_number"])
        in HIGH_RECURSION_WFROB_ROWS
        or (record["degree"] == 10 and record["index"] == 1)
    )
    if needs_high_recursion:
        source = source.replace(
            "  hwFrobComp := by decide",
            "  hwFrobComp := by\n"
            "    set_option maxRecDepth 100000 in\n"
            "      decide",
        )
    if native_finite_checks:
        source = source.replace("by decide", "by native_decide")
    metadata = {
        "degree": record["degree"],
        "row_number": record["row_number"],
        "field_discriminant": record["field_discriminant"],
        "index": record["index"],
        "bad_primes": dedekind["bad"],
        "local_certificates": {
            str(prime): {
                "kind": (
                    "unramified" if certificate["m"] == 0
                    else "multiplier_ring"
                ),
                "kernel_dimension": certificate["m"],
                "image_dimension": certificate["n"],
                "frobenius_iterations": certificate["t"],
            }
            for prime, certificate in maximalities.items()
        },
        "namespace": f"TraceEuclidean.{namespace}",
        "theorem": (
            f"TraceEuclidean.{namespace}.field_discriminant_eq_recorded"
        ),
        "native_finite_checks": native_finite_checks,
    }
    return row_body(source), metadata


def chunks(values: list, size: int):
    for start in range(0, len(values), size):
        yield values[start:start + size]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--scope",
        choices=("all", "nontrivial", "index-one"),
        default="all",
    )
    parser.add_argument(
        "--only",
        action="append",
        default=[],
        type=parse_row_key,
        metavar="DEGREE:ROW",
    )
    parser.add_argument("--chunk-size", type=int, default=8)
    parser.add_argument(
        "--chain-width",
        type=int,
        default=4,
        help="maximum number of generated chunks that Lake may build in parallel",
    )
    parser.add_argument(
        "--prerequisite-module",
        help="module imported by the first chunk in every dependency chain",
    )
    parser.add_argument(
        "--native-finite-checks",
        action="store_true",
        help="replay generated decidable certificate fields with native_decide",
    )
    parser.add_argument(
        "--module-prefix",
        default="VoightMaximalOrderCertificates",
    )
    args = parser.parse_args()
    if args.chunk_size <= 0:
        parser.error("--chunk-size must be positive")
    if args.chain_width <= 0:
        parser.error("--chain-width must be positive")
    if not args.module_prefix.isidentifier():
        parser.error("--module-prefix must be a Lean/Python identifier")

    warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)
    payload = json.loads(SOURCE.read_text(encoding="utf-8"))
    records = select_records(payload["records"], args.scope, args.only)
    if not records:
        raise LookupError("no rows selected")

    output_dir = LEAN_ROOT / args.module_prefix
    output_dir.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    generated: list[tuple[str, dict]] = []
    for position, record in enumerate(records, start=1):
        body, metadata = generate_row(record, args.native_finite_checks)
        generated.append((body, metadata))
        if position % 25 == 0 or position == len(records):
            print(
                "VOIGHT MAXIMAL-ORDER GENERATION:",
                f"{position}/{len(records)}",
                f"elapsed={time.monotonic() - started:.1f}s",
                flush=True,
            )

    module_names = []
    manifest_records = []
    for chunk_number, chunk in enumerate(chunks(generated, args.chunk_size)):
        stem = f"Chunk{chunk_number:03d}"
        path = output_dir / f"{stem}.lean"
        dependency_imports = []
        if chunk_number >= args.chain_width:
            previous = chunk_number - args.chain_width
            dependency_imports.append(
                f"import TraceEuclidean.{args.module_prefix}.Chunk{previous:03d}"
            )
        elif args.prerequisite_module:
            dependency_imports.append(
                f"import {args.prerequisite_module}"
            )
        dependency_header = (
            "\n".join(dependency_imports) + "\n" if dependency_imports else ""
        )
        text = dependency_header + HEADER + "\n".join(
            body for body, _ in chunk
        )
        text += "\nend TraceEuclidean\n"
        path.write_text(text, encoding="utf-8")
        module_names.append(f"TraceEuclidean.{args.module_prefix}.{stem}")
        for _, metadata in chunk:
            metadata["module"] = module_names[-1]
            manifest_records.append(metadata)

    aggregator = LEAN_ROOT / f"{args.module_prefix}.lean"
    terminal_modules = module_names[-min(args.chain_width, len(module_names)):]
    aggregator.write_text(
        "\n".join(f"import {module}" for module in terminal_modules) + "\n",
        encoding="utf-8",
    )
    manifest_path = ROOT / "results" / (
        args.module_prefix
        .replace("Voight", "voight-")
        .replace("Maximal", "maximal-")
        .replace("Order", "order-")
        .replace("Certificates", "certificates")
        .lower()
        + ".json"
    )
    manifest = {
        "source": str(SOURCE.relative_to(ROOT)).replace("\\", "/"),
        "scope": args.scope,
        "record_count": len(manifest_records),
        "chunk_size": args.chunk_size,
        "chain_width": args.chain_width,
        "prerequisite_module": args.prerequisite_module,
        "native_finite_checks": args.native_finite_checks,
        "module_prefix": f"TraceEuclidean.{args.module_prefix}",
        "aggregator": str(aggregator.relative_to(ROOT)).replace("\\", "/"),
        "modules": module_names,
        "records": manifest_records,
    }
    manifest_path.write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
    )
    print(
        "VOIGHT MAXIMAL-ORDER GENERATION: PASS",
        f"records={len(manifest_records)}",
        f"chunks={len(module_names)}",
        f"aggregator={aggregator}",
        f"manifest={manifest_path}",
    )


if __name__ == "__main__":
    main()
