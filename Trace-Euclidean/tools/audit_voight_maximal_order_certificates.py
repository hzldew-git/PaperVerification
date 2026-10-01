#!/usr/bin/env python3
"""Preflight every nontrivial Voight maximal-order certificate.

This script performs the exact rational and finite-field discovery phase used
by the Lean certificate generator.  It does not replace Lean checking: its
purpose is to ensure that every archived nontrivial-index row reaches one of
the supported certificate shapes before the much larger Lean sources are
emitted.
"""

from __future__ import annotations

import json
import time
import warnings
from collections import Counter
from pathlib import Path

from sympy.utilities.exceptions import SymPyDeprecationWarning

from generate_voight_maximal_order_pilot import (
    build_order,
    dedekind_global_certificate,
    maximality_certificate,
)


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "results" / "voight-nonsquarefree-basis-matrices.json"
OUTPUT = ROOT / "results" / "voight-maximal-order-certificate-audit.json"


def prime_divides(value: int, prime: int) -> bool:
    return value % prime == 0


def main() -> None:
    warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)
    payload = json.loads(SOURCE.read_text(encoding="utf-8"))
    records = [record for record in payload["records"] if record["index"] > 1]
    started = time.monotonic()
    audited = []
    local_kind_counts: Counter[str] = Counter()
    bad_prime_counts: Counter[int] = Counter()

    for position, record in enumerate(records, start=1):
        order = build_order(record)
        dedekind = dedekind_global_certificate(record["coefficients"])
        if not dedekind["bad"]:
            raise ArithmeticError(
                "nontrivial power-order index unexpectedly has no bad prime: "
                f"degree {record['degree']} row {record['row_number']}"
            )
        unexpected = [
            prime for prime in dedekind["bad"]
            if not prime_divides(record["index"], prime)
        ]
        if unexpected:
            raise ArithmeticError(
                f"bad primes {unexpected} do not divide index {record['index']}"
            )

        local = []
        for prime in dedekind["bad"]:
            certificate = maximality_certificate(record, order, prime)
            kind = "unramified" if certificate["m"] == 0 else "multiplier_ring"
            local_kind_counts[kind] += 1
            bad_prime_counts[prime] += 1
            local.append({
                "prime": prime,
                "kind": kind,
                "kernel_dimension": certificate["m"],
                "image_dimension": certificate["n"],
                "frobenius_iterations": certificate["t"],
            })

        audited.append({
            "degree": record["degree"],
            "row_number": record["row_number"],
            "field_discriminant": record["field_discriminant"],
            "index": record["index"],
            "bad_primes": dedekind["bad"],
            "local_certificates": local,
        })
        if position % 25 == 0 or position == len(records):
            print(
                "VOIGHT MAXIMAL-ORDER PREFLIGHT:",
                f"{position}/{len(records)}",
                f"elapsed={time.monotonic() - started:.1f}s",
                flush=True,
            )

    result = {
        "source": str(SOURCE.relative_to(ROOT)).replace("\\", "/"),
        "nontrivial_index_record_count": len(records),
        "local_certificate_count": sum(local_kind_counts.values()),
        "certificate_kind_counts": dict(sorted(local_kind_counts.items())),
        "bad_prime_counts": {
            str(prime): count for prime, count in sorted(bad_prime_counts.items())
        },
        "records": audited,
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(
        "VOIGHT MAXIMAL-ORDER PREFLIGHT: PASS",
        f"records={len(records)}",
        f"locals={sum(local_kind_counts.values())}",
        f"kinds={dict(local_kind_counts)}",
        f"output={OUTPUT}",
    )


if __name__ == "__main__":
    main()
