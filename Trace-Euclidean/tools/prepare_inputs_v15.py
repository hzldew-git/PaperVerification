"""Extract public v15 verification inputs from a private manuscript build.

The manuscript and its build products remain outside the tracked public tree.
Only short labels, table entries, finite certificates, and a source digest are
written to inputs/manuscript_inputs_v15.json.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def aux_labels(path: Path) -> dict[str, dict[str, str]]:
    raw = path.read_text(encoding="utf-8", errors="replace")
    pattern = re.compile(r"\\newlabel\{([^}]+)\}\{\{([^{}]*)\}\{([^{}]*)\}")
    labels: dict[str, dict[str, str]] = {}
    for label, number, page in pattern.findall(raw):
        if not label.endswith("@cref"):
            labels[label] = {"number": number, "page": page}
    return labels


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manuscript", required=True, type=Path)
    parser.add_argument("--aux", required=True, type=Path)
    parser.add_argument("--python-results", required=True, type=Path)
    parser.add_argument("--mathematica-results", required=True, type=Path)
    parser.add_argument(
        "--output", type=Path, default=ROOT / "inputs" / "manuscript_inputs_v15.json"
    )
    args = parser.parse_args()

    source = args.manuscript.read_bytes()
    digest = hashlib.sha256(source).hexdigest()
    python = read_json(args.python_results)
    mathematica = read_json(args.mathematica_results)
    if python["sha256"] != digest or mathematica["source_sha256"] != digest:
        raise ValueError("Private verifier results do not match the manuscript SHA-256")
    if not python["all_passed"] or not mathematica["all_passed"]:
        raise ValueError("A private verification check failed")

    labels = aux_labels(args.aux)
    required = {
        "defn:trace-Euclidean",
        "thm:finiteness-classic",
        "thm:finiteness-integral",
        "thm:rank-one-classification",
        "cor:trace-euclidean-quadratic",
        "lem:gram-det",
        "lem:bounded-discriminant-volume-finiteness",
        "prop:trace-euclidean-quadratic",
        "tab:admissible-classical",
        "tab:admissible-norm",
    }
    missing = sorted(required - labels.keys())
    if missing:
        raise ValueError(f"Missing compiled manuscript labels: {missing}")

    data = {
        "schema_version": 3,
        "manuscript": {
            "filename": "Trace-Euclidean-v15.tex",
            "version": "v15",
            "sha256": digest,
            "line_count": len(source.decode("utf-8").splitlines()),
        },
        "labels": labels,
        "table_rows": python["table_rows"],
        "table_pair_counts": {
            "classic": python["classic_pairs"],
            "integral": python["integral_pairs"],
        },
        "rank_bounds_by_degree": python["N_d"],
        "degree_bounds_by_rank": python["D_n"],
        "reduced_gram_triples": python["reduced_gram_triples"],
        "field_gram_candidates": python["field_gram_candidates"],
        "representatives": python["representatives"],
        "private_check_counts": {
            "python_sympy": python["check_count"],
            "mathematica": len(mathematica["checks"]),
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"Prepared {args.output} for SHA-256 {digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
