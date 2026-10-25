"""Check archived computational results against their code and public inputs."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SUPPLEMENT = ROOT / "mathematica"
RESULTS = SUPPLEMENT / "results"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(name):
    return json.loads((RESULTS / name).read_text(encoding="utf-8"))


def main():
    manifest = read("artifact_manifest.json")
    code = SUPPLEMENT / "TraceEuclideanVerification.m"
    assert manifest["code_sha256"] == sha(code)
    assert manifest["input_sha256"] == sha(ROOT / "inputs/verification_inputs.json")
    actual_results = {p.name for p in RESULTS.iterdir()
                      if p.is_file() and p.name != "artifact_manifest.json"}
    assert set(manifest["results"]) == actual_results
    for name, expected in manifest["results"].items():
        assert Path(name).name == name
        assert sha(RESULTS / name) == expected, name
    for name in ("verification_summary.json", "section4_tables.json",
                 "section6_exact_checks.json", "voight_integrity.json"):
        data = read(name)
        assert data["provenance"]["code_sha256"] == manifest["code_sha256"]
        assert data["provenance"]["input_sha256"] == manifest["input_sha256"]
        assert data.get("all_passed", data.get("pass")) is True
    section = read("section6_exact_checks.json")
    assert len(section["checks"]) == 115 and all(section["checks"].values())
    assert section["checks"] == json.loads(
        (ROOT / "results/section6_exact_checks.json").read_text())["checks"]
    tables = read("section4_tables.json")
    assert len(tables["checks"]) == 17 and all(tables["checks"].values())
    assert len(tables["grid"]) == 952 and len(tables["rows"]) == 87
    cert = read("rational_certificate.json")
    assert cert["comparisons"] == 952 and cert["unresolved_comparisons"] == 0
    voight = read("voight_integrity.json")
    assert voight["total_rows"] == 2773
    for table in voight["tables"]:
        assert sha(ROOT / "inputs/voight" / table["file"]) == table["sha256"]
        rows = read(f"voight-rows-{table['degree']}.json")
        assert len(rows) == table["rows"]
        assert all(all(row[k] is True for k in (
            "shape", "irreducible", "totallyReal", "indexSquare", "fieldDiscriminant"))
            for row in rows)
    print("COMPUTATIONAL RESULTS: PASS (18 result files; code, inputs, "
          "hashes, recorded outcomes and 2,773 archived rows checked)")


if __name__ == "__main__":
    main()
