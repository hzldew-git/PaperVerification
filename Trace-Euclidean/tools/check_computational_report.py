"""Check report provenance, complete outcomes and public PDF metadata."""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

from pypdf import PdfReader

from check_public_metadata import VERSION_LABEL, WINDOWS_PATH, LOCAL_HOME, PRIVATE_SOURCE_META

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
    pdf = SUPPLEMENT / "TraceEuclideanVerification.pdf"
    assert manifest["code_sha256"] == sha(code)
    assert manifest["input_sha256"] == sha(ROOT / "inputs/verification_inputs.json")
    assert manifest["pdf_sha256"] == sha(pdf)
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
    reader = PdfReader(pdf)
    assert len(reader.pages) == manifest["pdf_pages"]
    assert not list(reader.attachments), "Unexpected embedded attachment"
    assert "/OpenAction" not in reader.trailer["/Root"]
    assert "/JavaScript" not in str(reader.trailer["/Root"].get("/Names", {}))
    text = "\n".join(page.extract_text() for page in reader.pages)
    all_text = text + "\n" + str(reader.metadata)
    for pattern in (VERSION_LABEL, WINDOWS_PATH, LOCAL_HOME, PRIVATE_SOURCE_META):
        assert not pattern.search(all_text), "Private metadata in PDF"
    for required in ("Table S1.", "Table S2.", "Table S3.", "Table S4.",
                     "952 / 952", "115 PASS", "2,773 / 2,773",
                     manifest["code_sha256"], manifest["input_sha256"]):
        assert required in text, required
    # Each source line is numbered; verify the complete listing is present.
    appendix = text.split("Appendix B. Complete executable .m source", 1)[1]
    line_numbers = [int(n) for n in re.findall(r"(?m)^[ \t]*(\d+)[ \t]{2}", appendix)]
    expected = list(range(1, manifest["source_lines"] + 1))
    assert line_numbers == expected, "Incomplete or disordered code listing"
    for check in section["checks"]:
        assert check in text.replace("\n", ""), f"Missing check in PDF: {check}"
    print(f"COMPUTATIONAL REPORT: PASS ({len(reader.pages)} pages; "
          "source, results, hashes and PDF privacy checked)")


if __name__ == "__main__":
    main()
