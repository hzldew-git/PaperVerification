"""Check TeX/PDF provenance, all generated result blocks and the full code listing."""
from __future__ import annotations

import hashlib
import importlib.util
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
    tex = code.with_suffix(".tex")
    pdf = SUPPLEMENT / "TraceEuclideanVerification.pdf"
    assert code.stem == tex.stem == pdf.stem
    assert manifest["code_sha256"] == sha(code)
    assert manifest["tex_sha256"] == sha(tex)
    assert manifest["pdf_backend"] == "XeLaTeX"
    assert manifest["input_sha256"] == sha(ROOT / "inputs/verification_inputs.json")
    assert manifest["pdf_sha256"] == sha(pdf)
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
    # Recompute the expected TeX blocks from the original JSON, without writing.
    spec = importlib.util.spec_from_file_location("report_builder", SUPPLEMENT / "build_report.py")
    builder = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(builder)
    tex_text = tex.read_text(encoding="utf-8")
    assert builder.refreshed_tex(tex_text) == tex_text, "Stale or altered TeX result blocks"
    assert tex_text.count(
        r"\lstinputlisting[style=source]{TraceEuclideanVerification.m}") == 1
    assert not re.search(r"\\(?:include|input)\s*\{", tex_text), "Unexpected TeX input"
    reader = PdfReader(pdf)
    assert len(reader.pages) == manifest["pdf_pages"]
    assert not list(reader.attachments), "Unexpected embedded attachment"
    assert "/OpenAction" not in reader.trailer["/Root"]
    assert "/JavaScript" not in str(reader.trailer["/Root"].get("/Names", {}))
    pages = [page.extract_text() for page in reader.pages]
    text = "\n".join(pages)
    all_text = text + "\n" + str(reader.metadata) + "\n" + tex_text
    for pattern in (VERSION_LABEL, WINDOWS_PATH, LOCAL_HOME, PRIVATE_SOURCE_META):
        assert not pattern.search(all_text), "Private metadata in PDF"
    for required in ("Table S1.", "Table S2.", "Table S3.", "Table S4.",
                     "952 / 952", "115 PASS", "2,773 / 2,773",
                     manifest["code_sha256"], manifest["input_sha256"]):
        assert required in text, required
    # Strip page footers, collect each numbered line plus its continuations,
    # and compare the complete printed source to the actual .m file.
    appendix_lines = []
    in_appendix = False
    heading = "Appendix B. Complete executable .m source"
    for page_number, content in enumerate(pages, 1):
        if heading in content:
            content = content.split(heading, 1)[1]
            in_appendix = True
        if not in_appendix:
            continue
        lines = content.splitlines()
        while lines and not lines[-1].strip():
            lines.pop()
        assert lines[-1].strip() == str(page_number), "Unexpected footer layout"
        appendix_lines.extend(lines[:-1])
    printed = []
    for line in appendix_lines:
        match = re.match(r"^\s*(\d+)(?:[ \t]+(.*)|\s*)$", line)
        if match and int(match[1]) == len(printed) + 1:
            printed.append(match[2] or "")
        elif printed:
            printed[-1] += line
    original = code.read_text(encoding="utf-8").splitlines()
    assert len(printed) == len(original) == manifest["source_lines"], "Incomplete code listing"
    compact = lambda s: re.sub(r"\s+", "", s)
    for line_number, (actual, expected) in enumerate(zip(printed, original), 1):
        assert compact(actual) == compact(expected), f"Printed code mismatch at line {line_number}"
    for check in section["checks"]:
        assert compact(check) in compact(text), f"Missing check in PDF: {check}"
    for check in tables["checks"]:
        assert compact(check) in compact(text), f"Missing Section 4 check in PDF: {check}"
    print(f"COMPUTATIONAL REPORT: PASS ({len(reader.pages)} pages; "
          "TeX blocks, full printed code, results, hashes and privacy checked)")


if __name__ == "__main__":
    main()
