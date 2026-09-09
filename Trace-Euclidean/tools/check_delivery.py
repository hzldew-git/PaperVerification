from __future__ import annotations

import hashlib
import json
import re
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TEXT_SUFFIXES = {
    ".csv",
    ".json",
    ".lean",
    ".log",
    ".m",
    ".md",
    ".ps1",
    ".py",
    ".tex",
    ".toml",
    ".txt",
    ".wl",
    ".wls",
    ".yaml",
    ".yml",
}


def load_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def require(path: Path, errors: list[str]) -> None:
    if not path.is_file() or path.stat().st_size == 0:
        errors.append(f"Missing or empty file: {path.relative_to(ROOT)}")


def files_below(path: Path) -> list[Path]:
    return [item for item in path.rglob("*") if item.is_file()] if path.exists() else []


def write_text_lf(path: Path, text: str) -> None:
    normalized = text.replace("\r\n", "\n").replace("\r", "\n")
    path.write_bytes(normalized.encode("utf-8"))


def normalize_public_text_files() -> None:
    for path in ROOT.rglob("*"):
        if not path.is_file():
            continue
        relative = path.relative_to(ROOT)
        if any(part in {".lake", "tmp", "source_snapshot"} for part in relative.parts):
            continue
        if len(relative.parts) >= 2 and relative.parts[:2] == ("output", "manuscript"):
            continue
        if path.suffix.lower() not in TEXT_SUFFIXES and path.name != ".gitignore":
            continue
        raw = path.read_bytes()
        normalized = raw.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
        if normalized != raw:
            path.write_bytes(normalized)


def main() -> None:
    errors: list[str] = []
    snapshot = ROOT / "source_snapshot" / "Trace-Euclidean-v9.tex"
    manuscript_output = ROOT / "output" / "manuscript"
    private_mode = snapshot.is_file()

    required = [
        ROOT / ".gitignore",
        ROOT / "README.md",
        ROOT / "build_all.ps1",
        ROOT / "verify_trace_euclidean_v9.m",
        ROOT / "run_verification.wls",
        ROOT / "config" / "verification_manifest.json",
        ROOT / "lib" / "verification_core.wl",
        ROOT / "checks" / "analytic_bounds.wl",
        ROOT / "checks" / "admissible_tables.wl",
        ROOT / "checks" / "trace_geometry.wl",
        ROOT / "checks" / "gamma_diagnostics.wl",
        ROOT / "tools" / "prepare_inputs.py",
        ROOT / "tools" / "build_report.py",
        ROOT / "tools" / "check_delivery.py",
        ROOT / "inputs" / "manuscript_inputs.json",
        ROOT / "results" / "summary.json",
        ROOT / "results" / "tests.json",
        ROOT / "results" / "tests.csv",
        ROOT / "results" / "numeric_values.json",
        ROOT / "results" / "all_table_values.json",
        ROOT / "results" / "all_table_values.csv",
        ROOT / "results" / "rational_certificates.json",
        ROOT / "results" / "quadratic_fields.json",
        ROOT / "results" / "issues.json",
        ROOT / "results" / "verification_ledger.json",
        ROOT / "results" / "section4_coverage.json",
        ROOT / "results" / "verification_transcript.txt",
        ROOT / "generated" / "run_summary.tex",
        ROOT / "generated" / "module_map.tex",
        ROOT / "generated" / "manuscript_refs.tex",
        ROOT / "generated" / "section4_coverage.tex",
        ROOT / "generated" / "category_summary.tex",
        ROOT / "generated" / "numeric_claims.tex",
        ROOT / "generated" / "issues.tex",
        ROOT / "docs" / "verification_manual_v9.tex",
        ROOT / "output" / "pdf" / "verification_manual_v9.pdf",
        ROOT / "output" / "pdf" / "verification_manual_v9.log",
        ROOT / "lean" / "lean-toolchain",
        ROOT / "lean" / "lakefile.toml",
        ROOT / "lean" / "lake-manifest.json",
        ROOT / "lean" / "TraceEuclidean.lean",
        ROOT / "lean" / "TraceEuclideanTest.lean",
        ROOT / "lean" / "TraceEuclidean" / "Basic.lean",
        ROOT / "lean" / "TraceEuclidean" / "Scaling.lean",
        ROOT / "lean" / "TraceEuclidean" / "AnalyticCriticalPoint.lean",
        ROOT / "lean" / "TraceEuclidean" / "Finiteness.lean",
        ROOT / "lean" / "TraceEuclidean" / "VoronoiAlgebra.lean",
        ROOT / "lean" / "TraceEuclidean" / "QuadraticArithmetic.lean",
        ROOT / "lean" / "TraceEuclideanTest" / "MainTheoremAudit.lean",
        ROOT / "lean" / "audit" / "main_theorem_axioms.txt",
        ROOT / "THEOREM_INDEX.md",
        ROOT / "TRUST.md",
        ROOT / "REPRODUCING.md",
        ROOT / "SOURCES.md",
        ROOT / "docs" / "audit" / "12_executive_summary.md",
    ]
    if private_mode:
        required.extend(
            [
                snapshot,
                manuscript_output / "Trace-Euclidean-v9.pdf",
                manuscript_output / "Trace-Euclidean-v9.aux",
                manuscript_output / "Trace-Euclidean-v9.log",
            ]
        )

    for path in required:
        require(path, errors)
    if errors:
        raise SystemExit("\n".join(errors))

    if not private_mode:
        leaked_private_files = files_below(ROOT / "source_snapshot") + files_below(manuscript_output)
        if leaked_private_files:
            errors.extend(
                f"Public package contains a private manuscript artifact: {path.relative_to(ROOT)}"
                for path in leaked_private_files
            )

    inputs = load_json(ROOT / "inputs" / "manuscript_inputs.json")
    summary = load_json(ROOT / "results" / "summary.json")
    tests = load_json(ROOT / "results" / "tests.json")
    ledger = load_json(ROOT / "results" / "verification_ledger.json")
    coverage = load_json(ROOT / "results" / "section4_coverage.json")
    manifest = load_json(ROOT / "config" / "verification_manifest.json")

    input_hash = str(inputs.get("source_sha256", ""))
    summary_hash = str(summary.get("source_sha256", ""))
    source_hash_consistent = input_hash == summary_hash and bool(
        re.fullmatch(r"[0-9a-f]{64}", input_hash)
    )
    if not source_hash_consistent:
        errors.append("The extracted inputs and Mathematica summary have different or invalid source digests.")
    if private_mode and sha256(snapshot) != input_hash:
        errors.append("The private snapshot does not match the digest in the extracted inputs.")

    observed_counts = Counter(item["status"] for item in tests)
    if dict(observed_counts) != summary["counts"]:
        errors.append("The summary status counts do not equal the test-record counts.")
    if observed_counts.get("FAIL", 0):
        errors.append("At least one FAIL record remains in results/tests.json.")

    modules = {item["module"] for item in ledger}
    test_modules = {item["module"] for item in tests if item["module"] != "integrity"}
    if modules != test_modules:
        errors.append(
            f"Module mismatch between ledger and tests: ledger={sorted(modules)}, "
            f"tests={sorted(test_modules)}"
        )

    test_ids = {item["id"] for item in tests}
    required_labels = {
        anchor for module in manifest["modules"] for anchor in module["anchors"]
    }
    required_labels.update(item["anchor"] for item in manifest["section4_checks"])
    required_labels.update(item["anchor"] for item in manifest["numeric_claims"])
    required_labels.update(item["label"] for item in manifest["tables"])
    for label in sorted(required_labels):
        metadata = inputs.get("labels", {}).get(label)
        if metadata is None:
            errors.append(f"No extracted numbering metadata for manuscript label {label}")
            continue
        for field in ("number", "page", "kind", "display"):
            if not str(metadata.get(field, "")).strip():
                errors.append(f"Missing {field} for manuscript label {label}")

    manifest_coverage_ids = {item["id"] for item in manifest["section4_checks"]}
    result_coverage_ids = {item["id"] for item in coverage}
    if manifest_coverage_ids != result_coverage_ids:
        errors.append("The generated Section 4 coverage ledger does not match the manifest.")
    coverage_test_counts = Counter(
        test_id
        for item in manifest["section4_checks"]
        for test_id in item["test_ids"]
    )
    duplicated_coverage_tests = sorted(
        test_id for test_id, count in coverage_test_counts.items() if count != 1
    )
    if duplicated_coverage_tests:
        errors.append(
            "Section 4 test IDs must occur exactly once in the coverage manifest: "
            f"{duplicated_coverage_tests}"
        )
    mathematical_analytic_ids = {
        item["id"]
        for item in tests
        if item["module"] == "analytic_bounds" and item["category"] != "source binding"
    }
    if set(coverage_test_counts) != mathematical_analytic_ids:
        missing = sorted(mathematical_analytic_ids - set(coverage_test_counts))
        extra = sorted(set(coverage_test_counts) - mathematical_analytic_ids)
        errors.append(f"Section 4 analytic coverage mismatch: missing={missing}, extra={extra}")
    nonpassing_coverage = [item["id"] for item in coverage if item.get("status") != "PASS"]
    if nonpassing_coverage:
        errors.append(f"Section 4 contains non-PASS coverage entries: {nonpassing_coverage}")

    for claim in inputs["numeric_claims"]:
        if "numeric-" + claim["id"] not in test_ids:
            errors.append(f"No Mathematica result for numeric claim {claim['id']}")
    for row in inputs["tables"]:
        if not any(
            test_id.endswith(row["row_id"]) and test_id.startswith("table-h-")
            for test_id in test_ids
        ):
            errors.append(f"No h-value result for table row {row['row_id']}")
        if "table-G-bound-" + row["row_id"] not in test_ids:
            errors.append(f"No G-bound result for table row {row['row_id']}")

    log = (ROOT / "output" / "pdf" / "verification_manual_v9.log").read_text(
        encoding="utf-8", errors="replace"
    )
    forbidden_log_patterns = {
        "overfull box": r"Overfull \\hbox",
        "undefined references": r"undefined references",
        "undefined citations": r"undefined citations",
        "LaTeX error": r"! LaTeX Error",
        "undefined control sequence": r"Undefined control sequence",
    }
    for label, pattern in forbidden_log_patterns.items():
        if re.search(pattern, log, flags=re.IGNORECASE):
            errors.append(f"The verification-manual LaTeX log contains {label}.")

    manual_pdf = ROOT / "output" / "pdf" / "verification_manual_v9.pdf"
    if not manual_pdf.read_bytes().startswith(b"%PDF"):
        errors.append("The compiled verification manual is not a PDF file.")

    lean_files = [
        ROOT / "lean" / "TraceEuclidean.lean",
        ROOT / "lean" / "TraceEuclideanTest.lean",
        *files_below(ROOT / "lean" / "TraceEuclidean"),
        *files_below(ROOT / "lean" / "TraceEuclideanTest"),
    ]
    forbidden_lean = re.compile(
        r"(?i)(^|[^A-Za-z])sorry([^A-Za-z]|$)|sorryAx|^\s*axiom\s|"
        r"\bnative_decide\b|\brun_tac\b|^\s*unsafe\s|^\s*extern\s|implemented_by",
        flags=re.MULTILINE,
    )
    for path in lean_files:
        text = path.read_text(encoding="utf-8")
        if forbidden_lean.search(text):
            errors.append(f"Forbidden Lean proof construct in {path.relative_to(ROOT)}")

    axiom_report = (ROOT / "lean" / "audit" / "main_theorem_axioms.txt").read_text(
        encoding="utf-8", errors="replace"
    )
    axiom_lines = [
        line for line in axiom_report.splitlines() if "depends on axioms:" in line
    ]
    expected_axioms = "depends on axioms: [propext, Classical.choice, Quot.sound]"
    if len(axiom_lines) != 13 or any(expected_axioms not in line for line in axiom_lines):
        errors.append("The Lean endpoint report contains a missing or unexpected axiom set.")

    manuscript_pdf_present = False
    if private_mode:
        manuscript_log = (manuscript_output / "Trace-Euclidean-v9.log").read_text(
            encoding="utf-8", errors="replace"
        )
        for label, pattern in {
            "undefined references": r"undefined references",
            "undefined citations": r"undefined citations",
            "LaTeX error": r"! LaTeX Error",
            "undefined control sequence": r"Undefined control sequence",
        }.items():
            if re.search(pattern, manuscript_log, flags=re.IGNORECASE):
                errors.append(f"The private manuscript LaTeX log contains {label}.")
        manuscript_pdf = manuscript_output / "Trace-Euclidean-v9.pdf"
        manuscript_pdf_present = manuscript_pdf.is_file() and manuscript_pdf.read_bytes().startswith(b"%PDF")
        if not manuscript_pdf_present:
            errors.append("The private compiled manuscript is not a PDF file.")

    status = {
        "source_sha256": input_hash,
        "source_hash_consistent": source_hash_consistent,
        "test_counts": dict(observed_counts),
        "tests_match_summary": dict(observed_counts) == summary["counts"],
        "module_ledger_complete": modules == test_modules,
        "numeric_claims_mapped": len(inputs["numeric_claims"]),
        "table_rows_mapped": len(inputs["tables"]),
        "manuscript_numbering_available": not any(
            "manuscript label" in error for error in errors
        ),
        "section4_coverage_entries": len(coverage),
        "section4_analytic_tests_covered": len(mathematical_analytic_ids),
        "section4_coverage_complete": (
            manifest_coverage_ids == result_coverage_ids
            and set(coverage_test_counts) == mathematical_analytic_ids
            and not duplicated_coverage_tests
            and not nonpassing_coverage
        ),
        "latex_log_clean": not any("LaTeX log" in error for error in errors),
        "manual_pdf_present": manual_pdf.is_file(),
        "lean_forbidden_constructs_absent": not any(
            "Forbidden Lean proof construct" in error for error in errors
        ),
        "lean_endpoint_axiom_sets_expected": not any(
            "Lean endpoint report" in error for error in errors
        ),
        "errors": errors,
    }
    write_text_lf(ROOT / "results" / "delivery_check.json", json.dumps(status, indent=2) + "\n")
    normalize_public_text_files()

    hash_paths = sorted(
        path
        for path in ROOT.rglob("*")
        if path.is_file()
        and path.name != "SHA256SUMS.json"
        and "__pycache__" not in path.parts
        and ".lake" not in path.relative_to(ROOT).parts
        and "tmp" not in path.relative_to(ROOT).parts
        and "source_snapshot" not in path.relative_to(ROOT).parts
        and not (
            len(path.relative_to(ROOT).parts) >= 2
            and path.relative_to(ROOT).parts[:2] == ("output", "manuscript")
        )
        and path.suffix.lower() not in {".aux", ".fdb_latexmk", ".fls", ".out", ".xdv"}
        and not path.name.lower().endswith(".synctex.gz")
    )
    sums = {path.relative_to(ROOT).as_posix(): sha256(path) for path in hash_paths}
    write_text_lf(ROOT / "SHA256SUMS.json", json.dumps(sums, indent=2) + "\n")

    if errors:
        raise SystemExit("\n".join(errors))
    print(json.dumps(status, indent=2))


if __name__ == "__main__":
    main()
