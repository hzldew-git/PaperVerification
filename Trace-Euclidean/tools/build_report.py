from __future__ import annotations

import json
import re
from collections import Counter, defaultdict
from decimal import Decimal, ROUND_CEILING
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
INPUTS = ROOT / "inputs"
RESULTS = ROOT / "results"
GENERATED = ROOT / "generated"


def load_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_text_lf(path: Path, text: str) -> None:
    normalized = text.replace("\r\n", "\n").replace("\r", "\n")
    path.write_bytes(normalized.encode("utf-8"))


def tex(text) -> str:
    mapping = {
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
        "\\": r"\textbackslash{}",
    }
    return "".join(mapping.get(char, char) for char in str(text))


def url(text) -> str:
    return rf"\nolinkurl{{{text}}}"


def wl_decimal(text: str) -> Decimal:
    cleaned = re.sub(r"`[0-9.]*", "", str(text)).replace("*^", "E")
    return Decimal(cleaned)


def decimal_text(value: Decimal, places: int = 12) -> str:
    result = f"{value:.{places}f}".rstrip("0").rstrip(".")
    return result if result not in {"", "-0"} else "0"


def fixed_decimal_text(value: Decimal, places: int) -> str:
    return f"{value:.{places}f}"


def outward_ceiling(value: Decimal, digits: int) -> Decimal:
    scale = Decimal(10) ** digits
    return (value * scale).to_integral_value(rounding=ROUND_CEILING) / scale


def count_table(counts: dict) -> str:
    return f"{counts.get('PASS', 0)} / {counts.get('WARN', 0)} / {counts.get('FAIL', 0)}"


def manuscript_ref(manuscript: dict, label: str, include_page: bool = False) -> str:
    metadata = manuscript["labels"][label]
    if metadata["kind"] == "Equation":
        result = rf"Equation~({tex(metadata['number'])})"
    else:
        result = rf"{tex(metadata['kind'])}~{tex(metadata['number'])}"
    if include_page:
        result += rf", p.~{tex(metadata['page'])}"
    return result


def plain_location(manuscript: dict, label: str) -> str:
    metadata = manuscript["labels"][label]
    return f"{metadata['display']}, p. {metadata['page']}"


def longtable(
    headers: list[str],
    rows: list[list[str]],
    widths: list[str],
    font: str = r"\small",
    tabcolsep: str | None = None,
    ragged: bool = False,
) -> str:
    if ragged:
        columns = "".join(rf">{{\raggedright\arraybackslash}}p{{{width}}}" for width in widths)
    else:
        columns = "".join(f"p{{{width}}}" for width in widths)
    spec = "@{}" + columns + "@{}"
    header = " & ".join(headers) + r" \\"
    body = "\n".join(" & ".join(row) + r" \\" for row in rows)
    setup = "{" + font + "\n"
    if tabcolsep is not None:
        setup += rf"\setlength{{\tabcolsep}}{{{tabcolsep}}}" + "\n"
    return (
        setup +
        rf"\begin{{longtable}}{{{spec}}}" + "\n"
        r"\toprule" + "\n" + header + "\n" +
        r"\midrule\endfirsthead" + "\n" +
        r"\toprule" + "\n" + header + "\n" +
        r"\midrule\endhead" + "\n" +
        r"\bottomrule\endfoot" + "\n" +
        body + "\n" + r"\end{longtable}" + "\n" + r"}" + "\n"
    )


def module_list(rows: list[dict]) -> str:
    parts = [r"{\small"]
    for index, row in enumerate(rows):
        if index:
            parts.append(r"\medskip")
        parts.extend([
            rf"\noindent\textbf{{{tex(row['title'])}}}\par",
            rf"\textbf{{Code:}} {url(row['code'])}. "
            rf"\textbf{{Result (P/W/F):}} {row['counts']}.\par",
            rf"\textbf{{Manuscript locations:}} {row['locations']}.\par",
            rf"\textbf{{Evidence:}} {tex(row['evidence'])}.\par",
        ])
    parts.append(r"}")
    return "\n".join(parts) + "\n"


def span(values: list[int], symbol: str) -> str:
    if len(values) == 1:
        return rf"${symbol}={values[0]}$"
    if values == list(range(values[0], values[-1] + 1)):
        return rf"${values[0]}\le {symbol}\le {values[-1]}$"
    return rf"${symbol}\in\{{{','.join(map(str, values))}\}}$"


def main() -> None:
    GENERATED.mkdir(parents=True, exist_ok=True)
    manuscript = load_json(INPUTS / "manuscript_inputs.json")
    summary = load_json(RESULTS / "summary.json")
    tests = load_json(RESULTS / "tests.json")
    numeric = load_json(RESULTS / "numeric_values.json")
    table_values = load_json(RESULTS / "all_table_values.json")

    tests_by_module: dict[str, list[dict]] = defaultdict(list)
    tests_by_category: dict[str, list[dict]] = defaultdict(list)
    test_by_id = {}
    for item in tests:
        tests_by_module[item["module"]].append(item)
        tests_by_category[item["category"]].append(item)
        test_by_id[item["id"]] = item

    reference_lines = [r"\newcommand{\msref}[1]{\csname msref@#1\endcsname}"]
    for label, metadata in sorted(manuscript["labels"].items()):
        reference_lines.append(
            rf"\expandafter\def\csname msref@{label}\endcsname{{{manuscript_ref(manuscript, label)}}}"
        )
    write_text_lf(GENERATED / "manuscript_refs.tex", "\n".join(reference_lines) + "\n")

    summary_rows = [
        ["Private source identifier", url(manuscript["manuscript"]["filename"])],
        ["SHA-256", url(summary["source_sha256"])],
        ["Source lines", str(summary["source_line_count"])],
        ["Wolfram kernel", tex(summary["kernel"])],
        ["PASS / WARN / FAIL", count_table(summary["counts"])],
        ["Certified classical pairs", str(summary["classical_pairs"])],
        ["Certified integral pairs", str(summary["integral_pairs"])],
        ["Square-free parameters tested", str(summary["quadratic_fields_tested"])],
        ["Root precision", f"{summary['precision']} digits"],
        ["Rational interval output", f"{summary['interval_decimal_places']} decimal places, rounded outward"],
    ]
    write_text_lf(
        GENERATED / "run_summary.tex",
        longtable(["Item", "Recorded value"], summary_rows, ["46mm", "108mm"]),
    )

    module_rows = []
    ledger = []
    for module in manuscript["modules"]:
        module_tests = tests_by_module[module["id"]]
        counts = Counter(item["status"] for item in module_tests)
        module_rows.append({
            "title": module["title"],
            "code": module["code"],
            "locations": ", ".join(manuscript_ref(manuscript, label) for label in module["anchors"]),
            "evidence": module["evidence"],
            "counts": count_table(counts),
        })
        ledger.append({
            "module": module["id"],
            "title": module["title"],
            "code": module["code"],
            "manuscript_anchors": module["anchors"],
            "manuscript_locations": [plain_location(manuscript, label) for label in module["anchors"]],
            "evidence": module["evidence"],
            "test_count": len(module_tests),
            "counts": dict(counts),
            "result_records": "results/tests.json and results/tests.csv",
        })
    write_text_lf(GENERATED / "module_map.tex", module_list(module_rows))
    write_text_lf(RESULTS / "verification_ledger.json", json.dumps(ledger, indent=2) + "\n")

    coverage_rows = []
    coverage_ledger = []
    covered_test_ids: set[str] = set()
    for item in manuscript["section4_checks"]:
        missing = [test_id for test_id in item["test_ids"] if test_id not in test_by_id]
        if missing:
            raise ValueError(f"Missing Section 4 test records for {item['id']}: {missing}")
        records = [test_by_id[test_id] for test_id in item["test_ids"]]
        covered_test_ids.update(item["test_ids"])
        statuses = Counter(record["status"] for record in records)
        status = "FAIL" if statuses.get("FAIL", 0) else "WARN" if statuses.get("WARN", 0) else "PASS"
        coverage_rows.append([
            manuscript_ref(manuscript, item["anchor"], include_page=True),
            tex(item["description"]),
            tex(item["evidence"]),
            f"{status} ({len(records)})",
        ])
        coverage_ledger.append({
            **item,
            "manuscript_location": plain_location(manuscript, item["anchor"]),
            "test_count": len(records),
            "counts": dict(statuses),
            "status": status,
        })
    mathematical_analytic_ids = {
        item["id"] for item in tests_by_module["analytic_bounds"]
        if item["category"] != "source binding"
    }
    uncovered = sorted(mathematical_analytic_ids - covered_test_ids)
    if uncovered:
        raise ValueError(f"Analytic test records missing from the Section 4 coverage ledger: {uncovered}")
    write_text_lf(
        GENERATED / "section4_coverage.tex",
        longtable(
            ["Manuscript location", "Calculation checked", "Evidence", "Result"],
            coverage_rows,
            ["30mm", "64mm", "44mm", "16mm"],
            font=r"\footnotesize",
            tabcolsep="2pt",
            ragged=True,
        ),
    )
    write_text_lf(
        RESULTS / "section4_coverage.json", json.dumps(coverage_ledger, indent=2) + "\n"
    )

    category_rows = []
    for category in sorted(tests_by_category):
        counts = Counter(item["status"] for item in tests_by_category[category])
        category_rows.append([
            tex(category),
            str(len(tests_by_category[category])),
            str(counts.get("PASS", 0)),
            str(counts.get("WARN", 0)),
            str(counts.get("FAIL", 0)),
        ])
    write_text_lf(
        GENERATED / "category_summary.tex",
        longtable(
            ["Check category", "Total", "PASS", "WARN", "FAIL"],
            category_rows,
            ["64mm", "15mm", "15mm", "15mm", "15mm"],
        ),
    )

    numeric_rows = []
    for item in numeric:
        test = test_by_id["numeric-" + item["id"]]
        numeric_rows.append([
            url(item["id"]),
            manuscript_ref(manuscript, item["anchor"]),
            str(item["source_line"]),
            tex(item["reported"]),
            tex(decimal_text(wl_decimal(item["value"]), 10)),
            test["status"],
        ])
    write_text_lf(
        GENERATED / "numeric_claims.tex",
        longtable(
            ["Claim ID", "Manuscript location", "Line", "Printed", "Computed", "Status"],
            numeric_rows,
            ["36mm", "39mm", "9mm", "14mm", "27mm", "12mm"],
            font=r"\footnotesize",
            tabcolsep="2pt",
        ),
    )

    input_rows = {item["row_id"]: item for item in manuscript["tables"]}
    values_by_row: dict[str, list[dict]] = defaultdict(list)
    for item in table_values:
        values_by_row[item["row_id"]].append(item)

    issues = []
    issue_rows = []
    for test in tests:
        if test["status"] == "PASS":
            continue
        if test["id"].startswith("table-G-bound-"):
            row_id = test["id"][len("table-G-bound-") :]
            source = input_rows[row_id]
            maximum = max(wl_decimal(item["G"]) for item in values_by_row[row_id])
            digits = len(source["bound"].split(".")[1]) if "." in source["bound"] else 0
            suggestion = outward_ceiling(maximum, digits)
            pair_text = span(source["ranks"], "n") + ", " + span(source["degrees"], "d")
            issue = {
                "test_id": test["id"],
                "status": test["status"],
                "anchor": test["anchor"],
                "source_line": source["source_line"],
                "pairs": {"ranks": source["ranks"], "degrees": source["degrees"]},
                "printed_bound": source["bound"],
                "computed_G_max": str(maximum),
                "suggested_outward_bound": fixed_decimal_text(suggestion, digits),
                "reason": test["note"],
            }
            issues.append(issue)
            issue_rows.append([
                url(row_id),
                pair_text,
                str(source["source_line"]),
                tex(source["bound"]),
                tex(decimal_text(maximum, 10)),
                tex(fixed_decimal_text(suggestion, digits)),
            ])
        else:
            issues.append(test)
            issue_rows.append([
                url(test["id"]),
                url(test["anchor"]),
                "--",
                tex(test["expected"]),
                tex(test["actual"]),
                "inspect",
            ])
    write_text_lf(RESULTS / "issues.json", json.dumps(issues, indent=2) + "\n")
    if issue_rows:
        issues_tex = longtable(
            ["Row ID", "Parameters", "Line", "Printed", "Computed", "Outward value"],
            issue_rows,
            ["45mm", "22mm", "9mm", "14mm", "28mm", "17mm"],
            font=r"\footnotesize",
            tabcolsep="2pt",
        )
    else:
        issues_tex = "No WARN or FAIL record was produced by this run.\n"
    write_text_lf(GENERATED / "issues.tex", issues_tex)

    print(json.dumps({
        "generated_fragments": 7,
        "ledger_entries": len(ledger),
        "section4_coverage_entries": len(coverage_ledger),
        "issues": len(issues),
        "manual": str(ROOT / "docs" / "verification_manual_v9.tex"),
    }, indent=2))


if __name__ == "__main__":
    main()
