from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = ROOT / "config" / "verification_manifest.json"
AUX_PATH = ROOT / "output" / "manuscript" / "Trace-Euclidean-v9.aux"


def load_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def normalized_tex(text: str) -> str:
    return re.sub(r"\s+", "", text)


def label_kind(label: str) -> str:
    prefix = label.split(":", 1)[0]
    return {
        "sec": "Section",
        "eq": "Equation",
        "lem": "Lemma",
        "prop": "Proposition",
        "thm": "Theorem",
        "cor": "Corollary",
        "defn": "Definition",
        "re": "Remark",
        "ex": "Example",
        "tab": "Table",
        "conj": "Conjecture",
    }.get(prefix, "Reference")


def parse_aux_labels(path: Path) -> dict[str, dict[str, str]]:
    if not path.is_file():
        raise FileNotFoundError(f"Compiled manuscript auxiliary file not found: {path}")
    text = path.read_text(encoding="utf-8", errors="replace")
    records: dict[str, dict[str, str]] = {}
    pattern = re.compile(r"\\newlabel\{([^}]+)\}\{\{([^{}]*)\}\{([^{}]*)\}")
    for label, number, page in pattern.findall(text):
        if label.endswith("@cref"):
            continue
        kind = label_kind(label)
        if kind == "Equation":
            display = f"Equation ({number})"
        else:
            display = f"{kind} {number}"
        records[label] = {
            "number": number,
            "page": page,
            "kind": kind,
            "display": display,
        }
    return records


def find_unique_label(lines: list[str], label: str) -> int:
    needle = rf"\label{{{label}}}"
    hits = [i for i, line in enumerate(lines) if needle in line]
    if len(hits) != 1:
        raise ValueError(f"Expected one occurrence of {needle}; found {len(hits)}")
    return hits[0]


def environment_containing_label(lines: list[str], label: str, environment: str) -> tuple[int, int, list[str]]:
    label_index = find_unique_label(lines, label)
    begin = rf"\begin{{{environment}}}"
    end = rf"\end{{{environment}}}"
    start = next((i for i in range(label_index, -1, -1) if begin in lines[i]), None)
    stop = next((i for i in range(label_index, len(lines)) if end in lines[i]), None)
    if start is None or stop is None:
        raise ValueError(f"Could not locate {environment} environment containing {label}")
    return start, stop, lines[start : stop + 1]


def strip_math(cell: str) -> str:
    cell = cell.replace(r"\(", "").replace(r"\)", "").replace("$", "")
    cell = cell.replace(r"\,", "").replace(r"\;", "").replace(r"\!", "")
    return re.sub(r"\s+", "", cell)


def parse_span(cell: str, symbol: str) -> list[int]:
    clean = strip_math(cell)
    range_match = re.search(rf"(\d+)\\leq?{re.escape(symbol)}\\leq?(\d+)", clean)
    if range_match:
        lo, hi = map(int, range_match.groups())
        return list(range(lo, hi + 1))
    integers = [int(x) for x in re.findall(r"\d+", clean)]
    if len(integers) == 1:
        return integers
    raise ValueError(f"Could not parse a {symbol}-span from {cell!r}")


def table_rows(table_lines: list[str]) -> list[tuple[int, str]]:
    in_tabular = False
    rows: list[tuple[int, str]] = []
    for relative_index, line in enumerate(table_lines):
        if r"\begin{tabular}" in line:
            in_tabular = True
            continue
        if r"\end{tabular}" in line:
            break
        if in_tabular and "&" in line and r"\\" in line:
            rows.append((relative_index, line))
    return rows


def split_cells(line: str) -> list[str]:
    return [cell.strip() for cell in line.split(r"\\", 1)[0].split("&")]


def multirow_value(cell: str) -> str | None:
    match = re.search(r"\\multirow\{[^}]+\}\{[^}]+\}\{(.+)\}", cell)
    return match.group(1) if match else None


def parse_admissible_table(spec: dict, lines: list[str]) -> list[dict]:
    start, _, block = environment_containing_label(lines, spec["label"], "table")
    parsed: list[dict] = []
    current_degrees: list[int] | None = None
    in_tabular = False
    for relative_index, raw in enumerate(block):
        if r"\begin{tabular}" in raw:
            in_tabular = True
            continue
        if r"\end{tabular}" in raw:
            break
        if not in_tabular:
            continue
        standalone_multirow = multirow_value(raw)
        if standalone_multirow is not None:
            current_degrees = parse_span(standalone_multirow, spec["degree_symbol"])
        if "&" not in raw or r"\\" not in raw:
            continue
        cells = split_cells(raw)
        if len(cells) != 4 or "Degree" in cells[0]:
            continue
        degree_cell = cells[0]
        carried = multirow_value(degree_cell)
        if carried is not None:
            current_degrees = parse_span(carried, spec["degree_symbol"])
        elif strip_math(degree_cell):
            current_degrees = parse_span(degree_cell, spec["degree_symbol"])
        if current_degrees is None:
            raise ValueError(f"Missing carried degree before source line {start + relative_index + 1}")
        ranks = parse_span(cells[1], spec["rank_symbol"])
        displayed = re.findall(r"-?\d+\.\d+", cells[2])
        if not displayed:
            raise ValueError(f"No displayed decimal at source line {start + relative_index + 1}")
        bound_clean = strip_math(cells[3])
        bound = "<1" if "<1" in bound_clean else re.search(r"\d+(?:\.\d+)?", bound_clean).group(0)
        parsed.append(
            {
                "table_id": spec["id"],
                "label": spec["label"],
                "kind": spec["kind"],
                "row_id": f"{spec['id']}:r{len(parsed) + 1:02d}",
                "source_line": start + relative_index + 1,
                "degrees": current_degrees,
                "ranks": ranks,
                "displayed": displayed,
                "bound": bound,
                "source": raw.strip(),
            }
        )
    if not parsed:
        raise ValueError(f"No data rows parsed from {spec['label']}")
    return parsed


def parse_maxima_table(spec: dict, lines: list[str]) -> list[dict]:
    start, _, block = environment_containing_label(lines, spec["label"], "table")
    parsed: list[dict] = []
    for relative_index, raw in table_rows(block):
        cells = split_cells(raw)
        if len(cells) != 4 or "Degree" in cells[0]:
            continue
        parsed.append(
            {
                "table_id": spec["id"],
                "label": spec["label"],
                "kind": spec["kind"],
                "row_id": f"{spec['id']}:r{len(parsed) + 1:02d}",
                "source_line": start + relative_index + 1,
                "degrees": parse_span(cells[0], spec["degree_symbol"]),
                "maxrank": int(strip_math(cells[1])),
                "ranks": parse_span(cells[2], spec["rank_symbol"]),
                "maxdegree": int(strip_math(cells[3])),
                "source": raw.strip(),
            }
        )
    if not parsed:
        raise ValueError(f"No data rows parsed from {spec['label']}")
    return parsed


def find_near_anchor(lines: list[str], anchor_line: int, fragment: str, radius: int = 90) -> int:
    start = max(0, anchor_line - 3)
    stop = min(len(lines), anchor_line + radius)
    target = normalized_tex(fragment)
    for index in range(start, stop):
        if target in normalized_tex(lines[index]):
            return index
    joined = normalized_tex("\n".join(lines[start:stop]))
    if target in joined:
        return anchor_line
    raise ValueError(f"Fragment {fragment!r} was not found near source line {anchor_line + 1}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Extract manuscript-bound verification inputs by semantic LaTeX labels.")
    parser.add_argument("--manifest", type=Path, default=MANIFEST_PATH)
    parser.add_argument("--aux", type=Path, default=AUX_PATH)
    args = parser.parse_args()

    manifest = load_json(args.manifest.resolve())
    source_path = ROOT / "source_snapshot" / manifest["manuscript"]["filename"]
    raw = source_path.read_bytes()
    text = raw.decode("utf-8-sig")
    lines = text.splitlines()

    required_labels = sorted(
        {
            anchor
            for module in manifest["modules"]
            for anchor in module["anchors"]
        }
        | {claim["anchor"] for claim in manifest["numeric_claims"]}
        | {item["anchor"] for item in manifest["required_source_fragments"]}
        | {table["label"] for table in manifest["tables"]}
        | {item["anchor"] for item in manifest["section4_checks"]}
    )
    aux_labels = parse_aux_labels(args.aux.resolve())
    missing_aux_labels = [label for label in required_labels if label not in aux_labels]
    if missing_aux_labels:
        raise ValueError(f"Labels missing from compiled manuscript AUX: {missing_aux_labels}")
    labels = {
        label: {"line": find_unique_label(lines, label) + 1, **aux_labels[label]}
        for label in required_labels
    }

    source_checks = []
    for item in manifest["required_source_fragments"]:
        found = find_near_anchor(lines, labels[item["anchor"]]["line"] - 1, item["fragment"])
        source_checks.append({**item, "source_line": found + 1, "present": True})

    numeric_claims = []
    for claim in manifest["numeric_claims"]:
        found = find_near_anchor(lines, labels[claim["anchor"]]["line"] - 1, claim["reported"])
        numeric_claims.append({**claim, "source_line": found + 1})

    admissible_rows: list[dict] = []
    maxima_rows: list[dict] = []
    for table in manifest["tables"]:
        if table["type"] == "admissible":
            admissible_rows.extend(parse_admissible_table(table, lines))
        elif table["type"] == "maxima":
            maxima_rows.extend(parse_maxima_table(table, lines))
        else:
            raise ValueError(f"Unknown table type: {table['type']}")

    output = {
        "schema_version": manifest["schema_version"],
        "manuscript": manifest["manuscript"],
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "aux_sha256": hashlib.sha256(args.aux.resolve().read_bytes()).hexdigest(),
        "source_line_count": len(lines),
        "labels": labels,
        "modules": manifest["modules"],
        "section4_checks": manifest["section4_checks"],
        "source_checks": source_checks,
        "numeric_claims": numeric_claims,
        "tables": admissible_rows,
        "maxima": maxima_rows,
        "enumeration": manifest["enumeration"],
    }
    destination = ROOT / "inputs" / "manuscript_inputs.json"
    destination.write_bytes(
        (json.dumps(output, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    )
    print(
        json.dumps(
            {
                "source_sha256": output["source_sha256"],
                "labels": len(labels),
                "numeric_claims": len(numeric_claims),
                "table_rows": len(admissible_rows),
                "maxima_rows": len(maxima_rows),
                "output": str(destination),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
