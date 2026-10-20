"""Refresh marked TeX result blocks and compile the verification PDF.

Requires XeLaTeX, latexmk and pypdf. Mathematical computations are read from
the existing Wolfram result files; this script does not synthesize results.
Prose and layout outside the generated TeX blocks are preserved.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import shutil
import subprocess
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path

from pypdf import PdfReader

ROOT = Path(__file__).resolve().parent
RESULTS = ROOT / "results"
CODE = ROOT / "TraceEuclideanVerification.m"
TEX = CODE.with_suffix(".tex")
PDF = CODE.with_suffix(".pdf")
PUBLIC_INPUT = ROOT.parent / "inputs/verification_inputs.json"

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(name: str):
    return json.loads((RESULTS / name).read_text(encoding="utf-8"))


def decimal(value: str) -> Decimal:
    return Decimal(re.sub(r"`[0-9.]*", "", str(value)).replace("*^", "e"))


def rational_decimal(value: str) -> Decimal:
    q = Fraction(value.replace(" ", ""))
    with localcontext() as ctx:
        ctx.prec = 90
        return Decimal(q.numerator) / Decimal(q.denominator)


def six(value: str) -> str:
    v = rational_decimal(value)
    return format(v, ".6g") if v else "0"


def validate():
    summary = load("verification_summary.json")
    tables = load("section4_tables.json")
    classification = load("section6_exact_checks.json")
    cert = load("rational_certificate.json")
    voight = load("voight_integrity.json")
    for data in (summary, tables, classification, voight):
        assert data["provenance"]["code_sha256"] == digest(CODE), "Stale code/results"
        assert data["provenance"]["input_sha256"] == digest(PUBLIC_INPUT), "Stale inputs"
    assert summary["all_passed"] is True
    assert tables["all_passed"] and all(tables["checks"].values())
    assert classification["all_passed"] and len(classification["checks"]) == 115
    assert all(v is True for v in classification["checks"].values())
    assert len(tables["grid"]) == cert["comparisons"] == 952
    assert cert["unresolved_comparisons"] == 0
    assert len(tables["rows"]) == cert["upward_rounded_values"] == 87
    assert [tables["summary"][c]["count"] for c in ("classic", "integral")] == [24, 63]
    assert voight["pass"] and voight["total_rows"] == 2773
    for key in ("irreducible_pass", "totally_real_pass",
                "polynomial_discriminant_square_index_pass", "field_discriminant_pass"):
        assert voight[key] == 2773
    for table in voight["tables"]:
        data = load(f"voight-rows-{table['degree']}.json")
        assert len(data) == table["rows"]
        assert all(all(row[k] is True for k in
                       ("shape", "irreducible", "totallyReal", "indexSquare",
                        "fieldDiscriminant")) for row in data)
        assert table["sha256"] == digest(ROOT.parent / "inputs/voight" / table["file"])
    return summary, tables, classification, cert, voight



def tex(value) -> str:
    replacements = {
        "\\": r"\textbackslash{}", "&": r"\&", "%": r"\%",
        "$": r"\$", "#": r"\#", "_": r"\_",
        "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(c, c) for c in str(value))


def ident(value) -> str:
    # Permit breaks at separators without adding visible hyphens.
    return r"\texttt{" + tex(value).replace(r"\_", r"\_\allowbreak ") + "}"


def longtable(caption, label, spec, headers, rows, size=r"\small"):
    head = " & ".join(headers) + r" \\"
    return "\n".join([
        r"\begingroup", size, r"\begin{longtable}{" + spec + "}",
        r"\caption{" + caption + r"}\label{" + label + r"}\\",
        r"\toprule", head, r"\midrule", r"\endfirsthead",
        r"\multicolumn{" + str(len(headers)) + r"}{l}{\textit{Continued}}\\",
        r"\toprule", head, r"\midrule", r"\endhead",
        r"\midrule", r"\endfoot", r"\bottomrule", r"\endlastfoot",
        *[" & ".join(map(str, row)) + r" \\" for row in rows],
        r"\end{longtable}", r"\endgroup",
    ])


def generated_blocks():
    summary, tables, classification, cert, voight = validate()
    grams = load("gram_candidates.json")
    representatives = load("classification_table.json")
    voronoi = load("voronoi_certificates.json")
    blocks = {}
    blocks["overview"] = longtable(
        "Recorded computation results.", "tab:overview",
        "L{4.3cm}L{4.5cm}L{5.5cm}",
        ["Component", "Actual result", "Meaning"], [
            ["Section 4 grid", "952 / 952 resolved", "Exact rational interval comparisons"],
            ["Displayed volume bounds", "87 / 87 checked", "Six significant digits, rounded upwards"],
            ["Retained pairs", "24 classic-integral; 63 integral", "Necessary numerical conditions"],
            ["Classification", "115 PASS; 0 FAIL", "Exact finite checks"],
            ["Archived Voight rows", "2,773 / 2,773 verified", "Integrity of the supplied lists"],
        ])
    blocks["provenance"] = "\n".join([
        r"\noindent Core run (UTC): " + tex(summary["provenance"]["run_utc"]) + r".\par",
        r"\noindent Archived-row run (UTC): " + tex(voight["provenance"]["run_utc"]) + r".\par",
        r"\noindent Mathematica " + tex(summary["provenance"]["tool"]) + r".\par",
        r"\noindent Code SHA-256:\par",
        r"{\fontsize{8}{10}\selectfont\ttfamily " + digest(CODE) + r"\par}",
        r"\noindent Public input SHA-256:\par",
        r"{\fontsize{8}{10}\selectfont\ttfamily " + digest(PUBLIC_INPUT) + r"\par}",
    ])
    blocks["discriminants"] = longtable(
        "Input minimal discriminants in degrees one through nine.",
        "tab:discriminants", "rr", ["$d$", r"$D_{\min}(d)$"],
        [[i, v] for i, v in enumerate(tables["minimal_discriminants"], 1)])
    minimum = min(abs(decimal(row["log_feasibility_margin"])) for row in tables["grid"])
    blocks["margin"] = ("Smallest absolute log feasibility margin on the grid: $"
                        + format(minimum, ".20g") + "$.")
    for case, title, detail, maximum in (
        ("classic", "Classic-integral", "s1", "s2"),
        ("integral", "Integral", "s3", "s4"),
    ):
        selected = [r for r in tables["rows"] if r["case"] == case]
        blocks[detail] = longtable(
            f"{title} retained pairs ({len(selected)} rows).",
            "tab:" + detail, "rrrr",
            ["$d$", "$n$", "$h(n,d)$", "Upper bound for $V(n,d)$"],
            [[r["d"], r["n"], "$" + format(decimal(r["h_new"]), ".6f") + "$",
              six(r["upper_six_rational"])] for r in selected])
        nd, dn = (tables["summary"][case][key] for key in ("N_d", "D_n"))
        blocks[maximum] = longtable(
            f"{title} maximum retained rank and degree.",
            "tab:" + maximum, "rrrrrr",
            ["$d$", "$N(d)$", "$n$", "$D(n)$", "$n$", "$D(n)$"],
            [[i if i <= 14 else "", nd[i - 1] if i <= 14 else "",
              i, dn[i - 1], i + 17, dn[i + 16]] for i in range(1, 18)])
    blocks["grams"] = (
        "The maximum determinant in the following list is $"
        + str(grams["maximum_determinant"]) + "$.\n"
        + longtable("All 22 Gram candidates and independent Voronoi checks.",
                    "tab:grams", "rcrrr",
                    ["ID", "$(a,b,c)$", r"$\det G$", "Exact maximum $q$", "Constraints"],
                    [[i, tex(str(t)), t[0] * t[2] - t[1] ** 2,
                      tex(voronoi[str(i)]["maximum"]), voronoi[str(i)]["constraint_count"]]
                     for i, t in enumerate(grams["all_22_triples"], 1)]))
    blocks["candidates"] = longtable(
        "Nine field candidates and their integer solutions.", "tab:candidates",
        "rL{3.0cm}rrL{5.2cm}",
        ["$m$", "Gram triple", "Norm", "$R(G)$", "$(h,k)$ solutions"],
        [[r["m"], tex(r["triple"]), tex(r["norm"]), tex(r["rho"]),
          tex(r["h_k_solutions"])] for r in grams["nine_field_candidates"]])
    blocks["representatives"] = longtable(
        "Six constructed representatives.", "tab:representatives",
        "rL{3.4cm}L{6cm}L{2.1cm}r",
        ["$m$", r"$\alpha$", "Basis", "Gram triple", "$R(G)$"],
        [[tex(c) for c in row] for row in representatives], size=r"\footnotesize")
    blocks["voight"] = longtable(
        "Checks of all 2,773 archived rows.", "tab:voight", "rrrrrr",
        ["Degree", "Rows", "Irreducible", "Totally real", "Index square", "Field disc."],
        [[r["degree"], r["rows"], r["irreducible_pass"], r["totally_real_pass"],
          r["polynomial_discriminant_square_index_pass"], r["field_discriminant_pass"]]
         for r in voight["tables"]])
    blocks["section_checks"] = longtable(
        "All 17 Section 4 assertions.", "tab:section-checks",
        "L{12cm}cc", ["Assertion", "Actual", "Expected"],
        [[ident(k), str(v), "True"] for k, v in tables["checks"].items()],
        size=r"\footnotesize")
    blocks["classification_checks"] = longtable(
        "All 115 classification assertions.", "tab:classification-checks",
        "rL{11cm}cc", ["ID", "Assertion", "Actual", "Expected"],
        [[i, ident(k), str(v), "True"] for i, (k, v) in
         enumerate(classification["checks"].items(), 1)], size=r"\footnotesize")
    return blocks


def refreshed_tex(content):
    blocks = generated_blocks()
    names = re.findall(r"^% BEGIN GENERATED: (\w+)$", content, re.M)
    assert sorted(names) == sorted(blocks), "Missing, duplicated or unknown generated blocks"
    for name, value in blocks.items():
        pattern = rf"(?ms)(^% BEGIN GENERATED: {name}\n).*?(^% END GENERATED: {name}$)"
        content, count = re.subn(pattern, lambda m: m[1] + value + "\n" + m[2], content)
        assert count == 1, name
    return content


def write_csv():
    _, tables, _, _, _ = validate()
    # CSVs contain all retained rows and both directions of every summary table.
    for case, stem in (("classic", "S1-classic"), ("integral", "S3-integral")):
        rows = [r for r in tables["rows"] if r["case"] == case]
        with (RESULTS / f"table-{stem}.csv").open("w", encoding="utf-8", newline="") as stream:
            fields = ("d", "n", "h", "volume_approx", "volume_upper", "volume_upper_exact")
            writer = csv.DictWriter(stream, fieldnames=fields, lineterminator="\n")
            writer.writeheader()
            for row in rows:
                writer.writerow({
                    "d": row["d"], "n": row["n"],
                    "h": str(decimal(row["h_new"])),
                    "volume_approx": str(decimal(row["volume_bound"])),
                    "volume_upper": str(rational_decimal(row["upper_six_rational"])),
                    "volume_upper_exact": row["upper_six_rational"],
                })
    for case, stem in (("classic", "S2-classic"), ("integral", "S4-integral")):
        with (RESULTS / f"table-{stem}.csv").open("w", encoding="utf-8", newline="") as stream:
            writer = csv.writer(stream, lineterminator="\n")
            writer.writerow(["direction", "parameter", "bound"])
            for key, direction in (("N_d", "degree_to_rank"), ("D_n", "rank_to_degree")):
                writer.writerows((direction, i, v) for i, v in
                                 enumerate(tables["summary"][case][key], 1))



def compile_pdf(build_dir):
    latexmk = shutil.which("latexmk")
    if not latexmk or not shutil.which("xelatex"):
        raise RuntimeError("Install XeLaTeX and latexmk, and make both available on PATH.")
    build_dir.mkdir(parents=True, exist_ok=True)
    subprocess.run([
        latexmk, "-norc", "-xelatex", "-interaction=nonstopmode", "-halt-on-error",
        "-file-line-error", "-no-shell-escape", "-outdir=" + str(build_dir), TEX.name,
    ], cwd=ROOT, check=True)
    log = (build_dir / TEX.with_suffix(".log").name).read_text(
        encoding="utf-8", errors="replace")
    for bad in (r"Overfull \\[hv]box", r"(?i)undefined references",
                r"(?i)undefined citations", r"(?i)Rerun to get",
                r"(?i)Font Warning:",
                r"Missing character:"):
        assert not re.search(bad, log), f"Unresolved TeX diagnostic: {bad}"
    built = build_dir / PDF.name
    if built.resolve() != PDF.resolve():
        shutil.copyfile(built, PDF)
    return subprocess.check_output(
        ["xelatex", "--version"], text=True, encoding="utf-8").splitlines()[0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tex-only", action="store_true",
                        help="Refresh TeX and CSV; PDF/manifest remain stale until a full build")
    parser.add_argument("--build-dir", type=Path, default=ROOT / "tmp/tex-build")
    args = parser.parse_args()
    for result_file in RESULTS.glob("*.json"):
        if result_file.name != "artifact_manifest.json":
            normalized = result_file.read_text(encoding="utf-8")
            result_file.write_text(normalized, encoding="utf-8", newline="\n")
    content = refreshed_tex(TEX.read_text(encoding="utf-8"))
    TEX.write_text(content, encoding="utf-8", newline="\n")
    write_csv()
    if args.tex_only:
        print("TeX and CSV refreshed; run without --tex-only to compile and update the manifest.")
        return
    compiler = compile_pdf(args.build_dir.resolve())
    reader = PdfReader(PDF)
    assert not list(reader.attachments)
    manifest = {
        "code_sha256": digest(CODE),
        "tex_sha256": digest(TEX),
        "input_sha256": digest(PUBLIC_INPUT),
        "pdf_sha256": digest(PDF),
        "pdf_pages": len(reader.pages),
        "source_lines": len(CODE.read_text(encoding="utf-8").splitlines()),
        "pdf_backend": "XeLaTeX",
        "compiler": compiler,
        "results": {p.name: digest(p) for p in sorted(RESULTS.iterdir())
                    if p.is_file() and p.name != "artifact_manifest.json"},
    }
    (RESULTS / "artifact_manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"PASS: TeX compiled ({len(reader.pages)} pages; source and result hashes recorded).")


if __name__ == "__main__":
    main()
