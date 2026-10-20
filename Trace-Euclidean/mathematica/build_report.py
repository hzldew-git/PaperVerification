"""Build the verification PDF from the checked .m file and its actual results.

Run after run.wls and run_voight.wls. Requires reportlab and pypdf.
No Wolfram computations or mathematical results are synthesized here.
"""
from __future__ import annotations

import csv
import hashlib
import json
import os
import re
import subprocess
import textwrap
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
from xml.sax.saxutils import escape

from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (
    SimpleDocTemplate, Paragraph, Spacer, PageBreak, Table, TableStyle,
    Preformatted, KeepTogether,
)
from pypdf import PdfReader

ROOT = Path(__file__).resolve().parent
RESULTS = ROOT / "results"
CODE = ROOT / "TraceEuclideanVerification.m"
PDF = ROOT / "TraceEuclideanVerification.pdf"
PUBLIC_INPUT = ROOT.parent / "inputs/verification_inputs.json"
BASE_COMMIT = "7f8ecd2c60b72437e6e958b60e40d2638237ee36"


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


# Match the repository's LF policy before computing portable byte digests.
# This changes line endings only, not the JSON values produced by Mathematica.
for result_file in RESULTS.glob("*.json"):
    if result_file.name != "artifact_manifest.json":
        normalized = result_file.read_text(encoding="utf-8")
        result_file.write_text(normalized, encoding="utf-8", newline="\n")

summary, tables, classification, cert, voight = validate()
grams = load("gram_candidates.json")
representatives = load("classification_table.json")
voronoi = load("voronoi_certificates.json")
source = CODE.read_text(encoding="utf-8")

# Embed TrueType fonts so mathematical Greek and minus signs survive
# PDF viewers without an installed Symbol font.
def register_font(name, windows_name, fontconfig_name):
    location = Path(os.environ.get("WINDIR", "")) / "Fonts" / windows_name
    if not location.is_file():
        try:
            location = Path(subprocess.check_output(
                ["fc-match", "-f", "%{file}", fontconfig_name], text=True).strip())
        except (OSError, subprocess.CalledProcessError) as exc:
            raise RuntimeError("Install TrueType fonts and fontconfig to build the PDF") from exc
    pdfmetrics.registerFont(TTFont(name, str(location)))


register_font("ReportSerif", "times.ttf", "Liberation Serif")
register_font("ReportSerifBold", "timesbd.ttf", "Liberation Serif:style=Bold")
register_font("ReportSerifItalic", "timesi.ttf", "Liberation Serif:style=Italic")
register_font("ReportSans", "arial.ttf", "Liberation Sans")
register_font("ReportMono", "cour.ttf", "Liberation Mono")
pdfmetrics.registerFontFamily("ReportSerif", normal="ReportSerif",
                              bold="ReportSerifBold", italic="ReportSerifItalic",
                              boldItalic="ReportSerifBold")

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

styles = getSampleStyleSheet()
styles.add(ParagraphStyle("Body", fontName="ReportSerif", fontSize=10.5,
                          leading=14.0, spaceAfter=7))
styles.add(ParagraphStyle("SmallBody", parent=styles["Body"], fontSize=9, leading=11.5))
styles.add(ParagraphStyle("Math", fontName="ReportSerif", fontSize=12,
                          leading=19, alignment=TA_CENTER, spaceBefore=5, spaceAfter=8))
styles.add(ParagraphStyle("Cell", fontName="ReportSans", fontSize=8,
                          leading=10, wordWrap="CJK"))
styles.add(ParagraphStyle("CellSmall", parent=styles["Cell"], fontSize=7.2, leading=9))
styles.add(ParagraphStyle("CodeBlock", fontName="ReportMono", fontSize=8,
                          leading=10.2, spaceAfter=1.5))
styles.add(ParagraphStyle("Hash", fontName="ReportMono", fontSize=7.4, leading=10))
styles["Title"].fontName = "ReportSerifBold"
styles["Title"].fontSize = 26
styles["Title"].leading = 29
styles["Heading1"].fontName = "ReportSerifBold"
styles["Heading1"].fontSize = 17
styles["Heading1"].spaceBefore = 14
styles["Heading2"].fontName = "ReportSerifBold"
styles["Heading2"].fontSize = 12
styles["Heading2"].spaceBefore = 8
NAVY = colors.HexColor("#17354a")
PALE = colors.HexColor("#eef3f6")
styles["Heading1"].textColor = NAVY
styles["Heading2"].textColor = NAVY
WIDTH = A4[0] - 92
story = []


def para(text: str, style="Body"):
    story.append(Paragraph(text, styles[style]))


def heading(text: str, level=1):
    story.append(Paragraph(text, styles[f"Heading{level}"]))


def code(text: str):
    # Display source faithfully; indent wrapped continuations distinctly.
    for line in text.splitlines():
        for chunk in textwrap.wrap(line, 95, replace_whitespace=False,
                                   drop_whitespace=False) or [""]:
            story.append(Preformatted(chunk, styles["CodeBlock"]))


def tab(headers, rows, widths, small=False):
    cell_style = styles["CellSmall" if small else "Cell"]
    converted = [[Paragraph(escape(str(c)), cell_style) for c in row]
                 for row in [headers, *rows]]
    t = Table(converted, colWidths=widths, repeatRows=1, hAlign="LEFT")
    t.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, 0), PALE),
        ("LINEBELOW", (0, 0), (-1, 0), 0.6, NAVY),
        ("ROWBACKGROUNDS", (0, 1), (-1, -1), [colors.white, colors.HexColor("#fafbfc")]),
        ("VALIGN", (0, 0), (-1, -1), "TOP"),
        ("TOPPADDING", (0, 0), (-1, -1), 4),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 4),
        ("LEFTPADDING", (0, 0), (-1, -1), 5),
        ("RIGHTPADDING", (0, 0), (-1, -1), 5),
    ]))
    story.append(t)
    story.append(Spacer(1, 8))


para("Trace-Euclidean", "Title")
para("Mathematica verification<br/>Code, numerical tables and exact finite checks", "Heading1")
para("A reproducible computational supplement", "Body")
story.append(Spacer(1, 12))
tab(["Component", "Actual result", "Meaning"], [
    ["Section 4 grid", "952 / 952 resolved", "Exact rational interval comparisons"],
    ["Displayed volume bounds", "87 / 87 checked", "Six significant digits, rounded upwards"],
    ["Retained pairs", "24 classic-integral; 63 integral", "Necessary numerical conditions"],
    ["Classification", "115 PASS; 0 FAIL", "Exact symbolic, integer and rational checks"],
    ["Archived Voight rows", "2,773 / 2,773 verified", "Integrity of the supplied finite lists"],
], [133, 139, WIDTH-272])
para("<b>Scope.</b> This report records computations performed by the accompanying "
     "<font face='ReportMono'>TraceEuclideanVerification.m</font>. It includes all four "
     "Section 4 numerical tables, the finite classification outputs, and the complete "
     "Wolfram Language source. These calculations use the public extracted inputs.")
para("The retained pairs do not assert the existence of trace-Euclidean lattices. "
     "Checking every supplied field polynomial does not prove that the list of fields "
     "is complete or free of isomorphic duplicates. General mathematical arguments and "
     "Lean dependency statements are documented separately in TRUST.md and THEOREM_INDEX.md.")
heading("Run identification", 2)
para("Core run (UTC): " + escape(summary["provenance"]["run_utc"]), "SmallBody")
para("Archived-row run (UTC): " + escape(voight["provenance"]["run_utc"]), "SmallBody")
para(escape(summary["provenance"]["tool"]), "SmallBody")
para("Code SHA-256:", "SmallBody")
para(digest(CODE), "Hash")
para("Public input SHA-256:", "SmallBody")
para(digest(PUBLIC_INPUT), "Hash")
para("The hashes refer to public computation files, not to a private manuscript.", "SmallBody")

story.append(PageBreak())
heading("1. Reproduction and interpretation")
para("Keep the .m file, the command-line wrapper, and the repository inputs together. "
     "From the Trace-Euclidean directory, run the following commands with a licensed "
     "Mathematica or Wolfram Engine installation:")
code("wolframscript -file mathematica/run.wls\n"
     "wolframscript -file mathematica/run_voight.wls")
para("The first command writes the table, interval and classification results. The "
     "second command independently checks every archived field row and can take longer. "
     "Both commands return a nonzero exit code on a failed check. A missing result file "
     "is a failed or incomplete run, not a successful verification.")
para("In an interactive Mathematica session, load the package and call its public functions:")
code('Get["mathematica/TraceEuclideanVerification.m"];\n'
     'TraceEuclideanVerification`RunVerification[]\n'
     'TraceEuclideanVerification`RunVoightIntegrity[]')
para("An explicit output directory can be passed to either function. Loading the .m file "
     "does not start a computation, clear the user's symbols, change the current working "
     "directory or terminate the kernel.")
para("To rebuild this PDF after both runs:")
code("python -m pip install -r mathematica/requirements-report.txt\n"
     "python mathematica/build_report.py")
para("The report builder rejects stale code hashes, stale input hashes, missing row "
     "results and unsuccessful runs. It formats existing results; it does not invent "
     "or recompute Mathematica verification outcomes.")
heading("Verification levels", 2)
tab(["Level", "Used for", "Limit"], [
    ["90-digit evaluation", "Logarithms, Gamma values and displayed h values",
     "High precision alone is not an interval proof."],
    ["Exact rational intervals", "Grid signs, cutoff constants and volume rounding",
     "The arithmetic interpretation of beta(d) remains a mathematical input."],
    ["Exact finite algebra", "Gram matrices, roots, discriminants and Voronoi vertices",
     "Trusts Mathematica's implementation; not a Lean kernel proof."],
    ["General theory", "Covering inequalities and field-list completeness",
     "See the separate theorem index and trust statement."],
], [109, 186, WIDTH-295])
heading("Common problems", 2)
para("If wolframscript is unavailable, check the Wolfram installation and license. "
     "If an input is missing, restore the complete repository layout. If a hash check "
     "fails, use the code and inputs from the same repository revision. If the PDF "
     "builder reports stale results, rerun both commands above before rebuilding it. "
     "Treat warnings, unevaluated expressions and failed exports as issues to investigate.")

story.append(PageBreak())
heading("2. Section 4: formulas and exact decisions")
para("Let n be the lattice rank and d the degree of the totally real field. The input "
     "root-discriminant lower bound is denoted by β(d). Define")
para("V(n,d) = (πd)<super>nd</super> / "
     "[Γ(nd/2 + 1)<super>2</super> β(d)<super>nd</super>].", "Math")
para("The code evaluates log V to avoid numerical underflow. A pair is retained when "
     "V(n,d)c<super>nd</super> ≥ 1. Here c = 1 for the classic-integral case and "
     "also for rank one; c = 2 for the integral case of rank at least two.")
para("h<sub>classic</sub>(n,d) = log V(n,d)/n,<br/>"
     "h<sub>integral</sub>(n,d) = log V(n,d)/n + d log 2.", "Math")
para("The displayed integral h value uses the second formula even at n = 1; the "
     "rank-one retention decision still uses c = 1. This distinction is implemented "
     "explicitly and explains the different first-rank and higher-rank degree bounds.")
tab(["Degree", "Arithmetic input β(d)"], [
    ["1–9", "D_min(d)^(1/d), with D_min listed below"],
    ["10", "14"],
    ["11", "14083/1000"],
    ["12 and above", "(36347/1000) exp(-10667/(1000 d))"],
], [96, WIDTH-96])
tab(["d", "D_min(d)"], [[i, v] for i, v in enumerate(
    tables["minimal_discriminants"], 1)], [96, WIDTH-96])
para("These discriminant inputs agree with the released verification data. The "
     "degree-eleven constant has a separate Lean proof in the repository. The Voight "
     "list-completeness input and other theorem dependencies are not discharged by "
     "this numerical program. Consult TRUST.md for the exact current scope.")
heading("Why the grid comparison is exact", 2)
para("An 80-term alternating series bounds arctan(1/5) and arctan(1/239). Machin's "
     "identity π = 16 arctan(1/5) − 4 arctan(1/239) gives rational lower and upper "
     "bounds for π. The positive exponential series through term 180 is followed by "
     "a geometric upper bound for its tail. Endpoints are rounded outwards to a "
     "denominator of 10<super>85</super>.")
para("For nd even, Γ(nd/2+1) is a factorial. For nd odd, the half-integer Gamma formula "
     "expresses its square as a rational multiple of π. Consequently each V(n,d) "
     "is enclosed by rational arithmetic. The entire interval lies on one side of "
     "the threshold in every one of the 952 decisions.")
para("The exact endpoint comparisons also verify 4πe &lt; 35 and "
     "36.347 exp(−10.667/15) &gt; 2πe. With the analytical covering inequalities, these "
     "are the cutoff constants used to restrict the search to 1 ≤ n ≤ 34 and "
     "1 ≤ d ≤ 14. The code's finite Gamma checks are additional numerical checks "
     "and do not prove a Gamma inequality for all real arguments.")
minimum = min(abs(decimal(r["log_feasibility_margin"])) for r in tables["grid"])
para("Smallest absolute log feasibility margin on the grid: "
     + escape(format(minimum, ".20g")) + ".", "SmallBody")

for case, name, detail_num, summary_num in (
    ("classic", "Classic-integral", 1, 2), ("integral", "Integral", 3, 4)
):
    story.append(PageBreak())
    heading(f"Table S{detail_num}. {name} retained pairs")
    selected = [r for r in tables["rows"] if r["case"] == case]
    para(f"All {len(selected)} retained pairs are included. The h column is rounded "
         "to six decimal places. The V upper bound is rounded upwards to six "
         "significant digits and checked against the rational upper endpoint. "
         "Full precision values and exact rational display values are in the CSV.")
    tab(["d", "n", "h(n,d)", "Upper bound for V(n,d)"],
        [[r["d"], r["n"], format(decimal(r["h_new"]), ".6f"),
          six(r["upper_six_rational"])] for r in selected],
        [45, 45, 155, WIDTH-245])
    story.append(PageBreak())
    heading(f"Table S{summary_num}. {name} maximum rank and degree")
    para("N(d) is the maximum retained rank at degree d; D(n) is the maximum "
         "retained degree at rank n. A zero denotes an empty set of retained pairs "
         "at that parameter. Every entry of both summary arrays is shown.")
    nd = tables["summary"][case]["N_d"]
    dn = tables["summary"][case]["D_n"]
    tab(["d", "N(d)", "n", "D(n)", "n", "D(n)"],
        [[i if i <= 14 else "", nd[i-1] if i <= 14 else "",
          i, dn[i-1], i+17, dn[i+16]] for i in range(1, 18)],
        [WIDTH/6] * 6)

story.append(PageBreak())
heading("3. Finite rank-one classification")
para("The quadratic form is q(x) = x<super>t</super>Gx, with "
     "G = ((a,b),(b,c)). The value below is the squared covering radius in this "
     "normalization; it is named rho in the source:")
para("R(G) = ac(a + c − 2b) / [4(ac − b<super>2</super>)].", "Math")
para("The enumeration uses 2 ≤ c ≤ a ≤ 7 and 0 ≤ b ≤ c/2, together with R(G) &lt; 2. "
     "An independent exact Voronoi calculation intersects rational supporting "
     "half-planes and evaluates q at every retained vertex. Its search bound is "
     "computed from the parallelogram enclosed by the ±e<sub>i</sub> constraints. "
     "This verifies each enumerated instance without invoking the radius formula "
     "as the algorithm for that independent calculation.")
para("The maximum determinant in the following list is "
     f"<b>{grams['maximum_determinant']}</b>. The public input uses a canonical "
     "ordering of diagonal coefficients; the computational ordering is displayed here.")
tab(["ID", "(a,b,c)", "det G", "Exact maximum q", "Constraint count"],
    [[i, str(t), t[0]*t[2]-t[1]**2, voronoi[str(i)]["maximum"],
      voronoi[str(i)]["constraint_count"]]
     for i, t in enumerate(grams["all_22_triples"], 1)],
    [30, 126, 64, 125, WIDTH-345])
story.append(PageBreak())
heading("Nine field candidates and six survivors", 2)
para("Here m is the squarefree radicand; k is the integer index parameter. "
     "Empty solution sets exclude three rows. The h,k pairs solve the finite "
     "trace/norm/index equations, including their parity constraint.")
tab(["m", "Gram triple", "Norm", "R(G)", "(h,k) solutions"],
    [[r["m"], r["triple"], r["norm"], r["rho"], r["h_k_solutions"]]
     for r in grams["nine_field_candidates"]],
    [30, 110, 45, 65, WIDTH-250])
heading("Constructed representatives", 2)
para("The columns give the field radicand, coefficient α, integral basis, "
     "trace Gram triple and exact squared covering radius. Square roots are "
     "written in Wolfram Language syntax.")
tab(["m", "α", "Basis", "Gram triple", "R(G)"], representatives,
    [25, 110, 180, 85, WIDTH-400], small=True)
para("Each representative passes six checks: an integral unimodular basis, "
     "a totally positive integral coefficient, its trace Gram matrix, its determinant "
     "identity, the exact radius and the strict radius threshold. The report also "
     "records the remaining algebraic and elimination checks in Appendix A.")
para("The general rational-farthest-point input cited from Clark–Jagy and the "
     "general ideal-theoretic classification arguments are not inferred from this "
     "finite test suite. Their formalization scope is described in the repository.")

story.append(PageBreak())
heading("4. Archived Voight row integrity")
para("This optional run reads the six archived public data files, checks their "
     "SHA-256 digests and row counts, and then uses exact Mathematica calculations "
     "for every supplied polynomial. It tests shape and monicity, irreducibility, "
     "total reality, the positive square index equation, and the actual field "
     "discriminant. The number-field discriminant is recomputed independently.")
tab(["Degree", "Rows", "Irred.", "Totally real", "Index square", "Field disc."],
    [[r["degree"], r["rows"], r["irreducible_pass"], r["totally_real_pass"],
      r["polynomial_discriminant_square_index_pass"], r["field_discriminant_pass"]]
     for r in voight["tables"]], [48, 55, 70, 90, 100, WIDTH-363])
para("Each entry in the four final columns is the number of passing rows. "
     "All 2,773 rows pass all listed properties. Individual row outcomes are saved "
     "in results/voight-rows-DEGREE.json in the original input order; their "
     "defining polynomials remain in inputs/voight/.")
para("<b>Boundary.</b> These counts are counts of supplied rows. They are not a "
     "proof of field-list completeness and are not asserted to count pairwise "
     "non-isomorphic fields. In particular, the degree-ten table contains known "
     "fields. The separate completeness input used by the theorem must be "
     "read with its own precise hypotheses.")
heading("Sources and cross-checks", 2)
para("The archived files accompany John Voight, <i>Enumeration of totally real "
     "number fields of bounded root discriminant</i>. Original bounds, archive "
     "timestamps and file digests are listed in inputs/voight/README.md. "
     "The report uses those existing public copies rather than fetching a new "
     "dataset during verification.")
para("The original independent scripts remain available as checks/classification.wls "
     "and checks/voight_polynomial_integrity.wls. The consolidated package preserves "
     "the 115 classification assertions and adds the Section 4 table and interval "
     "calculations. The public Python checks provide a separate implementation.")
para("This computational supplement builds on repository revision "
     + BASE_COMMIT + ". It does not change Lean theorem sources, toolchain pins or "
     "the numerical inputs used by the released Lean project. Mathematica exact "
     "arithmetic and the disclosed Lean native_decide compiler dependency are "
     "different trust assumptions.")

story.append(PageBreak())
heading("Appendix A. Complete check outcomes")
heading("Section 4 assertions", 2)
tab(["Assertion", "Actual", "Expected"],
    [[k, str(v), "True"] for k, v in tables["checks"].items()],
    [WIDTH-94, 47, 47], small=True)
heading("Classification: all 115 assertions", 2)
tab(["ID", "Assertion", "Actual", "Expected"],
    [[i, k, str(v), "True"] for i, (k, v) in
     enumerate(classification["checks"].items(), 1)],
    [27, WIDTH-121, 47, 47], small=True)

story.append(PageBreak())
heading("Appendix B. Complete executable .m source")
para("The listing below is read directly from the file whose SHA-256 digest "
     "appears on the cover. Line numbers are editorial aids. Long lines are "
     "continued with an indented continuation marker; no source lines are omitted.")
for number, line in enumerate(source.splitlines(), 1):
    chunks = textwrap.wrap(line, width=94, expand_tabs=False,
                           replace_whitespace=False, drop_whitespace=False,
                           break_long_words=True, break_on_hyphens=False) or [""]
    for index, chunk in enumerate(chunks):
        prefix = f"{number:4}  " if index == 0 else "   >  "
        story.append(Preformatted(prefix + chunk, styles["CodeBlock"]))


def page_footer(canvas, doc):
    canvas.saveState()
    w, h = A4
    canvas.setStrokeColor(colors.HexColor("#c7d3db"))
    canvas.line(46, 39, w-46, 39)
    canvas.setFont("ReportSans", 8)
    canvas.setFillColor(NAVY)
    canvas.drawString(46, 26, "Trace-Euclidean | Mathematica verification")
    canvas.drawRightString(w-46, 26, str(doc.page))
    canvas.restoreState()


doc = SimpleDocTemplate(
    str(PDF), pagesize=A4, rightMargin=46, leftMargin=46,
    topMargin=43, bottomMargin=52,
    title="Trace-Euclidean: Mathematica Verification",
    author="Trace-Euclidean verification project",
    subject="Reproducible computations, code and actual results",
    creator="Trace-Euclidean report builder",
)
doc.build(story, onFirstPage=page_footer, onLaterPages=page_footer)
reader = PdfReader(PDF)
assert len(reader.pages) > 5
assert not list(reader.attachments)
text = "\n".join(page.extract_text() for page in reader.pages)
for phrase in ("952 / 952", "115 PASS", "2,773 / 2,773",
               "Table S1.", "Table S2.", "Table S3.", "Table S4.", "EndPackage[];"):
    assert phrase in text, phrase
assert digest(CODE) in text and digest(PUBLIC_INPUT) in text
manifest = {
    "code_sha256": digest(CODE),
    "input_sha256": digest(PUBLIC_INPUT),
    "pdf_sha256": digest(PDF),
    "pdf_pages": len(reader.pages),
    "source_lines": len(source.splitlines()),
    "results": {p.name: digest(p) for p in sorted(RESULTS.iterdir())
                if p.is_file() and p.name != "artifact_manifest.json"},
}
(RESULTS / "artifact_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n",
                                               encoding="utf-8", newline="\n")
print(f"PASS: report generated ({len(reader.pages)} pages; full source and results).")
