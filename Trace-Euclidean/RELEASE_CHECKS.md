# Release checks

The release was checked in a fresh working tree and reproduced from a separate
checkout. Both started without project build artifacts, used the pinned
dependencies and the official mathlib dependency cache, and completed the full
`lake build`. No Lean or mathlib upgrade was made for this release.

## Environment and results

- Lean 4.32.1, with the exact dependency revisions in `lean/lake-manifest.json`.
- Mathematica 15.0.0 on Windows.
- Public Python checks: **1,156 PASS, 0 FAIL**.
- Public Mathematica checks: **115 PASS, 0 FAIL**.
- Generated Voight certificates reproduce the committed source.
- Manuscript-exclusion and public-metadata checks: **PASS**.
- The full Lean build and all four documented axiom audits: **PASS in both checkouts**.

The audited proof sources and numerical inputs are those at commit
`72bfc64f98b11adbc0a625a95076e63c98219e79`; subsequent changes in this release only record
verification results and update documentation.

## Axiom audit

The counts below are reports, not a count of distinct theorems across files.
Every reported axiom is either `propext`, `Classical.choice`, `Quot.sound`, or
the explicitly disclosed native computation axiom. The product-coordinate
and Poitou audit files permit only the three standard logical axioms.

In the pinned Lean toolchain, `native_decide` records individual computation
axioms with names ending in `._native.native_decide.ax_...`. These are counted
as native computation dependencies. Each reported generated axiom was checked
to be a closed Boolean decision equality and traced to a `native_decide`
invocation in the unchanged proof sources. This provenance check identifies
the disclosed compiler dependency; it does not remove that trust assumption.

| Audit file | Reports | Reports using native computation |
| --- | ---: | ---: |
| `TraceProductCoordinatesAudit` | 12 | 0 |
| `PoitouDegreeElevenAudit` | 7 | 0 |
| `MainTheoremAudit` | 591 | 0 |
| `NumericalAxiomAudit` | 72 | 23 |

The audit does not discharge explicit theorem hypotheses. In particular,
Voight enumeration completeness remains a literature input, as documented
in `TRUST.md` and `THEOREM_INDEX.md`. This release does not claim that every
statement of the accompanying paper has been independently formalized.

## Reproduction

Use the commands and troubleshooting steps in `README.md`. The full local
build is broader than the GitHub-hosted checks, which build and audit the
product-coordinate and closed Poitou endpoints and run the public source,
certificate, and Python checks. A fixed release tag identifies the files
that should be used together.

## Computational supplement

The computational supplement provides `TraceEuclideanVerification.m`,
`TraceEuclideanVerification.tex`, and `TraceEuclideanVerification.pdf` under
`mathematica/`. They share the same basename. The 26-page PDF contains all
four numerical tables, the recorded check outcomes, and the complete
536-line Wolfram Language source.

The report is bound by SHA-256 to the code, public inputs, and 18 JSON/CSV
result files. Its archived Mathematica runs include 17 Section 4 assertions,
952 rational grid decisions, 87 rounded upper bounds, 115 classification
assertions, and checks of all 2,773 archived Voight rows. These finite checks
retain the mathematical-input and computational-trust scope in `TRUST.md`.

The report checker verifies the generated TeX blocks, all printed source
lines, the results, the file hashes, and PDF privacy. A separate directory
containing only the `.tex` and `.m` files reproduced the PDF text. The public
Python and publication checks were rerun for the supplement.

The complete Lean source tree, pinned dependencies, and public numerical
inputs are identical to those at the audited proof-source commit above.
The two full-build and four-audit results are therefore carried forward for
that unchanged proof tree; they are not described as newly executed full
builds for the report update. The report and its archived results have their
own checks described in `mathematica/README.md`.
