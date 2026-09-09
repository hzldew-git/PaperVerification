# Paper verification materials

This repository contains reproducible verification companions to research
papers: computational source, selected Lean 4 formalizations, extracted inputs,
machine-readable results, and verification documentation.

## Available package

- [Trace-Euclidean](Trace-Euclidean/README.md): Mathematica and Lean 4 checks,
  complete Section 4 calculation coverage, result certificates, and the
  [English verification manual](Trace-Euclidean/output/pdf/verification_manual_v9.pdf).

## Manuscript exclusion policy

Paper manuscripts are not published in this repository. In particular, the
repository must never contain a manuscript TeX source, a rendered manuscript
PDF, a source snapshot, or an archive that could conceal one.

The only tracked `.tex` and `.pdf` files are verification documentation listed
in [`.verification-document-allowlist`](.verification-document-allowlist).
[`tools/check_no_manuscripts.py`](tools/check_no_manuscripts.py) enforces this
policy locally, and the same check runs on every push and pull request.

To download a package, use GitHub's automatically generated repository archive.
No hand-built ZIP archive is stored here.
