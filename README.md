# Paper verification materials

This repository contains reproducible verification companions to research
papers: computational source, selected Lean 4 formalizations, extracted inputs,
machine-readable results, and verification documentation.

## Active package

- [Trace-Euclidean v15](Trace-Euclidean/README.md): Grade B scoped Lean 4
  formalization, Python and Wolfram checks, extracted inputs, and an
  [English semantic audit](Trace-Euclidean/docs/audit/v15/12_executive_summary.md).
  The prior [v9 release](Trace-Euclidean/docs/v9_release_notes/README.md),
  including its [verification manual](Trace-Euclidean/output/pdf/verification_manual_v9.pdf),
  remains available as historical evidence.

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
