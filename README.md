# Paper verification materials

This repository contains reproducible verification companions to research
papers: computational source, selected Lean 4 formalizations, extracted inputs,
machine-readable results, and reader-facing verification instructions.

## Active packages

- [Trace-Euclidean](Trace-Euclidean/README.md): selected Lean theorems, Python
  and Mathematica checks, and extracted numerical inputs. See the
  [theorem index](Trace-Euclidean/THEOREM_INDEX.md) and
  [trust statement](Trace-Euclidean/TRUST.md) for the exact scope.
- [Norm-Euclidean](Norm-Euclidean/README.md): selected core Lean results on
  class numbers, hyperbolic cancellation and fixed-field unary finiteness,
  including nonfree lattices. See the
  [theorem index](Norm-Euclidean/THEOREM_INDEX.md) and
  [trust statement](Norm-Euclidean/TRUST.md) for the precise scope and exclusions.

## Manuscript exclusion policy

Paper manuscripts are not published in this repository. The repository must
not contain a manuscript TeX source, rendered manuscript PDF, source snapshot,
or opaque archive. The repository-level
[`tools/check_no_manuscripts.py`](tools/check_no_manuscripts.py) and the package's
[`tools/check_public_metadata.py`](Trace-Euclidean/tools/check_public_metadata.py)
run on every push and pull request.

Use GitHub's automatically generated repository archive to download the code;
no hand-built archive is stored here.
