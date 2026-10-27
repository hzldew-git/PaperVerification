# Norm-Euclidean core formalization

This package contains selected Lean proofs about integral norm-Euclidean
quadratic lattices over number fields. It includes ordinary class number one,
the stable field-class-number equality, hyperbolic cancellation, the two stable
genus classes when the field class number is two, and fixed-field unary
finiteness including nonfree lattices.

The [theorem index](THEOREM_INDEX.md) specifies the exact release scope and
formal declarations. The [trust statement](TRUST.md) separates kernel checking,
mathematical hypotheses, source correspondence and the remaining paper-wide
work. This is a selected-results release, with provisional source correspondence;
it is not a certificate of complete formalization of the paper.

## Reproduce

Install Python 3.11 or later and Elan, then run from the repository root:

```text
python Norm-Euclidean/tools/verify_public.py
python tools/check_no_manuscripts.py --root .
```

Lean 4.32.1 and all dependency revisions are fixed by `lean/lean-toolchain` and
`lean/lake-manifest.json`. Detailed setup and audit commands are in
[REPRODUCING.md](REPRODUCING.md). No dependency upgrade is needed.

## Contents

- `lean/`: selected entrypoints and their full local import closure.
- `lean/validation/Core.lean`: actual statement and transitive axiom probes.
- `declarations.json`: the public declaration registry.
- `proof_manifest.json`: hashes and module names of the exported proof sources.
- [Verification report](results/verification.json) and
  [statement and axiom output](results/statement_types.txt): completed local
  checks for this candidate.
- `tools/`: portable static checks, build and axiom-audit driver.
- [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md): source provenance and licensing.

The initial selected import closure contains 1,413 local modules. Module count
does not measure theorem coverage. The original proof tokens are preserved;
line endings and historical manuscript labels in comments were normalized for
publication. The release aggregator and audit files are separate additions.

Manuscript sources, PDFs, private source bindings, build caches and opaque
archives are excluded. Use a fixed repository commit or release tag when
citing the verification package.
