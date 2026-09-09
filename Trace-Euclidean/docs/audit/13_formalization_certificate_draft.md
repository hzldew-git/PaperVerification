# Formalization certificate draft

This document is a draft review certificate. It is not signed and does not
certify complete formalization of the paper.

## Identified artifacts

- Manuscript identifier: `Trace-Euclidean-v9`.
- Manuscript SHA-256:
  `a2f522d077c600e0dc747dcaa8b06ba4e31ecd0b49b83dae468c9b61915a0e99`.
- Lean toolchain: `v4.32.1`.
- mathlib revision:
  `520045ab14e26149ee970e2e617ca04b09bde5d6`.
- Formalization status: `PARTIAL_FORMALIZATION`.
- Semantic-audit grade: C.

## Machine-checked claim

The declarations listed in
`lean/TraceEuclideanTest/MainTheoremAudit.lean` have Lean-kernel-accepted proof
terms under the pinned dependency graph. Their reported transitive axiom set is
exactly `propext`, `Classical.choice`, and `Quot.sound`. The formal source
scan found no forbidden proof placeholder or code-generation bypass.

## Computational claim

The frozen v9 computational package reports
`2165 PASS / 0 WARN / 0 FAIL`, including exact symbolic identities, rational
certificates, finite enumerations, and the displayed numerical claims described
in the verification ledger.

## Exclusions

This draft does not certify the full statements of Theorem 1.2, Theorem 1.3,
Proposition 6.1, or Theorem 1.8 in Lean. It does not certify cited external
theorems, manuscript prose outside the ledger, or semantic fidelity without
independent review.

## Signatures

- Mathematical author: ____________________  Date: __________
- Independent domain reviewer: ____________  Date: __________
- Independent Lean reviewer: ______________  Date: __________
- Reproducibility reviewer: ________________  Date: __________
