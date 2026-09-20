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
- Formalization status: `SUBSTANTIAL_FORMALIZATION`.
- Semantic-audit grade: B.

## Machine-checked claim

The declarations listed in
`lean/TraceEuclideanTest/MainTheoremAudit.lean` have Lean-kernel-accepted proof
terms under the pinned dependency graph. Their reported transitive axiom set is
exactly `propext`, `Classical.choice`, and `Quot.sound`. The formal source
scan found no forbidden proof placeholder or code-generation bypass. The
audited list contains 50 endpoints, including the general pseudobasis
determinant chain, fixed-field finite-code theorems, and all eight
unconditional global finiteness conclusions.

## Computational claim

The frozen v9 computational package reports
`2165 PASS / 0 WARN / 0 FAIL`, including exact symbolic identities, rational
certificates, finite enumerations, and the displayed numerical claims described
in the verification ledger.

## Exclusions

Theorems 1.2, 1.3, and 1.8 and Proposition 6.1 have complete concrete
endpoints and are `PROVISIONAL_MATCH` until independent review is recorded.
The eight finiteness conclusions are unconditional Lean theorems on the actual
quotient; `MainFinitenessFramework` does not occur in their hypotheses. This
draft does not certify cited-source correctness, manuscript prose outside the
inventory, the unformalized supporting results, or semantic fidelity without
the signatures below.

## Signatures

- Mathematical author: ____________________  Date: __________
- Independent domain reviewer: ____________  Date: __________
- Independent Lean reviewer: ______________  Date: __________
- Reproducibility reviewer: ________________  Date: __________
