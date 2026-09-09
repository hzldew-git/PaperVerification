# Coverage report

## Executable coverage

| Layer | Coverage |
|---|---|
| Mathematica | 2,165 passing records; no warnings or failures |
| Section 4 ledger | 22 calculation groups, covering all identified Mathematica-checkable calculations |
| Numeric claims | 15 displayed approximations |
| Tables | 42 rows and 12 maximum rows |
| Quadratic diagnostics | 121 square-free parameters in the configured range |
| Lean build | Six proof modules and two test entry points; 8,665 Lake jobs |
| Lean endpoint audit | 13 signatures and transitive axiom reports |

## Paper-result coverage

| Area | End-to-end Lean result | Component Lean result | Computational result |
|---|---|---|---|
| Definitions and radius bridge | No | Yes | Source binding |
| Global finiteness theorems | No | Parameter and scaling assembly | Bounds and finite tables |
| p-norm corollary | No | Witness transfer | Source binding |
| Trace Gram/covolume bounds | No | Two-dimensional Gram cases | Selected exact identities |
| Analytic Section 4 | No | Lemma 4.3 saddle component | Complete identified calculation ledger |
| Quadratic covering radii | No | Coordinate and vertex algebra | Exact configured geometry checks |
| Quadratic classification | No | Candidate arithmetic and obstruction | Finite diagnostics |

No theorem among Theorem 1.2, Theorem 1.3, Proposition 6.1, and Theorem 1.8 has
an end-to-end Lean endpoint. Coverage status is
`PARTIAL_FORMALIZATION_WITH_COMPLETE_IDENTIFIED_SECTION4_COMPUTATION`.
