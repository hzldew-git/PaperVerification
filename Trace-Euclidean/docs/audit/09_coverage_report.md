# Coverage report

## Executable coverage

| Layer | Coverage |
|---|---|
| Mathematica | 2,165 passing records; no warnings or failures |
| Section 4 ledger | 22 calculation groups, covering all identified Mathematica-checkable calculations |
| Numeric claims | 15 displayed approximations |
| Tables | 42 rows and 12 maximum rows |
| Quadratic diagnostics | 121 square-free parameters in the configured range |
| Lean build | 37 proof modules and two public/test entry points; 8,696 Lake jobs |
| Lean endpoint audit | 50 signatures and transitive axiom reports |

## Paper-result coverage

| Area | End-to-end Lean result | Component Lean result | Computational result |
|---|---|---|---|
| Definitions and radius bridge | Field/lattice definition yes; general geometric `Phi` no | Yes | Source binding |
| Global finiteness theorems | Yes, all eight unconditional clauses on the actual quotient | Pseudobases, trace determinant/covolume bounds, analytic tails, Hermite, and finite reduction codes | Bounds and finite tables |
| p-norm corollary | No | Witness transfer | Source binding |
| Trace Gram/covolume bounds | General projective squared-covolume identity and both discriminant inequalities | Scale/norm ideal consequences remain partial | Selected exact identities |
| Analytic Section 4 | No | Lemma 4.3 saddle component | Complete identified calculation ledger |
| Quadratic covering radii | Yes, full-plane specification | Coordinate and vertex algebra | Exact configured geometry checks |
| Quadratic classification | Yes, concrete iff endpoint | Integral bases, trace bridge, candidate arithmetic and obstruction | Finite diagnostics |

Core theorem coverage:

- fully formalized pending semantic sign-off: Theorems 1.2, 1.3, and 1.8,
  3/3 core theorem groups;
- proposition-level full-plane endpoint: Proposition 6.1, 1/1;
- `VERIFIED_MATCH`: 0, because independent reviews are unsigned;
- `PROVISIONAL_MATCH`: 4 result groups (Theorems 1.2, 1.3, 1.8, and
  Proposition 6.1);
- `FORMALIZATION_WEAKER`: 0 core theorem groups.

The resulting project status is `SUBSTANTIAL_FORMALIZATION`, Grade B.
