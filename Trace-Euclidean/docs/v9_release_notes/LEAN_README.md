# Lean formalization

This Lake project checks selected proof obligations from the manuscript whose
SHA-256 digest is recorded in `../results/summary.json`.

## Modules

| Module | Checked content |
|---|---|
| `Basic` | Strict and closed Euclidean predicates, squared-radius implications, obstruction witnesses, and the power-mean quantifier transfer |
| `Scaling` | Cancellation showing that nonzero scaling preserves and reflects form isometry |
| `AnalyticCriticalPoint` | The corrected stationary derivative and Hessian-saddle argument in Lemma 4.3 |
| `Finiteness` | Finite positive parameter sets, finite rectangles, and finite dependent families |
| `VoronoiAlgebra` | Exact two-dimensional Gram, vertex coefficient, and vertex norm identities |
| `QuadraticArithmetic` | Candidate bounds, the `m=3` midpoint obstruction, and the three final radius values |
| `QuadraticGeometry` | Full-plane covering upper bounds and exact deep-hole sharpness |
| `QuadraticIntegralBasis` | Both real-quadratic integer bases and the concrete field classification |
| `PseudoBasis` | Pseudobases for arbitrary full projective integer-ring lattices |
| `PseudoBasisDeterminant` | General trace determinant, covolume, and classic/integral discriminant lower bounds |
| `DirectFixedFieldFiniteness` | Finite Gram/module codes and fixed-field, fixed-rank class finiteness |
| `GlobalFiniteness` | Eight unconditional finiteness endpoints on the actual quotient |

`TraceEuclideanTest/MainTheoremAudit.lean` checks 50 public endpoint signatures
and prints their transitive axiom sets. The expected set for every listed
endpoint is `propext`, `Classical.choice`, and `Quot.sound`.

## Build

```text
lake exe cache get
lake build
lake env lean TraceEuclideanTest/MainTheoremAudit.lean
```

Lean compilation establishes that the encoded statements have kernel-accepted
proof terms. The English audit under `../docs/audit/` separately records
semantic correspondence, supporting-result coverage, and the confirmation
items that keep the project at Grade B rather than Grade A.
