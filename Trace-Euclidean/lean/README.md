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

`TraceEuclideanTest/MainTheoremAudit.lean` checks the public endpoint
signatures and prints their transitive axiom sets. The expected set for every
listed endpoint is `propext`, `Classical.choice`, and `Quot.sound`.

## Build

```text
lake exe cache get
lake build
lake env lean TraceEuclideanTest/MainTheoremAudit.lean
```

Lean compilation establishes that the encoded statements have kernel-accepted
proof terms. It does not establish that every manuscript statement was encoded,
or that these abstractions are semantically identical to all number-field and
lattice definitions in the manuscript.
