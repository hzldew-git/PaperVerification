# Verification index

Source version: `Trace-Euclidean-v9`, SHA-256
`a2f522d077c600e0dc747dcaa8b06ba4e31ecd0b49b83dae468c9b61915a0e99`.
The manuscript itself is intentionally absent from this repository.

The status labels mean:

- `FORMALIZED_COMPONENT`: Lean proves the stated component with its explicit
  hypotheses.
- `COMPUTATION_VERIFIED`: Mathematica checks the displayed algebra, finite
  enumeration, certified interval, or numerical value recorded in the ledger.
- `PARTIAL_FORMALIZATION`: some proof obligations are checked, but no Lean
  theorem has the full paper signature and conclusion.
- `NOT_FORMALIZED`: no corresponding Lean theorem is claimed.
- `EXTERNAL_INPUT`: the paper invokes a cited theorem that this package does
  not reprove.

| Paper item | Mathematica evidence | Lean evidence | Status |
|---|---|---|---|
| Definition 1.1, strict trace Euclideanity | Source binding | `StrictEuclidean`; radius bridge | `PARTIAL_FORMALIZATION` |
| Theorems 1.2 and 1.3, four finiteness assertions each | Complete admissible-pair tables and analytic tails | Finite parameter and scaling assembly lemmas | `PARTIAL_FORMALIZATION` |
| Definition 1.5 and Corollary 1.6, p-norm implication | Source binding | `pNormEuclidean_imp_traceEuclidean` | `FORMALIZED_COMPONENT` |
| Definition 1.7, trace Euclidean field | Source binding | None | `NOT_FORMALIZED` |
| Theorem 1.8, classification by `m = 2, 5, 13` | Exact quadratic-field calculations and finite diagnostics | Candidate elimination, `m=3` obstruction, exact candidate radii | `PARTIAL_FORMALIZATION` |
| Lemma 2.1, properties of `Phi` | None | None | `NOT_FORMALIZED` |
| Lemma 2.2, covering radius criterion | Source binding | Abstract strict/closed radius implications | `PARTIAL_FORMALIZATION` |
| Lemma 3.1, trace Gram determinant | Exact symbolic matrix checks | Two-dimensional special cases only | `COMPUTATION_VERIFIED` |
| Lemma 3.2, covolume formula | Source-bound downstream checks | None | `NOT_FORMALIZED` |
| Lemma 3.3, covering-volume inequality | None | None | `EXTERNAL_INPUT` |
| Lemma 3.4, discriminant and volume-ideal bound | Exact formula diagnostics | None | `PARTIAL_FORMALIZATION` |
| Lemmas 4.1 and 4.2 | Exact identities, signs, limits, and certified roots | Stationary derivative sublemma reused in 4.3 | `COMPUTATION_VERIFIED` |
| Lemma 4.3, global maximum of `g` | Exact calculus, rational intervals, boundary comparison, tail check | Corrected critical-point Hessian-saddle component | `PARTIAL_FORMALIZATION` |
| Lemmas 4.4-4.9 | Exact identities, monotonicity conditions, roots, and maxima | None | `COMPUTATION_VERIFIED` |
| Lemma 5.1, bounded-discriminant/volume finiteness | None | Scaling isometry equivalence and finite-family assembly only | `PARTIAL_FORMALIZATION` |
| Proposition 6.1, exact quadratic covering radii | Exact Gram/Voronoi calculations | Gram identities, vertex solution, vertex norm formula, radius algebra | `PARTIAL_FORMALIZATION` |

The machine-readable Mathematica map is `results/verification_ledger.json`.
The Lean endpoint report is `lean/audit/main_theorem_axioms.txt`. No row marked
`PARTIAL_FORMALIZATION` should be cited as an end-to-end Lean proof of the paper
item.
