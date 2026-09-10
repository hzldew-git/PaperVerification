# Verification index

Source version: `Trace-Euclidean-v9`, SHA-256
`a2f522d077c600e0dc747dcaa8b06ba4e31ecd0b49b83dae468c9b61915a0e99`.
The manuscript itself is intentionally absent from this repository.

The status labels mean:

- `PROVISIONAL_MATCH`: the full formal statement appears to match, subject to
  independent author/domain and Lean review.
- `FORMALIZED_COMPONENT`: Lean proves the stated component with its explicit
  hypotheses.
- `FORMALIZATION_WEAKER`: the Lean theorem has additional mathematical
  premises or a narrower object domain.
- `COMPUTATION_VERIFIED`: Mathematica checks the displayed algebra, finite
  enumeration, certified interval, or numerical value recorded in the ledger.
- `PARTIAL_FORMALIZATION`: some proof obligations are checked, but no Lean
  theorem has the full paper signature and conclusion.
- `NOT_FORMALIZED`: no corresponding Lean theorem is claimed.
- `EXTERNAL_INPUT`: the paper invokes a cited theorem that this package does
  not reprove.

| Paper item | Mathematica evidence | Lean evidence | Status |
|---|---|---|---|
| Definition 1.1, strict trace Euclideanity | Source binding | `IsTraceEuclidean`, `traceCost`, `NumberFieldLattice` | `PROVISIONAL_MATCH` |
| Theorems 1.2 and 1.3, four finiteness assertions each | Complete admissible-pair tables | Eight unconditional endpoints on `GlobalLatticeClass`, projective pseudobasis determinant bounds, Hermite field finiteness, direct fixed-field reduction codes, and analytic tails/envelopes | `PROVISIONAL_MATCH` |
| Definition 1.5 and Corollary 1.6, p-norm implication | Source binding | `pNormEuclidean_imp_traceEuclidean` | `FORMALIZED_COMPONENT` |
| Definition 1.7, trace Euclidean field | Source binding | `IsFieldTraceEuclidean` | `PROVISIONAL_MATCH` |
| Theorem 1.8, classification by `m = 2, 5, 13` | Exact quadratic-field calculations and finite diagnostics | `realQuadratic_two_trace_euclidean_iff` | `PROVISIONAL_MATCH` |
| Lemma 2.1, properties of `Phi` | None | None | `NOT_FORMALIZED` |
| Lemma 2.2, covering radius criterion | Source binding | Abstract strict/closed radius implications | `PARTIAL_FORMALIZATION` |
| Lemma 3.1, trace Gram determinant | Exact symbolic matrix checks | `abs_integralTraceGramDet_eq_discr_pow_absNorm_pseudo` for arbitrary full projective lattices | `PROVISIONAL_MATCH` |
| Lemma 3.2, covolume formula | Source-bound downstream checks | `euclideanCovolume_sq_eq_discr_pow_absNorm_pseudo` | `PROVISIONAL_MATCH` |
| Lemma 3.3, covering-volume inequality | None | `covolume_sq_le_of_sqrt_cover_above` and `euclideanCovolume_sq_le_of_traceEuclidean` | `FORMALIZED_COMPONENT` |
| Lemma 3.4, discriminant and volume-ideal bounds | Exact formula diagnostics | Sharp classic/integral discriminant inequalities and the analytic bounds needed by the main finiteness proof | `PARTIAL_FORMALIZATION` |
| Lemmas 4.1 and 4.2 | Exact identities, signs, limits, and certified roots | Stationary derivative sublemma reused in 4.3 | `COMPUTATION_VERIFIED` |
| Lemma 4.3, global maximum of `g` | Exact calculus, rational intervals, boundary comparison, tail check | Critical-point saddle component plus the tail/envelope estimates needed for finiteness | `PARTIAL_FORMALIZATION` |
| Lemmas 4.4-4.9 | Exact identities, monotonicity conditions, roots, and maxima | None | `COMPUTATION_VERIFIED` |
| Lemma 5.1, bounded-discriminant/volume finiteness | None | Hermite field finiteness plus the stronger-for-the-application direct fixed-field finite-code theorem | `PARTIAL_FORMALIZATION` |
| Proposition 6.1, exact quadratic covering radii | Exact Gram/Voronoi calculations | `realQuadratic_coveringRadiusSq_caseI`, `realQuadratic_coveringRadiusSq_caseII` | `PROVISIONAL_MATCH` |

The machine-readable Mathematica map is `results/verification_ledger.json`.
The Lean endpoint report is `lean/audit/main_theorem_axioms.txt`. The two
finiteness theorem groups are unconditional formal results. They remain
`PROVISIONAL_MATCH` until the author/domain and independent Lean review cards
confirm the object conventions and theorem correspondence.
