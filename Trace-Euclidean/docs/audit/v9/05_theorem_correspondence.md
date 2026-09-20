# Theorem correspondence

| Paper result | Formal or computational counterpart | Status | Material gap |
|---|---|---|---|
| Definition 1.1 | `traceCost`, `IsTraceEuclidean`, `NumberFieldLattice` | `PROVISIONAL_MATCH` | The objects, trace normalization, strict inequality, and quantifiers agree; independent review is unsigned. |
| Theorem 1.2(i)-(iv) | `GlobalFiniteness.finiteness_classic_...` | `PROVISIONAL_MATCH` | All four conclusions are unconditional on the actual quotient; rank, degree, total reality, classic integrality, strict trace bound, and `t ≤ d` are preserved. Domain and independent Lean review remain unsigned. |
| Theorem 1.3(i)-(iv) | `GlobalFiniteness.finiteness_integral_...` | `PROVISIONAL_MATCH` | All four integral conclusions are unconditional; the factor `2^(nd)` is derived from the scale-two pseudobasis determinant. Domain and independent Lean review remain unsigned. |
| Definition 1.5 and Corollary 1.6 | `pNormEuclidean_imp_traceEuclidean` | `FORMALIZED_COMPONENT` | The power-mean theorem, definitions of `M_p`, and uniform `t=d` application are supplied outside Lean. |
| Definition 1.7 | `IsFieldTraceEuclidean` | `PROVISIONAL_MATCH` | The definition omits a total-reality typeclass because its concrete Theorem 1.8 field is separately constructed; the quantified formula agrees. |
| Lemma 2.1 | None | `NOT_FORMALIZED` | Periodicity, continuity, compact quotient, and density are absent. |
| Lemma 2.2 | Two abstract radius implications and obstruction theorem | `PARTIAL_FORMALIZATION` | Construction of `Phi`, attainment of minima, and identification of `rho_T` are absent. |
| Lemma 3.1 | `abs_integralTraceGramDet_eq_discr_pow_absNorm_pseudo` | `PROVISIONAL_MATCH` | General rank and nonfree projective lattices are covered; independent confirmation of the volume-ideal naming and normalization remains. |
| Lemma 3.2 | `euclideanCovolume_sq_eq_discr_pow_absNorm_pseudo` | `PROVISIONAL_MATCH` | The squared formula is exact; the displayed square-root form follows over nonnegative reals but is not the exported endpoint. |
| Lemma 3.3 | `covolume_sq_le_of_sqrt_cover_above` and `euclideanCovolume_sq_le_of_traceEuclidean` | `FORMALIZED_COMPONENT` | The formal route uses Haar covolume and a limiting strict cover; reviewer confirmation of the manuscript notation remains. |
| Lemma 3.4 | Pseudobasis lower bounds, covering bounds, Minkowski/Gamma estimates, and `GlobalFiniteness.classic_discriminant_le_trace` / `integral_discriminant_le_trace` | `PARTIAL_FORMALIZATION` | The discriminant and positivity consequences used by Theorems 1.2 and 1.3 are proved; the paper's separate upper bounds for all three ideals are not exported in full. |
| Lemmas 4.1-4.2 | Mathematica exact calculus and certified roots | `COMPUTATION_VERIFIED` | No Lean definitions of the complete functions and derivatives. |
| Lemma 4.3 | Mathematica global checks; `criticalPoint_hessian_negative`; analytic tail theorems | `PARTIAL_FORMALIZATION` | Lean proves the saddle and the tails needed for finiteness; the exact global-maximum location and certified boundary comparison remain computational. |
| Lemmas 4.4-4.9 | Mathematica exact identities, signs, limits, roots, and maxima | `COMPUTATION_VERIFIED` | No Lean theorem carries the complete analytic statements. |
| Lemma 5.1 | `finite_objects_of_bounded_field_discriminant` plus `finite_fixedField_rank_*_traceEuclidean` | `PARTIAL_FORMALIZATION` | Lean proves a stronger fixed-field theorem for the trace-Euclidean application by finite reduction codes. It does not claim the full standalone bounded-volume lemma for arbitrary lattices. |
| Proposition 6.1 | `realQuadratic_coveringRadiusSq_caseI`, `realQuadratic_coveringRadiusSq_caseII` | `PROVISIONAL_MATCH` | Full real-plane upper and sharp lower properties give both formulas; equivalence of this specification with the manuscript's geometric radius awaits independent review. |
| Theorem 1.8 | `realQuadratic_two_trace_euclidean_iff` | `PROVISIONAL_MATCH` | Concrete field, both integer bases, trace formula, necessity, obstruction, and sufficiency are all proved; independent semantic sign-off remains. |

No result is assigned `VERIFIED_MATCH` because the required independent
author/domain and Lean reviews are unsigned. Theorem 1.8, Proposition 6.1,
and both four-part finiteness theorem groups are complete candidates for
`VERIFIED_MATCH`. Their public signatures contain no project-specific proof
obligation or unfinished proof.
