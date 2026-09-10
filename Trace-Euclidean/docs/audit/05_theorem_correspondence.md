# Theorem correspondence

| Paper result | Formal or computational counterpart | Status | Material gap |
|---|---|---|---|
| Definition 1.1 | `traceCost`, `IsTraceEuclidean`, `NumberFieldLattice` | `PROVISIONAL_MATCH` | The objects, trace normalization, strict inequality, and quantifiers agree; independent review is unsigned. |
| Theorem 1.2(i)-(iv) | Four `finiteness_classic_...` endpoints | `FORMALIZATION_WEAKER` | Every rank/degree/`t ≤ d` conclusion is present, but `MainFinitenessFramework` supplies the geometric bounds, actual quotient semantics, and fixed-volume lattice finiteness. |
| Theorem 1.3(i)-(iv) | Four `finiteness_integral_...` endpoints | `FORMALIZATION_WEAKER` | Same additional framework premise, including the factor-two-scaled volume ideal and its fixed-volume fibers. |
| Definition 1.5 and Corollary 1.6 | `pNormEuclidean_imp_traceEuclidean` | `FORMALIZED_COMPONENT` | The power-mean theorem, definitions of `M_p`, and uniform `t=d` application are supplied outside Lean. |
| Definition 1.7 | `IsFieldTraceEuclidean` | `PROVISIONAL_MATCH` | The definition omits a total-reality typeclass because its concrete Theorem 1.8 field is separately constructed; the quantified formula agrees. |
| Lemma 2.1 | None | `NOT_FORMALIZED` | Periodicity, continuity, compact quotient, and density are absent. |
| Lemma 2.2 | Two abstract radius implications and obstruction theorem | `PARTIAL_FORMALIZATION` | Construction of `Phi`, attainment of minima, and identification of `rho_T` are absent. |
| Lemma 3.1 | Mathematica exact Gram calculations; two-dimensional Lean Gram cases | `PARTIAL_FORMALIZATION` | General rank-degree determinant theorem is absent from Lean. |
| Lemma 3.2 | Source-bound downstream computation | `NOT_FORMALIZED` | Covolume and volume ideal are absent. |
| Lemma 3.3 | Cited Euclidean volume bound | `EXTERNAL_INPUT` | Not reproved computationally or formally. |
| Lemma 3.4 | Mathematica formula checks; framework fields | `ASSUMED_NOT_PROVED` | The inequalities are explicit premises of the finiteness endpoints, not Lean theorems about concrete lattices. |
| Lemmas 4.1-4.2 | Mathematica exact calculus and certified roots | `COMPUTATION_VERIFIED` | No Lean definitions of the complete functions and derivatives. |
| Lemma 4.3 | Mathematica global checks; `criticalPoint_hessian_negative`; analytic tail theorems | `PARTIAL_FORMALIZATION` | Lean proves the saddle and the tails needed for finiteness; the exact global-maximum location and certified boundary comparison remain computational. |
| Lemmas 4.4-4.9 | Mathematica exact identities, signs, limits, roots, and maxima | `COMPUTATION_VERIFIED` | No Lean theorem carries the complete analytic statements. |
| Lemma 5.1 | `bounded_discriminant_volume_finiteness` and scaling cancellation | `FORMALIZATION_WEAKER` | Hermite and ideal enumeration are proved via mathlib; O'Meara's fixed-volume fiber theorem is an explicit premise. |
| Proposition 6.1 | `realQuadratic_coveringRadiusSq_caseI`, `realQuadratic_coveringRadiusSq_caseII` | `PROVISIONAL_MATCH` | Full real-plane upper and sharp lower properties give both formulas; equivalence of this specification with the manuscript's geometric radius awaits independent review. |
| Theorem 1.8 | `realQuadratic_two_trace_euclidean_iff` | `PROVISIONAL_MATCH` | Concrete field, both integer bases, trace formula, necessity, obstruction, and sufficiency are all proved; independent semantic sign-off remains. |

No result is assigned `VERIFIED_MATCH` because the required independent
author/domain and Lean reviews are unsigned. Theorem 1.8 and Proposition 6.1
are complete candidates for `VERIFIED_MATCH`; the two finiteness theorem
groups are not, because their public signatures still contain a
project-specific proof-obligation structure.
