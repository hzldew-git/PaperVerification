# Trace-Euclidean v15 theorem index

Frozen author source SHA-256:
83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.
The manuscript is not redistributed.

Status vocabulary: PROVISIONAL_MATCH means the reviewed paper claim and Lean
statement appear aligned but independent sign-off is absent. FORMALIZED_COMPONENT
means a specified part is proved. COMPUTATION_VERIFIED means the encoded
calculation was rerun. EXTERNAL_INPUT means a cited result is an explicit premise.

| Paper item | Lean or computational evidence | Status |
| --- | --- | --- |
| Definition 1.1, strict trace Euclideanity | IsTraceEuclidean, V15IdealTraceEuclidean; strict threshold equals field degree | PROVISIONAL_MATCH |
| Theorem 1.2, classic integral finiteness | v15_classic_root_discriminant_lt; v15_classic_finite_of_odlyzko_table4_description; variable-degree finite assembly; Table 4 used only from degree 15 | PROVISIONAL_MATCH with full Table 4 description as EXTERNAL_INPUT |
| Theorem 1.3, integral finiteness | v15_integral_root_discriminant_lt; v15_rank_one_classic_input; v15_integral_finite_of_odlyzko_table4_description_source | PROVISIONAL_MATCH with full Table 4 description as EXTERNAL_INPUT |
| Corollary 1.6, p-norm finiteness | v15_pnorm_implies_trace and v15_pnorm_finite_of_odlyzko_table4_description; every finite p >= 1 and p = infinity, with varying field and rank | FORMALIZED_COMPONENT with full Table 4 description as EXTERNAL_INPUT; independent semantic review pending |
| Theorem 1.7, six rank-one classes | v15_actual_ideal_six_rows, v15_actual_ideal_principal, v15_rank_one_real_quadratic_classification_totally_positive; six representative validity and Euclidean proofs; distinction | PROVISIONAL_MATCH |
| Corollary 1.9, trace Euclidean fields | realQuadratic_two_trace_euclidean_iff and concrete square-form bridge | PROVISIONAL_MATCH |
| Reduced Gram sieve | 22 triples, nine field rows, six surviving rows, all linked to actual ideals | FORMALIZED_COMPONENT |
| Proposition 6.1, general binary radius and scalar formulas | v15_reduced_gram_exact_radius, v15_proposition_six_one_ideal, v15_proposition_six_one_scalar_cases, v15_proposition_six_one_full; arbitrary ideal basis, determinant, and both scalar formulas included | FORMALIZED_COMPONENT; independent semantic review pending |
| Abstract rank-one ideal presentation | GlobalLatticePresentation.rankOne_ideal_bridge_at and rankOne_ideal_bridge_degree: nonzero fractional ideal, quadratic coefficient, positivity, integrality, and equivalent strict trace condition at arbitrary and degree thresholds | FORMALIZED_COMPONENT in the canonical coordinate model |
| Abstract-space coordinate transport | v15AbstractToCanonicalAnyField and v15AbstractRankOneIdealBridgeAnyField: a code and field isomorphism for every totally real field, with transported full lattice, quadratic form, actual isometry, strict trace condition, classic integrality, and rank-one ideal data | FORMALIZED_COMPONENT; independent semantic review pending |
| Section 4 numerical tables | v15_classic_analytic_grid_iff_mem and v15_integral_analytic_grid_iff_mem prove that the exact analytic inequalities select the 24/63 rows on the full 34 by 14 grid; v15_degree_one_discriminant_bound is internal; v15_classic_pair_mem_of_literature and v15_integral_pair_mem_of_literature use separate degree 2--9, degree 10, degree 11, and Table 4-from-12 inputs; V15AdmissibleTables proves all rank/degree bounds, exact maxima, and quoted consequences | FORMALIZED_COMPONENT with source-specific field-discriminant EXTERNAL_INPUTS; independent Python/Wolfram COMPUTATION_VERIFIED |
| Odlyzko unconditional kernel and prime correction | v15OdlyzkoHCore_nonneg, v15OdlyzkoH_eq_autocorrelation, v15OdlyzkoH_fourier_eq_square, v15OdlyzkoSechFourier, v15OdlyzkoF4_fourier_eq_convolution, v15OdlyzkoF4_fourier_re_nonneg, v15OdlyzkoF4_source_test_hypotheses, v15OdlyzkoF4_archimedean_error_integral, v15OdlyzkoPhi_one_sub, v15OdlyzkoPhi_zero_add_one, v15OdlyzkoSinhIntegrand_integrableOn, V15OdlyzkoNumerical.abIntegralCertificate, v15OdlyzkoPrimeCorrection_eq_finite, v15OdlyzkoPrimeCorrection_nonneg, v15_odlyzkoTable4ExplicitCorrectionInput_of_sourceFormula, and v15_odlyzkoTable4DescriptionInput_of_explicitCorrection | FORMALIZED_COMPONENT; `H` is an autocorrelation, the complete `F` transform is real and nonnegative, source differentiability and derivative decay are proved, `Phi(0)=Phi(1)=16/3`, the exact error integral is `E=32/3`, both archimedean integrals converge, and strict `A,B` bounds follow from dyadic certificates with disclosed native-compiler trust; the complete prime sum is finite; the source formula and strict-integral certificate imply Table 4 conditionally; the explicit formula and paired-zero convergence remain EXTERNAL_INPUTS |

The active [v15 audit](docs/audit/v15/05_theorem_correspondence.md) expands the
assumptions and quantifiers. The [Lean axiom report](lean/audit/main_theorem_axioms.txt)
contains the elaborated endpoint signatures and trust dependencies.
