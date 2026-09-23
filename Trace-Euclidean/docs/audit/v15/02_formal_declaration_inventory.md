# Formal declaration inventory for v15

| Declaration | Actual elaborated role |
| --- | --- |
| v15_classic_root_discriminant_lt, v15_integral_root_discriminant_lt | Strict rank-times-root-discriminant bounds for the corresponding varying-field quotient classes. |
| V15OdlyzkoTable4ExactErrorInput, V15OdlyzkoTable4DescriptionInput | Literature-facing forms of Odlyzko's unconditional Table 4 row before and after upward rounding of E, including the signature exponents and nonnegative prime-ideal correction. They are explicit premises, not project axioms. |
| v15_odlyzkoTable4_error_rounding, v15_odlyzkoTable4FieldInputFrom_of_description | Prove 32/3 <= 10.667, the valid rounding direction, totally real signature specialization, and removal of the nonnegative correction. |
| v15OdlyzkoH_differentiable, v15OdlyzkoF4_differentiable, v15OdlyzkoF4_exp_decay, v15OdlyzkoF4_source_test_hypotheses | Prove and package all source test-function hypotheses in equation (2.1): evenness, normalization, global differentiability, and the eventual exponential bound for the function and its derivative. |
| v15OdlyzkoHCore_intervalIntegral_zero_two, v15OdlyzkoF4_archimedean_error_integral | Evaluate the printed `H` formula and derive the exact `E = 32/3` archimedean error integral from the source kernel. |
| v15OdlyzkoPhi_one_sub | Prove the exact source transform satisfies `Phi(1-s) = Phi(s)` for every complex `s`. |
| v15OdlyzkoPhi_one, v15OdlyzkoPhi_zero, v15OdlyzkoPhi_zero_add_one | Derive both exact endpoint values `16/3` and their sum `32/3` from the proved kernel error integral. |
| V15OdlyzkoABIntegralCertificate, V15OdlyzkoExplicitFormulaInput, v15_odlyzkoTable4ExplicitCorrectionInput_of_sourceFormula, v15_odlyzkoTable4ExplicitCorrectionInput_of_enumeratedZeros | State the two source archimedean integrals, strict `A,B` bounds, and exact equation (2.3), then prove the conditional bridge to Table 4. The integral certificate is proved below; equation (2.3) and its paired-zero convergence remain unproved. |
| v15OdlyzkoCoshIntegrand_integrable, v15OdlyzkoCoshIntegrand_integrableOn | Prove convergence of the cosh-denominator source integral using the integrable hyperbolic-secant factor and bounded compactly supported test function. |
| v15OdlyzkoSinhIntegrand_integrableOn, v15OdlyzkoSinhIntegral_zero_hundredth_le, v15OdlyzkoSinhIntegral_tail_le, v15OdlyzkoCoshIntegral_tail_le | Prove convergence of the sinh-denominator integral, a quadratic origin bound, and explicit exponential tail bounds for both integrals. |
| V15OdlyzkoNumerical.sinh_core_upper, V15OdlyzkoNumerical.cosh_core_upper, V15OdlyzkoNumerical.abIntegralCertificate | Verify finite-interval dyadic enclosures and assemble the strict source-normalized `A = 36.347`, `B = 16.593` certificate. The checks use `native_decide` and are audited under that disclosed compiler trust boundary. |
| V15OdlyzkoTable4FieldInputFrom, V15OdlyzkoTable4InputFrom | Restrict the Table 4 premise to the field degrees actually used; degree 12 begins the analytic table range and degree 15 begins the finiteness cutoff. |
| v15_degree_one_discriminant_bound | Proves the degree-one Section 4 discriminant input internally from Minkowski's bound. |
| V15DegreeTwoToNineMinimumInput, V15DegreeTenRootDiscriminantInput, V15DegreeElevenRootDiscriminantInput | Separate literature inputs for exact minima, Voight's empty degree-ten range at root discriminant at most 14, and the optimized degree-eleven bound 14.083. |
| V15SmallDegreeDiscriminantInput, V15SectionFourDiscriminantInput | Compatibility premise and combined piecewise discriminant bound used by Section 4. |
| v15_unitBallVolume_sq_closed, v15AnalyticH_eq_closed | Evaluate the squared unit-ball volume through factorials and rewrite the manuscript's Gamma-defined `H(n,d)` exactly. |
| v15HLower_le_analyticH_le_upper | Encloses the exact analytic quantity between rational expressions using proved bounds for pi and the exponential correction. |
| v15_classic_analytic_grid_iff_mem, v15_integral_analytic_grid_iff_mem | Prove on every cell with 1 <= n <= 34 and 1 <= d <= 14 that the exact analytic classic/integral inequality is equivalent to membership in the 24/63 pair list. |
| v15_classic_pair_mem_of_literature, v15_integral_pair_mem_of_literature | Derive the actual lattice class's table membership from the source-specific small-degree inputs, full Table 4 description, and rank-one input. |
| v15_odlyzko_degree_input_of_table4_from_fifteen | Proves the numerical degree cutoff from the published constants using Table 4 only from degree fifteen. |
| v15_rank_one_classic_input | Proves integral rank-one presentations are classically integral without freeness. |
| v15_classic_finite_of_odlyzko_table4_description, v15_integral_finite_of_odlyzko_table4_description_source | Global finiteness at the varying threshold equal to each field degree, conditional on the full cited Table 4 row. |
| v15_actual_ideal_six_rows | Obtains six surviving reduced Gram rows for every qualifying nonzero fractional ideal. |
| v15_actual_ideal_principal | Proves the ideal principal, including the exceptional m=3 case. |
| v15_rank_one_real_quadratic_classification_totally_positive | If and only if over all nonzero fractional ideals and totally positive integral coefficients, with actual module-isometry classes. |
| v15_m*_representative_euclidean, v15_m*_representative_valid | Six free representatives are strictly trace Euclidean, positive, and integral. |
| v15_mfive_one_two_not_isometric, v15_distinct_discriminants_no_field_isomorphism | Distinguish the two m=5 classes and the five quadratic fields. |
| realQuadratic_two_trace_euclidean_iff | Reused concrete field-square endpoint for Corollary 1.9. |
| v15_reduced_gram_exact_radius, v15_reduced_gram_exact_radius_rat | Exact generic reduced-binary squared covering radius over the real and rational planes. |
| GlobalLatticePresentation.rankOne_ideal_bridge | Represents every canonical rank-one global lattice by a nonzero fractional ideal and coefficient, preserving positivity, integrality, and trace Euclideanity. |
| v15_ideal_exact_radius_of, v15_proposition_six_one_ideal | Transfers the generic radius to every actual quadratic fractional ideal and packages its reduced basis and determinant identity. |
| GlobalLatticePresentation.rankOne_ideal_bridge_at, rankOne_ideal_bridge_degree | Preserve the rank-one ideal presentation and strict trace condition at any real threshold and at the field degree. |
| v15_number_field_has_code | Every number field is isomorphic to one finite intermediate field in the fixed algebraic closure. |
| v15_totally_real_field_code | A totally real field has a totally real code; its field isomorphism identifies the integer rings and preserves the rational trace. |
| NumberFieldLattice.v15AbstractToCanonical | An arbitrary positive-rank abstract lattice over an already coded totally real field has an actual canonical-coordinate isometry, preserving trace Euclideanity at the field degree and classic integrality. |
| NumberFieldLattice.v15AbstractRankOneIdealBridge | Composes the coordinate isometry with the rank-one ideal theorem at any real threshold, retaining positivity, integrality, membership, and the quadratic formula. |
| NumberFieldLattice.v15AbstractToCanonicalAnyField | For an arbitrary totally real number field, chooses a code and transports the scalar field, space, full lattice, and quadratic form to an actually isometric canonical presentation, preserving the degree threshold and classic integrality. |
| NumberFieldLattice.v15AbstractRankOneIdealBridgeAnyField | Composes the cross-field transport with the rank-one ideal theorem at any real threshold. |
| v15_classic_rank_bounds_by_degree, v15_classic_degree_bounds_by_rank | Kernel-check the complete rank and degree bound arrays in Table 2 from the 24 extracted classic pairs. |
| v15_integral_rank_bounds_by_degree, v15_integral_degree_bounds_by_rank | Kernel-check the complete rank and degree bound arrays in Table 4 from the 63 extracted integral pairs. |
| v15_classic_table_exact_global_maxima, v15_integral_table_exact_global_maxima | Prove the exact global table maxima, including witnesses. |
| v15_integral_table_degree_seven_to_nine, v15_integral_table_overall_rank_le_twelve | Prove the two numerical consequences stated in Remark 1.4(iii)--(iv), with the degree-one classification supplied explicitly to the latter. |
| v15_proposition_six_one_scalar_cases, v15_proposition_six_one_full | Both positive-integer scalar formulas on the quadratic integer ring and a combined endpoint for all clauses of Proposition 6.1. |
| GlobalLatticePresentation.v15_pnorm_implies_trace, v15_pnorm_finite_of_odlyzko_table4_description | Power-mean implication for finite p >= 1 and infinity, followed by global finite-class conclusion from the full cited Table 4 row. |
| v15OdlyzkoSechFourier, v15OdlyzkoSechFourier_integrable | Exact Fourier transform and Fourier-side integrability of the hyperbolic-secant factor in the unconditional kernel. |
| v15OdlyzkoF4_fourier_eq_convolution, v15OdlyzkoF4_fourier_re_nonneg, v15OdlyzkoF4_fourier_im_eq_zero | Product-to-frequency-convolution bridge and the reality and nonnegativity of the Fourier transform of the complete `b=4` kernel. |
| v15OdlyzkoTiltedSech_fourier_eq_sin, v15OdlyzkoTiltedF4_fourier_re_nonneg_closed, v15OdlyzkoPhi_eq_fourier, v15OdlyzkoPhi_re_nonneg_of_mem_closed_strip | Exact tilted-secant transform, closed-strip positivity of the complete kernel, and the source-normalization bridge for Odlyzko's zero transform. |
| v15OdlyzkoPhi_zero_tsum_re_nonneg | Nonnegative real part of a summable family of zero contributions, conditional on every parameter lying in the critical strip and on summability. |

Supporting modules prove the reduced-basis bridge, quotient-ideal index/norm identities, parity, determinant, exceptional two-vector exclusion, and constructive strict covers for all six forms.
