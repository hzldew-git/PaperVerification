# Theorem coverage

This index records what the exported Lean statements prove. The paper-to-code
correspondence requires mathematical review in addition to compilation. Names
below refer to the stable public modules and declarations.

| Paper claim or calculation | Public Lean evidence | Scope |
| --- | --- | --- |
| Real trace form and coordinates | `GlobalLatticePresentation.productTraceQuadraticForm_associated_rationalPoint`, `productTraceQuadraticForm_posDef`, `productCoordinateFin_int_range`, `productCoordinateFin_rat_range`, `productCoordinateFormFin_int`, and `productTraceNearestValue_fin_coordinates` | Proves the product-of-real-embeddings construction, its integer and rational coordinate images, positive definiteness, integer values, and the nearest-lattice infimum formula for the chosen integral basis. The scalar-extension and product models are identified by `tensorProductEmbeddingEquiv` and `productTraceCost_tensorProductEmbeddingEquiv`. |
| Rational trace compatibility and maximum transfer | `productTraceNearestValue_rationalPoint`, `productTraceNearestValue_max_of_rational_coordinate_max`, and `rationalTraceNearestValue_max_of_rational_coordinate_max` | Proves equality of the rational and real nearest-lattice values on embedded points. Given a rational tuple that maximizes the real coordinate covering value, proves that an embedded rational vector maximizes both the product-space and rational trace values. The rational-attainment premise remains the separate Clark--Jagy literature step. |
| Classic integral finiteness | `classic_finite_closed` | Closed Lean endpoint using the formalized unconditional discriminant bound and algebraic finiteness arguments. Paper correspondence remains subject to independent review. |
| Integral finiteness | `integral_finite_closed` | Closed Lean endpoint under the encoded definitions. Paper correspondence remains subject to independent review. |
| Finite and infinite p-norm finiteness | `pnorm_finite_closed` | Covers the encoded p-norm cases with varying field and rank. |
| Six rank-one classes | `actual_ideal_six_rows`, `rank_one_real_quadratic_classification_totally_positive` | Proves the encoded ideal models and both classification directions. Independent review of manuscript assumptions and quantifiers remains pending. |
| Trace Euclidean fields | `realQuadratic_two_trace_euclidean_iff` | Proves the encoded real-quadratic field classification. |
| General binary covering radius | `reduced_gram_exact_radius`, `proposition_six_one_full` | Covers reduced Gram forms and fractional-ideal scalar cases. |
| Odlyzko-style discriminant bound | `odlyzkoTable4DescriptionInput_closed` and `Odlyzko_discriminant_log_lower_bound` | The selected kernel, analytic continuation, explicit formula, contour, prime correction, and numerical constants are formalized. Some finite numerical certificates use `native_decide`, as disclosed in `TRUST.md`. |
| Section 4 analytic grid | `classic_analytic_grid_iff_mem`, `integral_analytic_grid_iff_mem` | Exact finite-grid inequalities and selected rows are proved for the encoded input. |
| Section 4 small-degree exclusions | `sectionFourDiscriminantInput_of_voightEnumeration_poitou` and `sectionFourDiscriminantInput_of_publishedVoightBounds_closed` | The first route assumes completeness of Voight's enumeration and Poitou's specialized degree-eleven explicit formula; its numerical optimization to 14.083 is proved in Lean. The second route assumes the published Odlyzko--Martinet bound directly. The archived polynomial rows have Lean certificates, but their completeness as a field list is not proved here. |
| Archived Voight polynomial data | `allVoightPolynomialRows_present_exactTotallyRealNumberField` | Each archived row yields an actual totally real field with its recorded discriminant. Generated finite certificates use the disclosed native compiler trust boundary. |

## What is not established by compilation alone

- The rational attainment of the global real trace covering maximum, cited
  from Clark--Jagy in the manuscript, is not exported as a Lean theorem here.
  The coordinate range and pointwise nearest-lattice identities are proved,
  but they do not by themselves establish that the maximum occurs at a
  rational point.
- The full general analytic lemma for the nearest-lattice value, including
  periodicity, continuity, and real maximum attainment, is outside the
  selected exported endpoints. The conditional rational maximum bridge above
  does not supply those statements.
- The completeness of Voight's published list of fields up to the relevant
  degree and discriminant bound is an external literature input. The partial
  Hunter search formalization does not yet close all candidate ranges.
- Poitou's specialized degree-eleven explicit formula remains a premise in
  the route that proves the 14.083 numerical optimization internally. The
  alternative source-facing route assumes the published Odlyzko--Martinet
  estimate. The unconditional Table 4 bound used for global finiteness is
  treated separately and has a Lean derivation in this project.
- Independent sign-off on the exact correspondence between all manuscript
  statements and the encoded Lean theorems is still pending.
- The author maintains the manuscript-to-public-input comparison separately.
  The manuscript and its private source metadata are not included here.

Run the axiom audit files listed in `README.md` to inspect transitive proof
dependencies. See `TRUST.md` for `native_decide` and source boundaries.
