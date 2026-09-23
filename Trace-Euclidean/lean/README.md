# Lean formalization for Trace-Euclidean v15

This Lake project pins Lean v4.32.1 and mathlib revision
520045ab14e26149ee970e2e617ca04b09bde5d6. It includes the shared
foundational modules required by the v15 proof chain and the v15-specific
proofs.

The v15 proof chain is organized as follows:

| Modules | Content |
| --- | --- |
| V15StrictDiscriminant, V15FinitenessAssembly, V15OdlyzkoBridge, V15RankOneIntegral | Strict bounds, varying-degree finite grid, full Table 4 description with rounding/signature bridges, rank-one classic-integrality |
| V15OdlyzkoKernel, V15OdlyzkoAutocorrelation, V15OdlyzkoFourier, V15OdlyzkoSechFourier, V15OdlyzkoFinalFourier, V15OdlyzkoPrimeCorrection, V15OdlyzkoAnalyticBridge | Source-exact unconditional `b = 4` kernel; autocorrelation identity and Fourier positivity of `H`; exact hyperbolic-secant transform and Fourier positivity of the complete kernel `F`; complete prime-ideal correction, exact finite-support reduction, nonnegativity, and substitution into the Table 4 interface |
| V15BinaryCriterion, V15BinaryCovering, V15GaussBasis | Rational deep hole, six direct covers, and reduced binary basis |
| V15IdealCoordinates, V15IdealNormQuotient, V15IdealDeterminant, V15VariableBasis | Actual fractional ideals, field coordinates, determinant and norm bridges |
| V15VariableSieve, V15ActualPrincipality | Six survivor rows and principality, including m=3 |
| V15CoefficientClassification, V15PositivityBridge | Actual isometries and the iff six-class theorem with total positivity |
| V15Representatives, V15RepresentativeValidity, V15Distinctness | Six strictly Euclidean integral positive representatives and distinction |
| QuadraticIntegralBasis, QuadraticFieldBridge | Concrete field-square corollary inherited and rechecked for v15 |
| V15FieldTransport | Scalar-field, quadratic-space, full-lattice, and form transport from any totally real number field to a coded canonical model |
| V15AdmissibleTables | Kernel-checked 24/63 finite tables, all rank/degree bound arrays, exact maxima, and quoted table consequences |
| V15AnalyticTable, V15AnalyticTableBridge | Exact Gamma normalization of `H(n,d)`, proved rational enclosures, full 34 by 14 analytic-table equivalences, and the field-discriminant-to-table bridge |

The public classification endpoint is
v15_rank_one_real_quadratic_classification_totally_positive. It quantifies
over all nonzero fractional ideals. The global finite-class endpoints are
v15_classic_finite_of_odlyzko_table4_description and
v15_integral_finite_of_odlyzko_table4_description_source. Their external
mathematical premise is the complete cited unconditional Table 4 row; Lean
proves its rounding, totally real specialization, and restriction to degrees
at least fifteen.

The endpoints v15AbstractToCanonicalAnyField and
v15AbstractRankOneIdealBridgeAnyField remove the earlier restriction that the
source field already be coded. The finite Section 4 table conclusions are
v15_classic_table_exact_global_maxima,
v15_integral_table_exact_global_maxima, and the associated row/column bound
theorems. The endpoints v15_classic_analytic_grid_iff_mem and
v15_integral_analytic_grid_iff_mem prove inside Lean that the exact analytic
inequalities select the 24 and 63 rows throughout the complete finite grid.
The class-level endpoints v15_classic_pair_mem_of_literature and
v15_integral_pair_mem_of_literature connect those equivalences to separate
degree 2--9, degree 10, degree 11, and Table 4-from-12 premises. Degree one is
proved internally from Minkowski's bound. The public Python verifier
independently replays the interval computation.

From this directory:

~~~text
lake exe cache get
lake build
lake env lean TraceEuclideanTest/MainTheoremAudit.lean
~~~

The final command prints signatures and transitive axiom dependencies.
The repository records its output in audit/main_theorem_axioms.txt.
See ../TRUST.md and ../docs/audit/v15 for the semantic boundary.
