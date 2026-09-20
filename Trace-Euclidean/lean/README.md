# Lean formalization for Trace-Euclidean v15

This Lake project pins Lean v4.32.1 and mathlib revision
520045ab14e26149ee970e2e617ca04b09bde5d6. It includes the inherited
v9 modules and the v15 proofs.

The v15 proof chain is organized as follows:

| Modules | Content |
| --- | --- |
| V15StrictDiscriminant, V15FinitenessAssembly, V15OdlyzkoBridge, V15RankOneIntegral | Strict bounds, varying-degree finite grid, explicit Odlyzko source premise, rank-one classic-integrality |
| V15BinaryCriterion, V15BinaryCovering, V15GaussBasis | Rational deep hole, six direct covers, and reduced binary basis |
| V15IdealCoordinates, V15IdealNormQuotient, V15IdealDeterminant, V15VariableBasis | Actual fractional ideals, field coordinates, determinant and norm bridges |
| V15VariableSieve, V15ActualPrincipality | Six survivor rows and principality, including m=3 |
| V15CoefficientClassification, V15PositivityBridge | Actual isometries and the iff six-class theorem with total positivity |
| V15Representatives, V15RepresentativeValidity, V15Distinctness | Six strictly Euclidean integral positive representatives and distinction |
| QuadraticIntegralBasis, QuadraticFieldBridge | Concrete field-square corollary inherited and rechecked for v15 |

The public endpoint is
v15_rank_one_real_quadratic_classification_totally_positive. It quantifies
over all nonzero fractional ideals. The global finite-class endpoints are
v15_classic_finite_of_odlyzko_table4 and
v15_integral_finite_of_odlyzko_table4_source. Their sole external
mathematical premise is the cited unconditional Table 4 inequality.

From this directory:

~~~text
lake exe cache get
lake build
lake env lean TraceEuclideanTest/MainTheoremAudit.lean
~~~

The final command prints signatures and transitive axiom dependencies.
The repository records its output in audit/main_theorem_axioms.txt.
See ../TRUST.md and ../docs/audit/v15 for the semantic boundary.
