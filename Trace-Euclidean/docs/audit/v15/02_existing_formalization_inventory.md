# Existing foundational formalization and v15 reuse assessment

This inventory describes the pre-v15 Lean project before version-specific
changes. The copied project is at commit
`c4aed60cc9405e4570d7b65eb308e8a71d5c7137`.

| V15 paper claim | Existing declaration or module | Current v15 status |
| --- | --- | --- |
| Strict trace Euclidean definition | `NumberFieldLattice.lean`: `IsTraceEuclidean`, `traceCost`; `GlobalLatticeClass.lean` quotient predicate | Reusable after checking that the threshold is the varying field degree. |
| Classic/integral global finiteness, Theorems 1.2 and 1.3 | `GlobalFiniteness.lean`: eight foundational endpoints for a single fixed positive threshold `t` | **Not a v15 proof.** The v15 threshold equals the degree of each varying field. A fixed-`t` theorem does not imply this varying-threshold assertion. The v15 strict root-discriminant constants also need new endpoint proofs. |
| Finite fixed field/rank class result | `DirectFixedFieldFiniteness.lean`, `GlobalFiniteness.classic_fixed_pair`, `integral_fixed_pair` | Reusable for a fixed degree after setting `t=d`, subject to a statement audit. |
| Full projective lattice determinant and covolume | `PseudoBasisDeterminant.lean`, `TraceVolumeBridge.lean`, `GlobalLatticeClass.lean` | Likely reusable; normalization and nonfree scope need independent comparison. |
| Quadratic field classification corollary, `m∈{2,5,13}` | `QuadraticClassification.lean`, `QuadraticIntegralBasis.lean`, concrete endpoint `realQuadratic_two_trace_euclidean_iff` | Reusable for v15 Corollary 1.9 after checking the field model and strict threshold. |
| Six-class rank-one integral lattice classification, Theorem 1.7 | No existing direct six-class lattice endpoint | **Missing core result.** Existing field classification treats only the square form on the integer ring and does not classify arbitrary rank-one fractional-ideal lattices or prove their freeness. |
| Binary covering formula for arbitrary reduced trace Gram matrices | `VoronoiAlgebra.lean` proves vertex algebra; `QuadraticGeometry.lean` proves the full-plane formula for the square form | A general reduced-Gram covering theorem and its bridge to arbitrary rank-one lattices are missing. |
| V15 finite grid and exact table results | The earlier Mathematica package uses removed analytic labels and the old finite grid | New v15 source binding and tests are required; earlier result files cannot be relabeled. |

This is a baseline inventory recorded before the new v15 proofs. Its missing
items have since been addressed as described in
02_formal_declaration_inventory.md and 05_theorem_correspondence.md. The
current scoped v15 assessment is Grade B.
