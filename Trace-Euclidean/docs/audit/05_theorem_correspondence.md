# Theorem correspondence

| Paper result | Formal or computational counterpart | Status | Material gap |
|---|---|---|---|
| Definition 1.1 | `StrictEuclidean` | `PROVISIONAL_MATCH` as an abstraction | Trace cost and algebraic structures are parameters. |
| Theorem 1.2(i)-(iv) | Mathematica bounds and tables; `Finiteness` assembly | `PARTIAL_FORMALIZATION` | No Lean theorem quantifies over totally real fields, lattices, rank, degree, or pair equivalence. |
| Theorem 1.3(i)-(iv) | Mathematica bounds and tables; `Finiteness` and `Scaling` | `PARTIAL_FORMALIZATION` | Integral-lattice ideal inclusions and external finiteness theorems are absent. |
| Definition 1.5 and Corollary 1.6 | `pNormEuclidean_imp_traceEuclidean` | `FORMALIZED_COMPONENT` | The power-mean theorem, definitions of `M_p`, and uniform `t=d` application are supplied outside Lean. |
| Definition 1.7 | None | `NOT_FORMALIZED` | Field-level definition absent. |
| Lemma 2.1 | None | `NOT_FORMALIZED` | Periodicity, continuity, compact quotient, and density are absent. |
| Lemma 2.2 | Two abstract radius implications and obstruction theorem | `PARTIAL_FORMALIZATION` | Construction of `Phi`, attainment of minima, and identification of `rho_T` are absent. |
| Lemma 3.1 | Mathematica exact Gram calculations; two-dimensional Lean Gram cases | `PARTIAL_FORMALIZATION` | General rank-degree determinant theorem is absent from Lean. |
| Lemma 3.2 | Source-bound downstream computation | `NOT_FORMALIZED` | Covolume and volume ideal are absent. |
| Lemma 3.3 | Cited Euclidean volume bound | `EXTERNAL_INPUT` | Not reproved computationally or formally. |
| Lemma 3.4 | Mathematica formula checks | `PARTIAL_FORMALIZATION` | General discriminant and ideal inequalities are absent from Lean. |
| Lemmas 4.1-4.2 | Mathematica exact calculus and certified roots | `COMPUTATION_VERIFIED` | No Lean definitions of the complete functions and derivatives. |
| Lemma 4.3 | Mathematica global checks; `criticalPoint_hessian_negative` | `PARTIAL_FORMALIZATION` | Lean proves the repaired interior-saddle step, while boundary and tail analysis remain outside Lean. |
| Lemmas 4.4-4.9 | Mathematica exact identities, signs, limits, roots, and maxima | `COMPUTATION_VERIFIED` | No Lean theorem carries the complete analytic statements. |
| Lemma 5.1 | `two_scaled_isometric_iff`, finite set and sigma lemmas | `PARTIAL_FORMALIZATION` | Number-field and lattice-class finiteness are external inputs. |
| Proposition 6.1 | Mathematica exact geometry; `VoronoiAlgebra` | `PARTIAL_FORMALIZATION` | Full Voronoi-cell and strict-superbase justification are absent from Lean. |
| Theorem 1.8 | Mathematica candidate checks; `QuadraticArithmetic` | `PARTIAL_FORMALIZATION` | No single Lean statement constructs the fields and proves the iff classification. |

No complete paper theorem is currently assigned `EXACT_MATCH`. The strongest
Lean correspondences are component proofs whose omitted bridge assumptions are
listed explicitly above.
