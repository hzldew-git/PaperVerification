# Definition dictionary

| Paper concept | Lean representation | Relationship |
|---|---|---|
| `t`-trace Euclidean lattice | `StrictEuclidean cost t` | Same quantifier order and strict inequality after the trace cost is supplied; field and lattice structures are abstracted away. |
| Pointwise non-strict approximation | `ClosedEuclidean cost t` | Direct abstract counterpart. |
| Squared trace covering radius | `SquaredCoveringRadiusSpec cost rhoSq` | Characterizes upper bound and sharpness; it does not construct the geometric radius. |
| Obstructing point | `not_strictEuclidean_of_witness` | Exact logical shape of a point whose every translate has cost at least the threshold. |
| `p`-norm Euclideanity | A second cost supplied to `StrictEuclidean` | Power means and endpoints `p=0,infinity` are not encoded. |
| Quadratic-form isometry | `IsometricForms Q Q'` | Function-level abstraction; module, scalar-ring, and semilinear data are omitted. |
| Scaling `L^(2)` | `scaleForm 2 Q` | Represents scaling of the form value, not a full lattice structure. |
| Two-dimensional trace norm | `R2`, `dot`, `normSq` | Exact coordinate algebra over the real numbers. |
| Case-I basis | `v1`, `caseI_v2` | Coordinates agree after a real parameter `s` with `s^2=m` is supplied. |
| Case-II basis and third vector | `v1`, `caseII_v2`, `caseII_v3` | Exact coordinate model. |
| Voronoi vertex coefficients | `vertexS`, `vertexT` | Exact solution of the two bisector equations under nonzero determinant. |
| Squared radius formulas | `caseIRadiusSq`, `caseIIRadiusSq` | Rational formulas used as arithmetic inputs; their geometric identification is separate. |
| Square-free positive integer | `IsSquarefreeNat` plus explicit positivity hypotheses | Elementary square-divisor predicate; positivity and `m>1` are theorem hypotheses rather than fields. |

No Lean definitions currently represent a totally real number field, its
embeddings, ring of integers, an `O_F`-lattice, scale/norm/volume ideals,
discriminant, covolume, a full Voronoi cell, or field-varying pair equivalence.
