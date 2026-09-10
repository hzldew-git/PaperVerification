# Definition dictionary

| Paper concept | Lean representation | Relationship |
|---|---|---|
| `t`-trace Euclidean lattice | `IsTraceEuclidean Q L t` and `NumberFieldLattice.IsTraceEuclidean` | Same trace, quantifier order, lattice witness, and strict inequality. |
| Totally real field | `NumberField F` and `NumberField.IsTotallyReal F` | Direct mathlib structures. |
| Positive-definite integral lattice | `NumberFieldLattice` | Requires a full lattice, nondegenerate form, total positivity away from zero, and algebraic-integral quadratic values. |
| Classic integral lattice | `LatticeClassicIntegral` | Uses the associated bilinear form with the paper's factor-one-half normalization. |
| Field trace Euclideanity | `IsFieldTraceEuclidean t` | Exact `forall x in F, exists y in O_F` strict trace-square predicate. |
| Pointwise non-strict approximation | `ClosedEuclidean cost t` | Direct abstract counterpart. |
| Squared trace covering radius | `SquaredCoveringRadiusSpec cost rhoSq` | Characterizes upper bound and sharpness; it does not construct the geometric radius. |
| Obstructing point | `not_strictEuclidean_of_witness` | Exact logical shape of a point whose every translate has cost at least the threshold. |
| `p`-norm Euclideanity | A second cost supplied to `StrictEuclidean` | Power means and endpoints `p=0,infinity` are not encoded. |
| Field-varying lattice equivalence | `NumberFieldLatticeEquiv` | Records the field isomorphism, semilinear additive bijection, lattice image, and form compatibility; a quotient type is not yet constructed. |
| Quadratic-form isometry in the scaling lemma | `IsometricForms Q Q'` | Function-level abstraction used only for cancellation of the scalar two. |
| Scaling `L^(2)` | `scaleForm 2 Q` | Represents scaling of the form value, not a full lattice structure. |
| Two-dimensional trace norm | `R2`, `dot`, `normSq` | Exact coordinate algebra over the real numbers. |
| Case-I basis | `v1`, `caseI_v2` | Coordinates agree after a real parameter `s` with `s^2=m` is supplied. |
| Case-II basis and third vector | `v1`, `caseII_v2`, `caseII_v3` | Exact coordinate model. |
| Voronoi vertex coefficients | `vertexS`, `vertexT` | Exact solution of the two bisector equations under nonzero determinant. |
| Squared radius formulas | `realQuadraticRadiusSq` and `SquaredCoveringRadiusSpecOver` | Full-plane upper bound and sharpness prove the formulas, rather than assuming them. |
| Square-free positive integer | `IsSquarefreeNat` plus explicit positivity hypotheses | Elementary square-divisor predicate; positivity and `m>1` are theorem hypotheses rather than fields. |
| Real quadratic field | `RealQuadraticAlgebra m := QuadraticAlgebra ℚ m 0` | Concrete degree-two field after the square-free nonsquare proof; independent review should confirm presentation equivalence with the paper's `Q(sqrt m)`. |
| Ring of integers of a real quadratic field | `RealQuadraticIntegers` with `caseIIntegerPointRingEquiv` and `caseIIIntegerPointRingEquiv` | Both standard integral bases are proved exhaustive. |
| Analytic functions `g_s,g_n` | `gClassicReal`, `gIntegralReal` | Exact formulas and asymptotic tails used by the finiteness proof. |
| Equivalence classes in global finiteness | Abstract type `α` in `MainFinitenessFramework` | Intended to be the paper quotient, but no formal quotient/instantiation is supplied; this is a material gap. |

Scale, norm, volume ideals and the Minkowski covolume of a general
number-field lattice are not yet constructed as concrete Lean objects in the
finiteness development. The framework uses integral volume ideals and their
norms only through explicit fields.
