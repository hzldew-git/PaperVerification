# Formal declaration inventory

This inventory is organized by Lean module and records what each declaration
proves without assigning a paper match.

## `Basic`

| Declaration | Formal content |
|---|---|
| `StrictEuclidean` | Abstract `forall x, exists y, cost x y < t` predicate. |
| `ClosedEuclidean` | Abstract non-strict counterpart. |
| `SquaredCoveringRadiusSpec` | Packages an upper bound and sharp failure of every smaller bound. |
| `strictEuclidean_of_radius_lt` | A radius bound strictly below `t` gives strict Euclideanity. |
| `radius_le_of_strictEuclidean` | Strict Euclideanity gives radius at most `t`. |
| `not_strictEuclidean_of_witness` | A universal lower-cost witness obstructs strict Euclideanity. |
| `strictEuclidean_of_pointwise_le` | Pointwise cost domination transfers strict Euclideanity. |
| `pNormEuclidean_imp_traceEuclidean` | The power-mean implication after the pointwise inequality is supplied. |

## `Scaling`

| Declaration | Formal content |
|---|---|
| `PreservesForm`, `scaleForm`, `IsometricForms` | Function-level form preservation through a type equivalence. |
| `preserves_scaled_iff` | A nonzero scalar can be cancelled from the preservation equation. |
| `isometric_scaled_iff` | Nonzero scaling preserves and reflects existence of a form-preserving equivalence. |
| `two_scaled_isometric_iff` | Real-valued factor-two specialization. |

## `AnalyticCriticalPoint`

| Declaration | Formal content |
|---|---|
| `stationaryPolynomial_pos` | Positivity of the polynomial controlling the stationary derivative for `b>0,y>=1`. |
| `stationaryDerivative_identity` | Exact rational identity for `y/(y+b)^2-1`. |
| `stationaryDerivative_neg` | Strict negativity on the stated domain. |
| `criticalPoint_hessian_identity` | Algebraic Hessian determinant reduction from two differentiated identities. |
| `criticalPoint_hessian_negative` | The determinant is negative when `z>0`, `gxx<0`, and the stationary derivative is negative. |

## `Finiteness`

| Declaration | Formal content |
|---|---|
| `finite_positive_of_eventually_nonpositive` | Eventual nonpositivity leaves finitely many positive natural inputs. |
| `finite_positive_of_tendsto_atTop_atBot` | Convergence to minus infinity implies that finiteness. |
| `finite_parameter_pairs_of_bounds` | A subset of a finite natural-number rectangle is finite. |
| `finite_sigma_family` | A finite index set with finite fibers has finite dependent sum. |

## `VoronoiAlgebra`

The module defines explicit real two-vectors, dot products, norm squares,
Case-I and Case-II basis vectors, vertex coefficients, and a vertex norm
expression. It proves:

- `caseI_gram` and `caseII_gram`: exact Gram identities;
- `vertex_coefficients_solve`: the two bisector equations;
- `voronoiVertexNorm_formula`: the rational norm formula;
- `caseI_vertexNorm`: the rectangular midpoint norm;
- `caseII_vertexNorm_first` and `caseII_vertexNorm_middle`: the two
  nontrivial hexagonal vertex norms;
- `caseII_radius_algebra`: simplification to `(m+1)^2/(8m)`.

## `QuadraticArithmetic`

The module defines the two rational candidate radius formulas and an elementary
square-free predicate. It proves the Case-I candidates, the Case-II polynomial
bound and upper bound `m<=13`, the square-free congruence candidates
`m=5 or 13`, the half-integer lower bound and `m=3` obstruction, the exact
radii at `m=2,5,13`, and strict inequality of those radii below two.

## Public audit entry point

`TraceEuclideanTest/MainTheoremAudit.lean` checks 13 selected endpoint
signatures and prints their transitive axiom dependencies. It is an audit
module, not an additional mathematical assumption.
