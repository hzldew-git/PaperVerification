# Analytic boundary progress, ordered by proof difficulty

This note records the final status of the four analytic tasks. A compiled
conditional theorem is still only a deduction from its named premises, but the
new closed endpoint below supplies the Table 4 premise without assuming the
source explicit formula.

| Task | Lean result | Status |
| --- | --- | --- |
| Direct zero control without ordered enumeration | `V15DedekindZetaUnorderedZeros.lean` proves absolute convergence and nonnegative real part of the direct `tsum` over multiplicity-aware strip-zero occurrences. `V15OdlyzkoContourFinite.lean` and `V15OdlyzkoContourSequence.lean` additionally work with finite zero sets inside zero-free rectangles. | Closed. The final inequality uses finite nonnegative sums directly; an infinite ordered enumeration is unnecessary. |
| Coarse and sharp zero count | `V15DedekindZetaCompletedJensen.lean` and `V15MellinGrowth.lean` derive a quadratic all-height count from the completed function's proved growth. | The count needed here is closed. The sharper HSW decimal estimate remains optional and unproved. |
| Entire continuation and functional equation | `DedekindZeta/ZetaRegularization.lean`, `DedekindZeta/GlobalContinuation.lean`, and `DedekindZeta/FractionalIdealRescaling.lean` construct the regularization and prove the completed functional equation. | Closed for the current scope. |
| Specialized Stark/Weil contour inequality | `V15DedekindZetaLandau.lean` and `V15DedekindZetaGoodHeights.lean` provide logarithmic-derivative control and zero-free heights. `V15OdlyzkoHorizontalLimit.lean` and `V15OdlyzkoVerticalLimit.lean` prove the contour limits. `V15OdlyzkoEndpointContour.lean` evaluates the endpoint residues as `32/3`. `V15OdlyzkoArchimedeanShift.lean` shifts and evaluates the infinite-place term. `V15OdlyzkoPrimeTransform.lean` evaluates the ordinary-zeta term. `V15OdlyzkoExplicitFormulaClosed.lean` combines these with finite zero-sum positivity. | Closed for the manuscript's unconditional `b=4` test function and the required discriminant inequality. |

The final theorem
`v15Odlyzko_discriminant_log_lower_bound` proves

```text
r_1 * log A_* + 2 * r_2 * log B_* + PrimeCorrection(K) - 32/3
  <= log |D_K|.
```

`v15_odlyzkoTable4ExplicitCorrectionInput_closed` inserts the certified strict
numerical bounds, and `v15_odlyzkoTable4DescriptionInput_closed` performs the
published rounding. The analytic theorems through the logarithmic lower bound
use only `propext`, `Classical.choice`, and `Quot.sound`. The final strict
constants inherit the separately disclosed five `native_decide` dependencies
from `V15OdlyzkoNumerical.abIntegralCertificate`.

The source path remains [Neukirch VII and Tate IV for continuation and the
functional equation, HSW for optional sharp zero counting, and Stark,
Poitou, and Odlyzko for the explicit-formula organization and
normalization](18_classical_analytic_sources.md). The project proves the
specialization needed here; it does not claim a reusable general Weil explicit
formula for arbitrary test functions.
