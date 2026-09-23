# Analytic boundary progress, ordered by proof difficulty

This note records the status of the four tasks discussed after the classical
source review. A compiled conditional theorem is a deduction from its named
premises; it does not prove those premises.

| Task | New Lean result | Remaining theorem |
| --- | --- | --- |
| Direct zero sum without ordered enumeration | `V15DedekindZetaUnorderedZeros.lean` proves absolute convergence and nonnegative real part of the direct `tsum` over actual multiplicity-aware strip-zero occurrences from a quadratic height count. Its Table 4 reduction accepts this sum directly. | The quadratic count and Stark/Weil source identity are inputs. |
| Coarse and sharp zero count | `quadraticCount_of_HSWNumeric` proves that the exact [HSW Corollary 1.2](https://arxiv.org/pdf/2102.04663) bound implies a quadratic all-height bound, including heights below one. The prior regular-height transfer supplies the estimate at boundary heights. | Prove a growth bound for a completed zeta function and use the pinned mathlib's `AnalyticOnNhd.sum_divisor_le` Jensen inequality to obtain a coarse count; separately formalize HSW's argument-principle estimates for the sharp constants. Neither analytic count is currently proved. |
| Entire continuation and functional equation | `V15DedekindZetaCompletion.lean` identifies HSW's Gamma factor with mathlib's `Gammaℝ`/`Gammaℂ`, proves the multiplier nonzero and analytic on the positive-real-part half-plane, and proves equality of critical-strip zero positions and analytic multiplicities with the pole-removed regularization. | Construct the entire regularization from number-field theta/Poisson and Mellin theory; then prove the global functional equation. Current completed expression is conditional on the regularization. |
| Stark/Weil explicit formula | `v15_odlyzkoTable4ExplicitCorrectionInput_of_unorderedZeros` connects the now-convergent direct zero sum to the existing source-normalized Table 4 reduction. | Prove the explicit formula itself, including the global contour or distribution argument, zero and prime terms, and equality with the present kernel. Its identity remains a named hypothesis. |

The source path is [Neukirch VII and Tate IV for continuation and the
functional equation, HSW Sections 2–4 for zero counting, and Odlyzko/Poitou
for the explicit formula](18_classical_analytic_sources.md). The order of
the last three constructions is constrained by their dependencies: an
independent HSW count and the explicit formula require global zeta theory.
The direct-sum result removes the separate ordered-enumeration obligation.
