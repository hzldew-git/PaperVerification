# Analytic boundary progress, ordered by proof difficulty

This note records the status of the four tasks discussed after the classical
source review. A compiled conditional theorem is a deduction from its named
premises; it does not prove those premises.

| Task | New Lean result | Remaining theorem |
| --- | --- | --- |
| Direct zero sum without ordered enumeration | `V15DedekindZetaUnorderedZeros.lean` proves absolute convergence and nonnegative real part of the direct `tsum` over actual multiplicity-aware strip-zero occurrences from a quadratic height count. Its Table 4 reduction accepts this sum directly. | The Jensen module derives the required count from a circle-growth estimate. That growth estimate and the Stark/Weil source identity remain inputs. |
| Coarse and sharp zero count | `V15DedekindZetaJensenCount.lean` identifies the divisor in a ball with analytic zero multiplicities, bounds actual strip-zero occurrences by that divisor, applies mathlib's Jensen inequality, and proves a quadratic all-height count from an explicit quadratic exponential circle-growth premise. This suffices for absolute convergence and nonnegativity of the direct zero sum. `quadraticCount_of_HSWNumeric` separately reduces the published sharp count to the same coarse interface. | Prove the circle-growth premise for an actual entire regularization, or formalize HSW's argument-principle estimates. Jensen closes the count deduction from growth, but it does not prove the growth premise. |
| Entire continuation and functional equation | `DedekindZeta/ZetaRegularization.lean` constructs an entire continuation of `(s-1) ζ_K(s)` from number-field theta/Mellin theory, and `V15DedekindZetaConstructed.lean` instantiates the zero-theory interface. `V15DedekindZetaCompletion.lean` identifies HSW's Gamma factor with mathlib's `Gammaℝ`/`Gammaℂ`, proves the multiplier nonzero and analytic on the positive-real-part half-plane, and proves equality of critical-strip zero positions and analytic multiplicities with the pole-removed regularization. | Prove the global completed-zeta functional equation and a sufficient circle-growth bound. The regularization now exists as a concrete Lean value. |
| Stark/Weil explicit formula | `v15_odlyzkoTable4ExplicitCorrectionInput_of_unorderedZeros` connects the now-convergent direct zero sum to the existing source-normalized Table 4 reduction. | Prove the explicit formula itself, including the global contour or distribution argument, zero and prime terms, and equality with the present kernel. Its identity remains a named hypothesis. |

The source path is [Neukirch VII and Tate IV for continuation and the
functional equation, HSW Sections 2–4 for zero counting, and Odlyzko/Poitou
for the explicit formula](18_classical_analytic_sources.md). The order of
the last three constructions is constrained by their dependencies: an
independent HSW count and the explicit formula require global zeta theory.
The direct-sum result removes the separate ordered-enumeration obligation.
The Jensen route also removes HSW's sharp numerical count as a necessary
premise for the convergence of the direct zero sum. It does not replace the
completed-zeta functional equation, a growth estimate, or the Stark/Weil identity.
