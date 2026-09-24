# Literature route for the remaining Odlyzko zero term

## Exact zero count located

Hasanalizade, Shen, and Wong, [*Counting zeros of Dedekind zeta functions*,
Corollary 1.2 (2021)](https://arxiv.org/pdf/2102.04663), define `N_K(T)` as
the number of zeros `rho = beta + i gamma` with `0 < beta < 1` and
`|gamma| <= T`, counted **with multiplicity**. For every `T >= 1` they prove

```text
|N_K(T) - (T/pi) log(d_K (T/(2 pi e))^n_K)|
  <= 0.228 (log d_K + n_K log T) + 23.108 n_K + 4.520.
```

Here `d_K` is the positive absolute field discriminant and `n_K` its degree.
The 2021 paper notes and repairs an error in an earlier explicit estimate of
Trudgian; its Corollary 1.2 is the count used here. The source also records
the completed zeta function and its functional equation in equations
(2.1)--(2.2), but these are *recalled*, not formalized in our Lean package.
The authors state after Corollary 1.2 that their explicit constants were
obtained by direct numerical computation with Maple; they do not carry out
the interval analysis used in related work. A fully kernel-checked rebuild
of those decimal constants would therefore need a separate certified
numerical argument. The coarse summability criterion does not need their
optimized constants, so a future symbolic `O(T log T)` proof is another route.

## Checked reduction in Lean

`V15OdlyzkoZeroCountLiterature.lean` records the exact absolute-error form of
Corollary 1.2 as `V15HasanalizadeShenWongCorollary12Input`. It models
multiple zeros by distinct *occurrences*, since a set of complex values would
lose multiplicity. The following deductions are Lean theorems:

1. `v15HasanalizadeShenWong_publishedUpper_of_corollary12` takes the upper
   half of the source inequality, and
   `v15HasanalizadeShenWong_log_main_term` expands its main logarithm exactly.
2. `v15HasanalizadeShenWong_pairCount_of_allZeroCount` transfers a bound on
   all zero occurrences to an injectively chosen sequence of conjugate-pair
   representatives; the representative count is no larger than the total.
3. `v15OdlyzkoZeroCountLargeHeightLogBound_of_HSW` derives, for `T >= 1`,
   a deliberately coarse bound
   `N_pair(T) <= (24 n_K + 5) + 3(log d_K + n_K) T log(2+T)`.
4. `v15OdlyzkoZeroCountLogBound_of_largeHeight` uses the finite set at
   `T = 1` to handle `0 <= T < 1`, increasing the constant term by
   `3(log d_K+n_K) log 3`.
5. `v15OdlyzkoZeroCountBound_of_HSW_published` combines these steps into
   the quadratic count required by the existing paired-zero convergence
   criterion. The argument uses `log(2+T) >= log 3 >= 2/3` for `T >= 1`.

The cited zero-count theorem itself is **still an external analytic input**.
`V15DedekindZetaZeros.lean` now defines an entire continuation of
`(s-1) ζ_K(s)` as an explicit structure. Existence of that continuation is
now proved in `V15DedekindZetaConstructed.lean` from the vendored number-field theta/Mellin development. Using mathlib's class-number-formula residue, Lean proves that
any such continuation is nonzero; the analytic identity theorem then makes
it unique. Its zero set is closed and discrete, so every compact region has
finitely many distinct zero positions. A sigma type gives each critical-strip
zero exactly as many occurrences as its analytic order. Lean proves that
the occurrence set at every finite height is finite, including the possible
boundary heights.

`V15DedekindZetaConjugation.lean` proves that real ideal-norm coefficients
force the Dirichlet series to commute with conjugation. Uniqueness then
transfers this identity to any entire regularization. Lean also proves that
conjugation preserves analytic order and gives an involution on actual
zero occurrences that preserves each finite-height set.

`V15DedekindZetaZeroHeight.lean` now constructs a finite-height exhaustion
of all multiplicity-aware occurrences and proves that their type is
countable. Local finiteness gives a right interval after every height with
no new occurrences. Its `bound_of_regular_heights` theorem uses that
interval and continuity to extend a bound from heights with no zero on the
boundary to every `T >= 1`. The field-specific
`HSWFieldInput_of_regular_heights` instantiates this with the precise main
term and decimal constants of Corollary 1.2. The inequality at regular
heights remains an explicit input. See the
[classical-source map](18_classical_analytic_sources.md).

The new `HSWFieldInput` fixes the count parameters to the field's actual
absolute discriminant and degree. Only the numerical inequality remains an
external premise; Lean constructs the finite set required by the older
Corollary 1.2 interface and derives the quadratic bound for any injective
occurrence sequence. With a height ordering and the proved conjugation
symmetry, the exact Odlyzko transform has a convergent paired series.
An infinite ordered sequence of representatives and the HSW inequality
have not been proved.

The newer `V15DedekindZetaUnorderedZeros.lean` removes the first requirement
from the source-formula route. It partitions the actual occurrence type by
integer height and proves that a quadratic all-height count together with
the already-proved fourth-power decay makes the direct `tsum` absolutely
convergent. `quadraticCount_of_HSWField` derives that count from the exact
HSW input, including `0 <= T < 1`; `phi_summable_of_HSWRegular` also uses the
proved regular-height transfer. The endpoint
`v15_odlyzkoTable4ExplicitCorrectionInput_of_unorderedZeros` uses the direct
zero sum and no ordered enumeration. HSW's inequality and the explicit
formula remain named analytic hypotheses.

`V15DedekindZetaCompletion.lean` identifies the factor in HSW (2.1) with
mathlib's `Gammaℝ` and `Gammaℂ`, proves its nonvanishing and analyticity in
the open critical strip, and proves equality of zero positions and analytic
zero orders with the pole-removed regularization there. These results are
conditional on the entire regularization and do not prove a global
functional equation or HSW's numerical bound.

## Transform decay and entire zeta continuation now proved; further global theory remains

For the transform estimate, the pinned mathlib module
[`FourierTransformDeriv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/FourierTransformDeriv.html)
provides `Real.fourier_iteratedDeriv`. The subsequent
[`fourth-decay proof`](17_odlyzko_fourth_decay.md) establishes global `C^4`
regularity, fourth-derivative integrability, uniform closed-strip `L^1`
bounds, and the exact `|t|^{-4}` Fourier estimate. Thus the transform decay
premise has been discharged in Lean for the printed `b=4` kernel.

For the remaining completed-zeta functional equation, mathlib's
[`WeakFEPair`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/AbstractFuncEq.html)
already supplies a **generic** Mellin-transform continuation and functional
equation. The pinned
[`DedekindZeta`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/DedekindZeta.html)
module gives the ideal-norm Dirichlet series and the right-hand residue at
one. The vendored number-field theta/Poisson modules now prove the entire
regularization and its agreement with that series on `Re(s)>1`; their
dual-ideal class reindexing has not yet yielded a global functional equation.
Hasanalizade--Shen--Wong, equations (2.1)--(2.2), fixes
the gamma-factor normalization to match. Odlyzko's
[1990 survey, equations (2.2)--(2.6)](https://www.numdam.org/item/JTNB_1990__2_1_119_0.pdf)
then provides the source normalization for the explicit formula. This is a
substantial separate development: a growth or sharp zero-count estimate,
the contour or distribution argument, and the identity for the exact
`b=4` test function still need Lean proofs.

## Practical next proof boundary

The next independent targets are proving the completed-zeta functional
equation and obtaining a coarse count from growth or HSW's sharp count from an
argument-principle proof. The pinned mathlib contains Jensen's inequality
in `Mathlib.Analysis.Complex.JensenFormula`; using it still requires a
global growth estimate; the bridge from divisor sums to the project's
multiplicity-aware occurrences is already proved. The Stark/Weil explicit formula remains a
separate, larger source-to-Lean gap.
