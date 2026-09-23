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
not asserted. Using mathlib's class-number-formula residue, Lean proves that
any such continuation is nonzero; the analytic identity theorem then makes
it unique. Its zero set is closed and discrete, so every compact region has
finitely many distinct zero positions. A sigma type gives each critical-strip
zero exactly as many occurrences as its analytic order. Lean proves that
the occurrence set at every finite height is finite, including the possible
boundary heights.

The new `HSWFieldInput` fixes the count parameters to the field's actual
absolute discriminant and degree. Only the numerical inequality remains an
external premise; Lean constructs the finite set required by the older
Corollary 1.2 interface and derives the quadratic bound for any injective
occurrence sequence. With a height ordering and conjugation symmetry as
explicit hypotheses, the exact Odlyzko transform has a convergent paired
series. An infinite ordered sequence of representatives, conjugation
symmetry of the continuation, and the HSW inequality have not been proved.

## Transform decay now proved; global zeta remains

For the transform estimate, the pinned mathlib module
[`FourierTransformDeriv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/FourierTransformDeriv.html)
provides `Real.fourier_iteratedDeriv`. The subsequent
[`fourth-decay proof`](17_odlyzko_fourth_decay.md) establishes global `C^4`
regularity, fourth-derivative integrability, uniform closed-strip `L^1`
bounds, and the exact `|t|^{-4}` Fourier estimate. Thus the transform decay
premise has been discharged in Lean for the printed `b=4` kernel.

For global zeta continuation and the functional equation, mathlib's
[`WeakFEPair`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/AbstractFuncEq.html)
already supplies a **generic** Mellin-transform continuation and functional
equation. The pinned
[`DedekindZeta`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/DedekindZeta.html)
module gives the ideal-norm Dirichlet series and the right-hand residue at
one, but no concrete number-field theta/Poisson data to instantiate that
generic framework. Hasanalizade--Shen--Wong, equations (2.1)--(2.2), fixes
the gamma-factor normalization to match. Odlyzko's
[1990 survey, equations (2.2)--(2.6)](https://www.numdam.org/item/JTNB_1990__2_1_119_0.pdf)
then provides the source normalization for the explicit formula. This is a
substantial separate development: the completed zeta function, its zeros,
the contour or distribution argument, and the identity for the exact
`b=4` test function still need Lean proofs.

## Practical next proof boundary

The next independent target is constructing the entire regularization from
number-field theta/Poisson data, proving its conjugation symmetry and
functional equation, and obtaining the HSW count from an argument-principle
proof. A height-ordered enumeration must then identify every required
conjugate pair. The Stark/Weil explicit formula remains a separate, larger
source-to-Lean gap.
