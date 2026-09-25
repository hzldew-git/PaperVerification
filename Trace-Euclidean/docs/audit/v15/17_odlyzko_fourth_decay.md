# Fourth-power decay of the exact Odlyzko transform

The v15 unconditional `b = 4` test function is the exact printed function
`F(x) = H(x/4)/cosh(x/2)`, supported on `[-8,8]`. The source-normalized
transform is `Phi(s) = integral F(x) exp((s-1/2)x) dx`.

## Lean proof now completed

`V15OdlyzkoFourthRegularity.lean` differentiates the printed trigonometric
core four times. Lean checks the derivative values at zero and two: the first
and third derivatives vanish at zero, and all derivatives through order four
vanish at two. A general one-dimensional gluing theorem then joins the
core across the right support endpoint, the reflection point, and the left
support endpoint. This proves `v15OdlyzkoH_contDiff_four` and, after division
by the strictly positive hyperbolic cosine, `v15OdlyzkoF4_contDiff_four`.

`V15OdlyzkoFourthDecayCriterion.lean` proves `C^4` regularity for every
exponentially tilted function `exp(a*x) F(x)`, including `a = +/-1/2`. Its
fourth derivative is identified by the finite Leibniz sum, and that sum is
jointly continuous in `(a,x)`. Compactness of
`[-1/2,1/2] x [-8,8]` gives finite uniform `L^1` bounds for both the
tilted kernel and its fourth derivative. Differentiation preserves the
common compact support.

Mathlib's `Real.fourier_iteratedDeriv` then gives four integrations by parts.
Lean checks the factor of `2*pi` in the paper-to-mathlib frequency conversion,
so the Fourier multiplier is exactly `|Im(s)|^4`. Combining the zero-frequency
and fourth-derivative bounds proves
`v15OdlyzkoPhi_exists_fourthPowerBound`:

```text
exists D >= 0, for all s with 0 <= Re(s) <= 1,
  ||Phi(s)|| <= D / (1 + |Im(s)|)^4.
```

The constant `D` is finite and uniform; it is obtained by compactness rather
than evaluated numerically. No numerical value is needed to prove convergence
of the zero contribution. `v15OdlyzkoPhi_conj_pair_summable_of_ordinalBound`
therefore needs only a quadratic ordinal bound for the zero enumeration.
`v15_odlyzkoTable4ExplicitCorrectionInput_of_count` removes the decay
premise from the conditional Table 4 reduction.

## Remaining analytic boundary

The theorem above concerns the exact source transform and does not assume
an actual zero count or Odlyzko's explicit formula. The Dedekind-zeta
continuation is now constructed in
`V15DedekindZetaConstructed.lean`. `V15DedekindZetaZeros.lean` defines
zero occurrences from analytic order for any entire regularization of
`(s-1) ζ_K(s)`. Lean proves uniqueness of such a regularization, discreteness
and finite-height finiteness of its zeros. `V15DedekindZetaConjugation.lean` proves
conjugation symmetry and its action on multiplicity-aware zero occurrences
from any entire regularization. `V15MellinGrowth.lean` proves quadratic
completed-function growth, obtains a quadratic count through Jensen, and
proves absolute convergence of the direct zero-occurrence sum. The sharp HSW
inequality remains unproved but is unnecessary here; no ordered enumeration
is required. The Stark/Weil explicit formula remains unproved. The global
completed-zeta functional equation is proved in
`DedekindZeta.FractionalIdealRescaling`.
Consequently the four reviewed v15 main results retain their
documented `PROVISIONAL_MATCH` status.
