# Odlyzko `b = 4` contour closure

## Scope

The Lean development proves the specialized unconditional discriminant
inequality needed for the manuscript's `b = 4` Table 4 route.  It does not
claim a reusable Stark--Weil formula for arbitrary test functions.

For every number field `K`, the endpoint
`v15Odlyzko_discriminant_log_lower_bound` proves

```text
r_1 log(A_*) + 2 r_2 log(B_*) + PrimeCorrection(K) - 32/3
  <= log |D_K|.
```

The prime correction is nonnegative.  The certified strict bounds
`log(36.347) < log(A_*)` and `log(16.593) < log(B_*)` therefore produce
`v15_odlyzkoTable4ExplicitCorrectionInput_closed` and the rounded
`v15_odlyzkoTable4DescriptionInput_closed`.

## Proof chain

1. `DedekindZeta.GlobalContinuation` constructs the pole-removed completed
   Dedekind zeta and proves its functional equation.
2. `V15MellinGrowth`, `V15DedekindZetaLandau`, and
   `V15DedekindZetaGoodHeights` give the growth, logarithmic-derivative
   control, finite zero counts, and zero-free contour heights needed by the
   contour argument.
3. `V15OdlyzkoContourFinite` expresses the weighted argument principle on
   finite rectangles.  Its zero contribution counts multiplicity and has
   nonnegative real part for the manuscript's kernel.
4. `V15OdlyzkoHorizontalLimit` makes the horizontal edges vanish, and
   `V15OdlyzkoVerticalLimit` identifies the limit of the two vertical edges.
5. `V15OdlyzkoEndpointContour` proves absolute integrability and evaluates
   the normalized endpoint contribution as exactly `32/3`.
6. `V15OdlyzkoArchimedeanShift` shifts the Gamma-factor line and evaluates
   the number-field archimedean contribution as
   `log |D_K| - r_1 log(A_*) - 2 r_2 log(B_*)`.
7. `V15OdlyzkoPrimeTransform` evaluates the ordinary-zeta line integral as
   minus the complete prime-ideal correction.
8. `V15OdlyzkoExplicitFormulaClosed` combines these identities and finite
   zero-sum positivity to prove the displayed discriminant inequality.

This finite-contour route avoids an ordered infinite enumeration of zeros and
does not assume the source explicit-formula identity as a premise.

## Downstream endpoints

- `v15_odlyzkoTable4DescriptionInput_closed` supplies the full rounded Table
  4 interface used by the project.
- `v15_sectionFourDiscriminantInput_of_degreeFourPrimitiveGenerator_closed`
  replaces the degree-four exact-minimum row by the explicit primitive Hunter
  short-generator premise. The cited exact-minimum data then begin in degree
  five; degrees one through three, the quartic projection, coefficient bounds,
  algebra and finite enumeration after that premise, and the Table 4 range are
  internal.
- `v15_classic_finite_closed`, `v15_integral_finite_closed`, and
  `v15_pnorm_finite_closed` discharge the Table 4 premise from the global
  finiteness endpoints.

## Trust boundary

The contour, endpoint, archimedean, prime-transform, and logarithmic
discriminant theorems reduce only to `propext`, `Classical.choice`, and
`Quot.sound`.  The final strict numerical Table 4 theorem additionally
inherits five disclosed native-computation dependencies from the certified
`A,B` interval bounds: one Euler--Mascheroni bound, two integral-core bounds,
and the two final strict scalar comparisons.

There is no `sorry`, project axiom, or assumed explicit-formula theorem in
this chain. Independent mathematical and Lean review remains unsigned. The
quartic primitive-short-generator premise and degree `5`--`11` source estimates
remain outside the closed proof, and
the sharper HSW numerical zero-count theorem remains an optional unformalized
result because the proved quadratic Jensen count is sufficient here.
