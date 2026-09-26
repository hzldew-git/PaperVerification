# Quartic discriminant reduction

## Target

The degree-four row used in Section 4 is the lower bound

```text
|D_K| >= 725
```

for every totally real quartic field `K`. The Lean development proves this
statement unconditionally. It does not assume the degree-four minimum, a
Hermite constant, a primitive-generator premise, or a relative-different
bound in its strongest endpoint.

## Finite quartic arithmetic

For

```text
X^4 - s1 X^3 + s2 X^2 - s3 X + s4,
```

`V15DegreeFourDiscriminant` defines the centered conjugate spread, the third
leading Hermite minor, and the quartic discriminant as exact integer
polynomials. Lean proves the effects of integral translation and root
negation. These operations preserve the spread, Hermite minor, discriminant,
absence of an integral root, and absence of a monic quadratic factor. Hence
the trace coefficient may be normalized to `s1` in `{0,1,2}`.

The Hunter spread bounds imply `-4 <= s2 <= 2`. With

```text
-24 <= s3 <= 24,  -4 <= s4 <= 4,
0 < spread < 29,
0 < third Hermite minor,
0 < discriminant,
```

the theorem `v15_normalized_quartic_discriminant_eq_725` checks the complete
finite coefficient box in the Lean kernel. Every row that has neither an
integral root nor a monic quadratic factor has discriminant exactly `725`.
This computation uses `decide`, not `native_decide`.

The coefficient box is no longer an input. The theorem
`v15_quartic_s3_s4_bounds_of_normalized` proves

```text
-24 <= s3 <= 24,  -4 <= s4 <= 4
```

from normalized trace, `0 < spread < 29`, positivity of the third Hermite
minor, and positivity of the discriminant. Its proof uses exact integer
nonlinear arithmetic and a finite elimination of the remaining `s3` values.

## Bridge to an algebraic integer

The modules `V15QuarticPowerBasis`, `V15QuarticGeneratorArithmetic`,
`V15QuarticGeneratorNormalization`, `V15QuarticGeneratorSpread`, and
`V15QuarticHermite` prove the following facts for a primitive integral
generator `a` of a quartic number field.

- The explicit quartic is the integer minpoly of `a`.
- Its power-basis discriminant equals the displayed quartic polynomial.
- Primitivity rules out both an integral root and a monic quadratic
  factorization.
- The polynomial discriminant is the square of a positive index times the
  field discriminant.
- The coefficient spread is four times the squared norm of the centered
  Minkowski embedding.
- The spread is the Gram determinant of the embedded vectors `1,a`, hence is
  strictly positive.
- The displayed third Hermite minor is the Gram determinant of the embedded
  vectors `1,a,a^2`, hence is strictly positive.
- Integral translation and the required translation-after-negation are
  performed on the actual algebraic integer, preserve primitivity, spread,
  Hermite minor, and discriminant, and produce an actual normalized generator
  with trace coefficient in `{0,1,2}`.

Thus irreducibility, positivity of the spread, positivity of the third Hermite
minor, positivity of the polynomial discriminant, and the index relation no
longer occur in the residual hypothesis. Neither do trace normalization or the
`s3,s4` bounds.

## Projected lattice

`V15QuarticHunterProjection` and
`V15QuarticHunterNumberFieldProjection` formalize the geometric step before
the primitive-generator issue.

- Centering the last three vectors of an integral basis whose first vector is
  `1` gives a basis of the three-dimensional orthogonal complement.
- The projected Gram determinant times `||1||^2 = 4` equals the full Gram
  determinant, so the projected covolume is exactly half the full covolume.
- Projected integral vectors lift back to algebraic integers, and every
  nonzero projected vector lifts outside `Q`.
- `V15HermiteThreeInput` states the sharp three-dimensional Hermite bound in
  the root-free form `||x||^6 <= 2*covolume^2`.
- Under `|D_K| < 725`, that bound produces `4*||x||^2 < 29` entirely inside
  Lean.

The classical fact `gamma_3^3 = 2` itself has not yet been proved in this
project.

An unconditional weaker route is now also formalized. The module
`V15QuarticHunterGeometry` applies the three-dimensional Minkowski
convex-body theorem to the ball of radius `sqrt(35)/2`. Exact rational bounds
for `sqrt(35)`, `sqrt(725)`, and `pi` prove the required strict volume
inequality. After the projection and number-field bridges this gives

```text
4*||x||^2 < 35
```

without `V15HermiteThreeInput`. The corresponding kernel-checked coefficient
search proves that an irreducible normalized quartic then has polynomial
coefficients in exactly the six rows

```text
(0,-4,-1,1), (0,-4,0,1), (0,-4,0,2),
(0,-4,1,1),  (1,-3,-1,1), (2,-2,-3,1).
```

Their polynomial discriminants lie in

```text
{725, 1957, 2048, 2304}.
```

The field-discriminant/index relation eliminates the `725` and `1957` rows
when `29 < |D_K| < 725`, leaving the `2048` and `2304` rows. The module
`V15QuarticOrderMaximality` then proves that the `2048` polynomial is
Eisenstein at `2`, that every algebraic integer belongs to its power order,
and hence that its field discriminant is exactly `2048`. This contradicts
`|D_K| < 725`, so the weak route reduces an actual primitive generator to the
single row `(0,-4,0,1)` of polynomial discriminant `2304`.

For this `2304` row, translating the generator by `-1` produces a polynomial
that is Eisenstein at `2`. Lean consequently proves that `9x` belongs to the
power order for every algebraic integer `x`. The module
`V15QuarticOrderMaximality2304` then writes a reduced relation as

```text
3z = A + B a + C a^2 + D a^3
```

and computes the exact traces of the first, second, and fourth powers. Since
the corresponding traces of `z`, `z^2`, and `z^4` are integers, the resulting
divisibilities force `3` to divide `A,B,C,D`. This proves `3`-saturation.
Applying it twice to the `9x` relation proves that the power order is the full
ring of integers and that the field discriminant is exactly `2304`. Hence the
last normalized row also contradicts `|D_K| < 725`.

## Two-short-vector selection

`V15DegreeFourMinkowskiReduction` packages the preceding arithmetic into a
degree-four theorem conditional on selecting a primitive projected vector of
spread below `35`. `V15QuarticSecondShortVector` closes the geometric part of
that selection. Starting with a nonzero first short vector `x`, it extends `x`
to an integral basis of the projected rank-three lattice, projects away the
line through `x`, applies the two-dimensional Minkowski disk bound, and lifts
a nonzero transverse vector `y`. Both lifts have spread below `35`.

If either lift generates `K`, the power-order argument above gives a
contradiction. Suppose both are imprimitive. Each generated intermediate field
has degree two. The trace-spread bound and the quadratic index-discriminant
identity show that its field discriminant is either `5` or `8`.

`V15QuadraticGeneratorArithmetic` proves that an integral quadratic generator
with a power basis of field discriminant `D` satisfies

```text
(2a - Tr(a))^2 = D.
```

It follows that two such subfields with equal discriminant coincide inside
`K`. Transversality proves that the two subfields are distinct, so their
discriminants must be `5` and `8`. These discriminants are coprime. The
compositum theorem in `V15QuarticSubfieldReduction` then gives

```text
|D_K| = |D_E|^2 |D_F|^2 = 5^2 8^2 = 1600,
```

contradicting `|D_K| < 725`. Thus
`v15_quartic_primitiveShortSelectionThirtyFive` discharges the selection
interface and `v15_coded_degree_four_discriminant_ge_725` proves the desired
bound without an external quartic premise.

## Compatibility routes

The earlier sharp-Hermite, no-proper-subfield, imprimitive-minimum, and
relative-different routes remain in the project for comparison. They are not
dependencies of the unconditional theorem. In particular, the seven-row
relative-different certificate and its input structures no longer mark a
formalization boundary.

## Section 4 endpoint

The strongest Section 4 endpoints are

```text
v15_sectionFourDiscriminantInput_of_degreeFiveToEleven_closed
v15_classic_pair_mem_of_degreeFiveToEleven_closed
v15_integral_pair_mem_of_degreeFiveToEleven_closed.
```

They prove all degree-one through degree-four rows internally. After the
Voight finite-data bridge, their remaining source premises are completeness
of Voight's enumeration through root discriminant 14 for degrees five through
ten and the optimized degree-eleven bound. The quartic
selection and lower-bound theorems add no compiler trust boundary; their axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
