# Quartic discriminant reduction

## Target

The degree-four row used in Section 4 is the lower bound

```text
|D_K| >= 725
```

for every totally real quartic field `K`. The Lean development now reduces
this statement to one explicit Hunter-generator premise. It does not assume
the degree-four minimum as an opaque table entry in its strongest endpoint.

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

## Bridge to an algebraic integer

The modules `V15QuarticPowerBasis`, `V15QuarticGeneratorArithmetic`,
`V15QuarticGeneratorSpread`, and `V15QuarticHermite` prove the following facts
for a primitive integral generator `a` of a quartic number field.

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

Thus irreducibility, positivity of the spread, positivity of the third Hermite
minor, positivity of the polynomial discriminant, and the index relation no
longer occur in the residual hypothesis.

## Section 4 endpoint

`V15DegreeFourPrimitiveGeneratorInput` asks that every totally real quartic
field with `|D_K| < 725` contain a primitive algebraic integer satisfying the
normalized trace coefficient, the displayed `s3` and `s4` bounds, and the
strict upper spread bound. Lean proves

```text
V15DegreeFourPrimitiveGeneratorInput
  -> V15DegreeFourHunterCertificateInput
  -> |D_K| >= 725.
```

The endpoints

```text
v15_sectionFourDiscriminantInput_of_degreeFourPrimitiveGenerator_closed
v15_classic_pair_mem_of_degreeFourPrimitiveGenerator_closed
v15_integral_pair_mem_of_degreeFourPrimitiveGenerator_closed
```

then require exact minimum-discriminant data only in degrees five through
nine, followed by the separate degree-ten and degree-eleven inputs.

## Remaining mathematical boundary

The remaining task is to construct the primitive generator with the stated
bounds. In a quartic field, a nonrational Hunter short vector need not be
primitive: in an imprimitive quartic field it may lie in a quadratic subfield.
The proof must either choose a short vector outside every proper subfield or
modify one while retaining the strict spread bound. It must also derive the
`s3` and `s4` inequalities from the real conjugates. Spread positivity and the
third-Hermite-minor inequality are now consequences of Gram-matrix positivity
inside Lean.

Once this premise is proved, no separate degree-four minimum-discriminant table
input remains in the strengthened Section 4 chain. The current code and axiom
audit introduce no new compiler trust boundary beyond the separately disclosed
`A,B` numerical certificate.
