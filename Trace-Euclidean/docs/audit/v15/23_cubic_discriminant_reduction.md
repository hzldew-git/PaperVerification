# Cubic discriminant reduction

## Source theorem and normalization

Jacques Martinet's
[*Small Discriminants, Class Numbers, and the Geometry of Numbers*](https://jamartin.perso.math.cnrs.fr/Othertexts/discgeom.pdf),
Corollary 3.5, records Hunter's theorem in the form

```text
S_K(theta) <= n gamma_(n-1) (|D_K| / n)^(1/(n-1)),
```

for an algebraic integer `theta` outside `Q`. In degree three,
`gamma_2 = 2 / sqrt(3)`, so this becomes
`S_K(theta) <= 2 sqrt(|D_K|)`. Under the contradiction hypothesis
`|D_K| < 49`, it gives `S_K(theta) < 14`, hence the weaker bound `< 16`
used by the Lean finite reduction. Integer translation and, if necessary,
negation normalize the trace to `0` or `1` without changing `S_K(theta)`.
Lean proves these translation and negation identities directly, including
preservation of the discriminant and the absence of an integer root.

For the monic cubic

```text
X^3 - s1 X^2 + s2 X - s3,
```

the conjugate spread is `2 s1^2 - 6 s2`. Since the field is totally real,
the polynomial discriminant is positive. Since the degree is prime and the
Hunter element is outside `Q`, it generates the cubic field and its polynomial
has no integer root. Its discriminant is the square of the order index times
the field discriminant.

## Lean result

`V15DegreeThreeDiscriminant` proves by exact integer arithmetic that

```text
s1 in {0,1},  0 < 2 s1^2 - 6 s2 < 16,
positive discriminant, and no integer root
```

force the polynomial discriminant to equal `49`. The inequalities leave five
coefficient pairs `(s1,s2)`; the root and positivity conditions eliminate all
but `X^3 - X^2 - 2X + 1`.

The theorem `v15_normalize_cubic_coefficients` starts from arbitrary integral
cubic coefficients. It uses Euclidean division of the trace coefficient by
three, translates the root, and negates it in the remainder-two case. Thus
the Hunter certificate no longer assumes `s1 in {0,1}`; normalization is a
kernel-checked consequence.

The theorem `v15_cubic_spread_pos_of_discriminant_pos` proves the depressed
cubic identity and derives positive spread from positive discriminant. Since
total reality and the index relation make the polynomial discriminant
positive, the Hunter certificate also no longer assumes the lower spread
inequality.

`V15HunterGeometry` also instantiates Lean's formal Minkowski convex-body
theorem on the radius `4 / sqrt(3)` disk in a two-dimensional projected
lattice. It proves from `pi > 3.14` that covolume below `7 / sqrt(3)` supplies
the required strict area inequality, then produces a nonzero vector satisfying
`3 * ‖x‖^2 < 16`. Its intrinsic form chooses the fundamental domain from a
full `Z`-lattice automatically.

`V15HunterNumberField` specializes mathlib's discriminant-covolume theorem.
For a totally real field, Lean proves that the full integer-ring lattice has
covolume `sqrt(|D_K|)` in both the mixed and Euclidean Minkowski models. Under
`|D_K| < 49` this is below `7`, and division by `sqrt(3)` gives exactly the
projected-covolume inequality required by the disk theorem once the projection
formula is established.

The compatibility theorem
`v15_coded_degree_three_discriminant_ge_49_of_hunterCertificate` requests the
certificate only under the contradiction hypothesis `|D_K| < 49`; it is not a
false uniform short-vector assertion for all cubic fields.

## Closed bridge

The former certificate boundary is now discharged by the following Lean
modules.

- `V15HunterProjection` proves the centered Gram-determinant and projected
  covolume identities.
- `V15PrimitiveBasis` extends a primitive integer-ring vector to a basis, and
  `V15HunterNumberFieldProjection` chooses such a basis beginning with `1`,
  constructs the projected full lattice, applies the disk theorem, lifts the
  short vector to an algebraic integer, and proves that it generates the cubic
  field.
- `V15CubicPowerBasis` proves the cubic companion and derivative matrices,
  their discriminant formula, and the two trace identities.
- `V15CubicGeneratorArithmetic` proves that the polynomial discriminant is a
  positive integer square times the field discriminant.
- `V15CubicGeneratorSpread` identifies the cubic spread with three times the
  squared norm of the centered Euclidean embedding.
- `v15_degree_three_hunterCertificate` assembles these results, while
  `v15_coded_degree_three_discriminant_ge_49` proves `|D_K| >= 49` without an
  external cubic premise.

Finally,
`v15_sectionFourDiscriminantInput_of_degreeFourToEleven_closed` and its two
table-membership corollaries substitute the proved certificate into the
Section 4 chain. The subsequent quartic reduction is recorded separately in
`24_quartic_discriminant_reduction.md`.
