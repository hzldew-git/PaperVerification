# Voight enumeration and general Hunter bridge

## Source and data

John Voight's
[*Enumeration of totally real number fields of bounded root discriminant*](https://jvoight.github.io/articles/ANTS144-fixed-errata-052714.pdf)
states that the totally real fields of root discriminant at most 14 have
degree at most nine. The public table site linked by the author now returns
404, so the package records Internet Archive copies under `inputs/voight`.
Their archive timestamps and SHA-256 digests appear in that directory's
README.

`tools/generate_voight_discriminant_data.py` verifies all six recorded
digests. For the degree 5--9 files used by Lean, it also checks the row count,
row shape, polynomial degree, monicity, first discriminant, and sorted order.
It generates `V15VoightDiscriminantData.lean`, which contains only the five
discriminant columns. A separate `native_decide` certificate checks the five
lengths and nondecreasing order inside Lean.

## Exact proof boundary

`V15VoightEnumerationUpToFourteenInput` says that every coded totally real
field of degree 5 through 10 and discriminant at most `14 ^ degree` occurs in
the selected Voight list. The list for degree ten is empty. This is the single
source-facing completeness statement.

From that premise and the checked columns, Lean proves

- `v15_degreeFiveToNineMinimumInput_of_voightEnumeration`, and
- `v15_degreeTenRootDiscriminantInput_of_voightEnumeration`.

`V15SectionFourVoightClosed.lean` substitutes them into the strongest Section
4 bridge. Its three public endpoints require only Voight completeness and the
optimized degree-eleven root-discriminant input.

`V15OdlyzkoMartinetAtLeastElevenInput` records the degree-at-least-eleven
bound in the form quoted by Voight. Three additional
`of_publishedVoightBounds_closed` endpoints use that source-aligned statement
directly. The bound itself remains an explicit literature premise.

The stored data do not prove that Voight's search found every field. A fully
internal proof would need the search completeness argument, including the
exact polynomial enumeration from the proved prime-degree coefficient bounds,
irreducibility and maximal-order checks, duplicate-field control, and the
relative enumeration and coefficient bounds needed for imprimitive composite
extensions.

## Hunter groundwork

The new general Hunter modules prove the reusable part before any finite
polynomial search:

1. a primitive vector can be extended to an arbitrary finite basis;
2. the centered integer-ring projection has the required basis and covolume;
3. the Minkowski ball inequality yields a nonrational algebraic integer with
   the strict quadratic trace bound;
4. signing and translating normalize its integral trace without changing the
   trace expression; and
5. in prime degree, nonrationality makes the element primitive.

`V15HunterGeneralCoefficientBridge.lean` now continues this chain through the
polynomial interface. It proves Newton's second identity for arbitrary finite
multisets, identifies the first two integral-minimal-polynomial coefficients
with the trace and square trace, proves that the integral minimal polynomial
of a primitive element in a totally real field splits over the reals, and
packages the output as `V15HunterPolynomialCandidate`. The candidate is monic,
irreducible, has the required degree and only real roots, has normalized first
coefficient, and satisfies the strict Hunter spread bound. Lean also reduces
the normalized trace coefficient to `0,1,2` in degree five and to `0,1,2,3`
in degree seven.

`V15HunterCoefficientFiniteness.lean` completes the coefficient-bounding
step. It derives a uniform root bound from the Hunter spread, applies Vieta's
formulas to every coefficient, constructs both an executable integer box and
a finite set of all Hunter candidates, and proves the exact box cardinality.

`V15HunterCoordinateBoxes.lean` sharpens this to the actual elementary-
symmetric degree of each coefficient and supplies executable interval boxes
with independent endpoints. In degrees five and seven, monicity, normalized
trace, the sum of squared roots, and the strict spread inequality reduce the
top three intervals further. The exact refined box sizes are
`3113966442781800060` and
`224291130941773441790640579990433850560116`.

`V15PowerBasisPolynomialDiscriminant.lean` and
`V15GeneralPowerIndex.lean` prove in arbitrary degree that the trace-pairing
discriminant of a separable power basis equals the polynomial discriminant of
its minimal polynomial, that the equality commutes with the integral-to-
rational map, and that a primitive integral generator satisfies
`disc(f) = index^2 disc(K)` for a positive natural index.

`V15HunterPrimeDegreeBoxes.lean` specializes the construction at root
discriminant 14. Radius 6 gives the degree-five spread bound 180 and the
uniform coefficient bound 7,593,750. Radius 7 gives the degree-seven spread
bound 343 and the uniform coefficient bound 44,800,000,000. Every qualifying
degree-five or degree-seven field lands in the corresponding finite candidate
set, and now in the corresponding refined executable box, together with its
generator and exact positive-index formula.

`V15HunterDiscriminantBoxes.lean` turns that formula into a finite dependent
filter. For each polynomial `f` it checks only positive indices up to
`|disc(f)|`, retains exactly the pairs satisfying
`disc(f) = index^2 D`, and projects the surviving pairs back to a polynomial
box. The general index bound and both degree-five and degree-seven field
existence statements are kernel checked. This removes incompatible
polynomial-index pairs before maximal-order and duplicate-field processing.

This closes the geometric, algebraic, all-coefficient, finiteness, and
field-discriminant filtering front end in degrees five and seven. The remaining
enumeration proof must exhaust these large boxes more efficiently, verify the
associated maximal orders and discriminants, control duplicate fields, and
treat the composite-degree relative extensions. It is finite but
substantially larger than the cubic and quartic searches already formalized.

## Trust and status

The general Hunter proofs use only the standard Lean logical axioms reported
by the main audit. The Voight list certificate adds one disclosed native
compiler dependency and is isolated in the numerical audit. Enumeration
completeness remains a literature input, while the optimized degree-eleven
bound remains a separate literature input. These boundaries preserve the
current Grade B and PROVISIONAL_MATCH assessments.
