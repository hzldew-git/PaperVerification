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
coefficient bounds, exact polynomial enumeration, irreducibility and maximal
order checks, duplicate-field control, and the relative enumeration needed
for imprimitive extensions.

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

This closes the geometric, algebraic, and first-two-coefficient front end in
degrees five and seven. The remaining enumeration proof must bound the higher
coefficients, exhaust the resulting polynomial boxes, verify the associated
maximal orders and discriminants, control duplicate fields, and treat the
composite-degree relative extensions. It is finite but substantially larger
than the cubic and quartic searches already formalized.

## Trust and status

The general Hunter proofs use only the standard Lean logical axioms reported
by the main audit. The Voight list certificate adds one disclosed native
compiler dependency and is isolated in the numerical audit. Enumeration
completeness remains a literature input, while the optimized degree-eleven
bound remains a separate literature input. These boundaries preserve the
current Grade B and PROVISIONAL_MATCH assessments.
