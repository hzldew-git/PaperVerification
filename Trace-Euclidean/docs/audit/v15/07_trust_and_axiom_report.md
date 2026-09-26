# Trust and axiom report

## Pinned environment

The Lean project builds on Lean 4.32.1 with mathlib v4.32.1. The checked
analytic contour endpoints reduce only to the standard logical dependencies
`propext`, `Classical.choice`, and `Quot.sound`. No delivered `.lean` proof
uses `sorry`, `sorryAx`, or a project axiom.

This statement is tied to the pinned environment. A future Lean or mathlib
upgrade must replay the complete build and axiom audit; the old successful
build remains reproducible from `lean-toolchain` and `lake-manifest.json`.

## Odlyzko route

`V15OdlyzkoTable4DescriptionInput` remains as a literature-facing interface,
but the final finiteness theorems do not assume it. The project constructs it
in `v15_odlyzkoTable4DescriptionInput_closed` from the specialized `b = 4`
contour proof.

The kernel-checked chain includes the completed Dedekind-zeta continuation
and functional equation, quadratic growth and Jensen count, finite
multiplicity-aware zero sums, zero-free contour heights, the weighted
argument principle on rectangles, vanishing horizontal edges, the vertical
limit, the exact `32/3` endpoint, the number-field archimedean line shift,
and the complete transformed prime correction. The resulting theorem is

```text
r_1 log(A_*) + 2 r_2 log(B_*) + PrimeCorrection(K) - 32/3
  <= log |D_K|.
```

The project therefore does not depend on an assumed Stark--Weil identity for
this specialized inequality. The older conditional explicit-formula
interfaces remain available for comparison and normalization audits.

## Native numerical boundary

The strict `A,B` interval certificate uses `native_decide`. Consequently the
closed exact-error and rounded Table 4 endpoints inherit five disclosed
native dependencies in addition to the standard logical axioms:

- one Euler--Mascheroni harmonic bound;
- the certified sinh and cosh integral-core upper bounds;
- the final strict scalar comparisons for `A = 36.347` and `B = 16.593`.

This is a compiler-backed numerical trust boundary. The contour,
archimedean identity, prime transform, and logarithmic discriminant inequality
themselves do not use it.

The imported Voight data use two separate `native_decide` certificates. The
first checks the five discriminant-column counts and sorted order. The second
checks all six full polynomial-row counts, structural conditions, positive
indices, column projections, and maximum indices. Their two generated native
dependencies are printed independently. File hashes and table structure are
checked by the reproducible generator before Lean runs.

The generator also verifies the 2,773 polynomial-discriminant index equations
with an exact integer Bareiss determinant. Mathematica independently verifies
irreducibility, total reality, the same equation, and the actual number-field
discriminant for every row. Lean now proves the semantics of an exact integer
Bareiss row-operation checker, its agreement with matrix determinants, the
Sylvester determinant/resultant identity, and the monic
resultant/discriminant bridge. Thirty-one generated `native_decide` chunks
replay all 2,773 exact resultants and close
`v15_voightPolynomialDiscriminantInput`. These thirty-one compiler-backed
dependencies are listed separately by the numerical audit; the generic
determinant and polynomial theorems remain in the kernel-only audit.

## Remaining external mathematics

Degrees one and two are proved internally. For degree two, Lean proves that
the field discriminant is not a square in `ℚ`; total-real positivity and
Minkowski's bound then give `|D_F| >= 5`. The Table 4 range is now internal.
For degree three, Lean constructs the projected lattice and its covolume,
lifts the Hunter vector to a nonrational integral generator, proves the spread
and index-discriminant identities, and combines them with trace normalization
and exact polynomial enumeration to obtain `|D_F| >= 49`. In degree four,
Lean proves the unconditional bound `|D_F| >= 725`. A Minkowski argument
produces a first projected short vector and, when its lift is imprimitive, a
second transverse vector. Primitive lifts are impossible by the exact six-row
enumeration and maximality of both residual power orders. If both lifts are
imprimitive, their distinct quadratic subfields have discriminants in
`{5,8}`. Equal discriminants force equality of the subfields; unequal
discriminants are coprime and the compositum theorem forces quartic
discriminant `1600`. The new quartic selection and lower-bound theorems have
only `propext`, `Classical.choice`, and `Quot.sound` in their axiom reports.
The sharp-Hermite, imprimitive-minimum, and relative-different routes remain
as compatibility interfaces and are not dependencies of the strongest
endpoint. Section 4 now derives the degree `5`--`9` minima and degree-ten
exclusion from checked Voight columns and one source-facing completeness
premise for the enumeration through root discriminant `14`. The full archived
polynomial rows, power-order indices, and independent arithmetic checks are
also public. The coefficient-discriminant interface is closed by the proved
checker and disclosed finite certificate computations. The
enumeration-completeness proof itself and the optimized degree-eleven bound
`14.083` remain. The online
November 1976 Table 2 gives `14.034` at degree eleven, so `14.083` remains a
separately attributed later optimized input. The source-facing
degree-at-least-eleven statement is connected to the exact Section 4 premise,
and Lean proves that `14.034` would admit the extra integral-table cell
`(2,11)`, whereas `14.083` excludes it.

The sharper HSW numerical zero-count theorem is also unproved, but it is not
needed: the internally proved quadratic Jensen count is sufficient for the
contour route. Historical, priority, and novelty claims remain outside the
formalization.

## Interpretation

The public Python and Wolfram checks trust their runtimes and the extracted
v15 input file. The private source-bound checks additionally verify the
manuscript hash and printed data. Neither computational PASS counts nor Lean
compilation alone establishes paper-to-code semantic fidelity. The author
and independent Lean review cards remain unsigned.
