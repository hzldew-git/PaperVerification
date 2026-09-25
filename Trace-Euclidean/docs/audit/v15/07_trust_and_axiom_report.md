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

## Remaining external mathematics

Degrees one and two are proved internally. For degree two, Lean proves that
the field discriminant is not a square in `ℚ`; total-real positivity and
Minkowski's bound then give `|D_F| >= 5`. The Table 4 range is now internal.
For degree three, Lean proves integral trace normalization, the exact
normalized polynomial enumeration, and that the conditional Hunter
certificate gives `|D_F| >= 49`. Section 4 still
takes source interfaces for that projected-lattice certificate, the exact
degree `4`--`9` minima, the degree-ten exclusion at root discriminant at most
`14`, and the optimized degree-eleven bound `14.083`. The online
November 1976 Table 2 gives `14.034` at degree eleven, so `14.083` remains a
separately attributed later optimized input.

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
