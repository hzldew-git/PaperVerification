# Degree-eleven discriminant boundary

## Source distinction

Voight's *Enumeration of totally real number fields of bounded root
discriminant*, Section 1.1, states that every totally real field of degree at
least eleven has root discriminant greater than `14.083`, citing the
unconditional Odlyzko bounds and Martinet. The online November 1976
[Table 2](https://www-users.cse.umn.edu/~odlyzko/unpublished/discr.bound.table2)
instead prints `14.034` in degree eleven. These are different inputs and the
formalization does not identify them.

`V15OdlyzkoMartinetAtLeastElevenInput` records the all-degrees statement in
the form quoted by Voight. Lean proves that it specializes to
`V15DegreeElevenRootDiscriminantInput`, the exact premise used in Section 4.
This is a statement-alignment bridge; the cited analytic bound itself remains
a literature input.

## Lean sensitivity check

`V15DegreeElevenSensitivity.lean` defines the degree-eleven Section 4
quantity obtained by replacing the manuscript's `14.083` with the online
Table 2 value `14.034`. It proves both

- `v15_degreeEleven_tableTwo_bound_admits_integral_pair`: the weaker value
  makes the rank-two, degree-eleven cell satisfy the manuscript's necessary
  integral condition; and
- `v15_degreeEleven_optimized_bound_excludes_integral_pair`: the manuscript's
  `14.083` value strictly excludes that cell.

The first proof uses the rational lower bound `333/106 < pi`, the exact
factorial expression for the 22-dimensional unit-ball volume, and exact
rational normalization. The second reuses the certified 34 by 14 grid.
Therefore substituting `14.034` without changing the integral table would be
mathematically invalid. The classic table does not acquire this extra cell,
but the integral table would acquire `(2,11)`.

## Remaining closure route

There are two logically valid routes:

1. retain `14.083` as the clearly cited Odlyzko--Martinet literature theorem;
2. reconstruct the optimized discriminant estimate in Lean, including its
   scaled test function, strict archimedean constants, and contour argument.

The existing internal `b=4` contour development yields a weaker degree-eleven
constant and cannot prove `14.083`. A full internal reconstruction therefore
requires a second optimized kernel and new certified integral estimates. Until
that work is complete, the source-facing premise remains visible in the
strongest Section 4 endpoints.
