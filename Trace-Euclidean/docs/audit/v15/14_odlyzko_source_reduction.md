# Odlyzko source reduction for v15

## Scope and finding

This note traces the discriminant inputs used by v15 back to the cited
literature and records the part now checked by Lean.  It does not claim a
kernel proof of Odlyzko's explicit-formula argument.

The primary table is A. M. Odlyzko, *Discriminant bounds*, dated November 29,
1976.  [Unconditional Table 4](https://www-users.cse.umn.edu/~odlyzko/unpublished/discr.bound.table4)
states

`D > A^r1 B^(2 r2) exp(-E)`

and its row `b = 4.000` gives `A = 36.347`, `B = 16.593`, and
`E = 10.667`.  The accompanying
[description of the tables](https://www-users.cse.umn.edu/~odlyzko/unpublished/discr.bound.tables.txt)
states the stronger form

`D > A^r1 B^(2 r2) exp(f-E)`,

where `f` is the prime-ideal sum formed with the unconditional kernel
`F(x) = H(x/b)/cosh(x/2)`.  It also states that Tables 2 and 4 are
unconditional, `A` and `B` are lower estimates, and `E` is rounded upward
from the exact value `8b/3`.

For `b = 4`, the exact error is `32/3`.  Lean proves

`32/3 <= 10.667`,

checks that upward rounding weakens the lower bound in the valid direction,
specializes `r2 = 0` and `r1 = [F:Q]` for a totally real field, and removes
the nonnegative correction `f`.  The resulting bound is

`|D_F| > 36.347^[F:Q] exp(-10.667)`.

## New Lean interfaces

`V15OdlyzkoTable4ExactErrorInput` records the complete row before the upward
rounding of `E`.  `V15OdlyzkoTable4DescriptionInput` records the published
rounded row, including the signature exponents and a nonnegative correction
term.  The following implications are now kernel checked:

1. exact `E = 32/3` row to the rounded `E = 10.667` row;
2. general signature row to the totally real field row;
3. field-level statements to the selected field of a lattice class;
4. the Table 4 input only from degree 12 for the Section 4 tables;
5. the Table 4 input only from degree 15 for the global degree cutoff and
   finiteness theorems.

The earlier unrestricted `V15OdlyzkoTable4Input` and its public theorem names
remain as compatibility interfaces.  The new interfaces expose the weaker
assumptions actually used.

## Small-degree inputs

The old single premise for degrees at most eleven is now decomposed by source:

- degree 1 is proved in Lean from mathlib's Minkowski discriminant bound;
- degrees 2--9 use exact minimum-discriminant data;
- degree 10 uses the absence of totally real degree-ten fields with root
  discriminant at most 14;
- degree 11 uses the optimized unconditional bound `delta_F > 14.083`.

John Voight's
[complete enumeration](https://jvoight.github.io/articles/ANTS144-fixed-errata-052714.pdf)
proves that all totally real fields with root discriminant at most 14 have
degree at most nine and explicitly states `NF(14,10) = empty`.  It also cites
the optimized unconditional Odlyzko--Martinet bound `delta_F > 14.083` for
degree at least eleven.

There is a source distinction that must remain visible.  The online
[November 1976 unconditional Table 2](https://www-users.cse.umn.edu/~odlyzko/unpublished/discr.bound.table2),
which the description says is derived from Table 4, lists `14.034` at degree
11.  It does not by itself justify the `14.083` constant in v15.  The latter
must be cited to the later optimized Odlyzko--Martinet tables, as Voight does,
or replaced in the manuscript by a bound directly derived from the online
1976 table after rechecking the Section 4 computation.

## Remaining analytic formalization boundary

Odlyzko's published proof method is developed in
[Lower bounds for discriminants of number fields](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/29/3/100995/lower-bounds-for-discriminants-of-number-fields)
and
[Lower bounds for discriminants of number fields II](https://www.jstage.jst.go.jp/article/tmj1949/29/2/29_2_209/_article/-char/en).
Poitou's
[Bourbaki exposition](https://www.numdam.org/item/?id=SB_1975-1976__18__136_0)
is a further proof-level account.  Eliminating the remaining Table 4 premise
requires a new analytic-number-theory development containing at least:

1. a completed Dedekind zeta function with meromorphic continuation and its
   functional equation;
2. the Stark/Weil explicit formula and control of its zero contribution;
3. the unconditional compactly supported test kernel and its positivity;
4. convergence and nonnegativity of the prime-ideal correction term;
5. rigorous archimedean integral bounds producing the tabulated lower
   estimates `A = 36.347` and `B = 16.593`.

Pinned mathlib defines the Dedekind zeta Dirichlet series and its residue at
one, but it does not currently provide this explicit formula or the required
global zero-sum theory.  Therefore the full Odlyzko theorem remains a
disclosed external mathematical input.  The new Lean work reduces that input
to the exact source statement and proves every specialization, rounding, and
downstream use needed by v15.
