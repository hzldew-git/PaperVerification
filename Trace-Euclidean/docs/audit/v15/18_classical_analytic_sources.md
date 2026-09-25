# Classical analytic sources and the next Lean bridge

This note identifies the source of each outstanding analytic theorem and
records what the pinned Lean project actually proves. A citation supplies a
mathematical reference, not a Lean proof.

| Topic | Source and exact location | Required construction |
| --- | --- | --- |
| Dedekind-zeta continuation and functional equation | J. Neukirch, [*Algebraic Number Theory*](https://link.springer.com/book/10.1007/978-3-662-03983-0), Chapter VII, especially Section 5 (Dedekind zeta), Section 7 (number-field theta series), and Section 8 (Hecke L-series); J. Tate, [*Fourier Analysis in Number Fields and Hecke's Zeta-Functions*](https://sites.math.rutgers.edu/~alexk/2023S572/Tate1950.pdf), Chapter IV, Sections 4.2 and 4.4--4.5 | The continuation, trace-dual class reindexing, exact norm/discriminant scaling, and completed-zeta functional equation are proved in Lean. |
| Completed zeta and quantitative zero count | E. Hasanalizade, Q. Shen, and P.-J. Wong, [*Counting zeros of Dedekind zeta functions*](https://arxiv.org/pdf/2102.04663), Corollary 1.2, equations (2.1)--(2.4), Section 3, and the footnote after (2.5) | The constructed completed zeta, functional equation, quadratic exponential growth, Jensen count, and direct zero-sum convergence are proved. The sharper published count and its decimal constants remain an optional unproved route. |
| Stark/Weil formula and discriminant bounds | H. Stark, [*Some effective cases of the Brauer--Siegel theorem*](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0023/PPN356556735_0023.pdf), Invent. Math. 23 (1974), 135--152; G. Poitou, [*Minorations de discriminants*](https://www.numdam.org/article/SB_1975-1976__18__136_0.pdf), Section 6; A. Odlyzko, [*Lower bounds for discriminants of number fields*](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/29/3/100995/lower-bounds-for-discriminants-of-number-fields), Acta Arith. 29 (1976), 275--297; Odlyzko's [1990 survey](https://www.numdam.org/item/JTNB_1990__2_1_119_0.pdf), Section 2 | Prove the explicit formula with its zero and prime-ideal terms, convergence and normalization, then specialize it to the printed unconditional test function and Table 4 constants. |

The 1976 unpublished [*Discriminant bounds* tables](https://www-users.cse.umn.edu/~odlyzko/unpublished/discr.bound.table4)
are the separate source for the numerical Table 4 row in the v15 audit. The
1990 survey's Table 4 is a different table and is not substituted for it.

## Source-normalized zero count

Hasanalizade--Shen--Wong define the completed function in (2.1), recall its
functional equation in (2.2), and apply the argument principle in (2.3)--(2.4).
Their Corollary 1.2 counts zeros with multiplicity in the open strip and
`|Im(s)| <= T`, including zeros at the boundary height. The footnote on page
three explains the passage from contours avoiding zero heights to all `T`.

`V15DedekindZetaZeroHeight.lean` formalizes that boundary-height passage:

- `heightExhaustion` constructs an increasing exhaustion of all genuine
  multiplicity-aware strip-zero occurrences by finite height sets; `countable`
  proves that this occurrence type is countable.
- `exists_right_regular_interval` proves that immediately above any height,
  the occurrence count is constant and no occurrence has exactly that larger
  height.
- `bound_of_regular_heights` extends any continuous main-term/error bound
  from regular heights to all heights at least one.
- `HSWNumericInput_of_regular_heights` and
  `HSWFieldInput_of_regular_heights` instantiate the transfer with the exact
  Corollary 1.2 main term and decimal error constants.

These are unconditional Lean deductions **from an arbitrary entire
regularization**. Such a regularization is now constructed in Lean; the HSW
inequality at regular heights remains an explicit mathematical input. A
separate completed-function Jensen proof now gives the coarser quadratic count
needed for the Odlyzko zero sum without this input.
Countability and finite
exhaustion do not prove that infinitely many strip zeros exist. A direct
unordered `tsum` theorem now makes a height-ordered enumeration unnecessary
for the Table 4 zero term.

The source footnote formulates contour avoidance using zeros of its
completed `xi_K`. The Lean input uses heights with no occurrence of a
zero of the pole-removed zeta function in the open strip. The new
`V15DedekindZetaCompletion.lean` proves exact HSW Gamma normalization and
identical zero positions and orders in the open critical strip for the
completed expression formed from an arbitrary entire regularization.
Its existence and functional equation are now proved; the correspondence
itself no longer needs to be assumed separately.

## Pinned-library boundary

The pinned mathlib `NumberField.DedekindZeta` module defines the ideal-norm
Dirichlet series and proves its right-hand residue at one. Its
`NumberTheory.LSeries.AbstractFuncEq` module provides a generic Mellin
functional-equation mechanism. The vendored number-field theta/Poisson and
Mellin data now construct an entire continuation of `(s-1) ζ_K(s)` in this
project, and the fractional-ideal rescaling module proves the global completed
functional equation. The
argument-principle specialization and Stark/Weil explicit formula are not
supplied by mathlib. This project now proves the required circle-growth
estimate and derives the coarse count. The next proof boundary is the explicit
formula itself, and every remaining analytic hypothesis must stay visible.
