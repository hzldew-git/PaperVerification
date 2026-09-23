# Identified sources and external inputs

## Author version

The target is the privately held author file Trace-Euclidean-v15.tex with
SHA-256 83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.
Public inputs/manuscript_inputs_v15.json records its extracted mathematical
data and labels without publishing the manuscript.

## Formal platform

Lean v4.32.1 and pinned mathlib revision
520045ab14e26149ee970e2e617ca04b09bde5d6.
Library theorems on number fields, fractional ideals, discriminants,
projective modules, Hermite finiteness, Haar covolume, and real analysis are
trusted as pinned mathlib dependencies.

## Odlyzko discriminant input

[Odlyzko, unconditional Table 4](https://www-users.cse.umn.edu/~odlyzko/unpublished/discr.bound.table4)
lists row b=4.000 with A=36.347 and E=10.667.
His [description of the tables](https://www-users.cse.umn.edu/~odlyzko/unpublished/discr.bound.tables.txt)
states that Table 4 is unconditional and gives the stronger formula
|D_F| > A^r1 B^(2r2) exp(f-E), where f is the prime-ideal correction.
It also states that A and B are lower estimates and that E is rounded upward
from 8b/3. For b=4, Lean derives the exact archimedean error integral
`4 * integral_(0,infinity) F(x)*cosh(x/2) dx = 32/3` and the
endpoint-transform identity `Phi(0) + Phi(1) = 32/3`, then checks
32/3 <= 10.667 and the direction of this
rounding, the totally real signature specialization, removal of the
nonnegative f, and all downstream uses. The new literature-facing premise is
V15OdlyzkoTable4DescriptionInput. V15OdlyzkoTable4Input remains as a
compatibility interface for the resulting totally real consequence
|D_F| > 36.347^d exp(-10.667).

The flexible analytic method used for tabular discriminant bounds is developed
in Odlyzko's [Inventiones paper](https://doi.org/10.1007/BF01389854),
*Some analytic estimates of class numbers and discriminants*, 29 (1975),
275--286. Related refinements are documented in his
[Acta Arithmetica paper](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/29/3/100995/lower-bounds-for-discriminants-of-number-fields),
DOI 10.4064/aa-29-3-275-297, his
[Tohoku paper](https://www.jstage.jst.go.jp/article/tmj1949/29/2/29_2_209/_article/-char/en),
DOI 10.2748/tmj/1178240652, and Poitou's
[Bourbaki exposition](https://www.numdam.org/item/?id=SB_1975-1976__18__136_0).
Odlyzko's [1990 survey, equations (2.2)--(2.4)](https://www.numdam.org/item/JTNB_1990__2_1_119_0.pdf)
defines `Phi(s) = integral F(x)*exp((s-1/2)*x) dx` and identifies
`Re Phi(s) >= 0` throughout the critical strip as the zero-term sign
condition for an unconditional bound. Lean now proves that sign condition for
the printed `b=4` kernel, including both strip boundaries. It also proves the
test function's global differentiability and its derivative's compact support,
which verifies the eventual decay hypothesis in equation (2.1). The
exact endpoint values `Phi(0) = Phi(1) = 16/3` are proved in Lean. The
explicit-formula identity, its paired-zero convergence, and certified A/B
integral estimates remain external. A Lean reduction now states the exact
archimedean integrals from equation (2.3), proves convergence of the
cosh-denominator integral, takes its explicit formula and strict `A,B` bounds
as named premises, and derives the Table 4 interface. See
[the source-reduction audit](docs/audit/v15/14_odlyzko_source_reduction.md).

Voight's
[totally real field enumeration](https://jvoight.github.io/articles/ANTS144-fixed-errata-052714.pdf)
supplies a complete list through root discriminant 14 and proves there is no
degree-ten field in that range. The small-degree interface is now separated
into exact minima for degrees 2--9, the degree-ten root-discriminant input,
and the optimized degree-eleven bound 14.083. Degree one is proved internally
from Minkowski's bound. The online November 1976
[Table 2](https://www-users.cse.umn.edu/~odlyzko/unpublished/discr.bound.table2)
lists 14.034, rather than 14.083, at degree eleven; therefore the v15 value
14.083 is tracked as a later optimized Odlyzko--Martinet input, following
Voight's citation, and is not attributed to the online 1976 Table 4 alone.

## Unformalized standalone material

The generic binary-radius formula, Proposition 6.1's two integer-scalar
specializations, the p-norm finiteness corollary, the Section 4 analytic grid,
and its finite-table maxima now have standalone Lean endpoints. The complete
periodic-minimum development, all separate ideal upper bounds, and historical
or novelty assertions are not claimed as standalone Lean results. See the
[coverage report](docs/audit/v15/09_coverage_report.md).
