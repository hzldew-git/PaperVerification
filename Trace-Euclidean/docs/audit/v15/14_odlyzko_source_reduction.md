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

For `b = 4`, the exact error is `32/3`. Lean now evaluates the source kernel's
archimedean error integral exactly:

`4 * integral_(0,infinity) F(x)*cosh(x/2) dx = 32/3`.

It also proves

`32/3 <= 10.667`,

checks that upward rounding weakens the lower bound in the valid direction,
specializes `r2 = 0` and `r1 = [F:Q]` for a totally real field, and removes
the nonnegative correction `f`.  The resulting bound is

`|D_F| > 36.347^[F:Q] exp(-10.667)`.

## New Lean interfaces

`V15OdlyzkoTable4ExactErrorInput` records the complete row before the upward
rounding of `E`.  `V15OdlyzkoTable4DescriptionInput` records the published
rounded row, including the signature exponents and a nonnegative correction
term. `V15OdlyzkoTable4ExplicitCorrectionInput` replaces that existential
term by the complete correction defined from the source kernel. Thus the
remaining analytic premise is a single discriminant inequality with a fully
specified correction. The following implications are now kernel checked:

1. exact `E = 32/3` row to the rounded `E = 10.667` row;
2. general signature row to the totally real field row;
3. field-level statements to the selected field of a lattice class;
4. the Table 4 input only from degree 12 for the Section 4 tables;
5. the Table 4 input only from degree 15 for the global degree cutoff and
   finiteness theorems;
6. the explicit complete correction inequality to the exact-error and rounded
   Table 4 interfaces.

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

The flexible explicit-formula method used for tabular discriminant bounds is
developed in Odlyzko's
[*Some analytic estimates of class numbers and discriminants*](https://doi.org/10.1007/BF01389854),
Inventiones Mathematicae 29 (1975), 275--286.  Related refinements appear in
his
[*Lower bounds for discriminants of number fields*](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/29/3/100995/lower-bounds-for-discriminants-of-number-fields)
and
[Lower bounds for discriminants of number fields II](https://www.jstage.jst.go.jp/article/tmj1949/29/2/29_2_209/_article/-char/en).
Poitou's
[Bourbaki exposition](https://www.numdam.org/item/?id=SB_1975-1976__18__136_0)
is a further proof-level account.

The first elementary layers of that development are now machine checked.
`V15OdlyzkoKernel` defines the source's unconditional function `H` and the
`b = 4` kernel `F(x) = H(x/4)/cosh(x/2)`. Lean proves that `H` and `F` are
even and nonnegative, that `H` is supported on `[-2,2]`, that `F` is supported
on `[-8,8]`, and that `F` is continuous, compactly supported, and Lebesgue
integrable. In particular, the interval where the sine term is negative is
handled by a derivative-monotonicity proof rather than numerical sampling.

`V15OdlyzkoAutocorrelation` then defines the compactly supported bump
`g(x) = 1 + cos(pi*x)` on `[-1,1]` and proves the exact identity

`H(x) = (1/3) integral g(t) g(t-x) dt`.

The overlap integral is evaluated by a formal antiderivative, including all
support cases. `V15OdlyzkoFourier` applies mathlib's convolution theorem and
proves, in its Fourier convention,

`Fourier(H)(xi) = (1/3) Fourier(g)(xi)^2`.

Evenness makes `Fourier(g)` real. Consequently Lean proves that the Fourier
transform of `H` is real and nonnegative at every real frequency. Thus the
basic positive-definite auxiliary function is no longer an external premise.

`V15OdlyzkoSechFourier` proves integrability of the remaining factor and,
using the sigmoid substitution, the complex beta integral, and Euler's
reflection formula, evaluates its transform in mathlib's convention as

`Fourier(1/cosh(x/2))(w) = 2*pi/cosh(2*pi^2*w)`.

The right side is real and strictly positive and is itself integrable.
`V15OdlyzkoFinalFourier` proves the required product-to-frequency-convolution
identity under the checked integrability and continuity hypotheses. After
combining this identity with Fourier scaling for `H(x/4)`, Lean rewrites the
transform of `F(x)=H(x/4)/cosh(x/2)` as an integral whose real integrand is
pointwise nonnegative. Therefore the complete transform is real and
nonnegative at every real frequency. The Fourier-positivity transfer to the
final kernel is no longer an external premise.

Odlyzko's [1990 survey, equations (2.2)--(2.4)](https://www.numdam.org/item/JTNB_1990__2_1_119_0.pdf)
requires the stronger condition `Re Phi(s) >= 0` throughout the entire
critical strip, where `Phi(s) = integral F(x)*exp((s-1/2)*x) dx`. Positivity of
the ordinary Fourier transform alone addresses only `Re(s) = 1/2`.
`V15OdlyzkoTiltedSech` now proves, for `-1/2 < a < 1/2`, the exact formula

`Fourier(exp(a*x)/cosh(x/2))(w) = 2*pi/sin(pi*(1/2+a-2*pi*i*w))`.

It proves integrability on both sides and strict positivity of the transform's
real part. `V15OdlyzkoZeroStrip` combines this with the nonnegative real
Fourier transform of `H(x/4)` to prove nonnegativity for the complete kernel
at every open-strip weight. The complete kernel is compactly supported, so
its transform is continuous in the weight; closure then gives both boundary
weights. Lean checks the exact change of variables between its Fourier
convention and Odlyzko's `Phi(s)`, and proves `Re Phi(s) >= 0` whenever
`0 <= Re(s) <= 1`. It also proves nonnegativity of the real part of any
summable family of such contributions. These theorems do not assert that the
Dedekind-zeta zero family exists or is summable in the paired convention of
the explicit formula. `V15OdlyzkoPhiSymmetry` also proves the source-normalized
reflection identity `Phi(1-s) = Phi(s)` from the evenness of `F`.

Odlyzko's [1990 survey, equation (2.1)](https://www.numdam.org/item/JTNB_1990__2_1_119_0.pdf)
requires global differentiability of `F` and exponential decay of both `F`
and `F'`. `V15OdlyzkoDifferentiability` proves that `H` and the exact
`b = 4` function `F` are differentiable at every real point. It handles the
origin and both support endpoints by matching their one-sided derivatives.
It also proves that `F'` vanishes whenever `|x| > 8`, hence verifies the
source's eventual decay inequality with `c = epsilon = 1`.

`V15OdlyzkoArchimedean` integrates the printed formula for `H` exactly on
`[0,2]`, scales to `[0,8]`, and removes the zero tail. This proves the
`E = 32/3` integral directly, rather than only accepting the table
description's value and checking its upward rounding.

`V15OdlyzkoPrimeCorrection` defines the source's exact summand for a nonzero
prime ideal and a positive exponent. It constructs the finite set of prime
ideals of bounded absolute norm, proves every summand and every finite partial
correction nonnegative, and proves monotonicity in the exponent cutoff. It
then derives two uniform support bounds: exponents at least twelve vanish for
every prime ideal, and every positive-exponent term vanishes when the ideal
norm is at least 4096. The complete double sum over all prime ideals and
positive exponents is therefore proved exactly equal to the finite sum over
norms at most 4095 and exponents at most eleven. In particular, the complete
prime correction is a nonnegative Lean theorem rather than an external
infinite-sum premise.

Eliminating the remaining Table 4 premise still requires a new
analytic-number-theory development containing at least:

1. a completed Dedekind zeta function with meromorphic continuation and its
   functional equation;
2. the Stark/Weil explicit formula and existence and convergence of its paired
   zero sum; the source test-function hypotheses, pointwise zero-transform
   sign, and conditional summable-family sign are already proved;
3. rigorous archimedean integral bounds producing the tabulated lower
   estimates `A = 36.347` and `B = 16.593`.

Pinned mathlib defines the Dedekind zeta Dirichlet series and its residue at
one, but it does not currently provide this explicit formula or the required
global zero-sum theory. Therefore the full Odlyzko theorem remains a
disclosed external mathematical input. The Lean work now verifies the source
kernel, the autocorrelation and Fourier positivity of `H`, the exact
hyperbolic-secant and tilted transforms, the product-to-convolution bridge,
source-normalized zero-transform positivity on the closed critical strip, the
test function's differentiability and derivative decay, the exact `E = 32/3`
integral, the complete prime-ideal correction and its
exact finite-support reduction, every specialization and rounding, and every
downstream use needed by v15.
