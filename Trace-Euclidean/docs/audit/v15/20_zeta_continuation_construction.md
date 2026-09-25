# Dedekind zeta continuation constructed in Lean

**Status update.** The continuation developed here now feeds a completed
specialized `b = 4` contour proof; see
[`22_odlyzko_contour_closure.md`](22_odlyzko_contour_closure.md).

The formalization now constructs, for every number field `K`, an entire
function agreeing with `(s - 1) * NumberField.dedekindZeta K s` whenever
`1 < Re(s)`. It is the concrete value
`TraceEuclidean.v15ConstructedDedekindZetaRegularization K`, rather than an
assumed instance of the zero-theory structure.

## Source and normalization

The number-field theta, Poisson, cone-integral, and ideal-class modules were
adapted from `mathlib-initiative/sum_product` at commit
`80e4127a67742659d521466204c6d2d7e0ca2b3f`. The source is Apache 2.0;
its license and the local adaptation note are in `lean/THIRD_PARTY_LICENSES`
and `lean/DedekindZeta/README.md`. The upstream abstract Mellin module had
already been vendored as `TraceEuclidean.AnalyticMellinPrinciple`. The local
proof adaptations make the number-field files compile with Lean 4.32.1 and
the repository's pinned mathlib.

The new `DedekindZeta.GlobalContinuation` module sums the Mellin
continuations of the partial zeta integrals over the finite ideal class
group. It proves the exact right-half-plane equality

```text
completedZetaContinuation K s = ZInfty K s * dedekindZeta K s
```

for `1 < Re(s)`. It then removes the possible poles at `0` and `1` by a
polynomial expression. `completedZetaPoleRemoved_analyticOn` proves this
expression entire, and `completedZetaPoleRemoved_eq_zeta` proves that it is
`s * (s - 1) * ZInfty K s * dedekindZeta K s` on the same half-plane.

The new `DedekindZeta.ZetaRegularization` module constructs an **entire**
reciprocal of `s * ZInfty K s`. It cancels the apparent pole at `s = 0` using
the shifted real Gamma relation and one of the field's infinite places.
`dedekindZetaRegularized_analyticOn` and
`dedekindZetaRegularized_eq` prove that the resulting product is entire and
equals `(s - 1) * dedekindZeta K s` for `1 < Re(s)`. The exact definitions and
right-half-plane identities are checked by Lean, including the discriminant
and both real and complex Gamma factors.

`TraceEuclidean.V15DedekindZetaConstructed` instantiates the existing
`V15DedekindZetaRegularization` structure. `V15DedekindZetaCompletedJensen`
matches its zeros and multiplicities with the entire completed function.
`V15MellinGrowth` proves the circle-growth estimate, quadratic zero count, and
direct zero-sum convergence. The endpoint
`v15_odlyzkoTable4_of_constructed_explicitFormula` therefore takes only the
source explicit formula as a mathematical premise; it uses the already
certified archimedean bounds internally.

The field-specific theorem `v15_completedPartialZeta_reflected_radial`
instantiates the abstract Mellin reflection for every nonzero integral ideal.
It identifies the reflected *dual radial* Mellin expression away from the
former poles.

`DedekindZeta.DualClassReindex` proves the algebraic part of the
reindexing: the dual ideal `(𝔞𝔡)⁻¹` lies in the class
`([𝔞][𝔡])⁻¹`, this correspondence permutes the finite class group, and
finite sums may be reindexed along it. The new
`DedekindZeta.FractionalIdealRescaling` module completes the analytic and
arithmetic bridge. It proves invariance of the fundamental-cone integral
under nonzero right translation, identifies the theta kernel of a principal
multiple of a fractional ideal, constructs a nonzero principal comparison
with the selected integral class representative, and proves the exact norm
identity containing the discriminant.

The resulting theorems prove the reflected identity for every partial
completed zeta, reindex its finite class sum, and then use analytic uniqueness
to obtain

```text
completedZetaPoleRemoved K s = completedZetaPoleRemoved K (1 - s)
```

for every complex `s`. Away from `0` and `1`, Lean also proves
`completedZetaContinuation K s = completedZetaContinuation K (1 - s)`.

## Quantitative growth and zero count

`TraceEuclidean.V15MellinGrowth` converts each radial theta function's
asymptotic exponential decay into a uniform pointwise bound on `[1,∞)`. It
proves the logarithmic inequality and Young estimate needed to absorb every
Mellin power into `exp(A * (1 + ‖s‖)^2)`, establishes integrability of the
remaining half-rate exponential tail, and bounds both Mellin-tail integrals.
The ideal norm and discriminant complex powers satisfy the same type of bound.

The bounds are stable under products and finite sums, so the finite class-group
sum `completedZetaPoleRemoved K` has global quadratic exponential growth.
Using a point where this entire function is nonzero, Lean turns the global
bound into the exact expanding-circle bound required by Jensen's inequality.
`exists_constructedDedekindZeta_quadraticCountInput` then gives a quadratic
count of the actual critical-strip zero occurrences, including multiplicity,
and `constructedDedekindZeta_odlyzkoPhi_summable` proves absolute convergence
of their direct Odlyzko transform.

## Logarithmic derivative and toolchain decision

`DedekindZeta.LogDeriv` supplies the first contour-integration interface. On
`Re(s) > 1`, Lean proves that `ZInfty K` is nonzero and differentiable and
that `NumberField.dedekindZeta K` is differentiable and nonzero. It then proves

```text
logDeriv completedZetaPoleRemoved(s)
  = 1/s + 1/(s-1) + logDeriv ZInfty(s) + logDeriv dedekindZeta(s),
```

without an additional pointwise nonvanishing premise. Differentiating the
already proved functional equation also gives the global reflection identity
for the completed logarithmic derivative.

`DedekindZeta.IdealEulerProduct` derives this nonvanishing from the ideal Euler
product. `DedekindZeta.PrimeLogDeriv` proves local-uniform convergence of the
non-inverted factors and absolute convergence of the logarithm-weighted double
series over prime ideals and positive powers. Consequently
`logDeriv_dedekindZeta_eq_neg_tsum_primePowers` identifies the ordinary-zeta
logarithmic derivative with that series. `DedekindZeta.ArchimedeanLogDeriv`
separately expands `logDeriv (ZInfty K)` into the discriminant, real-place, and
complex-place digamma terms. `DedekindZeta.DigammaSeries`, adapted from
`anthropics/formal-math` commit
`fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`, proves the Weierstrass product and
digamma partial-fraction expansion. `DedekindZeta.DigammaIdentities` then
proves conjugation and duplication and rewrites the two critical-line
archimedean logarithmic derivatives as the required real-part bracket.
`DedekindZeta.DigammaVertical` additionally maps the complex series through
the real-part functional and proves its absolutely convergent rational series
on every vertical line `a+it` with `0 < a < 1`.

The external `anthropics/formal-math` project contains a proof of the Riemann
zeta Weil formula under Lean 4.33.0-rc2 and mathlib commit
`51e6992efd06126df61a496bebf8f49482a4e129`. The present project remains pinned
to Lean/mathlib 4.32.1. At the time of comparison, the later mathlib did not
provide a directly reusable Dedekind-zeta Euler-product nonvanishing theorem.
The present project has now closed that gap locally. Upgrading would still
require replaying the whole project and would not by itself prove the
number-field contour specialization. Compatible generic contour lemmas were
ported selectively while retaining the stable 4.32.1 toolchain, and the
specialized proof has now been completed there.

## Trust and remaining work

The local full Lean build and `MainTheoremAudit` pass. The new construction,
right-half-plane equality, and Table 4 endpoint depend only on `propext`,
`Classical.choice`, and `Quot.sound`. There is no `sorry`, project axiom, or
`native_decide` in these new proofs. The separate numerical certificate's
previously disclosed native compiler dependence is unchanged.

This construction proves entire continuation of the **pole-removed ordinary
zeta** and the functional equation of the completed Dedekind zeta. The
subsequent quantitative module proves a global quadratic exponential bound
for the completed function and activates the Jensen zero-count theorem. The
ideal Euler product, right-half-plane nonvanishing, prime-power
logarithmic-derivative identity, complex and vertical real digamma series,
symmetric critical-line archimedean bracket, test-function transforms,
justified interchanges, residues, and contour limits are internal for the
specialized `b = 4` route.
The cited small-degree discriminant results remain separate literature
inputs. The four main manuscript results retain the scoped Grade B and
PROVISIONAL_MATCH assessments.
