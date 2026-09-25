# Vendored number-field theta and Mellin development

The Lean files in this directory are based on
[`mathlib-initiative/sum_product`](https://github.com/mathlib-initiative/sum_product),
commit `80e4127a67742659d521466204c6d2d7e0ca2b3f`, under Apache 2.0.
See `../THIRD_PARTY_LICENSES/sum_product_APACHE-2.0.txt`.

`PoissonSummation`, `Theta`, `Statements`, `GammaIntegral`,
`ConeRadialReduction`, `ConeMellinBridge`, and `PerClass` are upstream files
with small proof adaptations for Lean 4.32.1 and this repository's existing
copy of `MellinPrinciple` (`TraceEuclidean.AnalyticMellinPrinciple`).
`GlobalContinuation`, `ZetaRegularization`, `DualClassReindex`,
`FractionalIdealRescaling`, `IdealEulerProduct`, `PrimeLogDeriv`, `LogDeriv`,
`ArchimedeanLogDeriv`, `DigammaIdentities`, `DigammaVertical`, and
`DigammaIntegral` are new
modules added for this verification project.
Their public theorems prove an entire continuation of
`(s - 1) * NumberField.dedekindZeta K s` for every number field `K`, the
class-group permutation induced by the trace-dual fractional ideal, and the
completed functional equation with its logarithmic-derivative reflection.
They also prove the ideal Euler product and nonvanishing on `Re(s) > 1`, the
absolutely convergent prime-power logarithmic-derivative expansion, and the
discriminant/Gamma/digamma expansion of the archimedean logarithmic
derivative.

`DigammaSeries` adapts the Weierstrass-product and digamma-series development
from [`anthropics/formal-math`](https://github.com/anthropics/formal-math),
commit `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`, under Apache 2.0. See
`../THIRD_PARTY_LICENSES/formal-math_APACHE-2.0.txt`. The file retains the
upstream copyright notice and records the local namespace/import changes.
`DigammaIdentities` proves conjugation and duplication for digamma and combines
the two critical-line logarithmic derivatives of `ZInfty K` into the exact
real-part bracket needed by the explicit-formula normalization.
`DigammaVertical` converts the complex partial-fraction formula into an
absolutely convergent real series for `Re ψ(a+it)` when `0 < a < 1`; this is
the pointwise series needed for the integral step. `DigammaIntegral` justifies
the exchange of the sum and the improper integral, proves the Gauss integral
representation of `Re ψ(a+it)`, specializes it at `a = 1/4` and `a = 1/2`,
and rewrites the complete critical-line archimedean bracket as explicit
integrals.

The functional equation, quantitative growth bound, Euler-product
nonvanishing, prime-power line, complex and vertical real digamma series, Gauss
integral representation, and critical-line archimedean integral bracket are
proved. `TraceEuclidean/V15OdlyzkoCriticalTransform.lean` also proves the
critical transform's integrability, a quadratic moment, and its exact
Fourier/cosine inversion formulas. `V15OdlyzkoArchimedeanBridge.lean` performs
the required Fubini interchanges and evaluates the two source hyperbolic
terms. `V15OdlyzkoPrimeTransform.lean` identifies every transformed
prime-power term, justifies the infinite exchange, and proves the corresponding
identity for the actual Dedekind-zeta logarithmic derivative. The remaining
analytic work is the global Stark/Weil contour and residue identity.
