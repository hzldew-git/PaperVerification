# Analytic boundary progress, ordered by proof difficulty

This note records the status of the four tasks discussed after the classical
source review. A compiled conditional theorem is a deduction from its named
premises; it does not prove those premises.

| Task | New Lean result | Remaining theorem |
| --- | --- | --- |
| Direct zero sum without ordered enumeration | `V15DedekindZetaUnorderedZeros.lean` proves absolute convergence and nonnegative real part of the direct `tsum` over actual multiplicity-aware strip-zero occurrences from a quadratic height count. `V15MellinGrowth.lean` now supplies that count and hence discharges the summability premise. | No remaining count or ordering premise; the explicit formula must identify this convergent sum with the source zero term. |
| Coarse and sharp zero count | `V15DedekindZetaCompletedJensen.lean` transfers completed-function divisor multiplicities to the ordinary regularization and applies Jensen. `V15MellinGrowth.lean` proves the required global quadratic exponential bound from theta decay and Mellin tails, producing a quadratic all-height count. | The sharp HSW decimal bound remains unproved but is optional for the present Table 4 route. |
| Entire continuation and functional equation | `DedekindZeta/ZetaRegularization.lean` constructs an entire continuation of `(s-1) ζ_K(s)`. `DedekindZeta/FractionalIdealRescaling.lean` identifies each trace-dual fractional ideal with the selected integral class representative, proves the exact norm/discriminant scaling, reindexes the finite class sum, and proves the completed-zeta functional equation globally. `V15DedekindZetaCompletion.lean` matches HSW's Gamma factor and preserves critical-strip zero positions and multiplicities. | Closed for the current scope. |
| Stark/Weil explicit formula | `DedekindZeta/IdealEulerProduct.lean` proves Dedekind-zeta nonvanishing on `Re(s) > 1`. `DedekindZeta/PrimeLogDeriv.lean` and `DedekindZeta/LogDeriv.lean` prove local-uniform convergence, absolute summability, and the prime-power logarithmic-derivative formula. `DedekindZeta/ArchimedeanLogDeriv.lean` expands the full infinite-place logarithmic derivative into discriminant and digamma terms. `DedekindZeta/DigammaSeries.lean` supplies the Weierstrass/digamma series; `DedekindZeta/DigammaVertical.lean` derives the absolutely convergent real series on `a+it`; `DedekindZeta/DigammaIdentities.lean` proves conjugation, duplication, and the symmetric critical-line archimedean bracket; and `DedekindZeta/DigammaIntegral.lean` proves its Gauss integral form. `V15OdlyzkoCriticalTransform.lean` proves critical-line realness and integrability, a quadratic moment, and the exact source-normalized Fourier and cosine inversion formulas. `v15_odlyzkoTable4ExplicitCorrectionInput_of_unorderedZeros` connects the convergent direct zero sum to the source-normalized Table 4 reduction. | Convert the paired Gauss integrals to the source's two hyperbolic terms with justified Fubini and limiting interchanges, match every transformed prime-power term, and prove the global contour/residue limit. The resulting explicit-formula identity remains a named hypothesis. |

The source path is [Neukirch VII and Tate IV for continuation and the
functional equation, HSW Sections 2–4 for the optional sharp count, and
Odlyzko/Poitou for the explicit formula](18_classical_analytic_sources.md).
The continuation, functional equation, growth, coarse count, direct sum,
Euler-product nonvanishing, prime-power line, complex and vertical real
digamma series, the Gauss integral bridge, the symmetric critical-line
archimedean bracket, and the critical Fourier/cosine inversion are closed in
that dependency order. The remaining analytic construction consists of the
exact hyperbolic/Fubini specialization and the global Stark/Weil
test-function contour identity.
