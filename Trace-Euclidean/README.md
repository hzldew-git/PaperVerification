# Trace-Euclidean v15 verification package

Active author version: Trace-Euclidean-v15.tex, SHA-256
83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.
The manuscript TeX and PDF are deliberately absent.

The local [v16 statement-delta audit](docs/audit/v16/01_statement_delta_and_mellin_bridge.md)
compares the author's revised manuscript with this frozen v15 baseline: all
19 labelled theorem, corollary, proposition, lemma, and definition statements
match after whitespace and label normalization. One remark was reworded.
The comparison script accepts local TeX paths; neither manuscript is published.

The vendored number-field theta/Mellin development now constructs an entire
continuation of `(s-1) ζ_K(s)` for every number field. Its value is used by
`V15DedekindZetaConstructed.lean`, closing the existence premise of the zero
theory. The earlier uniqueness, nonvanishing, conjugation, and finite-height
theorems apply to this constructed function. The
[continuation proof note](docs/audit/v15/20_zeta_continuation_construction.md)
records its source and exact Lean endpoints. The completed-zeta functional
equation and an explicit quadratic growth bound are proved; Jensen supplies a
quadratic count and direct zero-sum convergence. The sharper published count
remains optional and unproved. Lean also proves right-half-plane Euler-product
nonvanishing, the absolutely convergent prime-power logarithmic derivative,
the archimedean Gamma/digamma decomposition, the digamma partial-fraction
series, the symmetric critical-line archimedean bracket, and its exact
Gauss-digamma/Fubini specialization to the source's two hyperbolic terms. The
project now also proves arbitrary vertical-line Fourier inversion, exchanges
the complete absolutely convergent prime-power series with the vertical
integral, and identifies the transformed actual zeta logarithmic derivative
with minus `pi` times the finite source correction. The finite weighted
argument principle, zero-free expanding rectangles, horizontal-side limits,
vertical integrability, endpoint residues, and archimedean line shift are now
also proved. Their combination gives the exact logarithmic discriminant lower
bound and constructs the Table 4 description inside Lean. See the
[contour-closure note](docs/audit/v15/22_odlyzko_contour_closure.md).

This package contains Lean 4 proofs, independent Python and Wolfram checks,
extracted v15 inputs, machine-readable results, and an English
[semantic-fidelity audit](docs/audit/v15/12_executive_summary.md).
Its scoped assessment is **Grade B: substantial formalization**.
Independent author, domain, and Lean review remains unsigned.

## Reproduce v15

From this directory in PowerShell:

~~~powershell
& 'D:\AI-Workspace\Environments\Python\math-research\Scripts\python.exe' '.\tools\generate_voight_discriminant_data.py' --check
& 'D:\AI-Workspace\Environments\Python\math-research\Scripts\python.exe' '.\tools\verify_public_v15.py'
& 'C:\Program Files\Wolfram Research\WolframScript\wolframscript.exe' -file '.\checks\v15_classification.wls'
Set-Location '.\lean'
& 'C:\Users\hzlde\.elan\bin\lake.exe' build
& 'C:\Users\hzlde\.elan\bin\lake.exe' env lean '.\TraceEuclideanTest\MainTheoremAudit.lean'
& 'C:\Users\hzlde\.elan\bin\lake.exe' env lean '.\TraceEuclideanTest\NumericalAxiomAudit.lean'
~~~

Expected public computation: 1156 Python PASS and 115 Wolfram PASS, with zero
failures. The Lean project pins Lean 4.32.1 and mathlib. The two audit commands
print main theorem signatures and the separate numerical trust dependencies.
The v15 source-bound checks
are run separately against the author manuscript in a private workspace; their
results are 1165 Python PASS and 112 Wolfram PASS.

## Formal scope

- Theorems 1.2 and 1.3: strict root-discriminant bounds and global finiteness
  with the threshold equal to each varying field's degree. Lean now derives
  the required `b=4` Table 4 inequality from the completed-zeta contour and
  constructs the table description with signature exponents and the
  nonnegative prime-ideal correction. It checks
  the upward rounding and totally real specialization, and needs the row only
  in degrees at least fifteen. The printed unconditional kernel at `b = 4`
  is now defined in Lean; its evenness, nonnegativity, continuity, compact
  support, and integrability are proved. Lean identifies `H` with one third
  of the autocorrelation of the compactly supported bump `1 + cos(pi*x)` and
  proves that the Fourier transform of `H` is real and nonnegative at every
  real frequency. Lean also proves integrability of `1/cosh(x/2)` and the
  exact formula `Fourier(1/cosh(x/2))(w) = 2*pi/cosh(2*pi^2*w)`. Fourier
  scaling and a proved product-to-convolution theorem then show that the
  transform of the complete kernel `F(x) = H(x/4)/cosh(x/2)` is real and
  nonnegative at every real frequency. The source-normalized transform
  `Phi(s) = integral F(x)*exp((s-1/2)*x) dx` now has nonnegative real part for
  every `0 <= Re(s) <= 1`, including the boundary, by an exact tilted-secant
  transform and a compact-support continuity argument. Its reflection identity
  and exact endpoint values `Phi(0) = Phi(1) = 16/3` are also proved. The complete double
  sum over all prime
  ideals and positive exponents is defined in Lean, proved equal to the finite
  box with norm at most 4095 and exponent at most eleven, and proved
  nonnegative. A
  kernel-checked bridge substitutes this complete correction for the
  existential correction in the exact-error and rounded table interfaces.
  The two source-normalized archimedean integrals converge. Their strict
  `A = 36.347` and `B = 16.593` estimates are assembled from analytic
  endpoint bounds and certified dyadic integration. The numerical checks use
  `native_decide`, which adds Lean's native compiler to their trust boundary.
  Lean also proves joint absolute integrability of the critical transform and
  both Gauss-digamma kernels, performs the Fubini interchanges and real-place
  rescaling, and derives the normalized number-field identity
  `log |D_K| - r_1 log A_* - 2 r_2 log B_*` for the symmetric infinite-place
  logarithmic-derivative bracket. It proves fourth-power decay on every fixed
  vertical line, the exact transform of each prime-power Euler term, the
  absolute sum/integral exchange on `Re(s) > 1`, and the identity between the
  transformed actual Dedekind-zeta logarithmic derivative and the complete
  finite-support source correction. Lean then applies the finite weighted
  argument principle on an expanding sequence of zero-free rectangles,
  proves both horizontal sides vanish, folds the vertical sides, evaluates
  the endpoint term as `32/3`, shifts the archimedean term to the critical
  line, and derives the full strict Table 4 inequality. The final numerical
  constants retain the disclosed `native_decide` compiler trust boundary.
- Theorem 1.7: an if-and-only-if classification for every nonzero fractional
  ideal presentation of a positive integral rank-one real-quadratic lattice.
  Lean proves principality, six actual module-isometry classes, six valid
  constructive representatives, and distinction of the classes.
- Corollary 1.9: the square-form field classification m in {2,5,13} is carried
  by the concrete real-quadratic Lean endpoint.
- Corollary 1.6: for each finite p at least 1 and for p = infinity, the
  embedding power mean implies strict trace Euclideanity; the same global
  finiteness theorem gives varying-field and varying-rank finiteness.

[THEOREM_INDEX.md](THEOREM_INDEX.md) lists exact declaration names and remaining
supporting-result gaps. [TRUST.md](TRUST.md) explains the cited source and proof
boundary. [REPRODUCING.md](REPRODUCING.md) gives the full rerun protocol.
The reduced-binary covering-radius formula for Proposition 6.1 trace Gram
forms (whose first diagonal entry is at least 2) is proved on both the real
and rational planes. A separate theorem transfers it to every integral,
totally positive real-quadratic fractional-ideal lattice, alongside the
reduced basis and determinant identity. The two displayed positive-integer
scalar formulas are proved on the full ring of integers, and all clauses are
bundled in one proposition-level Lean theorem. The canonical abstract
rank-one presentation is exported at an arbitrary real trace threshold and
at the manuscript's threshold equal to the field degree. An additional Lean
bridge now handles every totally real ground field: it chooses a code in the
fixed algebraic closure and transports the scalar field, quadratic space,
full lattice, and quadratic form to canonical coordinates. The resulting
actual isometry preserves trace Euclideanity and classic integrality, and rank
one composes with the fractional-ideal presentation at every real threshold.
The induced field isomorphism identifies the integer rings and preserves
rational traces. Lean evaluates the Gamma factor in the Section 4 quantity
`H(n,d)`, encloses its transcendental factors by proved rational bounds, and
checks all 34 by 14 cells. It proves that the analytic classic and integral
inequalities select exactly the recorded 24 and 63 pairs, then proves all row
and column bounds, the exact global maxima, the degree 7--9 rank-two assertion,
and the final rank-twelve consequence. The public Python and Wolfram runs are
    independent checks of the same finite computation. Degrees one and two of
    the small-degree discriminant input are proved internally. In degree two,
    Lean combines Minkowski's bound with positivity and a proof that a
    quadratic field discriminant is not a square in `ℚ`, excluding equality at
    four. In degree three, Lean constructs the projected integer-ring lattice,
    proves its quotient-covolume formula, obtains and lifts the Hunter short
    vector to a nonrational integral generator, identifies its conjugate
    spread, and proves the positive-index discriminant relation. Combined with
    trace normalization and the complete finite enumeration, this gives the
    unconditional Lean theorem `|D_F| >= 49`.
    In degree four, Lean proves the unconditional theorem `|D_F| >= 725`.
    The proof constructs a projected short vector with spread below `35` and,
    when necessary, a second transverse short vector. If either lift generates
    the field, exact normalization and the six-row search reduce it to the
    `2048` or `2304` power order; Lean proves both orders maximal, so each row
    contradicts `|D_F| < 725`. If both lifts generate quadratic subfields,
    their discriminants are each `5` or `8`. Equal discriminants force the two
    subfields to coincide, contrary to transversality; unequal discriminants
    are coprime and the compositum discriminant formula gives
    `|D_F| = 5^2*8^2 = 1600`. Thus degree four has no external premise. The
    earlier sharp-Hermite and relative-different interfaces remain available
    as compatibility reductions.
    Archived Voight degree 5--9 data are hash checked, structurally validated,
    imported, and certified for count and sorted order. In degrees five and
    seven, Lean proves uniform bounds for every coefficient, constructs a
    finite candidate-polynomial set, places every field of root discriminant
    at most 14 in that set, and proves the exact positive-index relation
    `disc(f) = index^2 disc(K)`. Lean derives the exact minima and degree-ten
    exclusion from one explicit source-facing premise
    asserting completeness of Voight's enumeration through root discriminant
    14. Exhausting those finite boxes, treating the composite degrees, and the
    optimized degree-eleven bound 14.083 remain external mathematical inputs.
    Lean checks that the
    weaker online Table 2 value 14.034 would add the integral-table cell
    `(2,11)`, so it cannot replace 14.083 without changing the table.
    Odlyzko's Table 4 is
    retained as the source and normalization
reference, while the `b=4` inequality used here is now derived internally.
Lean proves the
completed-zeta functional equation, a global quadratic exponential growth
bound, the resulting Jensen count of actual zero occurrences, the uniform
fourth-power decay estimate for the exact source transform, and absolute
convergence of the direct unordered zero sum. It proves the ideal Euler
product and nonvanishing on `Re(s) > 1`, expands the ordinary logarithmic
derivative as an absolutely convergent prime-power series, evaluates the
infinite-place logarithmic derivative in terms of digamma, proves the digamma
partial-fraction series, derives the symmetric critical-line bracket, and
proves its complete Gauss-integral, Fourier-inversion, Fubini, and hyperbolic
specialization with the exact `A_*` and `B_*` normalization. It also proves
the arbitrary-line transform of the prime-power series and of the actual zeta
logarithmic derivative, including the justified infinite sum/integral
exchange and exact source prime correction. It
also matches the HSW Gamma
normalization to mathlib's Deligne factors and proves that the completed zeta
function has the same zero positions and multiplicities in the open critical
strip as the pole-removed regularization. Lean checks the test function's
differentiability and derivative decay, and derives the exact
`E = 32/3` integral from the kernel. The source separation and Lean reduction are
recorded in the [Odlyzko source audit](docs/audit/v15/14_odlyzko_source_reduction.md)
and [zero-count literature note](docs/audit/v15/16_zero_count_literature.md);
the [fourth-decay proof](docs/audit/v15/17_odlyzko_fourth_decay.md) records
the new regularity and Fourier argument, while the
[prime-transform certificate](docs/audit/v15/21_odlyzko_prime_transform.md)
records the complete Euler-term and sum/integral bridge, and the
[contour-closure note](docs/audit/v15/22_odlyzko_contour_closure.md)
records the completed argument. The
[analytic boundary progress note](docs/audit/v15/19_analytic_boundary_progress.md)
records the ordered proof tasks and their final status.

## Version scope

The current package publishes only v15 verification artifacts. The Lean
project retains shared foundational modules that are imported by the v15 proof
chain; they are required for the current build and are not a separate release.

Before publication, run the repository-level manuscript-exclusion gate:

~~~powershell
& 'D:\AI-Workspace\Environments\Python\math-research\Scripts\python.exe' '..\tools\check_no_manuscripts.py' --root '..'
~~~
