# Trace-Euclidean v15 verification package

Active author version: Trace-Euclidean-v15.tex, SHA-256
83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.
The manuscript TeX and PDF are deliberately absent.

This package contains Lean 4 proofs, independent Python and Wolfram checks,
extracted v15 inputs, machine-readable results, and an English
[semantic-fidelity audit](docs/audit/v15/12_executive_summary.md).
Its scoped assessment is **Grade B: substantial formalization**.
Independent author, domain, and Lean review remains unsigned.

## Reproduce v15

From this directory in PowerShell:

~~~powershell
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
  with the threshold equal to each varying field's degree. The finite
  conclusions use [Odlyzko's unconditional Table 4](SOURCES.md) as an explicit
  external mathematical premise. Lean now starts from the table description
  with signature exponents and the nonnegative prime-ideal correction, checks
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
  Equation (2.3) and a convergent paired-zero contribution remain the
  mathematical inputs needed to derive the full Table 4 inequality.
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
independent checks of the same finite computation. Degree one of the
small-degree discriminant input is now proved from Minkowski's bound. The
exact minima in degrees 2--9, the degree-ten enumeration result, the optimized
degree-eleven bound 14.083, and the analytic theorem behind Odlyzko's Table 4
remain explicit external mathematical inputs. Within that last theorem, the
unformalized analytic steps are Dedekind-zeta continuation and its functional
equation, the Stark/Weil explicit formula, and an actual zero count connected
to a height-ordered occurrence enumeration. Lean now proves the uniform
fourth-power decay estimate for the exact source transform and deduces
paired-zero convergence from a quadratic count. It also checks
that the source's explicit multiplicity-aware zero-count inequality reduces to the
quadratic count used by this criterion, conditional on that analytic theorem
and an injective occurrence enumeration. Lean checks the test function's
differentiability and derivative decay, and derives the exact
`E = 32/3` integral from the kernel. The source separation and Lean reduction are
recorded in the [Odlyzko source audit](docs/audit/v15/14_odlyzko_source_reduction.md)
and [zero-count literature note](docs/audit/v15/16_zero_count_literature.md);
the [fourth-decay proof](docs/audit/v15/17_odlyzko_fourth_decay.md) records
the new regularity and Fourier argument.

## Version scope

The current package publishes only v15 verification artifacts. The Lean
project retains shared foundational modules that are imported by the v15 proof
chain; they are required for the current build and are not a separate release.

Before publication, run the repository-level manuscript-exclusion gate:

~~~powershell
& 'D:\AI-Workspace\Environments\Python\math-research\Scripts\python.exe' '..\tools\check_no_manuscripts.py' --root '..'
~~~
