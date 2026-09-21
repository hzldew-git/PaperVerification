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
~~~

Expected public computation: 1156 Python PASS and 115 Wolfram PASS, with zero
failures. The Lean project pins Lean 4.32.1 and mathlib. The last command prints
public theorem signatures and transitive axiom sets. The v15 source-bound checks
are run separately against the author manuscript in a private workspace; their
results are 1165 Python PASS and 112 Wolfram PASS.

## Formal scope

- Theorems 1.2 and 1.3: strict root-discriminant bounds and global finiteness
  with the threshold equal to each varying field's degree. The finite
  conclusions use [Odlyzko's unconditional Table 4](SOURCES.md) as an explicit
  external mathematical premise.
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
independent checks of the same finite computation. The small-degree field
discriminant estimates and Odlyzko's Table 4 remain explicit external
mathematical inputs to the class-level bridge.

## Historical v9 evidence

The prior v9 verification scripts, result summary, manual, and PDF remain
available for comparison. Their [release notes](docs/v9_release_notes/README.md)
and [audit](docs/audit/v9/12_executive_summary.md) are labeled by version.
They are not counted as v15 results.
The root-level build_all.ps1 and run_verification.wls still operate on v9;
the complete immutable v9 package is Git commit
c4aed60cc9405e4570d7b65eb308e8a71d5c7137.

Before publication, run the repository-level manuscript-exclusion gate:

~~~powershell
& 'D:\AI-Workspace\Environments\Python\math-research\Scripts\python.exe' '..\tools\check_no_manuscripts.py' --root '..'
~~~
