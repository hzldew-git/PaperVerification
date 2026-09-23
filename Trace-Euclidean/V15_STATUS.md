# Trace-Euclidean v15: active Grade B assessment

Frozen author source SHA-256:
83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.
The manuscript is excluded from this public repository.

The complete pinned Lean build passes. The v15 public Python and Wolfram
reruns pass 1156 and 115 checks, respectively; private source-bound reruns
pass 1165 and 112 checks. The 193 previously audited main Lean endpoints use
only standard logical axioms. The new numerical certificate separately uses
`native_decide`, with its compiler trust disclosed in TRUST.md.
Formalization commit 741dc24 passed the [fresh GitHub Actions Lean, Python,
and 95-endpoint axiom run](https://github.com/hzldew-git/PaperVerification/actions/runs/35542188896)
and the [manuscript-exclusion run](https://github.com/hzldew-git/PaperVerification/actions/runs/35542188716).
Formalization commit ee76166 adds cross-field lattice transport and
finite-table theorems. It passed a complete local Lean build and 105-endpoint
axiom audit, followed by the
[fresh GitHub Actions Lean and Python run](https://github.com/hzldew-git/PaperVerification/actions/runs/35581394526)
and the
[manuscript-exclusion run](https://github.com/hzldew-git/PaperVerification/actions/runs/35581394493).
Formalization commit 4ff3057 adds the analytic `H(n,d)` interval bridge and
class-level table membership. It passed the
[fresh GitHub Actions Lean and Python run](https://github.com/hzldew-git/PaperVerification/actions/runs/35607296207)
and the
[manuscript-exclusion run](https://github.com/hzldew-git/PaperVerification/actions/runs/35607296280).
Formalization commit d507fc9 reduces the Odlyzko boundary to the published
Table 4 description, proves its rounding and totally real specialization,
and separates the small-degree literature inputs. It passed the
[fresh GitHub Actions Lean and Python run](https://github.com/hzldew-git/PaperVerification/actions/runs/35614064862)
with 125 audited endpoints and the
[manuscript-exclusion run](https://github.com/hzldew-git/PaperVerification/actions/runs/35614064890).

Formalization commit 69289c1 formalizes the unconditional `b=4` kernel,
identifies `H` as a normalized autocorrelation, proves that its Fourier
transform is real and nonnegative, defines the complete prime-ideal
correction, and reduces that correction exactly to norms at most 4095 and
exponents at most eleven. It substitutes the correction into the Table 4
interface. A complete local 8737-job build and the 149-endpoint axiom audit
pass; the audit reports only propext, Classical.choice, and Quot.sound. It
also passed the
[fresh GitHub Actions Lean, Python, and 149-endpoint axiom run](https://github.com/hzldew-git/PaperVerification/actions/runs/35795731415)
and the
[manuscript-exclusion run](https://github.com/hzldew-git/PaperVerification/actions/runs/35795731409).

Formalization commit 065f2354ff2836890c3159ce93aeb672453deba7 proves integrability and the exact
Fourier transform of `1/cosh(x/2)`, the scaling law for `H(x/4)`, a
product-to-frequency-convolution identity under the required integrability
hypotheses, and the resulting reality and nonnegativity of the Fourier
transform of `F(x)=H(x/4)/cosh(x/2)`. A complete local 8742-job build and the
expanded 164-endpoint axiom audit pass; every audited endpoint again reports
only propext, Classical.choice, and Quot.sound. It also passed the
[fresh GitHub Actions Lean, Python, and 164-endpoint axiom run](https://github.com/hzldew-git/PaperVerification/actions/runs/35800505233)
and the
[manuscript-exclusion run](https://github.com/hzldew-git/PaperVerification/actions/runs/35800504968).

Theorems 1.2 and 1.3 have strict bounds and variable-degree global
finiteness from the explicit cited Odlyzko Table 4 premise. Theorem 1.7
has a two-direction six-class endpoint for all nonzero fractional ideals,
principality, actual isometries, six positive integral strictly Euclidean
representatives, and distinctness. Corollary 1.9 retains its concrete
field-square iff proof. Corollary 1.6 now has a full varying-field p-norm
finiteness endpoint for finite p >= 1 and p = infinity. Proposition 6.1 now
has a combined endpoint for its general fractional-ideal clause and both
integer-scalar formulas. The canonical rank-one-to-ideal bridge now works at
an arbitrary real threshold and at the manuscript's field-degree threshold.

Assessment: SUBSTANTIAL_FORMALIZATION, Grade B. Four main results are
PROVISIONAL_MATCH pending independent review; none is marked
VERIFIED_MATCH. Corollary 1.6 and Proposition 6.1 also await independent
semantic review. Abstract-space transport is now proved over every totally
real number field, including the scalar field, quadratic space, full lattice,
and quadratic form. The finite Section 4 table arrays and maxima are Lean
theorems, and the analytic interval-to-table-row bridge is kernel checked on
all 476 cells. The Odlyzko source interface now mirrors the full Table 4 row,
checks the error-term rounding and totally real specialization, and restricts
the premise to the degrees actually used. Degree one of the small-degree
input is internal; the cited degree 2--11 estimates, the Odlyzko
explicit-formula theorem, selected supporting lemmas, and independent
semantic sign-off remain outside the current signed scope. Within the
explicit-formula theorem, the remaining analytic layers include
Dedekind-zeta continuation and the functional equation, and the Stark/Weil
formula with its convergent paired-zero term. Lean now proves convergence of
both archimedean integrals and the strict tabulated-constant inequalities,
using a disclosed native-compiler trust boundary for the interval certificates.

Start with [README.md](README.md), [THEOREM_INDEX.md](THEOREM_INDEX.md),
and the [v15 audit](docs/audit/v15/12_executive_summary.md).
