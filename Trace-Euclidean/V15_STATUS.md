# Trace-Euclidean v15: active Grade B assessment

Frozen author source SHA-256:
83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.
The manuscript is excluded from this public repository.

The complete pinned 8883-job Lean build passes. The v15 public Python and
Wolfram reruns pass 1156 and 115 checks, respectively; private source-bound
reruns pass 1165 and 112 checks. The current 531-declaration main audit uses
only subsets of the standard logical axioms. The 47-declaration numerical
audit separately identifies five Odlyzko and one Voight `native_decide`
dependencies, with their compiler trust disclosed in TRUST.md.
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
PROVISIONAL_MATCH pending independent review; none is marked VERIFIED_MATCH.
Corollary 1.6 and Proposition 6.1 also await independent semantic review.
Abstract-space transport is proved over every totally real number field,
including the scalar field, quadratic space, full lattice, and quadratic
form. The finite Section 4 table arrays and maxima are Lean theorems, and the
analytic interval-to-table-row bridge is kernel checked on all 476 cells. The
specialized unconditional `b = 4` Odlyzko inequality is derived internally
from the completed-zeta functional equation, finite zero sums, contour limits,
and the exact endpoint, archimedean, and prime contributions. Degrees one
through three are internal, including the cubic Hunter projected lattice,
quotient covolume, integral lift, normalization, and finite enumeration. In
degree four, the rank-three projection, exact covolume quotient, integral
lift, normalization, coefficient bounds, field-discriminant bridges, and
finite enumeration are internal. An unconditional Minkowski-ball alternative
now gives spread below 35 and reduces the arithmetic to polynomial
discriminants 725, 1957, 2048, and 2304. Both residual power-order index cases
are closed: Lean proves maximality for the 2048 and 2304 rows and derives a
contradiction whenever a primitive generator satisfies the weak spread bound.
If the first lift is imprimitive, Lean produces a second transverse short
lift. If the second lift is also imprimitive, the two distinct quadratic
subfields have discriminants in `{5,8}`. Equal discriminants force equality of
the subfields; unequal discriminants are coprime and force quartic
discriminant `1600`. Both cases contradict the construction. Hence
`v15_coded_degree_four_discriminant_ge_725` is unconditional and no quartic
source boundary remains. The sharp-Hermite and relative-different routes stay
in the project as compatibility reductions. Voight's archived degree 5--9
discriminant columns are now hash checked, validated, imported, and certified
in Lean. For degrees five and seven, Lean now proves explicit Hunter ball and
all-coefficient bounds, constructs a finite polynomial candidate set, proves
that every field below root discriminant 14 lands in that set, and derives the
computable relation `disc(f) = index^2 disc(K)` with positive index. One
source-facing statement retains the completeness of Voight's enumeration
through root discriminant 14; it implies both the degree 5--9 minima and the
degree-ten exclusion. The optimized degree-eleven bound, a Lean exhaustion of
the finite prime-degree boxes, the composite-degree relative enumeration,
selected supporting lemmas, and independent semantic sign-off remain outside
the current signed scope.
The source-facing degree-at-least-eleven formulation is connected to the
exact Section 4 premise in Lean, and a separate exact check proves that the
weaker online Table 2 value 14.034 would add the integral-table cell `(2,11)`.
The strict tabulated-constant inequalities use a disclosed native-compiler
trust boundary for the interval certificates and the Voight finite-data
certificate.

Start with [README.md](README.md), [THEOREM_INDEX.md](THEOREM_INDEX.md),
and the [v15 audit](docs/audit/v15/12_executive_summary.md).
