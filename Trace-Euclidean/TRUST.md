# Trace-Euclidean v15 trust boundary

Lean accepts the encoded proof terms under Lean 4.32.1 and pinned mathlib
revision 520045ab14e26149ee970e2e617ca04b09bde5d6. The 236
audited main v15 endpoints depend only on the standard logical axioms propext,
Classical.choice, and Quot.sound. The archimedean numerical certificate uses
LeanCert's `native_decide` checks and therefore also trusts Lean's native
compiler. The axiom audit prints five generated `_native.native_decide.ax_*`
dependencies for the final certificate; these are checked separately.
The delivered proof modules contain no sorry, sorryAx, or project axiom.

The global finite-class results can now accept
V15OdlyzkoTable4DescriptionInput, the full published unconditional Table 4
row b=4 with signature exponents and its nonnegative prime-ideal correction.
Lean proves the upward rounding 32/3 <= 10.667, the totally real
specialization |D_F| > 36.347^d exp(-10.667), field-to-class transport, and
that only degrees at least fifteen are needed for global finiteness. The
earlier V15OdlyzkoTable4Input remains as a compatibility interface. The
source's `b=4` unconditional kernel is now formalized directly: Lean proves
its evenness, nonnegativity, continuity, compact support, and integrability.
Lean also proves that `H` is one third of the autocorrelation of the compactly
supported bump `1 + cos(pi*x)`, derives its Fourier transform as one third of
the square of the bump's Fourier transform, and proves that this transform is
real and nonnegative at every real frequency.
The exact prime-ideal summands and the complete sum over all prime ideals and
positive exponents are formalized. Compact support is proved to reduce this
sum exactly to norms at most 4095 and exponents at most eleven, and the full
correction is proved nonnegative. A bridge substitutes this explicit
correction into the exact-error and rounded Table 4 interfaces. Lean proves
the exact Fourier transform of `1/cosh(x/2)`, its strict positivity, the
Fourier scaling of `H(x/4)`, and the product-to-convolution identity for the
complete kernel `F(x) = H(x/4)/cosh(x/2)`. Hence the Fourier transform of `F`
is real and nonnegative at every real frequency. Lean now also evaluates the
transform of `exp(a*x)/cosh(x/2)` for every `-1/2 < a < 1/2`, proves its real
part positive and Fourier-side integrability, and applies convolution to the
complete kernel. Continuity in `a`, obtained from compact support, covers the
two boundary weights. The resulting theorem proves `Re Phi(s) >= 0` for every
`0 <= Re(s) <= 1` in Odlyzko's equation (2.2) normalization. A separate
theorem makes any summable family of such zero contributions nonnegative.
The existence and functional equation of the completed Dedekind zeta function,
the quantitative count of its actual zeros, and the Stark/Weil explicit
formula remain outside the Lean proof. For an entire regularization and a
quantitative ordered zero count, Lean proves paired-zero convergence.
It also proves a finite-height exhaustion of actual multiplicity-aware
strip-zero occurrences and a right interval of constant count after every
height. A continuous count bound established at heights with no strip zero
is transferred to all heights, but the HSW bound at those regular heights
remains an explicit input. Lean proves the
test function's differentiability and derivative decay condition, and derives
the exact `E = 32/3` error integral from the source kernel. It also proves
`Phi(0) = Phi(1) = 16/3` and their sum equals the exact error.
The source-formula reduction states Odlyzko's two archimedean integrals and
equation (2.3) explicitly. Both integrals converge, and strict bounds for the
tabulated `A` and `B` values follow from analytic endpoint estimates and
LeanCert's dyadic interval certificates. Its Table 4 deduction remains
conditional on equation (2.3) and a nonnegative convergent paired-zero sum.

The public Python and Wolfram runs trust their kernels and the extracted
input file. The private maintainer run also checks the SHA-256 digest and
printed entries against the manuscript. Public reruns alone cannot
reconstruct a source file that is intentionally absent.

Theorem 1.7's Lean endpoint covers all nonzero fractional-ideal
presentations. The paper uses the standard representation of an abstract
rank-one lattice by such an ideal and a coefficient. The theorem
GlobalLatticePresentation.rankOne_ideal_bridge_at now exports this
presentation for the canonical rank-one global lattice model, including
positivity, integrality, and the strict trace condition at any real threshold.
Its degree specialization matches the manuscript. The theorem
v15AbstractToCanonicalAnyField adds an actual isometry from any positive-rank
abstract lattice over any totally real number field to a coded canonical
coordinate model, transporting the scalar field, full lattice, and quadratic
form while preserving strict trace Euclideanity and classic integrality;
v15AbstractRankOneIdealBridgeAnyField composes this with the ideal
representation. The field isomorphism identifies the integer rings and
preserves rational traces.
The theorem v15_proposition_six_one_full
exports the general reduced-binary covering
radius and determinant identity for actual fractional ideals and both
positive-integer scalar specializations on the full integer ring. Corollary
1.6 has a varying-field endpoint for finite p >= 1 and p = infinity. These
proofs have the same standard logical axiom dependencies as the existing
endpoints.
The main six-class theorem still uses its direct rational deep-hole argument
and constructive covers for the six survivors.

V15AnalyticTable evaluates the Gamma factor in `H(n,d)`, proves rational
enclosures for pi and the exponential correction, and kernel-checks all 476
rank-degree cells. Its two equivalence theorems prove that the analytic classic
and integral inequalities select exactly the 24 and 63 rows recorded in
V15AdmissibleTables. V15AnalyticTableBridge proves the downstream class-level
membership statements from source-specific field premises. Degree one is
internal. Degrees 2--9 use exact minimum-discriminant data, degree 10 uses the
absence of a totally real field with root discriminant at most 14, degree 11
uses the later optimized bound 14.083, and Table 4 is required only from
degree 12. The online November 1976 Table 2 gives 14.034 at degree 11, so the
value 14.083 is explicitly kept separate from that table. These cited
arithmetic and analytic source theorems remain external; all specialization,
combination, analytic enclosure, and finite-grid classification steps are in
Lean. Python and Wolfram provide independent computational checks.

Compilation and PASS counts do not certify the complete manuscript.
The first-party [v15 semantic audit](docs/audit/v15/12_executive_summary.md)
records definition comparison, hidden assumptions, theorem scope,
reproducibility, and unsigned review cards. Grade B reflects substantial
formalization of the core claims; Grade A is not claimed.
