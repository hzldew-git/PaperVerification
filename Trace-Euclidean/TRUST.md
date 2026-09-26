# Trace-Euclidean v15 trust boundary

Lean accepts the encoded proof terms under Lean 4.32.1 and pinned mathlib
revision 520045ab14e26149ee970e2e617ca04b09bde5d6. The audited endpoints depend
only on the standard logical axioms propext,
Classical.choice, and Quot.sound. The archimedean numerical certificate and
the two imported Voight table-data certificates use `native_decide` checks
and therefore also trust Lean's native compiler. The separate numerical axiom
audit identifies the five generated Odlyzko dependencies and the two
generated Voight-data dependencies.
The delivered proof modules contain no sorry, sorryAx, or project axiom.

The global finite-class results now receive an internally constructed
`V15OdlyzkoTable4DescriptionInput`, matching the published unconditional
Table 4 row `b=4` with signature exponents and its nonnegative prime-ideal
correction.
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
The completed Dedekind-zeta functional equation and a global quadratic
exponential growth bound are now Lean theorems. Jensen's inequality then
proves a coarse quantitative count of actual strip zeros. The sharp HSW
count remains external but is unnecessary for zero-sum convergence. The
completed logarithmic-derivative and reflection bridges are Lean theorems.
Lean now also proves the ideal Euler product and Dedekind-zeta nonvanishing on
`Re(s) > 1`, absolute convergence of the prime-power logarithmic-derivative
series, its equality with the zeta logarithmic derivative, and the full
archimedean logarithmic derivative in terms of digamma. It also checks the
digamma partial-fraction series, conjugation and duplication, and the symmetric
critical-line archimedean bracket. The Gauss integral representation of the
digamma terms, the critical transform's realness and integrability, its
quadratic moment, and the exact Fourier and cosine inversion formulas are Lean
theorems as well. Lean also proves the required Fubini and limiting arguments,
the transformed prime-power matching, the finite weighted argument principle,
the zero-free rectangle sequence, horizontal decay, vertical convergence,
the endpoint residues, and the archimedean line shift. These assemble into
the exact logarithmic discriminant lower bound.
The Apache-2.0 number-field theta/Poisson and Mellin development from
`mathlib-initiative/sum_product` has been ported to the pinned toolchain.
`DedekindZeta.ZetaRegularization` proves the entire normalization factor and
right-half-plane identity with `NumberField.dedekindZeta`; the resulting
`V15DedekindZetaRegularization` is now constructed. The separate
`V15AnalyticMellinBridge` retains its abstract reflection theorem. The
source and exact proof boundary are recorded in
[the continuation note](docs/audit/v15/20_zeta_continuation_construction.md).
For the constructed regularization, the proved growth estimate supplies the
quadratic count on actual zero occurrences. Lean therefore proves absolute
convergence of the direct unordered zero sum and nonnegativity of its real
part. The earlier paired sequence endpoint remains for compatibility but is
not required by the direct-sum reduction.
It also proves a finite-height exhaustion of actual multiplicity-aware
strip-zero occurrences and a right interval of constant count after every
height. A continuous count bound established at heights with no strip zero
is transferred to all heights, but the HSW bound at those regular heights
remains an explicit input. The exact HSW Gamma normalization is identified
with mathlib's Deligne factors, and the resulting completed function has
the same zero positions and analytic multiplicities as the entire
regularization inside the open critical strip. The regularization and the
completed-zeta functional equation now have concrete constructions.
Lean proves the
test function's differentiability and derivative decay condition, and derives
the exact `E = 32/3` error integral from the source kernel. It also proves
`Phi(0) = Phi(1) = 16/3` and their sum equals the exact error.
The source-formula reduction states Odlyzko's two archimedean integrals and
equation (2.3) explicitly. Both integrals converge, and strict bounds for the
tabulated `A` and `B` values follow from analytic endpoint estimates and
LeanCert's dyadic interval certificates. The direct zero sum and its sign are
discharged internally. The completed contour theorem proves the inequality
needed from equation (2.3) directly and constructs the exact-error and rounded
Table 4 interfaces. The analytic part before the numerical `A,B` certificate
uses only `propext`, `Classical.choice`, and `Quot.sound`; the final strict
constants add the five disclosed native-compiler dependencies.

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
membership statements from source-specific field premises. Degrees one and
two are internal. In degree two, Lean proves that the field discriminant is
not a square in `ℚ` and combines this with positivity and Minkowski's lower
bound to obtain `|D_F| >= 5`. For degree three, Lean constructs the projected
integer-ring lattice, proves the quotient-covolume relation, obtains and lifts
the Hunter short vector to a nonrational integral generator, identifies the
conjugate spread, and proves the positive-index discriminant relation. Together
with integral trace normalization and exact finite coefficient enumeration,
this proves `|D_F| >= 49` internally. In degree four, Lean proves the
unconditional lower bound `|D_F| >= 725`. The projected rank-three lattice,
Minkowski short vectors, integral lifts, normalization, exact six-row search,
and maximality of the `2048` and `2304` power orders are internal. If the first
short lift lies in a quadratic subfield, a second transverse lift is produced.
Two imprimitive lifts would generate distinct quadratic subfields of
discriminant `5` and `8`; the coprime-compositum formula would force quartic
discriminant `1600`, a contradiction. The older sharp-Hermite and
relative-different interfaces remain available only as compatibility routes.
The archived Voight tables supply the complete degree 5--10 defining
polynomial rows and the degree 5--9 discriminant columns. Their hashes, row
structure, counts, first entries, sorted order, positive indices, and column
projections are checked. Python uses an exact Bareiss determinant and
Mathematica independently verifies irreducibility, total reality, the
polynomial-discriminant index equation, and the number-field discriminant for
all 2,773 rows. Lean connects the full rows to its exact Hunter filter through
`V15VoightPolynomialDiscriminantInput`; the concrete coefficient-discriminant
equations are not yet Lean-kernel computations. Lean derives the required
minima from one source-facing completeness premise for Voight's enumeration
through root discriminant 14. The same premise proves the required degree-ten
exclusion. It does not yet have an internal Lean proof of the enumeration
algorithm's completeness.
Degree 11 uses the later optimized bound 14.083, and Table 4 is required only
from degree 12. The online November 1976 Table 2 gives 14.034 at degree 11,
so the value 14.083 remains separate from that table. All subsequent
specialization, combination, analytic enclosure, and finite-grid
classification steps are in Lean. Lean also checks that replacing 14.083 by
14.034 would add the integral-table cell `(2,11)`, so the weaker value cannot
support the unchanged manuscript table. Python and Wolfram provide
independent computational checks.

Compilation and PASS counts do not certify the complete manuscript.
The first-party [v15 semantic audit](docs/audit/v15/12_executive_summary.md)
records definition comparison, hidden assumptions, theorem scope,
reproducibility, and unsigned review cards. Grade B reflects substantial
formalization of the core claims; Grade A is not claimed.
